//! **A wall that spans days: the kernel's day is the fork's** — stage 6 W-39
//! track K found it (README gap 3556), the W-39 repair closed it (gap 3712).
//!
//! `plan-basic` with one more calendar line — a conference from Tuesday 09:00 to
//! Friday 09:00 — planned on the Wednesday.  Both planners draw the conference
//! clipped to the day (a Wall row 00:00–24:00).  The **fork's**
//! `Planner::window_and_budget` extends §8.1's window by the day's walls clipped
//! to the day, so Wednesday's window ends on THURSDAY morning, inside §8.2's
//! night, and step 3 cuts nothing.  Until the W-39 repair the **kernel's** window
//! read day 0's walls WHOLE (fork `Ctx::walls_on`, quirk (e), kept for the
//! capacity lookahead), ran to FRIDAY, and cut Friday's small hours — while the
//! conference still ran — into slots step 5 filled.  Since the repair
//! `Planner.PlanReq.window` reads `Look.wallsClippedOn`, which is step 1's own
//! clip (`Planner.PlanReq.the_windows_walls_are_the_walls_step_one_places`).
//!
//! The generated classes (`plangen`) draw every wall inside one day, so
//! `planner_invariants`' census and the frozen class comparand never meet this.
//! So the fork's Wednesday is FROZEN BY VALUE here — three instants, the state
//! and the instant carried with each day — and
//! [`the_kernel_plans_the_forks_conference_wednesday`] compares the kernel with
//! it in plain `cargo test --workspace`, outside the region R3 deletes (D21:
//! the instrument before the change).  Inside the region the frozen days are
//! checked against the live fork, and blessed.

mod planner_common;

#[allow(dead_code)]
#[path = "support/forkday.rs"]
mod forkday;

/// The committed history a bless holds its lines against (README gap 4151).
#[allow(dead_code)]
#[path = "support/frozenhist.rs"]
mod frozenhist;

use std::path::Path;

use chrono::{DateTime, NaiveDate};
use chrono_tz::Tz;
use tm_core::dayplan::DayPlan;
use tm_core::energy::Model;
use tm_core::store::{MemStore, RuntimeState, Store};
use tm_core::tree::Tree;

use planner_common::{at, chokepoint, planreq, Fixture};

/// The conference: Tuesday 09:00 to Friday 09:00, beside `plan-basic`'s four walls.
const CONFERENCE: &str = "- [ ] 1 Conference           at:2026-09-08T09:00/2026-09-11T09:00 manual ^c9\n";

fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).expect("a directory");
    for e in std::fs::read_dir(from).expect("the fixture reads") {
        let e = e.expect("an entry");
        let p = e.path();
        let q = to.join(e.file_name());
        if p.is_dir() {
            copy_dir(&p, &q);
        } else {
            std::fs::copy(&p, &q).expect("a copy");
        }
    }
}

/// `plan-basic` with the conference, in a scratch directory, and the Wednesday's
/// state as the binary leaves it on a day nobody has arrived yet (the date and
/// nothing else).
fn conference() -> (tempfile::TempDir, Fixture) {
    let dir = tempfile::tempdir().expect("a scratch directory");
    copy_dir(Path::new(&planner_common::fixture_path("plan-basic")), dir.path());
    let cal = dir.path().join("calendar/2026-W37.md");
    let mut text = std::fs::read_to_string(&cal).expect("the calendar reads");
    text.push_str(CONFERENCE);
    std::fs::write(&cal, text).expect("the calendar writes");
    let store = MemStore::from_dir(dir.path()).expect("the tree reads");
    let plan = store.read_tree().expect("the tree parses");
    let tree = Tree::build(&plan.files, &plan.config);
    let replay = chokepoint::replay_of_text("", plan.config.tz);
    let docs = planreq::docs_of_dir(dir.path());
    let fx = Fixture {
        tree,
        cfg: plan.config,
        replay,
        state: RuntimeState::default(),
        model: Model::default(),
        docs,
        log: String::new(),
    };
    (dir, fx)
}

fn wednesday() -> RuntimeState {
    RuntimeState {
        date: Some(NaiveDate::from_ymd_opt(2026, 9, 9).expect("a date")),
        ..RuntimeState::default()
    }
}

/// The work rows of `day` that start in `[lo, hi)`.
fn work_in(day: &DayPlan, lo: DateTime<Tz>, hi: DateTime<Tz>) -> usize {
    day.segments.iter().filter(|s| s.kind.is_work() && lo <= s.start && s.start < hi).count()
}

/// The frozen conference Wednesday: one JSON line per instant, `{name, state, now, hash, day}`
/// (`forkday::basic_line`'s shape), each day the fork's as the shipped binary plans it (D53).
const FROZEN_CONFERENCE: &str = "fork-4748911-planner-conference.jsonl";

/// The instants the Wednesday is planned at: before, inside and after the lecture's afternoon.
const INSTANTS: [(u32, u32); 3] = [(8, 0), (13, 0), (20, 0)];

fn frozen_conference() -> Vec<serde_json::Value> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(FROZEN_CONFERENCE);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("{}: {e}", path.display()))
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).expect("a frozen conference day is JSON"))
        .collect()
}

/// **The kernel plans the fork's conference Wednesday, by value** (README gaps 3556
/// and 3712).  Every frozen day — the state and the instant it carries, planned
/// by the kernel through the FFI — is the fork's: the date, the window, the
/// budget, every diagnostic, every row in order and the hash.  And the window
/// ends before Friday with no work planned after the day's start, so the kernel
/// plans nothing inside the conference.  This arm names no fork planner and
/// survives R3.
#[test]
fn the_kernel_plans_the_forks_conference_wednesday() {
    let (_dir, fx) = conference();
    let lines = frozen_conference();
    assert_eq!(lines.len(), INSTANTS.len(), "one frozen day per instant");
    let mut t = forkday::DayTally::default();
    let mut findings = Vec::new();
    for line in &lines {
        let name = line["name"].as_str().expect("a name");
        let state: RuntimeState = serde_json::from_value(line["state"].clone()).expect("a state");
        let now = DateTime::parse_from_rfc3339(line["now"].as_str().expect("an instant"))
            .expect("an instant")
            .with_timezone(&fx.cfg.tz);
        let d = fx.kernel_day(&state, now).unwrap_or_else(|e| panic!("{name}: the kernel did not plan: {e}"));
        assert!(d.window.1 < at("2026-09-11", 0, 0), "{name}: the kernel's window ends {}", d.window.1);
        assert_eq!(work_in(&d, at("2026-09-09", 0, 0), at("2026-09-12", 0, 0)), 0, "{name}: the kernel planned work");
        let date = tm_core::planwire::plan_date(&state, now);
        let cands = tm_core::priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, date, now);
        let w = planreq::World { docs: &fx.docs, log: &fx.log, tree: &fx.tree, cfg: &fx.cfg, state: &state, now, cands: &cands, replay: &fx.replay };
        let (k, _) = planreq::kernel_day(&w, None).unwrap_or_else(|e| panic!("{name}: the kernel did not plan: {e}"));
        findings.extend(forkday::compare_day_with_fork(name, &k, line, now, &mut t));
    }
    println!("{}", t.line("the conference Wednesday", findings.len()));
    forkday::no_disagreement(&findings);
    assert_eq!((t.days, t.hashes_equal), (INSTANTS.len(), INSTANTS.len()), "{t:?}");
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gaps 3556, 3712)
/// The fork's conference Wednesday at `now`, ranked by the kernel's §7 as the binary ranks it (D53).
fn fork_conference_day(fx: &Fixture, state: &RuntimeState, now: DateTime<Tz>) -> DayPlan {
    let day = tm_core::planwire::plan_date(state, now);
    let cands = tm_core::priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, day, now);
    let w = planreq::World { docs: &fx.docs, log: &fx.log, tree: &fx.tree, cfg: &fx.cfg, state, now, cands: &cands, replay: &fx.replay };
    let (_, ans) = planreq::kernel_day(&w, None).expect("the kernel ranks the day");
    tm_core::planner::plan(&fx.input(state, now).with_ranking(&cands, &ans.prios))
}

/// **The fork's Wednesday ends on Thursday, inside the night, and plans no work —
/// and the frozen days ARE the fork's today.**  Each frozen line is recomputed
/// from the live fork and must be byte-equal; a line the fork answers
/// differently is a finding, never a line to rewrite (D64).
#[test]
fn the_fork_ends_the_wednesday_inside_the_night() {
    let (_dir, fx) = conference();
    let state = wednesday();
    let lines = frozen_conference();
    assert_eq!(lines.len(), INSTANTS.len());
    for ((h, m), line) in INSTANTS.iter().zip(&lines) {
        let now = at("2026-09-09", *h, *m);
        let f = fork_conference_day(&fx, &state, now);
        assert!(f.window.1 < at("2026-09-11", 0, 0), "{h:02}:{m:02}: the fork's window ends {}", f.window.1);
        assert_eq!(work_in(&f, at("2026-09-09", 0, 0), at("2026-09-12", 0, 0)), 0, "{h:02}:{m:02}: the fork planned work");
        let want = forkday::basic_line(&format!("wednesday {h:02}:{m:02}"), &state, now, &f);
        assert_eq!(want.trim_end(), serde_json::to_string(line).expect("a line"), "{h:02}:{m:02}: the frozen day is not the fork's today");
    }
}

/// **Freeze the conference Wednesday** — inert without `TM_PLANNER_BLESS_CONFERENCE`.
/// Writes a line for every instant the file does not hold and REFUSES, by name, to
/// change one it holds (D64; its lines record no departure, so D85's D64(c) reaches none).
/// What a line is held against is the file's COMMITTED history (W-42 track C, README gap 4151;
/// `frozenhist::held`), never the working copy, so deleting the file is not a fresh freeze; a
/// line HEAD holds that no instant draws is refused.  After R3 it is gone with the region and the
/// file is final.
#[test]
#[ignore]
fn the_frozen_conference_days_are_blessed() {
    if std::env::var_os("TM_PLANNER_BLESS_CONFERENCE").is_none() {
        eprintln!("inert: set TM_PLANNER_BLESS_CONFERENCE=1 to write {FROZEN_CONFERENCE}");
        return;
    }
    let (_dir, fx) = conference();
    let state = wednesday();
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(FROZEN_CONFERENCE);
    let held = frozenhist::held(&path, frozenhist::key_of("name")).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", held.census(FROZEN_CONFERENCE));
    let (mut out, mut names) = (String::new(), Vec::new());
    for (h, m) in INSTANTS.iter() {
        let now = at("2026-09-09", *h, *m);
        let name = format!("wednesday {h:02}:{m:02}");
        let line = forkday::basic_line(&name, &state, now, &fork_conference_day(&fx, &state, now));
        if let Some(old) = held.ever.get(&name) {
            assert_eq!(old.raw.as_str(), line.trim_end(), "{h:02}:{m:02}: a held line is not rewritten (held since {})", old.sha);
        }
        names.push(name);
        out.push_str(&line);
    }
    let stale: Vec<&String> = held.head.iter().filter(|n| !names.contains(n)).collect();
    assert!(stale.is_empty(), "frozen lines no instant draws any more: {stale:?}");
    std::fs::write(&path, out).expect("the frozen conference days are written");
}
// END THE FORK PLANNER
