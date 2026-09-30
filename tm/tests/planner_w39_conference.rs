//! **A wall that spans days: the kernel's day and the fork's disagree** — stage 6
//! W-39 track K (README gap 3556).
//!
//! `plan-basic` with one more calendar line — a conference from Tuesday 09:00 to
//! Friday 09:00 — planned on the Wednesday.  Both planners draw the conference
//! clipped to the day (a Wall row 00:00–24:00), and there they part:
//!
//! * the **fork's** `Planner::window_and_budget` extends §8.1's window by the day's
//!   walls clipped to the day, so Wednesday's window ends on THURSDAY morning,
//!   inside §8.2's night, and step 3 cuts nothing;
//! * the **kernel's** window is day 0's (`Planner.PlanReq.window` reads
//!   `Look.day0Window`, fork `Ctx::walls_on`'s unclipped walls — quirk (e), README
//!   gap 85, ported for the capacity lookahead), which runs to FRIDAY, and step 3
//!   cuts Friday's small hours — while the conference still runs — into slots that
//!   step 5 fills.
//!
//! The generated classes (`plangen`) draw every wall inside one day, so
//! `planner_invariants`' census and the frozen class comparand never meet this.
//! [`the_kernel_plans_inside_a_wall_that_spans_days`] PINS the kernel's half and
//! fails the day its window is the fork planner's; the fork's half is in the one
//! region R3 deletes.

mod planner_common;

#[allow(dead_code)]
#[path = "support/forkday.rs"]
mod forkday;

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

/// **The kernel's Wednesday runs to Friday and puts work inside the conference.**
/// At 08:00 and at 13:00 the kernel's window ends on Friday, and work rows start
/// on Friday before 09:00, while the conference the calendar holds still runs; at
/// 20:00 the window has closed and there is none.  Pinned: this fails the day the
/// kernel's window is the fork planner's (README gap 3556).
#[test]
fn the_kernel_plans_inside_a_wall_that_spans_days() {
    let (_dir, fx) = conference();
    let state = wednesday();
    let friday = at("2026-09-11", 0, 0);
    let conference_ends = at("2026-09-11", 9, 0);
    for (h, m) in [(8, 0), (13, 0)] {
        let now = at("2026-09-09", h, m);
        let k = fx.kernel_day(&state, now).unwrap_or_else(|e| panic!("{h:02}:{m:02}: the kernel did not plan: {e}"));
        assert!(k.window.1 > friday, "{h:02}:{m:02}: the kernel's window ends {} — not past the night", k.window.1);
        let inside = work_in(&k, friday, conference_ends);
        assert!(inside > 0, "{h:02}:{m:02}: no work row starts on Friday before the conference ends");
        println!(
            "kernel at {h:02}:{m:02}: window ends {}, {inside} work row(s) inside the conference on Friday",
            k.window.1.format("%a %H:%M")
        );
    }
    let k = fx.kernel_day(&state, at("2026-09-09", 20, 0)).expect("the kernel plans the evening");
    assert_eq!(work_in(&k, at("2026-09-09", 0, 0), at("2026-09-12", 0, 0)), 0, "work planned after the window closed");
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gap 3556)
/// **The fork's Wednesday ends on Thursday, inside the night, and plans no work.**
/// Its window is the day's walls clipped to the day, so it ends before Friday, and
/// no work row starts after the day's start — the day the kernel's window is the
/// fork planner's, [`the_kernel_plans_inside_a_wall_that_spans_days`] fails and
/// this is the comparison it should become.
#[test]
fn the_fork_ends_the_wednesday_inside_the_night() {
    let (_dir, fx) = conference();
    let state = wednesday();
    for (h, m) in [(8, 0), (13, 0)] {
        let now = at("2026-09-09", h, m);
        let day = tm_core::planwire::plan_date(&state, now);
        let cands = tm_core::priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, day, now);
        let w = planreq::World { docs: &fx.docs, log: &fx.log, tree: &fx.tree, cfg: &fx.cfg, state: &state, now, cands: &cands };
        let (k, ans) = planreq::kernel_day(&w, None).unwrap_or_else(|e| panic!("{h:02}:{m:02}: the kernel did not plan: {e}"));
        let f = tm_core::planner::plan(&fx.input(&state, now).with_ranking(&cands, &ans.prios));
        assert!(f.window.1 < at("2026-09-11", 0, 0), "{h:02}:{m:02}: the fork's window ends {}", f.window.1);
        assert_eq!(work_in(&f, at("2026-09-09", 0, 0), at("2026-09-12", 0, 0)), 0, "{h:02}:{m:02}: the fork planned work");
        let frozen = serde_json::json!({"day": serde_json::to_value(&f).expect("a day serialises"), "hash": f.hash()});
        let mut t = forkday::DayTally::default();
        let findings = forkday::compare_day_with_fork(&format!("{h:02}:{m:02}"), &k, &frozen, now, &mut t);
        assert!(!findings.is_empty(), "{h:02}:{m:02}: the kernel's day is the fork's");
        println!("fork at {h:02}:{m:02}: window ends {}; {} finding(s) against the kernel", f.window.1.format("%a %H:%M"), findings.len());
    }
}
// END THE FORK PLANNER
