//! §8 end to end on the fixture days (§17.1, M4's definition of done):
//! `plan-basic` with an early start, `plan-basic` with a late start and the
//! 12:50 wall, `plan-home-day` (the `home_max_ci` cap) and `plan-travel-day`
//! (a `buffer:2h travel-day` flight zeroing the budget).
//!
//! # Two arms since stage 6 W-35 (README gap 2722)
//!
//! **The arm that survives R3** plans the four days with the **kernel** —
//! through `tm_core::planwire`, the codec R3 swaps into the binary — and
//! compares each day, by value, with the fork's day frozen into
//! `tests/fixtures/` (`support/forkday.rs`): the fork as the shipped binary
//! runs it, ranked by the kernel's own grants (D53). It then holds the kernel's
//! day to the same §8 properties the fork's day is held to — the functions
//! below are one set, read by both arms. Nothing in it reaches the fork's
//! planner, so R3's deletion leaves it building, running and comparing.
//!
//! **The fork's arm** — its four tests, their timeline and diagnostics
//! snapshots and the re-bless of the frozen days — plans with
//! `planner::plan` and its own §7 pass. It is one region, `BEGIN THE FORK
//! PLANNER` … `END THE FORK PLANNER`, and R3 deletes it whole;
//! [`the_fork_half_of_this_suite_is_one_region`] holds this file and
//! `planner_common` to that.
//!
//! What the kernel's day may differ from the fork's by is nothing: the two
//! classes it did differ by (gaps 551 and 435, `support/forkday.rs`) CLOSED at
//! W-37 (track R), and their rows are compared by value and counted exactly.

mod planner_common;

#[allow(dead_code)]
#[path = "support/planreq.rs"]
mod planreq;

#[allow(dead_code)]
#[path = "support/forkday.rs"]
mod forkday;

/// The committed history a bless holds its lines against (README gap 4151).
#[allow(dead_code)]
#[path = "support/frozenhist.rs"]
mod frozenhist;

use chrono::{DateTime, NaiveTime};
use chrono_tz::Tz;
use planner_common::{
    assert_break_rule, at, basic_state, date, fixture_path, load, load_with_log, timeline, Fixture,
    BASIC_LOG,
};
use tm_core::dayplan::{DayPlan, SegKind, Segment};
use tm_core::priority::{self, Candidate};
use tm_core::store::RuntimeState;

// ---------------------------------------------------------------------------
// The four fixture days, named once
// ---------------------------------------------------------------------------

/// One fixture day: the tree, the log it is read with (the fixture's own when
/// `None`), the runtime state (the fixture's own `.tm/state.json` when
/// `None`) and the instant it is planned at.
struct FixtureDay {
    name: &'static str,
    fixture: &'static str,
    log: Option<&'static str>,
    state: Option<fn() -> RuntimeState>,
    h: u32,
    m: u32,
}

/// `plan-basic` arriving at 10:30 with the 12:50–13:50 meeting ahead.
fn late_state() -> RuntimeState {
    RuntimeState {
        date: Some(date("2026-09-07")),
        wake: Some(NaiveTime::from_hms_opt(9, 0, 0).expect("time")),
        arrival: Some(NaiveTime::from_hms_opt(10, 30, 0).expect("time")),
        loc: Some("lounge".to_string()),
        ..RuntimeState::default()
    }
}

const DAYS: [FixtureDay; 4] = [
    FixtureDay { name: "plan-basic early 07:00", fixture: "plan-basic", log: Some(BASIC_LOG), state: Some(basic_state), h: 7, m: 0 },
    FixtureDay { name: "plan-basic late 10:30", fixture: "plan-basic", log: Some(BASIC_LOG), state: Some(late_state), h: 10, m: 30 },
    FixtureDay { name: "plan-home-day 09:00", fixture: "plan-home-day", log: None, state: None, h: 9, m: 0 },
    FixtureDay { name: "plan-travel-day 07:00", fixture: "plan-travel-day", log: None, state: None, h: 7, m: 0 },
];

/// A fixture day, loaded: the tree, its documents and log, the state, the
/// instant and the candidates the request sends.
struct Loaded {
    fx: Fixture,
    docs: Vec<(String, String)>,
    log: String,
    state: RuntimeState,
    now: DateTime<Tz>,
    cands: Vec<Candidate>,
}

impl Loaded {
    fn of(d: &FixtureDay) -> Loaded {
        let fx = match d.log {
            Some(l) => load_with_log(d.fixture, Some(l)),
            None => load(d.fixture),
        };
        let log = match d.log {
            Some(l) => l.to_string(),
            None => std::fs::read_to_string(format!("{}/.tm/log.jsonl", fixture_path(d.fixture))).unwrap_or_default(),
        };
        let state = d.state.map_or_else(|| fx.state.clone(), |f| f());
        let now = at("2026-09-07", d.h, d.m);
        let cands = priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, date("2026-09-07"), now);
        let docs = planreq::docs_of_dir(std::path::Path::new(&fixture_path(d.fixture)));
        Loaded { fx, docs, log, state, now, cands }
    }

    fn world(&self) -> planreq::World<'_> {
        planreq::World {
            docs: &self.docs,
            log: &self.log,
            tree: &self.fx.tree,
            cfg: &self.fx.cfg,
            state: &self.state,
            now: self.now,
            cands: &self.cands,
            replay: &self.fx.replay,
        }
    }
}

// ---------------------------------------------------------------------------
// §8's properties of each day — one set, held by both arms
// ---------------------------------------------------------------------------

/// **(a) `plan-basic`, early start** — §4.3's day, planned at 07:00 from
/// `.tm/state.json` (`window 07:00..16:00`, `budget 6`, lounge) with the log
/// the fixture ships (wake 06:05, breakfast done, arrive 07:00).
///
/// Every difference from the §4.3 printed timeline, and why the spec's own
/// steps produce it:
///
/// 1. **§4.3 works the tasks `^t1 ^t3 ^t4 ^t5`; this plan works `^t3 ^m1
///    ^m2`.** §6.2 makes every open line of `week/` a candidate, milestones
///    included, and `^m1`/`^m2` carry their own `6b` estimate; §7.4 then ranks
///    `^m1` (`!1`, `ci 5`) above the `ci 3` tasks. Nothing in §7 or §8 hides a
///    parent whose children are also candidates, so the high-energy morning
///    goes to the milestone. (§6.4's rollup means the same minutes are counted
///    twice — once on `^m1`, once on its child `^t3`. That is a property of
///    `priority::collect_candidates`, not of the planner.)
/// 2. **§4.3's second row, "Read ch.6 §3", is not in the week file at all**,
///    so no plan can produce it.
/// 3. **§4.3 puts "Pick up package" at 15:10; here it is at 09:00.** `^a3` is
///    a `win:…T09:00/21:00` instance whose window closes today, so §5.2 makes
///    it mandatory and §8.2 step 2 places it at the earliest feasible position
///    in its window — before the tasks, which is exactly what "placed before
///    any task" means.
/// 4. **§4.3's lunch is at 11:20, ten minutes before its own `win:11:30`.**
///    Step 2 places it at 11:30.
/// 5. **§4.3 has no workout, laundry, groceries or shower row.** `routines.md`
///    has all four; the Monday workout is mandatory (its window closes today)
///    and lands at 16:00, and the three deferred ones take the lowest-energy
///    free positions of the evening (§8.2 step 6).
/// 6. **§4.3 breaks at 09:00 and at 13:50.** A rest of at least `break_min`
///    satisfies a pending break, so `^a3`'s 20-minute routine at 09:00 *is*
///    the first break and lunch (30m, 11:30) is the second. The counter is
///    therefore back to zero at 12:00; the 12:50 wall is not work and does not
///    move it; and the two blocks that follow — 12:00 and 13:50 — earn the
///    break at 14:50, drawn as the day's one Break row, 14:50–15:10. (Until
///    W-37 the kernel kept those 20 minutes free and drew no row — gap 551 —
///    so the row was asserted in the fork's arm only; both arms assert it now.)
/// 7. **§4.3 marks two blocks `✓` and one `▶`, and shows `(67m)` actuals.**
///    Those are log facts; at 07:00 the log holds only wake, breakfast and
///    arrive.
/// 8. **§4.3's `2b×1.6`** needs a learned `model.json`; the fixture ships
///    none, so every multiplier here is 1.
/// 9. **§4.3's `15:10 ─── window ends 16:00` divider** is an `emit.rs` row,
///    not a segment.
fn check_basic_early(day: &DayPlan, fx: &Fixture, now: DateTime<Tz>) {
    assert_eq!(day.window, (at("2026-09-07", 7, 0), at("2026-09-07", 16, 0)));
    assert_eq!(day.budget_blocks, 6);
    // §8.3: no overbooking.
    assert!(day.block_minutes() <= 6 * 60, "{}", day.block_minutes());
    // The 12:50 meeting is where the calendar says.
    let wall = day
        .segments
        .iter()
        .find(|s| s.kind == SegKind::Wall)
        .expect("the meeting is a wall");
    assert_eq!(wall.start, at("2026-09-07", 12, 50));
    assert_eq!(wall.end, at("2026-09-07", 13, 50));
    // Lunch is inside 11:30–13:30.
    let lunch = day
        .segments
        .iter()
        .find(|s| s.item.as_ref().is_some_and(|i| i.as_str() == "lunch"))
        .expect("lunch is placed");
    assert!(lunch.start >= at("2026-09-07", 11, 30));
    assert!(lunch.end <= at("2026-09-07", 13, 30));
    // §8.2 step 3's rule: never more than `break_after_blocks` blocks in a row
    // without a rest of `break_min`, whatever fills it.
    assert_break_rule(day, now, &fx.cfg);
    // …and the one Break row the cut keeps, 14:50–15:10 (item 6 above), drawn
    // on both arms since W-37 (README gap 551 closed).
    let breaks: Vec<&Segment> = day.segments.iter().filter(|s| s.kind == SegKind::Break).collect();
    assert_eq!(breaks.len(), 1, "{}", timeline(day));
    assert_eq!((breaks[0].start, breaks[0].end), (at("2026-09-07", 14, 50), at("2026-09-07", 15, 10)));
    // §8.2 step 8: what this day could not do.
    assert_eq!(
        day.diagnostics.blocked,
        vec![(
            tm_core::model::Id::new("t5"),
            vec![tm_core::model::Dep::Item(tm_core::model::Id::new("t4"))]
        )]
    );
    assert_eq!(day.diagnostics.waiting, vec![tm_core::model::Id::new("a4")]);
    assert!(!day.diagnostics.dropped_tail.is_empty());
    assert_eq!(day.diagnostics.rest_debt_min, 0, "no break was cut today");
    // §11: the day opens three milestones it cannot finish, so plan honesty is
    // well above the 1.1 the monitor warns at (see `Diagnostics::plan_honesty`).
    let honesty = day.diagnostics.plan_honesty.expect("a six-block budget");
    assert!((honesty - 780.0 / 360.0).abs() < 0.01, "{honesty}");
    // Nothing works after wind-down.
    let wind = at("2026-09-07", 21, 30);
    assert!(!day
        .segments
        .iter()
        .any(|s| s.kind.is_work() && s.end > wind));
}

/// **(b) `plan-basic`, late start with a wall** — arriving at 10:30 with the
/// 12:50–13:50 meeting ahead: §8.1's window is `min(10:30 + 8h, 19:00) + 1h
/// wall = 19:30`, the budget is unchanged (§8.1: "a late start gets a later end
/// and the same budget formula"), and the morning simply is not there.
fn check_basic_late(day: &DayPlan, fx: &Fixture, now: DateTime<Tz>) {
    assert_break_rule(day, now, &fx.cfg);
    // §8.1: the wall inside the window pushes the end out by its duration.
    assert_eq!(day.window.0, at("2026-09-07", 10, 30));
    assert_eq!(day.window.1, at("2026-09-07", 19, 30));
    assert_eq!(day.budget_blocks, 6);
    assert!(day.block_minutes() <= 6 * 60);
    // Nothing is *planned* before `now` (what is there came from the log),
    // and nothing overlaps the wall.
    for seg in &day.segments {
        if seg.end > now
            && matches!(
                seg.kind,
                SegKind::Block | SegKind::Batch(_) | SegKind::Rest | SegKind::Break
            )
        {
            assert!(seg.start >= now, "{seg:?}");
        }
        if seg.kind.is_work() {
            assert!(
                seg.end <= at("2026-09-07", 12, 50) || seg.start >= at("2026-09-07", 13, 50),
                "{seg:?}"
            );
        }
    }
}

/// **(c) `plan-home-day`** — the same tree at home (§8.2 step 3's
/// `min(energy, home_max_ci)`): no slot is worth more than `ci 3`, so the
/// `ci 4`/`ci 5` milestones cannot be started at all and the low-`ci` work
/// rises to the top. `state.json` stores no window here, so §8.1's formula
/// runs: `09:00 + 8h = 17:00`, plus the 12:50 meeting, is 18:00.
fn check_home_day(day: &DayPlan, fx: &Fixture, now: DateTime<Tz>) {
    assert_eq!(day.window, (at("2026-09-07", 9, 0), at("2026-09-07", 18, 0)));
    assert_eq!(day.budget_blocks, 6);
    assert_break_rule(day, now, &fx.cfg);
    // §8.2 step 3: the home cap holds every slot at or below `home_max_ci`.
    for seg in day.segments.iter().filter(|s| s.energy.is_some()) {
        assert!(
            seg.energy.expect("checked") <= fx.cfg.location.home_max_ci,
            "{seg:?}"
        );
    }
    // §8.3's energy filter, on the items that did get a block.
    for seg in day.segments.iter().filter(|s| s.kind.is_work()) {
        let energy = seg.energy.expect("a block has an energy");
        for id in seg.items() {
            let ci = fx.tree.get(&id).map_or(0, |i| i.ci);
            assert!(ci <= energy, "{id} ci {ci} in a slot of {energy}");
        }
    }
}

/// **(d) `plan-travel-day`** — a `buffer:2h travel-day` flight at 08:15: the
/// blocked time starts at 06:15 (clipped to the window at 07:00), and §8.2 step
/// 1's "travel-day zeroing" takes the whole block budget away — routines, walls
/// and optionals stay, no Block is planned.
fn check_travel_day(day: &DayPlan, _fx: &Fixture, _now: DateTime<Tz>) {
    assert_eq!(day.block_minutes(), 0, "a travel day plans no blocks");
    assert!(day
        .diagnostics
        .notes
        .iter()
        .any(|n| n.contains("travel day")));
    // The flight and its buffer are both walls, and neither moved.
    let walls: Vec<&Segment> = day
        .segments
        .iter()
        .filter(|s| s.kind == SegKind::Wall && s.item.as_ref().is_some_and(|i| i.as_str() == "g3"))
        .collect();
    assert_eq!(walls.len(), 2, "buffer + flight");
    assert_eq!(walls[0].start, at("2026-09-07", 6, 15)); // the `buffer:2h`
    assert_eq!(walls[1].start, at("2026-09-07", 8, 15));
    assert_eq!(walls[1].end, at("2026-09-07", 10, 40));
}

/// The day's own properties, by its name.
fn check(d: &FixtureDay, day: &DayPlan, fx: &Fixture, now: DateTime<Tz>) {
    match d.name {
        "plan-basic early 07:00" => check_basic_early(day, fx, now),
        "plan-basic late 10:30" => check_basic_late(day, fx, now),
        "plan-home-day 09:00" => check_home_day(day, fx, now),
        "plan-travel-day 07:00" => check_travel_day(day, fx, now),
        other => panic!("no properties are written for `{other}`"),
    }
}

// ---------------------------------------------------------------------------
// The arm that survives R3: the kernel's day, the frozen fork's day
// ---------------------------------------------------------------------------

/// **The kernel plans the four fixture days the fork planned** — by value,
/// against the fork's days frozen before R3 (README gap 2722), and each held
/// to §8's properties above.
///
/// The two classes this arm bounded EXACTLY at W-35 — three planned breaks the
/// kernel did not draw (gap 551: every day but the travel day, whose budget is
/// zero) and four `⚠` marks it did not set (gap 435: `^a3`'s row on every
/// day) — CLOSED at W-37 (track R). The same three rows and four marks are now
/// COMPARED BY VALUE and counted exactly, and all four days hash alike (one of
/// four did while the breaks were missing). A frozen set that moves fails here.
#[test]
fn the_kernel_plans_the_fixture_days_the_fork_planned() {
    let frozen = forkday::frozen_days();
    let mut t = forkday::DayTally::default();
    let mut findings = Vec::new();
    for d in &DAYS {
        let l = Loaded::of(d);
        let (k, _) = planreq::kernel_day(&l.world(), None).unwrap_or_else(|e| panic!("{}: {e}", d.name));
        match frozen.get(d.name) {
            Some(fork) => findings.extend(forkday::compare_day_with_fork(d.name, &k, fork, l.now, &mut t)),
            None => t.skipped += 1,
        }
        check(d, &k.day, &l.fx, l.now);
    }
    println!("{}", t.line("planner_fixtures", findings.len()));
    forkday::no_disagreement(&findings);
    assert_eq!((t.days, t.skipped), (4, 0), "every day was compared: {t:?}");
    assert_eq!(t.rows, 73, "the fork's four days hold 73 rows: {t:?}");
    assert_eq!(t.break_rows_551, 3, "planned break rows compared by value (gap 551 closed): {t:?}");
    assert_eq!(t.hot_marks_435, 4, "routine `⚠` marks compared by value (gap 435 closed): {t:?}");
    // Gap 550's class needs a running block, and no fixture day holds one; the
    // classes that do are `planner_classes.rs`' (W-36 track H, gap 2925).
    assert_eq!(t.mult_rows_550, 0, "gap 550's rows on a day with nothing running: {t:?}");
    // No fixture day holds an under-used row, so the by-design note class is
    // bounded at zero here; the generated classes carry it (W-36 track H).
    assert_eq!(t.underused_notes, 0, "under-used notes on the fixture days: {t:?}");
    assert_eq!(t.hashes_equal, 4, "every day hashes as the fork's, its breaks drawn (gap 551 closed): {t:?}");
}

/// **R3's deletion is mechanical here**: every line of this file and of
/// `planner_common` that reaches the fork's planner sits inside its one
/// `BEGIN THE FORK PLANNER` … `END THE FORK PLANNER` region, so R3 deletes
/// the two regions and the arm above still builds. With the regions gone, no
/// reference may remain — this test is then the assertion that the comparand
/// really moved.
#[test]
fn the_fork_half_of_this_suite_is_one_region() {
    let here = env!("CARGO_MANIFEST_DIR");
    for file in ["tests/planner_fixtures.rs", "tests/planner_common/mod.rs"] {
        let text = std::fs::read_to_string(format!("{here}/{file}")).expect("the source reads");
        let scan = forkday::fork_scan(&text);
        assert!(scan.escapes.is_empty(), "{file}: the fork reached outside its region:\n  {}", scan.escapes.join("\n  "));
        assert!(scan.deleted || scan.region_bytes > 0, "{file}: an empty region");
    }
}

/// **The scan bites, both ways** (AGENTS §5.8): a check nothing can fail is
/// decoration, and a check a legitimate file fails is a trapdoor. The banners
/// and the needles are spelled into the sources below by pieces, so this file
/// never holds one outside its own region — the scan above reads this file too.
#[test]
fn the_fork_scan_sees_a_reference_outside_its_region_and_only_there() {
    let b = ["// BEGIN THE FORK", " PLANNER\n"].concat();
    let e = ["// END THE FORK", " PLANNER\n"].concat();
    let call = ["    let d = ", "planner", "::plan(&x);\n"].concat();
    let quiet = ["    let d = 1;\n    // a comment may name ", "planner", "::plan freely\n"].concat();
    let quiet = quiet.as_str();
    // Inside the region: nothing escapes.
    let inside = format!("{quiet}{b}{call}{e}{quiet}");
    let scan = forkday::fork_scan(&inside);
    assert!(scan.escapes.is_empty() && !scan.deleted && scan.region_bytes > 0, "{:?}", scan.escapes);
    // The same line below the region: it escapes, by line.
    let outside = format!("{quiet}{b}{e}{call}");
    assert_eq!(forkday::fork_scan(&outside).escapes.len(), 1);
    // After R3 (no banners): any reference at all is an escape, and none is clean.
    let after = format!("{quiet}{call}");
    let scan = forkday::fork_scan(&after);
    assert!(scan.deleted && scan.escapes.len() == 1, "{:?}", scan.escapes);
    assert!(forkday::fork_scan(quiet).escapes.is_empty());
    // The fixture's own builder is a needle too, however it is reached.
    let input = ["    let i = fx.", "input(&state, now);\n"].concat();
    assert_eq!(forkday::fork_scan(&format!("{b}{e}{input}")).escapes.len(), 1);
    // A needle or a banner spelled inside a STRING is not code (W-36 track H):
    // `forkday.rs`' own NEEDLES and banner constants are the case, and a banner
    // is one only at the start of a line.
    let quoted = ["    const B: &str = \"", b.trim_end(), "\";\n    const N: &str = \"planner", "::\";\n"].concat();
    let scan = forkday::fork_scan(&quoted);
    assert!(scan.deleted && scan.escapes.is_empty(), "{:?}", scan.escapes);
    // …and a needle after code on its line, behind `//`, is prose.
    let trailing = ["    let d = 1; // ", "planner", "::plan here is prose\n"].concat();
    assert!(forkday::fork_scan(&trailing).escapes.is_empty());
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gap 2722)
use tm_core::planner;

/// (a) on the fork, with its own §7 pass — and its timeline and diagnostics
/// pinned by snapshot.
#[test]
fn plan_basic_early_start() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = basic_state();
    let now = at("2026-09-07", 7, 0);
    let day = planner::plan(&fx.input(&state, now));
    insta::assert_snapshot!("plan_basic_early_timeline", timeline(&day));
    insta::assert_snapshot!("plan_basic_early_diagnostics", planner_common::diagnostics(&day));
    check_basic_early(&day, &fx, now);
    // The one Break row this day takes, at 14:50, is `check_basic_early`'s
    // since W-37 (gap 551 closed): asserted of both arms there.
}

/// (b) on the fork.
#[test]
fn plan_basic_late_start_with_a_wall() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = late_state();
    let now = at("2026-09-07", 10, 30);
    let day = planner::plan(&fx.input(&state, now));
    insta::assert_snapshot!("plan_basic_late_timeline", timeline(&day));
    insta::assert_snapshot!("plan_basic_late_diagnostics", planner_common::diagnostics(&day));
    check_basic_late(&day, &fx, now);
}

/// (c) on the fork.
#[test]
fn plan_home_day() {
    let fx = load("plan-home-day");
    let now = at("2026-09-07", 9, 0);
    let day = planner::plan(&fx.input(&fx.state, now));
    insta::assert_snapshot!("plan_home_day_timeline", timeline(&day));
    insta::assert_snapshot!("plan_home_day_diagnostics", planner_common::diagnostics(&day));
    check_home_day(&day, &fx, now);
}

/// (d) on the fork.
#[test]
fn plan_travel_day() {
    let fx = load("plan-travel-day");
    let now = at("2026-09-07", 7, 0);
    let day = planner::plan(&fx.input(&fx.state, now));
    insta::assert_snapshot!("plan_travel_day_timeline", timeline(&day));
    insta::assert_snapshot!("plan_travel_day_diagnostics", planner_common::diagnostics(&day));
    check_travel_day(&day, &fx, now);
}

/// **Re-bless the frozen fork days** — inert without `TM_PLANNER_BLESS`.
///
/// Each day is the fork as the shipped binary plans it (D53): the kernel's own
/// grants for this request, read by the binary's reader, handed to
/// `planner::plan` through `with_ranking` — `planning::build_ranked`'s call.
/// Rewriting a committed comparand is a decision and never a repair (AGENTS
/// §7.2); after R3 this test is gone with the region and the file is final.
///
/// **It holds the lines it already has, since W-42 track C** (README gaps 4151 and
/// 4283): until then it rewrote the whole file with nothing held — a re-bless held
/// to no rule at all, beside siblings that refuse to change a held line. These four
/// days record no departure (a line is the shipped fork's day and its digest), so
/// no parity number (D64(a)) and no corrected harness reading (D64(c)) can license
/// moving one; a day the fork answers differently is a finding to report, and is
/// REFUSED by name. A day no committed version holds is added; what a line is held
/// against is the file's COMMITTED history (`frozenhist::held`), never the working
/// copy; a line HEAD holds that no day of [`DAYS`] writes is refused.
#[test]
#[ignore]
fn the_frozen_fork_days_are_reblessed() {
    if std::env::var_os("TM_PLANNER_BLESS").is_none() {
        eprintln!("inert: set TM_PLANNER_BLESS=1 to rewrite {}", forkday::FROZEN_DAYS);
        return;
    }
    let held = frozenhist::held(&forkday::frozen_path(), frozenhist::key_of("name")).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", held.census(forkday::FROZEN_DAYS));
    let (mut out, mut refused) = (String::new(), Vec::new());
    for d in &DAYS {
        let l = Loaded::of(d);
        let (_, ans) = planreq::kernel_day(&l.world(), None).unwrap_or_else(|e| panic!("{}: {e}", d.name));
        let fork = planner::plan(&l.fx.input(&l.state, l.now).with_ranking(&l.cands, &ans.prios));
        let line = forkday::frozen_line(d.name, &fork);
        if held.ever.get(d.name).is_some_and(|old| old.raw.as_str() != line.trim_end()) {
            refused.push(format!("{}: the fork answers this frozen day differently, and it is not rewritten", d.name));
        }
        out.push_str(&line);
    }
    refused.extend(held.head.iter().filter(|n| !DAYS.iter().any(|d| d.name == n.as_str())).map(|n| format!("{n}: a frozen line no day writes")));
    assert!(refused.is_empty(), "the re-bless is refused and wrote nothing:\n  {}", refused.join("\n  "));
    std::fs::write(forkday::frozen_path(), out).expect("the frozen days are written");
}
// END THE FORK PLANNER
