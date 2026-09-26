//! §8 end to end on the fixture days (§17.1, M4's definition of done):
//! `plan-basic` with an early start, `plan-basic` with a late start and the
//! 12:50 wall, `plan-home-day` (the `home_max_ci` cap) and `plan-travel-day`
//! (a `buffer:2h travel-day` flight zeroing the budget).
//!
//! Each snapshot is the whole timeline — every segment, in order — plus the
//! §8.2 step 8 diagnostics, so a change to any step of §8.2 shows up here.

mod planner_common;

use chrono::NaiveTime;
use planner_common::{
    assert_break_rule, at, basic_state, date, diagnostics, load, load_with_log, timeline,
    BASIC_LOG,
};
use tm_core::dayplan::{SegKind, Segment};
use tm_core::planner;
use tm_core::store::RuntimeState;

// ---------------------------------------------------------------------------
// (a) plan-basic, early start
// ---------------------------------------------------------------------------

/// §4.3's day, planned at 07:00 from `.tm/state.json` (`window 07:00..16:00`,
/// `budget 6`, lounge) with the log the fixture ships (wake 06:05, breakfast
/// done, arrive 07:00).
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
///    break at 14:50.
/// 7. **§4.3 marks two blocks `✓` and one `▶`, and shows `(67m)` actuals.**
///    Those are log facts; at 07:00 the log holds only wake, breakfast and
///    arrive.
/// 8. **§4.3's `2b×1.6`** needs a learned `model.json`; the fixture ships
///    none, so every multiplier here is 1.
/// 9. **§4.3's `15:10 ─── window ends 16:00` divider** is an `emit.rs` row,
///    not a segment.
#[test]
fn plan_basic_early_start() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = basic_state();
    let now = at("2026-09-07", 7, 0);
    let day = planner::plan(&fx.input(&state, now));
    insta::assert_snapshot!("plan_basic_early_timeline", timeline(&day));
    insta::assert_snapshot!("plan_basic_early_diagnostics", diagnostics(&day));

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
    // without a rest, and this day takes its break at 14:50.
    assert_break_rule(&day, now, &fx.cfg);
    let breaks: Vec<&Segment> = day
        .segments
        .iter()
        .filter(|s| s.kind == SegKind::Break)
        .collect();
    assert_eq!(breaks.len(), 1, "{}", timeline(&day));
    assert_eq!(breaks[0].start, at("2026-09-07", 14, 50));
    assert_eq!(breaks[0].end, at("2026-09-07", 15, 10));
    // §8.2 step 8: what this day could not do (the snapshot pins the rest).
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

// ---------------------------------------------------------------------------
// (b) plan-basic, late start with a wall
// ---------------------------------------------------------------------------

/// Arriving at 10:30 with the 12:50–13:50 meeting ahead: §8.1's window is
/// `min(10:30 + 8h, 19:00) + 1h wall = 19:30`, the budget is unchanged (§8.1:
/// "a late start gets a later end and the same budget formula"), and the
/// morning simply is not there.
#[test]
fn plan_basic_late_start_with_a_wall() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = RuntimeState {
        date: Some(date("2026-09-07")),
        wake: Some(NaiveTime::from_hms_opt(9, 0, 0).expect("time")),
        arrival: Some(NaiveTime::from_hms_opt(10, 30, 0).expect("time")),
        loc: Some("lounge".to_string()),
        ..RuntimeState::default()
    };
    let now = at("2026-09-07", 10, 30);
    let day = planner::plan(&fx.input(&state, now));
    insta::assert_snapshot!("plan_basic_late_timeline", timeline(&day));
    insta::assert_snapshot!("plan_basic_late_diagnostics", diagnostics(&day));

    assert_break_rule(&day, now, &fx.cfg);
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

// ---------------------------------------------------------------------------
// (c) plan-home-day
// ---------------------------------------------------------------------------

/// The same tree at home (§8.2 step 3's `min(energy, home_max_ci)`): no slot
/// is worth more than `ci 3`, so the `ci 4`/`ci 5` milestones cannot be
/// started at all and the low-`ci` work rises to the top. `state.json` stores
/// no window here, so §8.1's formula runs: `09:00 + 8h = 17:00`, plus the
/// 12:50 meeting, is 18:00.
#[test]
fn plan_home_day() {
    let fx = load("plan-home-day");
    let now = at("2026-09-07", 9, 0);
    let day = planner::plan(&fx.input(&fx.state, now));
    insta::assert_snapshot!("plan_home_day_timeline", timeline(&day));
    insta::assert_snapshot!("plan_home_day_diagnostics", diagnostics(&day));

    assert_eq!(day.window, (at("2026-09-07", 9, 0), at("2026-09-07", 18, 0)));
    assert_eq!(day.budget_blocks, 6);
    assert_break_rule(&day, now, &fx.cfg);
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

// ---------------------------------------------------------------------------
// (d) plan-travel-day
// ---------------------------------------------------------------------------

/// A `buffer:2h travel-day` flight at 08:15: the blocked time starts at 06:15
/// (clipped to the window at 07:00), and §8.2 step 1's "travel-day zeroing"
/// takes the whole block budget away — routines, walls and optionals stay, no
/// Block is planned.
#[test]
fn plan_travel_day() {
    let fx = load("plan-travel-day");
    let now = at("2026-09-07", 7, 0);
    let day = planner::plan(&fx.input(&fx.state, now));
    insta::assert_snapshot!("plan_travel_day_timeline", timeline(&day));
    insta::assert_snapshot!("plan_travel_day_diagnostics", diagnostics(&day));

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
