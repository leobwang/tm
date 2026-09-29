//! Regression tests for the review findings on §8/§9 — one test per bug, each
//! named after the rule it broke.
//!
//! The §8.3 invariants live in `planner_invariants.rs` as properties and the
//! fixture days in `planner_fixtures.rs`; what is here are the cases those two
//! could not reach: a block that is *running* (`state.active`), an open
//! interruption, a batch of mixed `loc:`, an `atomic` item longer than the
//! stretch between two breaks, an evening that reaches the wind-down, and the
//! diagnostics nothing else asserts.
//!
//! # Two arms since W-36 track H (README gap 2872)
//!
//! Every property is written ONCE, over a `planner_common::DayPlanner`, and
//! asked of the KERNEL (the test under the property's own name — the arm that
//! survives R3: the whole request through `planreq`, the day read back by the
//! host's codec `tm_core::planwire`) and of the fork (`<name>_on_the_fork`, in
//! the one `BEGIN THE FORK PLANNER` … `END THE FORK PLANNER` region R3
//! deletes). Where the kernel's day differs from the fork's BY DECISION the
//! property says so by name and asks each planner its own half.

mod planner_common;

use chrono::Duration;
use planner_common::{
    assert_break_rule, at, basic_state, date, load, load_with_log, of_texts, time, timeline, DayPlanner,
    Fixture, Kernel, BASIC_LOG, TZ,
};
use tm_core::model::Id;
use tm_core::dayplan::{fmt_clock, DayPlan, SegKind, Segment};
use tm_core::store::{ActiveBlock, InterruptState, RuntimeState};
use tm_core::tree::Tree;

// ---------------------------------------------------------------------------
// A synthetic day: a week file, a log, and nothing else
// ---------------------------------------------------------------------------

/// A hand-written week (and optional calendar) with its own log — the smallest
/// world a planner test can run in. Since W-36 track H it is a
/// `planner_common::Fixture`, so the same world is handed to both planners.
fn world(week: &str, calendar: &str, log_text: &str) -> Fixture {
    of_texts(&[("week/2026-W37.md", week), ("calendar/2026-W37.md", calendar)], log_text)
}

/// `wake` + `arrive`, the two events every day starts with.
const ARRIVED: &str = concat!(
    r#"{"t":"2026-09-07T06:00:00-05:00","ev":"wake","slept_min":480}"#,
    "\n",
    r#"{"t":"2026-09-07T07:00:00-05:00","ev":"arrive","loc":"lounge","window":["07:00","16:00"],"budget":6}"#,
    "\n",
);

fn week_header(body: &str) -> String {
    format!("---\nweek: 2026-W37\n---\n# Milestones\n{body}")
}

/// `state.json` for the synthetic world: arrived at 07:00 in the lounge.
fn synthetic_state() -> RuntimeState {
    RuntimeState {
        date: Some(date("2026-09-07")),
        wake: Some(time(6, 0)),
        arrival: Some(time(7, 0)),
        loc: Some("lounge".to_string()),
        window: Some((time(7, 0), time(16, 0))),
        budget: Some(6),
        ..RuntimeState::default()
    }
}

/// Every `(start, end)` pair of segments that overlap.
fn overlapping(day: &DayPlan) -> Vec<(&Segment, &Segment)> {
    let mut out = Vec::new();
    let placed: Vec<&Segment> = day
        .segments
        .iter()
        .filter(|s| !matches!(s.kind, SegKind::WindDown | SegKind::Sleep | SegKind::Lost))
        .collect();
    for (i, a) in placed.iter().enumerate() {
        for b in placed.iter().skip(i + 1) {
            // §8.2 step 1 reports overlapping walls rather than resolving them.
            if a.kind == SegKind::Wall && b.kind == SegKind::Wall {
                continue;
            }
            if a.start < b.end && b.start < a.end {
                out.push((*a, *b));
            }
        }
    }
    out
}

/// The ci the tree gives an item.
fn ci_of(tree: &Tree, id: &Id) -> u8 {
    tree.get(id).map_or(0, |i| i.ci)
}

// ---------------------------------------------------------------------------
// §9: the running block
// ---------------------------------------------------------------------------

/// §8.3's energy filter has no Active exception, and §9 has no "put it
/// anywhere" clause either: the block that is running keeps *its own* time —
/// `[now, now + est − worked]` — and takes no cut slot at all, so it can never
/// be the ci-5 item sitting in a slot of energy 3.
fn the_running_block_takes_no_slot_below_its_ci_on(p: &dyn DayPlanner) {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    for (h, m) in [(14, 30), (15, 0), (9, 30)] {
        let state = RuntimeState {
            active: Some(ActiveBlock {
                id: Id::new("m1"), // `Finish ch.5 exercises`, ci 5
                started: time(h, m),
                est_min: 120,
                paused: false,
            }),
            ..basic_state()
        };
        let now = at("2026-09-07", h, m) + Duration::minutes(30);
        let day = p.day(&fx, &state, now);
        for seg in day.segments.iter().filter(|s| s.kind.is_work()) {
            let Some(energy) = seg.energy else { continue };
            for id in seg.items() {
                assert!(
                    ci_of(&fx.tree, &id) <= energy,
                    "{id} (ci {}) in a slot of energy {energy} at {h}:{m:02}\n{}",
                    ci_of(&fx.tree, &id),
                    timeline(&day)
                );
            }
        }
        // The running block is there, from `now`, and holds no slot energy.
        let current = day
            .current_segment()
            .unwrap_or_else(|| panic!("^m1 is running at {h}:{m:02}\n{}", timeline(&day)));
        assert_eq!(current.item.as_ref().map(Id::as_str), Some("m1"));
        assert_eq!(current.start, now);
        assert!(current.energy.is_none(), "{current:?}");
        assert!(overlapping(&day).is_empty(), "{}", timeline(&day));
    }
}

/// [`the_running_block_takes_no_slot_below_its_ci_on`], asked of the kernel — the arm that survives R3.
#[test]
fn the_running_block_takes_no_slot_below_its_ci() {
    the_running_block_takes_no_slot_below_its_ci_on(&Kernel);
}

/// §9: "the Active item keeps its current slot regardless of key" — including
/// when §8.2 step 5 would refuse the item. A `max:`-exhausted (or dep-blocked)
/// item forms no assignable group, and the block running right now must not
/// vanish from the timeline because of it.
fn the_running_block_survives_an_exhausted_cap_on(p: &dyn DayPlanner) {
    // ^d1 carries `max:2b/d`; two blocks are already done today.
    let log = format!(
        "{ARRIVED}{}",
        concat!(
            r#"{"t":"2026-09-07T07:02:00-05:00","ev":"start","id":"d1","pred":5,"hsw":1.0,"slept_min":480,"loc":"lounge","blocks_done":0,"since_break_min":0}"#,
            "\n",
            r#"{"t":"2026-09-07T08:02:00-05:00","ev":"done","id":"d1","est_min":60,"actual_min":60,"went":1,"tags":[],"ci":4,"partial":true}"#,
            "\n",
            r#"{"t":"2026-09-07T08:05:00-05:00","ev":"start","id":"d1","pred":5,"hsw":2.0,"slept_min":480,"loc":"lounge","blocks_done":1,"since_break_min":60}"#,
            "\n",
            r#"{"t":"2026-09-07T09:05:00-05:00","ev":"done","id":"d1","est_min":60,"actual_min":60,"went":1,"tags":[],"ci":4,"partial":true}"#,
            "\n",
            r#"{"t":"2026-09-07T09:10:00-05:00","ev":"start","id":"d1","pred":4,"hsw":3.1,"slept_min":480,"loc":"lounge","blocks_done":2,"since_break_min":0}"#,
            "\n",
        )
    );
    let fx = load_with_log("plan-basic", Some(&log));
    let state = RuntimeState {
        active: Some(ActiveBlock {
            id: Id::new("d1"),
            started: time(9, 10),
            est_min: 60,
            paused: false,
        }),
        ..basic_state()
    };
    let now = at("2026-09-07", 9, 40);
    let day = p.day(&fx, &state, now);
    let current = day
        .current_segment()
        .unwrap_or_else(|| panic!("^d1 is running:\n{}", timeline(&day)));
    assert_eq!(current.item.as_ref().map(Id::as_str), Some("d1"));
    assert_eq!(current.start, now);
    assert_eq!(current.end, at("2026-09-07", 10, 10)); // 60 − 30 worked
    // The cap is still respected for everything the planner *chooses*: no
    // further ^d1 block is planned after the running one.
    assert!(
        !day.assigned_from(current.end).contains(&Id::new("d1")),
        "{}",
        timeline(&day)
    );
}

/// [`the_running_block_survives_an_exhausted_cap_on`], asked of the kernel — the arm that survives R3.
#[test]
fn the_running_block_survives_an_exhausted_cap() {
    the_running_block_survives_an_exhausted_cap_on(&Kernel);
}

/// §9: "Active block paused" — an interruption, not a routine, is what stops
/// it. Step 2 must not place a mandatory instance on top of a block that is
/// running right now.
fn a_mandatory_routine_never_lands_on_the_running_block_on(p: &dyn DayPlanner) {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    for (h, m) in [(15, 0), (9, 40), (11, 45)] {
        let state = RuntimeState {
            active: Some(ActiveBlock {
                id: Id::new("m1"),
                started: at("2026-09-07", h, m).time() - Duration::minutes(30),
                est_min: 120,
                paused: false,
            }),
            ..basic_state()
        };
        let now = at("2026-09-07", h, m);
        let day = p.day(&fx, &state, now);
        let current = day
            .current_segment()
            .unwrap_or_else(|| panic!("^m1 is running at {h}:{m:02}\n{}", timeline(&day)));
        assert_eq!(current.start, now, "{}", timeline(&day));
        for seg in day.segments.iter().filter(|s| s.kind == SegKind::Routine) {
            assert!(
                seg.end <= current.start || seg.start >= current.end,
                "{seg:?} over the running block at {h}:{m:02}\n{}",
                timeline(&day)
            );
        }
    }
}

/// [`a_mandatory_routine_never_lands_on_the_running_block_on`], asked of the kernel — the arm that survives R3.
#[test]
fn a_mandatory_routine_never_lands_on_the_running_block() {
    a_mandatory_routine_never_lands_on_the_running_block_on(&Kernel);
}

/// §12.1: left of the cursor the timeline is the log. A block that is still
/// running has no closed sub-segment, so the minutes it has been running for
/// were covered by nothing at all — a hole in the day bar.
fn the_elapsed_part_of_the_running_block_is_on_the_timeline_on(p: &dyn DayPlanner) {
    let log = format!(
        "{ARRIVED}{}",
        concat!(
            r#"{"t":"2026-09-07T09:30:00-05:00","ev":"start","id":"t3","pred":4,"hsw":3.5,"slept_min":480,"loc":"lounge","blocks_done":0,"since_break_min":0}"#,
            "\n",
        )
    );
    let fx = load_with_log("plan-basic", Some(&log));
    let state = RuntimeState {
        active: Some(ActiveBlock {
            id: Id::new("t3"),
            started: time(9, 30),
            est_min: 120,
            paused: false,
        }),
        ..basic_state()
    };
    let now = at("2026-09-07", 10, 0);
    let day = p.day(&fx, &state, now);
    let elapsed: Vec<&Segment> = day
        .segments
        .iter()
        .filter(|s| {
            s.kind.is_work()
                && s.item.as_ref().is_some_and(|i| i.as_str() == "t3")
                && s.start < now
        })
        .collect();
    assert_eq!(elapsed.len(), 1, "{}", timeline(&day));
    assert_eq!(elapsed[0].start, at("2026-09-07", 9, 30));
    assert_eq!(elapsed[0].end, now);
    assert!(elapsed[0].flags.open, "it has not finished: {elapsed:?}");
    // Nothing else claims those minutes.
    assert!(overlapping(&day).is_empty(), "{}", timeline(&day));
}

/// [`the_elapsed_part_of_the_running_block_is_on_the_timeline_on`], asked of the kernel — the arm that survives R3.
#[test]
fn the_elapsed_part_of_the_running_block_is_on_the_timeline() {
    the_elapsed_part_of_the_running_block_is_on_the_timeline_on(&Kernel);
}

/// §9 / §9.1: the overtime prompt runs in exactly the state where the budget is
/// spent. A plan that drops the running block there tells the user to stop
/// working on something they are working on, and `overtime_drops` would diff
/// two plans neither of which holds the item.
fn the_running_block_shows_when_the_budget_is_spent_on(p: &dyn DayPlanner) {
    // A travel day zeroes the budget outright (§8.2 step 1).
    let fx = load("plan-travel-day");
    let state = RuntimeState {
        active: Some(ActiveBlock {
            id: Id::new("m1"),
            started: time(11, 0),
            est_min: 60,
            paused: false,
        }),
        ..fx.state.clone()
    };
    let now = at("2026-09-07", 11, 30);
    let day = p.day(&fx, &state, now);
    let current = day
        .current_segment()
        .unwrap_or_else(|| panic!("^m1 is running:\n{}", timeline(&day)));
    assert_eq!(current.item.as_ref().map(Id::as_str), Some("m1"));
    assert_eq!(current.end, at("2026-09-07", 12, 0));
    // Nothing *else* is planned: the travel day still plans no work.
    assert_eq!(
        day.planned_block_minutes(now) - current.minutes(),
        0,
        "{}",
        timeline(&day)
    );
    assert!(overlapping(&day).is_empty(), "{}", timeline(&day));
}

/// [`the_running_block_shows_when_the_budget_is_spent_on`], asked of the kernel — the arm that survives R3.
#[test]
fn the_running_block_shows_when_the_budget_is_spent() {
    the_running_block_shows_when_the_budget_is_spent_on(&Kernel);
}

/// §9: an open interruption is an ad-hoc wall "from t_i to now" — it has no end
/// yet, so a later replan necessarily shows it longer. §8.3's stability
/// invariant is about settled segments; [`tm_core::dayplan::SegFlags::open`]
/// says which segment is not one, and the growth is all it may do.
fn an_open_interruption_grows_and_never_moves_on(p: &dyn DayPlanner) {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = RuntimeState {
        interrupt: Some(InterruptState {
            started: Some(time(12, 10)),
            id: Some(Id::new("t4")),
        }),
        ..basic_state()
    };
    let (t1, t2) = (at("2026-09-07", 13, 5), at("2026-09-07", 13, 35));
    let early = p.day(&fx, &state, t1);
    let later = p.day(&fx, &state, t2);
    for seg in early.segments.iter().filter(|s| s.end <= t1) {
        if seg.flags.open {
            let grown = later
                .segments
                .iter()
                .find(|s| s.start == seg.start && s.kind == seg.kind && s.item == seg.item)
                .unwrap_or_else(|| panic!("the open segment is gone: {seg:?}"));
            assert!(grown.end >= seg.end, "an open segment shrank: {grown:?}");
            assert!(grown.flags.open);
            continue;
        }
        assert!(
            later.segments.contains(seg),
            "a replan moved a settled segment: {seg:?}"
        );
    }
    let lost: Vec<&Segment> = early
        .segments
        .iter()
        .filter(|s| s.kind == SegKind::Lost)
        .collect();
    assert_eq!(lost.len(), 1, "{}", timeline(&early));
    assert!(lost[0].flags.open, "{lost:?}");
    assert_eq!(lost[0].end, t1);
}

/// [`an_open_interruption_grows_and_never_moves_on`], asked of the kernel — the arm that survives R3.
#[test]
fn an_open_interruption_grows_and_never_moves() {
    an_open_interruption_grows_and_never_moves_on(&Kernel);
}

// ---------------------------------------------------------------------------
// §7.5 batching and §8.2 step 5's filters
// ---------------------------------------------------------------------------

/// §7.5: several small items share one block — the whole reason the `+3` bin
/// ever gets a slot.
fn small_items_share_one_block_on(p: &dyn DayPlanner) {
    let week = week_header(
        "- [ ] 3 15m Errand one !1 ^zaa\n\
         - [ ] 3 15m Errand two !1 ^zab\n\
         - [ ] 3 10m Errand three !1 ^zac\n\
         - [ ] 3 20m Errand four !1 ^zad\n",
    );
    let w = world(&week, "", ARRIVED);
    let state = synthetic_state();
    let day = p.day(&w, &state, at("2026-09-07", 7, 0));
    let batch = day
        .segments
        .iter()
        .find(|s| matches!(s.kind, SegKind::Batch(_)))
        .unwrap_or_else(|| panic!("four 10–20m items batch:\n{}", timeline(&day)));
    let SegKind::Batch(ids) = &batch.kind else {
        unreachable!()
    };
    assert!(ids.len() > 1, "{ids:?}");
    assert_eq!(batch.start, at("2026-09-07", 7, 0));
    // Every member is a real candidate, and the batch is one block of the day.
    for id in ids {
        assert!(w.tree.get(id).is_some(), "{id}");
    }
    assert!(batch.minutes() <= w.cfg.block_min());
}

/// [`small_items_share_one_block_on`], asked of the kernel — the arm that survives R3.
#[test]
fn small_items_share_one_block() {
    small_items_share_one_block_on(&Kernel);
}

/// §8.2 step 5's `loc` filter is written about the item. §7.5 batches by `ci`
/// and size alone, so a batch may mix a `loc:out` errand with a desk task:
/// neither may ride the other into a slot, or out of the day.
fn a_batch_never_carries_one_members_location_onto_another_on(p: &dyn DayPlanner) {
    for week in [
        "- [ ] 3 15m Desk thing !1 ^zaa\n- [ ] 3 15m Post the parcel !1 loc:out ^zab\n",
        // …and the other way round: the errand first must not take the desk
        // task out of the day with it.
        "- [ ] 3 15m Post the parcel !1 loc:out ^zab\n- [ ] 3 15m Desk thing !1 ^zaa\n",
    ] {
        let w = world(&week_header(week), "", ARRIVED);
        let state = RuntimeState {
            loc: Some("lounge".to_string()),
            ..synthetic_state()
        };
        let day = p.day(&w, &state, at("2026-09-07", 7, 0));
        let assigned = day.assigned();
        assert!(
            assigned.contains(&Id::new("zaa")),
            "the desk task fits the lounge:\n{}",
            timeline(&day)
        );
        assert!(
            !assigned.contains(&Id::new("zab")),
            "a `loc:out` errand was scheduled at the desk:\n{}",
            timeline(&day)
        );
        assert!(day.diagnostics.dropped_tail.contains(&Id::new("zab")));
    }
}

/// [`a_batch_never_carries_one_members_location_onto_another_on`], asked of the kernel — the arm that survives R3.
#[test]
fn a_batch_never_carries_one_members_location_onto_another() {
    a_batch_never_carries_one_members_location_onto_another_on(&Kernel);
}

/// §8.2 step 5: "if !splittable: contiguous free slots ≥ remaining exist
/// **before the next wall**". The 20-minute break the planner itself inserts is
/// not a wall — reading it as one makes every `atomic` item longer than
/// `break_after_blocks × block_min` unplaceable on any day at all.
fn an_atomic_item_may_run_through_a_planned_break_on(p: &dyn DayPlanner) {
    let w = world(
        &week_header("- [ ] 3 3b Long atomic thing !1 atomic ^zaa\n"),
        "",
        ARRIVED,
    );
    let state = synthetic_state();
    let now = at("2026-09-07", 7, 0);
    let day = p.day(&w, &state, now);
    let mine: Vec<&Segment> = day
        .segments
        .iter()
        .filter(|s| s.item.as_ref().is_some_and(|i| i.as_str() == "zaa"))
        .collect();
    assert!(
        !mine.is_empty(),
        "an atomic 3b item on an empty day:\n{}",
        timeline(&day)
    );
    // §8.5's multiplier makes 3b into 234 minutes, so it needs four slots —
    // two breaks' worth — and gets them.
    let minutes: u32 = mine.iter().map(|s| s.minutes()).sum();
    assert!(minutes >= 3 * w.cfg.block_min(), "{minutes}m: {mine:?}");
    assert!(!day.diagnostics.dropped_tail.contains(&Id::new("zaa")));
    // A wall, on the other hand, does end the run: with the afternoon walled
    // off there is no contiguous stretch left and the item waits for a day
    // that has one.
    let walled = world(
        &week_header("- [ ] 3 3b Long atomic thing !1 atomic ^zaa\n"),
        "- [ ] 3 Wall at:2026-09-07T09:00/16:00 ^waa\n",
        ARRIVED,
    );
    let day = p.day(&walled, &state, now);
    assert!(
        !day.assigned().contains(&Id::new("zaa")),
        "two hours is not three blocks:\n{}",
        timeline(&day)
    );
}

/// [`an_atomic_item_may_run_through_a_planned_break_on`], asked of the kernel — the arm that survives R3.
#[test]
fn an_atomic_item_may_run_through_a_planned_break() {
    an_atomic_item_may_run_through_a_planned_break_on(&Kernel);
}

// ---------------------------------------------------------------------------
// §8.2 steps 3 and 6
// ---------------------------------------------------------------------------

/// §8.2 step 6 places a deferred routine into a *free* position: the breaks
/// step 3 cut are not free, and a routine laid over one used to be emitted
/// twice — the break and the routine, at the same minute.
fn a_deferred_routine_never_lands_on_a_break_on(p: &dyn DayPlanner) {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    for (h, m) in [(7, 0), (8, 30), (9, 45), (11, 0), (13, 0)] {
        for loc in ["lounge", "home"] {
            let state = RuntimeState {
                loc: Some(loc.to_string()),
                ..basic_state()
            };
            let day = p.day(&fx, &state, at("2026-09-07", h, m));
            assert!(
                overlapping(&day).is_empty(),
                "{loc} at {h}:{m:02}: {:?}\n{}",
                overlapping(&day)
                    .iter()
                    .map(|(a, b)| (a.start, &a.kind, b.start, &b.kind))
                    .collect::<Vec<_>>(),
                timeline(&day)
            );
        }
    }
}

/// [`a_deferred_routine_never_lands_on_a_break_on`], asked of the kernel — the arm that survives R3.
#[test]
fn a_deferred_routine_never_lands_on_a_break() {
    a_deferred_routine_never_lands_on_a_break_on(&Kernel);
}

/// §8.2 step 3: "a break of `break_min` after every `break_after_blocks`
/// blocks" — the rule, not just the presence of one break somewhere.
fn a_break_comes_after_every_two_blocks_on(p: &dyn DayPlanner) {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    for (h, m) in [(7, 0), (9, 45), (11, 0)] {
        let now = at("2026-09-07", h, m);
        let day = p.day(&fx, &basic_state(), now);
        assert_break_rule(&day, now, &fx.cfg);
    }
    let w = world(
        &week_header("- [ ] 3 8b Long thing !1 ^zaa\n"),
        "",
        ARRIVED,
    );
    let now = at("2026-09-07", 7, 0);
    let day = p.day(&w, &synthetic_state(), now);
    assert_break_rule(&day, now, &w.cfg);
    // Six blocks need two breaks: two stretches of at least `break_min`
    // between consecutive work rows, whatever fills them.
    let work: Vec<&Segment> = day.segments.iter().filter(|s| s.kind.is_work() && s.start >= now).collect();
    let rests = work
        .windows(2)
        .filter(|pair| (pair[1].start - pair[0].end).num_minutes() >= i64::from(w.cfg.day.break_min))
        .count();
    assert!(rests >= 2, "six blocks need two breaks:\n{}", timeline(&day));
    // …and each of them is DRAWN as a Break row, on both planners: README gap
    // 551's class, bounded exactly here until W-37, when the kernel began to
    // draw the cut's kept breaks as the fork does (`Planner.PlanReq.keptBreakRows`).
    let drawn = day.segments.iter().filter(|s| s.kind == SegKind::Break && s.start >= now).count();
    assert!(drawn >= 2, "six blocks need two Break rows on {}:\n{}", p.name(), timeline(&day));
}

/// [`a_break_comes_after_every_two_blocks_on`], asked of the kernel — the arm that survives R3.
#[test]
fn a_break_comes_after_every_two_blocks() {
    a_break_comes_after_every_two_blocks_on(&Kernel);
}

/// §8.3: "no ci ≥ 4 Block after wind-down". The fixture days end long before
/// 21:30; §8.1's window can reach past it — a late arrival and an evening wall
/// push the end into the night — and the rule has to hold there.
fn no_demanding_block_after_wind_down_on(p: &dyn DayPlanner) {
    let w = world(
        &week_header(
            "- [ ] 5 6b Big thing !1 ^zaa\n\
             - [ ] 3 6b Small thing !1 ^zab\n\
             - [ ] 1 6b Tiny thing !1 ^zac\n",
        ),
        "- [ ] 3 Long evening at:2026-09-07T15:00/21:00 ^waa\n",
        concat!(
            r#"{"t":"2026-09-07T09:30:00-05:00","ev":"wake","slept_min":480}"#,
            "\n",
            r#"{"t":"2026-09-07T11:00:00-05:00","ev":"arrive","loc":"lounge","window":["11:00","19:00"],"budget":6}"#,
            "\n",
        ),
    );
    let state = RuntimeState {
        date: Some(date("2026-09-07")),
        wake: Some(time(9, 30)),
        arrival: Some(time(11, 0)),
        loc: Some("lounge".to_string()),
        ..RuntimeState::default()
    };
    let now = at("2026-09-07", 11, 0);
    let day = p.day(&w, &state, now);
    // §8.1: 11:00 + 8h = 19:00, plus the six-hour wall inside it.
    assert!(
        day.window.1 > at("2026-09-07", 21, 30),
        "the window reaches past the wind-down: {:?}",
        day.window
    );
    let wind = at("2026-09-07", 21, 30);
    for seg in day.segments.iter().filter(|s| s.kind.is_work()) {
        for id in seg.items() {
            assert!(
                seg.end <= wind || ci_of(&w.tree, &id) < 4,
                "{id} (ci {}) works past the wind-down:\n{}",
                ci_of(&w.tree, &id),
                timeline(&day)
            );
        }
        // This planner is stricter than §8.3 and plans no work at all there.
        assert!(seg.end <= wind, "{seg:?}\n{}", timeline(&day));
    }
}

/// [`no_demanding_block_after_wind_down_on`], asked of the kernel — the arm that survives R3.
#[test]
fn no_demanding_block_after_wind_down() {
    no_demanding_block_after_wind_down_on(&Kernel);
}

// ---------------------------------------------------------------------------
// §8.2 step 8 and §11
// ---------------------------------------------------------------------------

/// The five diagnostics no snapshot shows (they are all `·` on the fixture
/// days) and the two §11 monitors: each one on a day that produces it.
fn the_diagnostics_are_produced_where_the_spec_says_on(p: &dyn DayPlanner) {
    // `underused` and the `↓` flag: a ci-1 item in a slot of energy 5.
    let w = world(&week_header("- [ ] 1 2b Filing !1 ^zaa\n"), "", ARRIVED);
    let day = p.day(&w, &synthetic_state(), at("2026-09-07", 7, 0));
    assert!(
        day.diagnostics
            .underused
            .iter()
            .any(|(id, energy, ci)| id.as_str() == "zaa" && *energy >= ci + 2),
        "{:?}\n{}",
        day.diagnostics.underused,
        timeline(&day)
    );
    assert!(day
        .segments
        .iter()
        .any(|s| s.kind.is_work() && s.flags.underused));

    // `hot` and `impossible`: 20 blocks of ci-3 work due tonight.
    let w = world(
        &week_header("- [ ] 3 20b Impossible thing due:2026-09-07T23:59 ^zaa\n"),
        "",
        ARRIVED,
    );
    let day = p.day(&w, &synthetic_state(), at("2026-09-07", 7, 0));
    assert!(day.diagnostics.hot.contains(&Id::new("zaa")), "{:?}", day.diagnostics);
    assert!(
        day.diagnostics
            .impossible
            .iter()
            .any(|(id, short, _)| id.as_str() == "zaa" && *short > 0),
        "{:?}",
        day.diagnostics.impossible
    );
    assert!(day.segments.iter().any(|s| s.kind.is_work() && s.flags.hot));

    // `conflicts`: two calendar walls over the same hour, and nothing placed
    // in the overlap.
    let w = world(
        &week_header("- [ ] 3 2b Work !1 ^zaa\n"),
        "- [ ] 3 Meeting at:2026-09-07T10:00/12:00 ^waa\n\
         - [ ] 3 Other meeting at:2026-09-07T11:00/13:00 ^wab\n",
        ARRIVED,
    );
    let day = p.day(&w, &synthetic_state(), at("2026-09-07", 7, 0));
    assert_eq!(
        day.diagnostics.conflicts,
        vec![(Id::new("waa"), Id::new("wab"))],
        "{}",
        timeline(&day)
    );
    for seg in day.segments.iter().filter(|s| s.kind != SegKind::Wall) {
        assert!(
            seg.end <= at("2026-09-07", 11, 0) || seg.start >= at("2026-09-07", 12, 0),
            "{seg:?} sits in the overlap:\n{}",
            timeline(&day)
        );
    }

    // §11 rest debt: a break the log says was cut short.
    let morning = concat!(
        r#"{"t":"2026-09-07T06:05:00-05:00","ev":"wake","slept_min":490}"#,
        "\n",
        r#"{"t":"2026-09-07T07:00:00-05:00","ev":"arrive","loc":"lounge","window":["07:00","16:00"],"budget":6}"#,
        "\n",
        r#"{"t":"2026-09-07T07:02:00-05:00","ev":"start","id":"t1","pred":5,"hsw":0.95,"slept_min":490,"loc":"lounge","blocks_done":0,"since_break_min":0}"#,
        "\n",
        r#"{"t":"2026-09-07T08:09:00-05:00","ev":"done","id":"t1","est_min":60,"actual_min":67,"went":1,"tags":[],"ci":5}"#,
        "\n",
        r#"{"t":"2026-09-07T09:08:00-05:00","ev":"break","planned_min":20,"actual_min":10,"where":"walk"}"#,
        "\n",
    );
    let fx = load_with_log("plan-basic", Some(morning));
    let day = p.day(&fx, &basic_state(), at("2026-09-07", 9, 30));
    assert_eq!(day.diagnostics.rest_debt_min, 10, "20m planned, 10m taken");
}

/// [`the_diagnostics_are_produced_where_the_spec_says_on`], asked of the kernel — the arm that survives R3.
#[test]
fn the_diagnostics_are_produced_where_the_spec_says() {
    the_diagnostics_are_produced_where_the_spec_says_on(&Kernel);
}

/// §8.2 step 8's `deferred`: an energy report that lowers today's curve costs a
/// ci-5 item the slot the raw prediction had for it.
fn a_posterior_downgrade_defers_the_high_ci_item_on(p: &dyn DayPlanner) {
    let week = week_header("- [ ] 5 2b Deep work !1 ^zaa\n- [ ] 2 2b Light work !2 ^zab\n");
    let downgraded = format!(
        "{ARRIVED}{}",
        concat!(
            r#"{"t":"2026-09-07T07:05:00-05:00","ev":"energy","pred":5,"rep":1,"hsw":1.08,"loc":"lounge"}"#,
            "\n",
        )
    );
    // Planned after the report, so every remaining slot carries the
    // correction (§8.5: the posterior only reaches slots later than the
    // report).
    let w = world(&week, "", &downgraded);
    let day = p.day(&w, &synthetic_state(), at("2026-09-07", 7, 30));
    assert!(
        day.diagnostics.deferred.contains(&Id::new("zaa")),
        "{:?}\n{}",
        day.diagnostics,
        timeline(&day)
    );
    assert!(!day.assigned().contains(&Id::new("zaa")));
    // Without the report the same day works it.
    let w = world(&week, "", ARRIVED);
    let day = p.day(&w, &synthetic_state(), at("2026-09-07", 7, 30));
    assert!(day.assigned().contains(&Id::new("zaa")), "{}", timeline(&day));
    assert!(day.diagnostics.deferred.is_empty());
}

/// [`a_posterior_downgrade_defers_the_high_ci_item_on`], asked of the kernel — the arm that survives R3.
#[test]
fn a_posterior_downgrade_defers_the_high_ci_item() {
    a_posterior_downgrade_defers_the_high_ci_item_on(&Kernel);
}

/// §11's plan honesty, pinned: `Σ` the minutes every group the day *starts*
/// still needs, over `remaining_budget × block_min`. It is above 1 exactly when
/// the day opens more work than it can finish — which is what the monitor's
/// "warning when > 1.1" is for, and the only reading under which the ratio can
/// exceed 1 at all (assignment itself never exceeds the budget).
fn plan_honesty_measures_what_the_day_starts_on(p: &dyn DayPlanner) {
    // One block of work in a six-block day: 60 / 360.
    let w = world(&week_header("- [ ] 3 1b One block !1 ^zaa\n"), "", ARRIVED);
    let day = p.day(&w, &synthetic_state(), at("2026-09-07", 7, 0));
    let honesty = day.diagnostics.plan_honesty.expect("a budget of six blocks");
    assert!((honesty - 60.0 / 360.0).abs() < 0.01, "{honesty}");

    // A single milestone twice the size of the day: 12b of 6b = 2.0, and the
    // monitor warns.
    let w = world(&week_header("- [ ] 3 12b One big thing !1 ^zaa\n"), "", ARRIVED);
    let day = p.day(&w, &synthetic_state(), at("2026-09-07", 7, 0));
    let honesty = day.diagnostics.plan_honesty.expect("a budget of six blocks");
    assert!((honesty - 2.0).abs() < 0.01, "{honesty}");
    assert!(honesty > 1.1, "the day is over-committed");

    // A travel day spends nothing, so there is no ratio to report.
    let fx = load("plan-travel-day");
    let day = p.day(&fx, &fx.state, at("2026-09-07", 7, 0));
    assert_eq!(day.diagnostics.plan_honesty, None);
}

/// [`plan_honesty_measures_what_the_day_starts_on`], asked of the kernel — the arm that survives R3.
#[test]
fn plan_honesty_measures_what_the_day_starts() {
    plan_honesty_measures_what_the_day_starts_on(&Kernel);
}

/// §7.2/§8.3: HOT before queue. Four `p = 0` items and three slots — the day
/// works the hot ones, in key order, and no `p > 0` item takes their place.
fn hot_items_take_the_slots_before_the_queue_on(p: &dyn DayPlanner) {
    let week = week_header(
        "- [ ] 3 2b Hot one due:2026-09-07T23:59 !2 ^zaa\n\
         - [ ] 3 2b Hot two due:2026-09-07T23:59 !2 ^zab\n\
         - [ ] 3 2b Hot three due:2026-09-07T23:59 !2 ^zac\n\
         - [ ] 3 6b Ordinary work !1 ^zad\n",
    );
    let w = world(&week, "", ARRIVED);
    let state = RuntimeState {
        budget: Some(3),
        ..synthetic_state()
    };
    let now = at("2026-09-07", 7, 0);
    let day = p.day(&w, &state, now);
    let prios: Vec<(Id, u8)> = day
        .priorities
        .iter()
        .map(|(id, p)| (id.clone(), p.p))
        .collect();
    let assigned = day.assigned_from(now);
    for (id, p) in &prios {
        if *p != 0 {
            continue;
        }
        assert!(
            assigned.contains(id) || assigned.iter().all(|a| prios
                .iter()
                .find(|(i, _)| i == a)
                .is_some_and(|(_, q)| *q == 0)),
            "{id} (p 0) was left out while a p > 0 item worked:\n{}",
            timeline(&day)
        );
    }
    assert!(
        !assigned.contains(&Id::new("zad")),
        "the queue took a hot item's slot:\n{}",
        timeline(&day)
    );
    assert!(assigned.contains(&Id::new("zaa")));
}

/// [`hot_items_take_the_slots_before_the_queue_on`], asked of the kernel — the arm that survives R3.
#[test]
fn hot_items_take_the_slots_before_the_queue() {
    hot_items_take_the_slots_before_the_queue_on(&Kernel);
}

/// §10.2: `state.json` is a hand-editable file. A nonsense budget must give a
/// day, not a panic in the middle of the TUI's event loop.
fn a_nonsense_budget_does_not_panic_on(p: &dyn DayPlanner) {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    for budget in [0, 1, 100_000_000, u32::MAX] {
        let state = RuntimeState {
            budget: Some(budget),
            ..basic_state()
        };
        let day = p.day(&fx, &state, at("2026-09-07", 7, 0));
        assert_eq!(day.budget_blocks, budget);
        assert!(!day.segments.is_empty());
    }
}

/// [`a_nonsense_budget_does_not_panic_on`], asked of the kernel — the arm that survives R3.
#[test]
fn a_nonsense_budget_does_not_panic() {
    a_nonsense_budget_does_not_panic_on(&Kernel);
}

// ---------------------------------------------------------------------------
// §8.5: the day with no `wake`
// ---------------------------------------------------------------------------

/// §8.5's prior is a step function of hours since wake, but `tm wake` is
/// optional: arriving without it is a normal state. The planner used to fall
/// back to the start of the day, so at 09:21 `hsw` was 9.35 and the lounge
/// curve was in its `8-10 → 3`, `10+ → 2` tail: every ci-4 and ci-5 item was
/// ineligible and the whole day went to ci-2 work. The fallback §8.4 and §16
/// actually name is the weekday's expected arrival, and
/// `Model::wake_or_expected` is the one place both this and the CLI's
/// `Ctx::wake_time` read it from.
fn a_day_with_no_wake_starts_at_the_weekday_expected_arrival_on(p: &dyn DayPlanner) {
    let fx = load("plan-basic");
    let now = at("2026-09-07", 9, 21);
    let arrived = |wake: Option<chrono::NaiveTime>| RuntimeState {
        date: Some(date("2026-09-07")),
        wake,
        arrival: Some(time(9, 20)),
        loc: Some("lounge".to_string()),
        window: Some((time(9, 20), time(18, 20))),
        budget: Some(6),
        ..RuntimeState::default()
    };

    // Nothing logged the wake, and §16's `[expected] arrival` for a Monday is
    // 07:00: the two days are the same day.
    let unknown = p.day(&fx, &arrived(None), now);
    let expected = p.day(&fx, &arrived(Some(time(7, 0))), now);
    assert_eq!(
        timeline(&unknown),
        timeline(&expected),
        "an unlogged wake is the weekday's expected arrival"
    );
    assert!(unknown == expected, "…and the same DayPlan throughout");

    // And that day works: the morning is at the top of the curve, so the ci-5
    // milestone gets its slot.
    let peak = unknown
        .segments
        .iter()
        .filter(|s| matches!(s.kind, SegKind::Block))
        .filter_map(|s| s.energy)
        .max();
    assert_eq!(peak, Some(5), "{}", timeline(&unknown));
    assert!(
        unknown.assigned_from(now).contains(&Id::new("m1")),
        "the ci-5 milestone is planned:\n{}",
        timeline(&unknown)
    );

    // The day the old fallback produced, for contrast: midnight puts every
    // slot in the tail of the curve and no ci-5 item can be placed at all.
    let midnight = p.day(&fx, &arrived(Some(time(0, 0))), now);
    let ci5: Vec<Id> = midnight
        .assigned_from(now)
        .into_iter()
        .filter(|id| ci_of(&fx.tree, id) == 5)
        .collect();
    assert!(
        ci5.is_empty() && midnight != unknown,
        "midnight is the bug, not the fallback: {ci5:?}\n{}",
        timeline(&midnight)
    );
}

/// [`a_day_with_no_wake_starts_at_the_weekday_expected_arrival_on`], asked of the kernel — the arm that survives R3.
#[test]
fn a_day_with_no_wake_starts_at_the_weekday_expected_arrival() {
    a_day_with_no_wake_starts_at_the_weekday_expected_arrival_on(&Kernel);
}

/// §5.3: a routine reaches the day once. The laundry's carried `persist`
/// instance *is* its pending instance, so the occurrence that came round this
/// week is not a second load — the planner used to place both, mandatory in
/// the morning and deferred to the evening.
fn a_persisted_routine_is_not_planned_twice_in_one_day_on(p: &dyn DayPlanner) {
    let fx = load("plan-basic");
    let now = at("2026-09-07", 9, 21);
    let state = RuntimeState {
        date: Some(date("2026-09-07")),
        arrival: Some(time(9, 20)),
        loc: Some("lounge".to_string()),
        window: Some((time(9, 20), time(18, 20))),
        budget: Some(6),
        ..RuntimeState::default()
    };
    let day = p.day(&fx, &state, now);

    let laundry: Vec<String> = day
        .segments
        .iter()
        .filter(|s| s.item.as_ref() == Some(&Id::new("laundry")))
        .map(|s| fmt_clock(s.start))
        .collect();
    assert_eq!(laundry.len(), 1, "one laundry: {laundry:?}\n{}", timeline(&day));

    // The one that survives is keyed on *today's* occurrence — the newest,
    // so `tm routine done laundry` discharges the whole carry in one go —
    // while carrying last week's missed window with it: §5.3's overdue,
    // mandatory instance, which §7.2 puts at `p = 0`.
    let seg = day
        .segments
        .iter()
        .find(|s| s.item.as_ref() == Some(&Id::new("laundry")))
        .expect("laundry is placed");
    assert_eq!(
        seg.instance.map(|k| k.to_string()).as_deref(),
        Some("2026-09-07")
    );
    assert!(seg.flags.mandatory, "still §5.2 mandatory: {:?}", seg.flags);
    let ps: Vec<u8> = day
        .priorities
        .iter()
        .filter(|(id, _)| id.as_str() == "laundry")
        .map(|(_, p)| p.p)
        .collect();
    assert_eq!(ps, vec![0], "one row in §10.2's per-id map");
}

/// [`a_persisted_routine_is_not_planned_twice_in_one_day_on`], asked of the kernel — the arm that survives R3.
#[test]
fn a_persisted_routine_is_not_planned_twice_in_one_day() {
    a_persisted_routine_is_not_planned_twice_in_one_day_on(&Kernel);
}

/// The timezone every fixture uses, kept honest.
#[test]
fn the_fixtures_plan_in_the_configured_zone() {
    let fx = load("plan-home-day");
    assert_eq!(fx.cfg.tz, TZ);
}

// ---------------------------------------------------------------------------
// §5.1 / §8.2 steps 2 and 6: a routine stays inside its daily window
// ---------------------------------------------------------------------------

/// `win:HH:MM-HH:MM` is the daily window on the date (§5.1). An occurrence
/// that spans several days — `every:week`, `after-done:2d~1d` — reports one
/// span covering all of them (`2026-09-07T10:00 .. 2026-09-13T20:00` for the
/// weekly groceries), and the planner used to clip that to today alone, which
/// leaves 00:00–24:00: the routine was then placed anywhere left in the day.
fn a_multi_day_occurrence_keeps_its_daily_hours_on(p: &dyn DayPlanner) {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = basic_state();

    // 20:00, after `groceries win:10:00-20:00 every:week` has closed for the
    // day: it must not be placed at all, never at 20:20.
    let evening = p.day(&fx, &state, at("2026-09-07", 20, 0));
    for seg in &evening.segments {
        if seg.item.as_ref() == Some(&Id::new("groceries")) {
            panic!(
                "groceries placed outside its 10:00–20:00 window\n{}",
                timeline(&evening)
            );
        }
    }

    // Earlier the same evening, `laundry win:09:00-21:00` may still be placed
    // — but only before 21:00.
    let late = p.day(&fx, &state, at("2026-09-07", 17, 50));
    for seg in &late.segments {
        if seg.item.as_ref() == Some(&Id::new("laundry")) {
            assert!(
                seg.end <= at("2026-09-07", 21, 0),
                "laundry ends after its window closes\n{}",
                timeline(&late)
            );
        }
    }

    // And a window that has not opened yet still holds the routine back:
    // `vitamins win:07:00-11:00 after-done:2d` at 05:00.
    let recur = load("plan-recur");
    let early_state = RuntimeState {
        date: Some(date("2026-09-07")),
        wake: Some(time(4, 30)),
        arrival: Some(time(5, 0)),
        loc: Some("lounge".to_string()),
        window: Some((time(5, 0), time(14, 0))),
        budget: Some(6),
        ..RuntimeState::default()
    };
    let dawn = p.day(&recur, &early_state, at("2026-09-07", 5, 0));
    for seg in &dawn.segments {
        if seg.item.as_ref() == Some(&Id::new("vitamins")) {
            assert!(
                seg.start >= at("2026-09-07", 7, 0),
                "vitamins placed before its window opens\n{}",
                timeline(&dawn)
            );
        }
    }
}

/// [`a_multi_day_occurrence_keeps_its_daily_hours_on`], asked of the kernel — the arm that survives R3.
#[test]
fn a_multi_day_occurrence_keeps_its_daily_hours() {
    a_multi_day_occurrence_keeps_its_daily_hours_on(&Kernel);
}


// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gaps 2722, 2872)
//
// Each property above, asked of the fork's planner with its own §7 pass — what
// this suite pinned until W-36 track H. R3 deletes this region whole and the
// kernel arm above is what remains.
use planner_common::Fork;

#[test]
fn the_running_block_takes_no_slot_below_its_ci_on_the_fork() {
    the_running_block_takes_no_slot_below_its_ci_on(&Fork);
}

#[test]
fn the_running_block_survives_an_exhausted_cap_on_the_fork() {
    the_running_block_survives_an_exhausted_cap_on(&Fork);
}

#[test]
fn a_mandatory_routine_never_lands_on_the_running_block_on_the_fork() {
    a_mandatory_routine_never_lands_on_the_running_block_on(&Fork);
}

#[test]
fn the_elapsed_part_of_the_running_block_is_on_the_timeline_on_the_fork() {
    the_elapsed_part_of_the_running_block_is_on_the_timeline_on(&Fork);
}

#[test]
fn the_running_block_shows_when_the_budget_is_spent_on_the_fork() {
    the_running_block_shows_when_the_budget_is_spent_on(&Fork);
}

#[test]
fn an_open_interruption_grows_and_never_moves_on_the_fork() {
    an_open_interruption_grows_and_never_moves_on(&Fork);
}

#[test]
fn small_items_share_one_block_on_the_fork() {
    small_items_share_one_block_on(&Fork);
}

#[test]
fn a_batch_never_carries_one_members_location_onto_another_on_the_fork() {
    a_batch_never_carries_one_members_location_onto_another_on(&Fork);
}

#[test]
fn an_atomic_item_may_run_through_a_planned_break_on_the_fork() {
    an_atomic_item_may_run_through_a_planned_break_on(&Fork);
}

#[test]
fn a_deferred_routine_never_lands_on_a_break_on_the_fork() {
    a_deferred_routine_never_lands_on_a_break_on(&Fork);
}

#[test]
fn a_break_comes_after_every_two_blocks_on_the_fork() {
    a_break_comes_after_every_two_blocks_on(&Fork);
}

#[test]
fn no_demanding_block_after_wind_down_on_the_fork() {
    no_demanding_block_after_wind_down_on(&Fork);
}

#[test]
fn the_diagnostics_are_produced_where_the_spec_says_on_the_fork() {
    the_diagnostics_are_produced_where_the_spec_says_on(&Fork);
}

#[test]
fn a_posterior_downgrade_defers_the_high_ci_item_on_the_fork() {
    a_posterior_downgrade_defers_the_high_ci_item_on(&Fork);
}

#[test]
fn plan_honesty_measures_what_the_day_starts_on_the_fork() {
    plan_honesty_measures_what_the_day_starts_on(&Fork);
}

#[test]
fn hot_items_take_the_slots_before_the_queue_on_the_fork() {
    hot_items_take_the_slots_before_the_queue_on(&Fork);
}

#[test]
fn a_nonsense_budget_does_not_panic_on_the_fork() {
    a_nonsense_budget_does_not_panic_on(&Fork);
}

#[test]
fn a_day_with_no_wake_starts_at_the_weekday_expected_arrival_on_the_fork() {
    a_day_with_no_wake_starts_at_the_weekday_expected_arrival_on(&Fork);
}

#[test]
fn a_persisted_routine_is_not_planned_twice_in_one_day_on_the_fork() {
    a_persisted_routine_is_not_planned_twice_in_one_day_on(&Fork);
}

#[test]
fn a_multi_day_occurrence_keeps_its_daily_hours_on_the_fork() {
    a_multi_day_occurrence_keeps_its_daily_hours_on(&Fork);
}
// END THE FORK PLANNER
