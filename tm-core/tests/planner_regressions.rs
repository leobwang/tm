//! Regression tests for the review findings on §8/§9 — one test per bug, each
//! named after the rule it broke.
//!
//! The §8.3 invariants live in `planner_invariants.rs` as properties and the
//! fixture days in `planner_fixtures.rs`; what is here are the cases those two
//! could not reach: a block that is *running* (`state.active`), an open
//! interruption, a batch of mixed `loc:`, an `atomic` item longer than the
//! stretch between two breaks, an evening that reaches the wind-down, and the
//! diagnostics nothing else asserts.

mod planner_common;

use chrono::{DateTime, Duration};
use chrono_tz::Tz;
use planner_common::{
    assert_break_rule, at, basic_state, date, load, load_with_log, time, timeline, BASIC_LOG, TZ,
};
use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::{self, Log, Replay};
use tm_core::model::Id;
use tm_core::planner::{self, DayPlan, PlanInput, SegKind, Segment};
use tm_core::store::{ActiveBlock, InterruptState, RuntimeState};
use tm_core::tree::Tree;

// ---------------------------------------------------------------------------
// A synthetic day: a week file, a log, and nothing else
// ---------------------------------------------------------------------------

/// A hand-written week (and optional calendar) with its own log — the smallest
/// world a planner test can run in.
struct World {
    tree: Tree,
    cfg: Config,
    log: Log,
    replay: Replay,
    model: Model,
}

impl World {
    fn new(week: &str, calendar: &str, log_text: &str) -> World {
        let cfg = Config::default();
        let tree = Tree::from_texts(
            &[
                ("week/2026-W37.md", week),
                ("calendar/2026-W37.md", calendar),
            ],
            &cfg,
        );
        assert!(tree.problems().is_empty(), "{:?}", tree.problems());
        let log = Log::parse(log_text);
        assert!(log.warnings.is_empty(), "{:?}", log.warnings);
        let replay = log::replay(&log.entries, None, cfg.tz);
        World {
            tree,
            cfg,
            log,
            replay,
            model: Model::default(),
        }
    }

    fn input<'a>(&'a self, state: &'a RuntimeState, now: DateTime<Tz>) -> PlanInput<'a> {
        PlanInput::new(
            &self.tree,
            &self.log,
            &self.replay,
            &self.cfg,
            &self.model,
            state,
            now,
        )
    }
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
#[test]
fn the_running_block_takes_no_slot_below_its_ci() {
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
        let day = planner::plan(&fx.input(&state, now));
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

/// §9: "the Active item keeps its current slot regardless of key" — including
/// when §8.2 step 5 would refuse the item. A `max:`-exhausted (or dep-blocked)
/// item forms no assignable group, and the block running right now must not
/// vanish from the timeline because of it.
#[test]
fn the_running_block_survives_an_exhausted_cap() {
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
    let day = planner::plan(&fx.input(&state, now));
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

/// §9: "Active block paused" — an interruption, not a routine, is what stops
/// it. Step 2 must not place a mandatory instance on top of a block that is
/// running right now.
#[test]
fn a_mandatory_routine_never_lands_on_the_running_block() {
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
        let day = planner::plan(&fx.input(&state, now));
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

/// §12.1: left of the cursor the timeline is the log. A block that is still
/// running has no closed sub-segment, so the minutes it has been running for
/// were covered by nothing at all — a hole in the day bar.
#[test]
fn the_elapsed_part_of_the_running_block_is_on_the_timeline() {
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
    let day = planner::plan(&fx.input(&state, now));
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

/// §9 / §9.1: the overtime prompt runs in exactly the state where the budget is
/// spent. A plan that drops the running block there tells the user to stop
/// working on something they are working on, and `overtime_drops` would diff
/// two plans neither of which holds the item.
#[test]
fn the_running_block_shows_when_the_budget_is_spent() {
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
    let day = planner::plan(&fx.input(&state, now));
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

/// §9: an open interruption is an ad-hoc wall "from t_i to now" — it has no end
/// yet, so a later replan necessarily shows it longer. §8.3's stability
/// invariant is about settled segments; [`tm_core::planner::SegFlags::open`]
/// says which segment is not one, and the growth is all it may do.
#[test]
fn an_open_interruption_grows_and_never_moves() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = RuntimeState {
        interrupt: Some(InterruptState {
            started: Some(time(12, 10)),
            id: Some(Id::new("t4")),
        }),
        ..basic_state()
    };
    let (t1, t2) = (at("2026-09-07", 13, 5), at("2026-09-07", 13, 35));
    let early = planner::plan(&fx.input(&state, t1));
    let later = planner::plan(&fx.input(&state, t2));
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

// ---------------------------------------------------------------------------
// §7.5 batching and §8.2 step 5's filters
// ---------------------------------------------------------------------------

/// §7.5: several small items share one block — the whole reason the `+3` bin
/// ever gets a slot.
#[test]
fn small_items_share_one_block() {
    let week = week_header(
        "- [ ] 3 15m Errand one !1 ^zaa\n\
         - [ ] 3 15m Errand two !1 ^zab\n\
         - [ ] 3 10m Errand three !1 ^zac\n\
         - [ ] 3 20m Errand four !1 ^zad\n",
    );
    let w = World::new(&week, "", ARRIVED);
    let state = synthetic_state();
    let day = planner::plan(&w.input(&state, at("2026-09-07", 7, 0)));
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

/// §8.2 step 5's `loc` filter is written about the item. §7.5 batches by `ci`
/// and size alone, so a batch may mix a `loc:out` errand with a desk task:
/// neither may ride the other into a slot, or out of the day.
#[test]
fn a_batch_never_carries_one_members_location_onto_another() {
    for week in [
        "- [ ] 3 15m Desk thing !1 ^zaa\n- [ ] 3 15m Post the parcel !1 loc:out ^zab\n",
        // …and the other way round: the errand first must not take the desk
        // task out of the day with it.
        "- [ ] 3 15m Post the parcel !1 loc:out ^zab\n- [ ] 3 15m Desk thing !1 ^zaa\n",
    ] {
        let w = World::new(&week_header(week), "", ARRIVED);
        let state = RuntimeState {
            loc: Some("lounge".to_string()),
            ..synthetic_state()
        };
        let day = planner::plan(&w.input(&state, at("2026-09-07", 7, 0)));
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

/// §8.2 step 5: "if !splittable: contiguous free slots ≥ remaining exist
/// **before the next wall**". The 20-minute break the planner itself inserts is
/// not a wall — reading it as one makes every `atomic` item longer than
/// `break_after_blocks × block_min` unplaceable on any day at all.
#[test]
fn an_atomic_item_may_run_through_a_planned_break() {
    let w = World::new(
        &week_header("- [ ] 3 3b Long atomic thing !1 atomic ^zaa\n"),
        "",
        ARRIVED,
    );
    let state = synthetic_state();
    let now = at("2026-09-07", 7, 0);
    let day = planner::plan(&w.input(&state, now));
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
    let walled = World::new(
        &week_header("- [ ] 3 3b Long atomic thing !1 atomic ^zaa\n"),
        "- [ ] 3 Wall at:2026-09-07T09:00/16:00 ^waa\n",
        ARRIVED,
    );
    let day = planner::plan(&walled.input(&state, now));
    assert!(
        !day.assigned().contains(&Id::new("zaa")),
        "two hours is not three blocks:\n{}",
        timeline(&day)
    );
}

// ---------------------------------------------------------------------------
// §8.2 steps 3 and 6
// ---------------------------------------------------------------------------

/// §8.2 step 6 places a deferred routine into a *free* position: the breaks
/// step 3 cut are not free, and a routine laid over one used to be emitted
/// twice — the break and the routine, at the same minute.
#[test]
fn a_deferred_routine_never_lands_on_a_break() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    for (h, m) in [(7, 0), (8, 30), (9, 45), (11, 0), (13, 0)] {
        for loc in ["lounge", "home"] {
            let state = RuntimeState {
                loc: Some(loc.to_string()),
                ..basic_state()
            };
            let day = planner::plan(&fx.input(&state, at("2026-09-07", h, m)));
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

/// §8.2 step 3: "a break of `break_min` after every `break_after_blocks`
/// blocks" — the rule, not just the presence of one break somewhere.
#[test]
fn a_break_comes_after_every_two_blocks() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    for (h, m) in [(7, 0), (9, 45), (11, 0)] {
        let now = at("2026-09-07", h, m);
        let day = planner::plan(&fx.input(&basic_state(), now));
        assert_break_rule(&day, now, &fx.cfg);
    }
    let w = World::new(
        &week_header("- [ ] 3 8b Long thing !1 ^zaa\n"),
        "",
        ARRIVED,
    );
    let now = at("2026-09-07", 7, 0);
    let day = planner::plan(&w.input(&synthetic_state(), now));
    assert_break_rule(&day, now, &w.cfg);
    assert!(
        day.segments
            .iter()
            .filter(|s| s.kind == SegKind::Break && s.start >= now)
            .count()
            >= 2,
        "six blocks need two breaks:\n{}",
        timeline(&day)
    );
}

/// §8.3: "no ci ≥ 4 Block after wind-down". The fixture days end long before
/// 21:30; §8.1's window can reach past it — a late arrival and an evening wall
/// push the end into the night — and the rule has to hold there.
#[test]
fn no_demanding_block_after_wind_down() {
    let w = World::new(
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
    let day = planner::plan(&w.input(&state, now));
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

// ---------------------------------------------------------------------------
// §8.2 step 8 and §11
// ---------------------------------------------------------------------------

/// The five diagnostics no snapshot shows (they are all `·` on the fixture
/// days) and the two §11 monitors: each one on a day that produces it.
#[test]
fn the_diagnostics_are_produced_where_the_spec_says() {
    // `underused` and the `↓` flag: a ci-1 item in a slot of energy 5.
    let w = World::new(&week_header("- [ ] 1 2b Filing !1 ^zaa\n"), "", ARRIVED);
    let day = planner::plan(&w.input(&synthetic_state(), at("2026-09-07", 7, 0)));
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
    let w = World::new(
        &week_header("- [ ] 3 20b Impossible thing due:2026-09-07T23:59 ^zaa\n"),
        "",
        ARRIVED,
    );
    let day = planner::plan(&w.input(&synthetic_state(), at("2026-09-07", 7, 0)));
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
    let w = World::new(
        &week_header("- [ ] 3 2b Work !1 ^zaa\n"),
        "- [ ] 3 Meeting at:2026-09-07T10:00/12:00 ^waa\n\
         - [ ] 3 Other meeting at:2026-09-07T11:00/13:00 ^wab\n",
        ARRIVED,
    );
    let day = planner::plan(&w.input(&synthetic_state(), at("2026-09-07", 7, 0)));
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
    let day = planner::plan(&fx.input(&basic_state(), at("2026-09-07", 9, 30)));
    assert_eq!(day.diagnostics.rest_debt_min, 10, "20m planned, 10m taken");
}

/// §8.2 step 8's `deferred`: an energy report that lowers today's curve costs a
/// ci-5 item the slot the raw prediction had for it.
#[test]
fn a_posterior_downgrade_defers_the_high_ci_item() {
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
    let w = World::new(&week, "", &downgraded);
    let day = planner::plan(&w.input(&synthetic_state(), at("2026-09-07", 7, 30)));
    assert!(
        day.diagnostics.deferred.contains(&Id::new("zaa")),
        "{:?}\n{}",
        day.diagnostics,
        timeline(&day)
    );
    assert!(!day.assigned().contains(&Id::new("zaa")));
    // Without the report the same day works it.
    let w = World::new(&week, "", ARRIVED);
    let day = planner::plan(&w.input(&synthetic_state(), at("2026-09-07", 7, 30)));
    assert!(day.assigned().contains(&Id::new("zaa")), "{}", timeline(&day));
    assert!(day.diagnostics.deferred.is_empty());
}

/// §11's plan honesty, pinned: `Σ` the minutes every group the day *starts*
/// still needs, over `remaining_budget × block_min`. It is above 1 exactly when
/// the day opens more work than it can finish — which is what the monitor's
/// "warning when > 1.1" is for, and the only reading under which the ratio can
/// exceed 1 at all (assignment itself never exceeds the budget).
#[test]
fn plan_honesty_measures_what_the_day_starts() {
    // One block of work in a six-block day: 60 / 360.
    let w = World::new(&week_header("- [ ] 3 1b One block !1 ^zaa\n"), "", ARRIVED);
    let day = planner::plan(&w.input(&synthetic_state(), at("2026-09-07", 7, 0)));
    let honesty = day.diagnostics.plan_honesty.expect("a budget of six blocks");
    assert!((honesty - 60.0 / 360.0).abs() < 0.01, "{honesty}");

    // A single milestone twice the size of the day: 12b of 6b = 2.0, and the
    // monitor warns.
    let w = World::new(&week_header("- [ ] 3 12b One big thing !1 ^zaa\n"), "", ARRIVED);
    let day = planner::plan(&w.input(&synthetic_state(), at("2026-09-07", 7, 0)));
    let honesty = day.diagnostics.plan_honesty.expect("a budget of six blocks");
    assert!((honesty - 2.0).abs() < 0.01, "{honesty}");
    assert!(honesty > 1.1, "the day is over-committed");

    // A travel day spends nothing, so there is no ratio to report.
    let fx = load("plan-travel-day");
    let day = planner::plan(&fx.input(&fx.state, at("2026-09-07", 7, 0)));
    assert_eq!(day.diagnostics.plan_honesty, None);
}

/// §7.2/§8.3: HOT before queue. Four `p = 0` items and three slots — the day
/// works the hot ones, in key order, and no `p > 0` item takes their place.
#[test]
fn hot_items_take_the_slots_before_the_queue() {
    let week = week_header(
        "- [ ] 3 2b Hot one due:2026-09-07T23:59 !2 ^zaa\n\
         - [ ] 3 2b Hot two due:2026-09-07T23:59 !2 ^zab\n\
         - [ ] 3 2b Hot three due:2026-09-07T23:59 !2 ^zac\n\
         - [ ] 3 6b Ordinary work !1 ^zad\n",
    );
    let w = World::new(&week, "", ARRIVED);
    let state = RuntimeState {
        budget: Some(3),
        ..synthetic_state()
    };
    let now = at("2026-09-07", 7, 0);
    let day = planner::plan(&w.input(&state, now));
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

/// §10.2: `state.json` is a hand-editable file. A nonsense budget must give a
/// day, not a panic in the middle of the TUI's event loop.
#[test]
fn a_nonsense_budget_does_not_panic() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    for budget in [0, 1, 100_000_000, u32::MAX] {
        let state = RuntimeState {
            budget: Some(budget),
            ..basic_state()
        };
        let day = planner::plan(&fx.input(&state, at("2026-09-07", 7, 0)));
        assert_eq!(day.budget_blocks, budget);
        assert!(!day.segments.is_empty());
    }
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
#[test]
fn a_day_with_no_wake_starts_at_the_weekday_expected_arrival() {
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
    let unknown = planner::plan(&fx.input(&arrived(None), now));
    let expected = planner::plan(&fx.input(&arrived(Some(time(7, 0))), now));
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
    let midnight = planner::plan(&fx.input(&arrived(Some(time(0, 0))), now));
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

/// §5.3: a routine reaches the day once. The laundry's carried `persist`
/// instance *is* its pending instance, so the occurrence that came round this
/// week is not a second load — the planner used to place both, mandatory in
/// the morning and deferred to the evening.
#[test]
fn a_persisted_routine_is_not_planned_twice_in_one_day() {
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
    let day = planner::plan(&fx.input(&state, now));

    let laundry: Vec<String> = day
        .segments
        .iter()
        .filter(|s| s.item.as_ref() == Some(&Id::new("laundry")))
        .map(|s| planner::fmt_clock(s.start))
        .collect();
    assert_eq!(laundry.len(), 1, "one laundry: {laundry:?}\n{}", timeline(&day));

    // The one that survives is last week's missed window: §5.3's overdue,
    // mandatory instance, which §7.2 puts at `p = 0`.
    let seg = day
        .segments
        .iter()
        .find(|s| s.item.as_ref() == Some(&Id::new("laundry")))
        .expect("laundry is placed");
    assert_eq!(
        seg.instance.map(|k| k.to_string()).as_deref(),
        Some("2026-08-31")
    );
    let ps: Vec<u8> = day
        .priorities
        .iter()
        .filter(|(id, _)| id.as_str() == "laundry")
        .map(|(_, p)| p.p)
        .collect();
    assert_eq!(ps, vec![0], "one row in §10.2's per-id map");
}

/// The timezone every fixture uses, kept honest.
#[test]
fn the_fixtures_plan_in_the_configured_zone() {
    let fx = load("plan-home-day");
    assert_eq!(fx.cfg.tz, TZ);
}
