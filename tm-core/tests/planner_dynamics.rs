//! §9 dynamic adjustment on the `plan-basic` fixture — the Active block keeps
//! its slot, an interruption is an ad-hoc wall, a lost block drops the tail —
//! plus §9.1's "x extend → drops: …", §13's `tm plan --diff`,
//! `tm plan --explain ^id`, `tm plan --allow-home` and `tm plan --week`.

mod planner_common;

use planner_common::{at, date, load, load_with_log, time, timeline, BASIC_LOG};
use tm_core::energy::Model;
use tm_core::model::Id;
use tm_core::planner::{self, DayPlan, PlanOverrides, SegKind};
use tm_core::priority::{self, Candidate};
use tm_core::store::{ActiveBlock, InterruptState, RuntimeState};

/// The morning of §4.3: wake, breakfast, arrive, two blocks worked, a break.
const MORNING: &str = concat!(
    r#"{"t":"2026-09-07T06:05:00-05:00","ev":"wake","slept_min":490}"#,
    "\n",
    r#"{"t":"2026-09-07T06:40:00-05:00","ev":"routine","item":"breakfast","inst":"2026-09-07","status":"done","actual_min":30}"#,
    "\n",
    r#"{"t":"2026-09-07T07:00:00-05:00","ev":"arrive","loc":"lounge","window":["07:00","16:00"],"budget":6}"#,
    "\n",
    r#"{"t":"2026-09-07T07:02:00-05:00","ev":"start","id":"t1","pred":5,"rep":5,"hsw":0.95,"slept_min":490,"loc":"lounge","blocks_done":0,"since_break_min":0}"#,
    "\n",
    r#"{"t":"2026-09-07T08:09:00-05:00","ev":"done","id":"t1","est_min":60,"actual_min":67,"went":1,"tags":["lean"],"ci":5}"#,
    "\n",
    r#"{"t":"2026-09-07T08:10:00-05:00","ev":"start","id":"t4","pred":5,"rep":5,"hsw":2.08,"slept_min":490,"loc":"lounge","blocks_done":1,"since_break_min":67}"#,
    "\n",
    r#"{"t":"2026-09-07T09:08:00-05:00","ev":"done","id":"t4","est_min":60,"actual_min":58,"went":1,"tags":[],"ci":3}"#,
    "\n",
    r#"{"t":"2026-09-07T09:08:00-05:00","ev":"break","planned_min":20,"actual_min":10,"where":"walk"}"#,
    "\n",
);

use planner_common::basic_state as arrived;

fn candidates(fx: &planner_common::Fixture, now: chrono::DateTime<chrono_tz::Tz>) -> Vec<Candidate> {
    priority::collect_candidates(
        &fx.tree,
        &fx.replay,
        &fx.cfg,
        &Model::default(),
        date("2026-09-07"),
        now,
    )
}

// ---------------------------------------------------------------------------
// Purity and stability (§8.3, §17.2)
// ---------------------------------------------------------------------------

/// The same input twice gives the same plan, and the same hash.
#[test]
fn plan_is_pure() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = arrived();
    let input = fx.input(&state, at("2026-09-07", 7, 0));
    let a = planner::plan(&input);
    let b = planner::plan(&input);
    assert_eq!(a, b);
    assert_eq!(a.hash(), b.hash());
    assert_eq!(a.hash().len(), 16);
}

/// A replan later in the day never rewrites what already happened: every
/// segment of the 07:00 plan that had ended by 09:30 is still in the 09:30
/// plan, byte for byte.
#[test]
fn a_replan_never_moves_the_past() {
    let fx = load_with_log("plan-basic", Some(MORNING));
    let state = arrived();
    let early = planner::plan(&fx.input(&state, at("2026-09-07", 7, 0)));
    let later = planner::plan(&fx.input(&state, at("2026-09-07", 9, 30)));
    let cutoff = at("2026-09-07", 7, 0);
    for seg in early.segments.iter().filter(|s| s.end <= cutoff) {
        assert!(
            later.segments.contains(seg),
            "the replan moved a settled segment: {seg:?}"
        );
    }
    // The blocks the log already holds are in the later plan, marked done.
    let t1 = later
        .segments
        .iter()
        .find(|s| s.item.as_ref().is_some_and(|i| i.as_str() == "t1"))
        .expect("^t1 was worked this morning");
    assert_eq!(t1.start, at("2026-09-07", 7, 2));
    assert!(t1.flags.done);
    // Two blocks are gone from the budget (§8.1): the plan from 09:30 on may
    // spend four, whatever the morning already cost.
    let from = at("2026-09-07", 9, 30);
    assert!(
        later.planned_block_minutes(from) <= 4 * 60,
        "{}",
        timeline(&later)
    );
}

// ---------------------------------------------------------------------------
// §9: the Active block, interruptions, the dropped tail
// ---------------------------------------------------------------------------

/// §9: "Active item keeps its current slot regardless of key (no preemption
/// mid-block)", with `est_min − elapsed` minutes still to run. The running
/// block is reserved from `now`, so nothing else — no routine, no higher-key
/// item, no break — is planned on top of it.
#[test]
fn the_active_block_keeps_the_slot_containing_now() {
    let fx = load_with_log("plan-basic", Some(MORNING));
    let state = RuntimeState {
        active: Some(ActiveBlock {
            id: Id::new("m4"), // `Pick winter courses`, ci 2, p 5 — last in key order
            started: time(9, 30),
            est_min: 120,
            paused: false,
        }),
        ..arrived()
    };
    let now = at("2026-09-07", 10, 0);
    let day = planner::plan(&fx.input(&state, now));
    let current = day
        .current_segment()
        .unwrap_or_else(|| panic!("a block is running:\n{}", timeline(&day)));
    assert_eq!(current.item.as_deref_id(), Some("m4"));
    assert!(current.kind.is_work());
    // 120 − 30 elapsed = 90 minutes still to run, from `now`.
    assert_eq!(current.start, now);
    assert_eq!(current.end, at("2026-09-07", 11, 30));
    assert_eq!(current.flags.planned_min, Some(90));
    // Exactly one `▶`, and nothing at all overlaps the running block.
    assert_eq!(
        day.segments.iter().filter(|s| s.flags.current).count(),
        1,
        "{}",
        timeline(&day)
    );
    for seg in day.segments.iter().filter(|s| !s.flags.current) {
        assert!(
            seg.end <= current.start || seg.start >= current.end,
            "{seg:?} runs over the block that is running:\n{}",
            timeline(&day)
        );
    }
}

/// §9: an interruption that has not been resumed is an ad-hoc wall from its
/// start to `now`, and the day flows around it.
#[test]
fn an_open_interruption_is_a_wall_up_to_now() {
    let fx = load_with_log("plan-basic", Some(MORNING));
    let state = RuntimeState {
        interrupt: Some(InterruptState {
            started: Some(time(12, 10)),
            id: Some(Id::new("t4")),
        }),
        ..arrived()
    };
    let now = at("2026-09-07", 13, 5);
    let day = planner::plan(&fx.input(&state, now));
    let lost = day
        .segments
        .iter()
        .find(|s| s.kind == SegKind::Lost)
        .expect("the interruption is on the timeline");
    assert_eq!(lost.start, at("2026-09-07", 12, 10));
    assert_eq!(lost.end, now);
    // Nothing is planned inside it, and the window is *not* extended by it
    // (§9: an interruption drops the tail, it does not lengthen the day).
    assert_eq!(day.window.1, at("2026-09-07", 16, 0));
    for seg in day.segments.iter().filter(|s| s.kind.is_work() && s.end > now) {
        assert!(seg.start >= now, "{seg:?}");
    }
}

/// §8.3's tail-drop, in its operational form: taking a block away from the day
/// never re-shuffles the plan — every slot both days keep holds the same item,
/// and the smaller day's assigned set is a subset of the larger one's.
#[test]
fn losing_a_block_drops_a_tail_and_nothing_else() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let now = at("2026-09-07", 7, 0);
    let full = planner::plan(&fx.input(&arrived(), now));
    let short_state = RuntimeState {
        budget: Some(5),
        ..arrived()
    };
    let short = planner::plan(&fx.input(&short_state, now));

    let starts = |p: &DayPlan| -> Vec<(String, Vec<Id>)> {
        p.segments
            .iter()
            .filter(|s| s.kind.is_work())
            .map(|s| (planner::fmt_clock(s.start), s.items()))
            .collect()
    };
    let (a, b) = (starts(&full), starts(&short));
    assert!(b.len() < a.len(), "a block was lost");
    assert_eq!(b, a[..b.len()], "the kept slots hold the same items");
    for id in short.assigned() {
        assert!(full.assigned().contains(&id), "{id} appeared out of nowhere");
    }
}

// ---------------------------------------------------------------------------
// §9.1 the overtime prompt
// ---------------------------------------------------------------------------

/// §9.1: `x extend +1 block → drops: …`. The prompt runs `plan()` with the
/// option applied and diffs; [`planner::overtime_drops`] is that call.
#[test]
fn extending_a_block_names_what_it_drops() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let now = at("2026-09-07", 7, 0);
    let base = planner::plan(&fx.input(&arrived(), now));
    let drops = planner::overtime_drops(&fx.input(&arrived(), now), &Id::new("t3"), 1);
    // Everything named was in the day and is not any more.
    for id in &drops {
        assert!(base.assigned().contains(id), "{id} was not planned anyway");
    }
    let extended = PlanOverrides::new().extending(&Id::new("t3"), 60);
    let alt = planner::plan(&fx.input(&arrived(), now).with_overrides(&extended));
    for id in &drops {
        assert!(!alt.assigned().contains(id));
    }
    // The extension itself is honoured: ^t3 gets more of the day.
    let minutes = |p: &DayPlan, id: &str| -> u32 {
        p.segments
            .iter()
            .filter(|s| s.kind.is_work() && s.items().iter().any(|i| i.as_str() == id))
            .map(tm_core::planner::Segment::minutes)
            .sum()
    };
    assert!(minutes(&alt, "t3") > minutes(&base, "t3"), "{}", timeline(&alt));

    // `d done` is the same machinery with a drop: the item leaves the day and
    // the tail moves up.
    let done = PlanOverrides::new().dropping(&Id::new("t3"));
    let after = planner::plan(&fx.input(&arrived(), now).with_overrides(&done));
    assert!(!after.assigned().contains(&Id::new("t3")));
}

// ---------------------------------------------------------------------------
// §13 tm plan --diff
// ---------------------------------------------------------------------------

/// `tm plan --diff` (§13) and the `plan` event's `drift_min` (§10.1, §11).
#[test]
fn diff_reports_what_moved_and_the_drift() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let now = at("2026-09-07", 7, 0);
    let before = planner::plan(&fx.input(&arrived(), now));
    assert!(planner::diff(&before, &before).is_empty());
    assert_eq!(planner::diff(&before, &before).drift_min, 0);

    // Replanning half an hour later shifts the whole grid: that is drift.
    let later = planner::plan(&fx.input(&arrived(), at("2026-09-07", 7, 30)));
    let shift = planner::diff(&before, &later);
    assert!(!shift.moved.is_empty(), "{shift:?}");
    assert!(shift.drift_min > 0, "{shift:?}");
    let sum: u32 = shift
        .moved
        .iter()
        .map(|(_, a, b)| (*b - *a).num_minutes().unsigned_abs() as u32)
        .sum();
    assert_eq!(shift.drift_min, sum);
    for (id, old, new) in &shift.moved {
        assert_ne!(old, new, "{id} is listed as moved but did not move");
    }

    // Extending the first task pushes work out of the day: that is a drop.
    let extended = PlanOverrides::new().extending(&Id::new("t3"), 120);
    let after = planner::plan(&fx.input(&arrived(), now).with_overrides(&extended));
    let d = planner::diff(&before, &after);
    assert!(!d.is_empty());
    // Everything removed really is gone, everything added really is new.
    for id in &d.removed {
        assert!(before.assigned().contains(id) || before.segment_of(id).is_some());
        assert!(after.segment_of(id).is_none());
    }
    for id in &d.added {
        assert!(before.segment_of(id).is_none());
    }
}

// ---------------------------------------------------------------------------
// §13 tm plan --explain ^id
// ---------------------------------------------------------------------------

/// §13: `p = k(3) + bin(u=0.31 → +1) = 4; slot 11:50 energy 4, ci 3, gap 1;
/// deps ok; cap 2b/d: 1b used` — §7's half from `priority`, §8's from the plan.
#[test]
fn explain_completes_the_priority_line_with_the_slot() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = arrived();
    let now = at("2026-09-07", 7, 0);
    let day = planner::plan(&fx.input(&state, now));
    let cands = candidates(&fx, now);

    let placed = planner::explain(&day, &Id::new("t3"), &cands, &fx.cfg);
    assert!(placed.contains("slot 07:00 energy 4, ci 4, gap 0"), "{placed}");
    insta::assert_snapshot!("explain_t3_planned", placed);

    // An item that got no slot says so where the slot part goes.
    let dropped = planner::explain(&day, &Id::new("p1"), &cands, &fx.cfg);
    assert!(dropped.contains("no slot"), "{dropped}");
    insta::assert_snapshot!("explain_p1_dropped", dropped);

    // A blocked item keeps `priority`'s reason.
    let blocked = planner::explain(&day, &Id::new("t5"), &cands, &fx.cfg);
    assert!(blocked.contains("blocked by ^t4"), "{blocked}");

    assert_eq!(
        planner::explain(&day, &Id::new("nope"), &cands, &fx.cfg),
        "^nope is not a candidate today"
    );
}

// ---------------------------------------------------------------------------
// §13 tm plan --allow-home
// ---------------------------------------------------------------------------

/// `--allow-home` lifts §8.2 step 3's `home_max_ci` cap: the same home day
/// gets its high-`ci` slots back and the milestones become workable.
#[test]
fn allow_home_lifts_the_home_cap() {
    let fx = load("plan-home-day");
    let now = at("2026-09-07", 9, 0);
    let capped = planner::plan(&fx.input(&fx.state, now));
    let lifted = planner::plan(&fx.input(&fx.state, now).with_allow_home(true));

    let top = |p: &DayPlan| -> u8 {
        p.segments
            .iter()
            .filter_map(|s| s.energy)
            .max()
            .unwrap_or(0)
    };
    assert_eq!(top(&capped), fx.cfg.location.home_max_ci);
    assert!(top(&lifted) > fx.cfg.location.home_max_ci, "{}", timeline(&lifted));
    // The `ci 4` milestone becomes workable; `ci 5` still is not, because the
    // *home energy curve* itself tops out at 4 (§16's `energy.prior.home`).
    assert!(
        lifted.assigned().contains(&Id::new("m2")),
        "the ci-4 milestone is workable again: {}",
        timeline(&lifted)
    );
    assert!(!capped.assigned().contains(&Id::new("m2")));
}

// ---------------------------------------------------------------------------
// §13 tm plan --week
// ---------------------------------------------------------------------------

/// `tm plan --week` (§8.4): today is the real plan, the rest of the week is
/// the capacity grid with a light EDF-ish allocation on top.
#[test]
fn week_plan_fills_the_grid() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = arrived();
    let now = at("2026-09-07", 7, 0);
    let week = planner::week_plan(&fx.input(&state, now));

    assert_eq!(week.from, date("2026-09-07"));
    assert_eq!(week.days.len(), 7);
    // Day 0 is exactly what `plan()` produced: the same minutes, and the same
    // number of blocks — six here, though only 350 minutes, because the day
    // ends in a short block and the 12:00 slot is cut off by the 12:50 wall.
    // (`planned_min / block_min` would say 5, which is the one thing the grid
    // must not say about a day the planner filled.)
    let day = planner::plan(&fx.input(&state, now));
    let blocks = day.segments.iter().filter(|s| s.kind.is_work()).count() as u32;
    assert_eq!(week.days[0].planned_min, day.block_minutes());
    assert_eq!(week.days[0].blocks, blocks);
    assert_eq!(blocks, 6, "{}", timeline(&day));
    assert_eq!(week.days[0].planned_min, 350);
    // No later day is allocated more than its own capacity (day 0 is the plan
    // itself, and §8.1's window may exceed the §8.4 grid's expectation).
    for d in week.days.iter().skip(1) {
        assert!(d.planned_min <= d.capacity_min, "{d:?}");
    }
    // The grid has a header, seven days and a total.
    assert_eq!(week.grid.lines().count(), 9, "{}", week.grid);
    insta::assert_snapshot!("week_plan_grid", week.grid);
    insta::assert_snapshot!(
        "week_plan_days",
        week.days
            .iter()
            .map(|d| format!(
                "{} cap {:>4}m planned {:>4}m ({}b): {}",
                d.date,
                d.capacity_min,
                d.planned_min,
                d.blocks,
                d.items
                    .iter()
                    .map(|(i, m)| format!("{}:{m}m", i.as_str()))
                    .collect::<Vec<_>>()
                    .join(" ")
            ))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// A small convenience the assertions above want.
trait AsDeref {
    fn as_deref_id(&self) -> Option<&str>;
}

impl AsDeref for Option<Id> {
    fn as_deref_id(&self) -> Option<&str> {
        self.as_ref().map(Id::as_str)
    }
}
