//! **The rows and the window the kernel's day now reads as the shipped fork does,
//! and the order it serves in** — stage 6 W-38 track R (README gaps 3281, 320
//! and 3343; gap 3390 pinned, and closed at W-39).
//!
//! # What changed in the kernel, and what each test here compares
//!
//! * **Gap 3281** — fork `collect_walls` pushes a running interruption after the
//!   day's calendar walls and sorts them all by `(blocked_start, id)`, so a Lost
//!   row and a Wall row that start and end at one instant are drawn in THAT
//!   order; the kernel drew the Lost row first every time. `Planner.dayRows`
//!   walks step 1 through `Planner.stepOneOrder` since W-38.
//!   the_interruption_and_the_meeting_are_drawn_as_the_fork_draws_them, in the
//!   fork region R3 deleted, planned `plan-basic` with an interruption running
//!   since `^g1`'s meeting began, naming a block that sorts after `g1`, one that
//!   sorts before it and none, and compared every row, every diagnostic and the
//!   hash with the in-tree fork.
//! * **Gap 320** — fork `Planner::window_and_budget` reads `state.window`,
//!   `state.budget` and `state.arrival` on `plan_date`'s day, a state naming no
//!   day included, and a window with no budget beside it; the kernel read day
//!   0's capacity rule (a window only with its budget, only on a state dated
//!   today). gap_320s_inputs_are_planned_as_the_forks_planner_plans_them, in the
//!   fork region R3 deleted, compared them with the in-tree fork.
//! * **Gap 3390, CLOSED at W-39 (track A)** — with no arrival in the state the
//!   fork's planner falls back to the day's first logged `arrive`, and since W-39
//!   so does the kernel's (`Look.Today.planArrivalSec` over
//!   `Planner.PlanReq.loggedArrival`). The W-38 pin that asserted the divergence
//!   is refuted and renamed: [`the_logged_arrival_is_the_forks_planners_and_the_kernels`]
//!   compares the woken day with the fork by value at four instants.
//! * **Gap 3343** — the day carries step 5's served order,
//!   `diagnostics.served` (`{ix, id, ci}` per ranked answer, in the order the
//!   walk serves them). [`the_day_carries_the_order_step_five_serves`] reads it
//!   off the kernel's own answer and compares it, BY VALUE, with the order
//!   `planner_invariants`' monotone-rank check computes in Rust today
//!   (`forkclass::d60_cands` under `priority::sorted_candidates`) — so the
//!   harness can read the kernel's order instead of a copy (README gap 3343; the
//!   switch is the harness owner's). It is OUTSIDE the fork region: neither
//!   `sorted_candidates` nor `d60_cands` is the fork planner.
//!
//! The three fork comparisons were one `BEGIN THE FORK PLANNER` region, which R3
//! deleted; the kernel's half of each is `PlannerWit`'s W-38 block — and, since W-45
//! track C (README gap 4682), the same three days asked of the kernel through the FFI
//! outside the region ([`the_kernel_draws_the_interruption_and_the_meeting_in_the_forks_order`],
//! [`gap_320s_inputs_are_planned_by_the_kernel_from_the_states_window`],
//! [`the_kernel_plans_the_woken_day_from_the_logged_arrival`]): until W-45 the region's tests
//! asserted the kernel's rows and windows beside the fork's, and R3 would have deleted them.

mod planner_common;

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[allow(dead_code)]
#[path = "support/planreq.rs"]
mod planreq;

#[allow(dead_code)]
#[path = "support/forkday.rs"]
mod forkday;

#[allow(dead_code)]
#[path = "support/forkclass.rs"]
mod forkclass;

#[allow(dead_code)]
#[path = "support/plangen.rs"]
mod plangen;

#[allow(dead_code)]
#[path = "support/srcwalk.rs"]
mod srcwalk;

use chrono::{DateTime, Duration, NaiveTime};
use chrono_tz::Tz;
use serde_json::Value;
use tm_core::priority::{self, Candidate};
use tm_core::store::RuntimeState;

use planner_common::{at, basic_state, Fixture};

/// `plan-basic` with the history the planner suites plan it against.
fn basic() -> Fixture {
    planner_common::load_with_log("plan-basic", Some(planner_common::BASIC_LOG))
}

/// The candidates, the kernel's raw response and the order they were sent in.
fn ask(fx: &Fixture, state: &RuntimeState, now: DateTime<Tz>) -> (Vec<Candidate>, Value, Vec<usize>) {
    let day = tm_core::planwire::plan_date(state, now);
    let cands = priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, day, now);
    let w = planreq::World {
        docs: &fx.docs,
        log: &fx.log,
        tree: &fx.tree,
        cfg: &fx.cfg,
        state,
        now,
        cands: &cands,
        replay: &fx.replay,
    };
    let (req, order) = planreq::request(&w, None);
    let resp = planreq::call(&req);
    (cands, resp, order)
}

/// Every ten minutes from `from` to 20:50.
fn instants(from: (u32, u32)) -> Vec<DateTime<Tz>> {
    let mut out = Vec::new();
    let mut t = at("2026-09-07", from.0, from.1);
    let end = at("2026-09-07", 20, 50);
    while t <= end {
        out.push(t);
        t += Duration::minutes(10);
    }
    out
}

/// `plan-basic` arriving at 10:30 — `planner_fixtures.rs`' late state.
fn late_state() -> RuntimeState {
    RuntimeState {
        wake: Some(NaiveTime::from_hms_opt(9, 0, 0).expect("time")),
        arrival: Some(NaiveTime::from_hms_opt(10, 30, 0).expect("time")),
        window: None,
        budget: None,
        ..basic_state()
    }
}

/// What one served-order comparison counted.
#[derive(Default)]
struct Served {
    days: usize,
    entries: usize,
    reordered: usize,
    impossible_first: usize,
}

/// **One day's `diagnostics.served`, against the Rust copy of the kernel's order**:
/// each `{ix, id, ci}` names the candidate the request sent at `ix`, with its id
/// and the `ci` the wire sent, and the sequence is `priority::sorted_candidates`
/// over `forkclass::d60_cands` — D63's order with D60's component — candidate
/// for candidate.
fn served_is_the_copy(label: &str, cands: &[Candidate], resp: &Value, order: &[usize], c: &mut Served) {
    let ans = tm_core::planwire::read_capacity_answer(resp, order, true)
        .unwrap_or_else(|e| panic!("{label}: the capacity answer does not read: {e}"));
    let served = resp["ok"]["plan"]["diagnostics"]["served"]
        .as_array()
        .unwrap_or_else(|| panic!("{label}: the day carries no `served` array: {}", resp["ok"]["plan"]["diagnostics"]))
        .clone();
    let kernel: Vec<usize> = served
        .iter()
        .map(|e| {
            let ix = e["ix"].as_u64().unwrap_or_else(|| panic!("{label}: an entry with no `ix`: {e}")) as usize;
            let i = *order.get(ix).unwrap_or_else(|| panic!("{label}: `ix` {ix} names no candidate sent"));
            assert_eq!(e["id"].as_str(), Some(cands[i].id.as_str()), "{label}: entry {e} is not the candidate sent at {ix}");
            assert_eq!(e["ci"].as_u64(), Some(u64::from(cands[i].ci)), "{label}: entry {e} carries another `ci` than the one sent");
            i
        })
        .collect();
    let d60 = forkclass::d60_cands(cands, &ans.prios);
    let copy: Vec<usize> = priority::sorted_candidates(&ans.prios, &d60)
        .into_iter()
        .map(|x| d60.iter().position(|y| std::ptr::eq(x, y)).expect("a candidate of the list"))
        .collect();
    assert_eq!(kernel, copy, "{label}: the kernel serves {kernel:?}, the Rust copy of its order says {copy:?}");
    c.days += 1;
    c.entries += kernel.len();
    c.reordered += usize::from(kernel.iter().zip(order).any(|(k, o)| k != o) || kernel.len() != order.len());
    c.impossible_first += usize::from(kernel.first().is_some_and(|&i| forkclass::is_impossible_tie(&ans.prios[i])));
}

/// **The kernel's served order is the order the harness computes in Rust, by
/// value** — `plan-basic` every half hour from two states, and every world of the
/// frozen class comparand (whose impossible-tie lines are served by D60's order).
#[test]
fn the_day_carries_the_order_step_five_serves() {
    let mut c = Served::default();
    let fx = basic();
    for (name, state, from) in [("early", basic_state(), (7, 0)), ("late", late_state(), (10, 30))] {
        for now in instants(from).into_iter().step_by(3) {
            let (cands, resp, order) = ask(&fx, &state, now);
            served_is_the_copy(&format!("plan-basic {name} {}", now.format("%H:%M")), &cands, &resp, &order, &mut c);
        }
    }
    let tz = fx.cfg.tz;
    for line in forkclass::frozen_lines() {
        let w = forkclass::ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        let b = forkclass::Built::of(w);
        let (req, order) = planreq::request(&b.request_world(), None);
        let resp = planreq::call(&req);
        served_is_the_copy(line["class"].as_str().unwrap_or("<no class>"), &b.cands, &resp, &order, &mut c);
    }
    println!(
        "served order: {} days, {} entries compared by value with the Rust copy; {} day(s) served in an \
         order that is not the request's; {} day(s) serving an impossible item first",
        c.days, c.entries, c.reordered, c.impossible_first
    );
    // The floors: something was compared, on some day the order is not the request's own
    // (a served list equal to the request order on every day would pin nothing about the
    // sort), and on some day D60's component moved an impossible item to the front.
    assert!(c.entries > c.days, "{} entries over {} days", c.entries, c.days);
    assert!(c.reordered > 0, "on no day did the kernel serve in another order than the request's");
    assert!(c.impossible_first > 0, "on no day was an impossible item served first");
}

/// The kinds and items of the rows that start at `t`, in the day's order.
fn rows_at(day: &tm_core::dayplan::DayPlan, t: DateTime<Tz>) -> Vec<(String, Option<String>)> {
    day.segments
        .iter()
        .filter(|s| s.start == t)
        .map(|s| (tm_core::dayplan::kind_label(&s.kind).to_string(), s.item.as_ref().map(ToString::to_string)))
        .collect()
}

/// **The kernel's day for `state` at `now`, through the FFI** — the request R3's host sends
/// (`planner_common::planreq`), read back by the host's codec. `label` names a refusal.
fn kernel_day(fx: &Fixture, label: &str, state: &RuntimeState, now: DateTime<Tz>) -> tm_core::dayplan::DayPlan {
    fx.kernel_day(state, now).unwrap_or_else(|e| panic!("{label}: the kernel did not plan the day: {e}"))
}

/// `plan-basic`'s state with an interruption running since `^g1`'s meeting began at 12:50, naming
/// `id` (README gap 3281).
fn interrupted_at_the_meeting(id: Option<&str>) -> RuntimeState {
    RuntimeState {
        interrupt: Some(tm_core::store::InterruptState {
            started: Some(NaiveTime::from_hms_opt(12, 50, 0).expect("time")),
            id: id.map(tm_core::model::Id::new),
        }),
        ..basic_state()
    }
}

/// README gap 320's three states and the window each is planned in: a stored window with no
/// date, the same window dated today with NO budget beside it (08:00–15:00, which §8.1's formula
/// from the 07:00 arrival does not give, so the two readings are told apart), and a state naming
/// no day that carries an arrival and no window.
fn gap_320_states() -> [(&'static str, RuntimeState, (u32, u32, u32, u32)); 3] {
    let eight_to_three = Some((NaiveTime::from_hms_opt(8, 0, 0).expect("time"), NaiveTime::from_hms_opt(15, 0, 0).expect("time")));
    [
        ("undated window and budget", RuntimeState { date: None, ..basic_state() }, (7, 0, 16, 0)),
        ("window with no budget", RuntimeState { budget: None, window: eight_to_three, ..basic_state() }, (8, 0, 15, 0)),
        ("undated arrival, no window", RuntimeState { date: None, window: None, budget: None, ..basic_state() }, (7, 0, 16, 0)),
    ]
}

/// README gap 3390's woken day: no arrival stored (`tm wake` after `tm arrive` clears it), the
/// log keeping the 07:00 `arrive`.
fn woken_state() -> RuntimeState {
    RuntimeState { arrival: None, window: None, budget: None, ..basic_state() }
}

/// **README gap 3281, of the kernel alone**: planned at 13:50 the Lost row and the Wall row of
/// `^g1`'s meeting tie on start and end, and the kernel draws them in fork collect_walls'
/// `(blocked_start, id)` order — an interruption naming `t4` after `g1`, one naming `a1` or no
/// block before it; at 13:30 the Lost row ends first and is drawn first. The fork's half, against
/// the live fork, is the region's the_interruption_and_the_meeting_are_drawn_as_the_fork_draws_them.
#[test]
fn the_kernel_draws_the_interruption_and_the_meeting_in_the_forks_order() {
    let fx = basic();
    let begun = at("2026-09-07", 12, 50);
    let wall = (String::from("wall"), Some(String::from("g1")));
    let mut days = 0;
    for (id, after_the_wall) in [(Some("t4"), true), (Some("a1"), false), (None, false)] {
        let state = interrupted_at_the_meeting(id);
        let lost = (String::from("lost"), id.map(str::to_string));
        for (h, m, tie) in [(13, 50, true), (13, 30, false)] {
            let now = at("2026-09-07", h, m);
            let label = format!("interrupted {id:?} at {h}:{m:02}");
            let k = kernel_day(&fx, &label, &state, now);
            let want = if tie && after_the_wall { vec![wall.clone(), lost.clone()] } else { vec![lost.clone(), wall.clone()] };
            assert_eq!(rows_at(&k, begun), want, "{label}: the kernel's rows at 12:50");
            days += 1;
        }
    }
    assert_eq!(days, 6);
}

/// **README gap 320's inputs, of the kernel alone**: each state's day is the window the state
/// says, at four instants — not one from `now`. The fork's half is the region's
/// gap_320s_inputs_are_planned_as_the_forks_planner_plans_them.
#[test]
fn gap_320s_inputs_are_planned_by_the_kernel_from_the_states_window() {
    let fx = basic();
    let tz = fx.cfg.tz;
    let mut days = 0;
    for (name, state, (h0, m0, h1, m1)) in &gap_320_states() {
        for (h, m) in [(8, 0), (10, 30), (12, 0), (14, 0)] {
            let now = at("2026-09-07", h, m);
            let label = format!("{name} at {h}:{m:02}");
            let k = kernel_day(&fx, &label, state, now);
            let want = (at("2026-09-07", *h0, *m0), at("2026-09-07", *h1, *m1));
            assert_eq!((k.window.0.with_timezone(&tz), k.window.1.with_timezone(&tz)), want, "{label}: the kernel's window");
            days += 1;
        }
    }
    assert_eq!(days, 12);
}

/// **README gap 3390, of the kernel alone**: the woken day starts at the logged 07:00 arrival
/// (`Look.Today.planArrivalSec`), not at `now`, at four instants. The fork's half is the region's
/// the_logged_arrival_is_the_forks_planners_and_the_kernels.
#[test]
fn the_kernel_plans_the_woken_day_from_the_logged_arrival() {
    let fx = basic();
    let tz = fx.cfg.tz;
    let state = woken_state();
    for (h, m) in [(8, 0), (10, 30), (12, 0), (14, 0)] {
        let now = at("2026-09-07", h, m);
        let label = format!("woken after arriving, at {h}:{m:02}");
        let k = kernel_day(&fx, &label, &state, now);
        let want = (at("2026-09-07", 7, 0), at("2026-09-07", 16, 0));
        assert_eq!((k.window.0.with_timezone(&tz), k.window.1.with_timezone(&tz)), want, "{label}: the kernel's window");
        assert_ne!(k.window.0.with_timezone(&tz), now, "{label}: the kernel no longer starts the day at `now`");
    }
}


