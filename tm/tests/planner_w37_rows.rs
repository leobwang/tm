//! **The three rows where the kernel's day was not the fork's**, compared by
//! value on generated days — stage 6 W-37 track R (README gaps 551, 550 and
//! 2870/435).
//!
//! W-36's land step left R3 three rows short of the day the shipped binary
//! draws: the cut's kept breaks (gap 551), the reservation row's `×`
//! multiplier (gap 550) and a scheduled window task's Routine-row `⚠` (gap
//! 2870, which is gap 435). The kernel draws all three since W-37
//! (`Planner.PlanReq.keptBreakRows`, `Planner.PlanReq.candMult`,
//! `Planner.PlanReq.routineHot`), and `support/forkday.rs` compares their rows
//! by value like any other. Gaps 551 and 550 are compared on every generated
//! day `planner_invariants.rs` draws and on the frozen classes; **gap 2870's
//! mark was compared on no generated day**, because that generator writes no
//! scheduled window task (its routines are `routines.md` lines, which carry no
//! `⚠` on either side), and on no frozen class day. This file is where it is.
//!
//! # What is generated
//!
//! `plan-basic` — §4.3's own tree, whose backlog holds `^a3`, "Pick up package",
//! a dated window task due today — planned at every ten minutes from the
//! arrival to the evening, from the two states the fixture suite plans it
//! from. Each day is the kernel's (the whole request through
//! `support/planreq.rs`, read back by the host's codec) against the fork as
//! the shipped binary runs it (D53: `planner::plan` over the kernel's own
//! grants, `planning::build_ranked`'s call), compared by
//! `forkday::compare_day_with_fork`: the date, the window, the budget, all
//! twelve diagnostic fields, the priorities and every row in order, by value,
//! and the plan hash.
//!
//! # What it cannot see
//!
//! * A running block: `plan-basic`'s states run none, so gap 550's row is not
//!   drawn here — it is compared on `planner_invariants.rs`' generated days
//!   (with drawn multipliers) and the frozen running-state classes.
//! * Any tree but `plan-basic`: the scheduled window task is `^a3` and `^a3`
//!   only, `p = 0` because it is due today.
//! * After R3: the fork's arm is one region, and R3 deletes it; what outlives
//!   it is the frozen comparand, which holds `^a3`'s mark on the four fixture
//!   days (`planner_fixtures.rs`) and on no generated class (README gap 3200).
//!
//! # What it found that was none of the three
//!
//! From 13:30 on the early day the kernel REFUSED the whole planner section,
//! `routineRefused emptyWindow lunch`: the host's encoder
//! (`planwire::routine_instances`, fork `collect_routines`' span) sent `lunch`'s
//! closed 11:30–13:30 window as an empty span, which the fork passes over and
//! the kernel refuses by name. The encoder now sends no empty span (README gap
//! 3201), and this arm counts the instances that left unsent.

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

use chrono::Duration;
use tm_core::config::Config;
use tm_core::dayplan::{SegKind, Segment};

/// **P45's rule counts the running break by a property, and still bites on a
/// second Break row inside it** (AGENTS §5.8). Since W-37 the kernel draws the
/// cut's kept breaks, so a break day holds more than one Break row, and the
/// rule's "exactly one Break row" became "exactly one Break row starting before
/// the running break's end" (`forkclass::p45_rule`). On every frozen break day
/// the kernel's own day passes it, and the same day with a one-minute Break row
/// planted inside the running break fails it by name.
#[test]
fn the_p45_rule_counts_the_running_break_by_its_span_and_bites_a_second_one() {
    let tz = Config::default().tz;
    let (mut checked, mut beside) = (0, 0);
    for line in forkclass::frozen_lines() {
        let w = forkclass::ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        let Some(brk) = w.state.break_.clone().filter(|b| b.started.is_some()) else { continue };
        let b = forkclass::Built::of(w);
        let k = forkclass::kernel_answer(&b).expect("the kernel plans a break day");
        let now = b.world.now;
        // P73's reading, the binary's (the W-41 repair, README gap 4143).
        let started = brk.started_at(b.cfg.tz, now).expect("filtered");
        let rule = |day: &tm_core::dayplan::DayPlan| {
            forkclass::p45_rule(day, started, brk.planned_min, brk.place.as_deref(), now, b.day_bounds())
        };
        let (lo, hi, _) = rule(&k.day).unwrap_or_else(|e| panic!("{}: {e}", line["class"]));
        // Every other Break row of the kernel's day is a kept break of the cut,
        // after the running one.
        beside += k.day.segments.iter().filter(|s| s.kind == SegKind::Break && s.start >= hi).count();
        let at = k.day.segments.iter().position(|s| s.kind == SegKind::Break).expect("the Break row");
        let mut planted = k.day.clone();
        let mut second: Segment = planted.segments[at].clone();
        second.start = lo;
        second.end = lo + Duration::minutes(1);
        second.flags.note = None;
        planted.segments.push(second);
        let err = rule(&planted).expect_err("a second Break row inside the running break passed P45's rule");
        assert!(err.contains("2 Break rows"), "{}: {err}", line["class"]);
        checked += 1;
    }
    assert!(checked >= 2, "{checked} frozen break day(s)");
    println!("P45's rule: {checked} frozen break day(s) passed and bit; {beside} kept break row(s) beside the running one");
}

