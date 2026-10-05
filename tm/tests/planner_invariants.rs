//! §8.3's invariants as `proptest` properties over random trees, random logs
//! and a random `now` — "tests first for §8.3 invariants: they are the
//! specification" (§17.2).
//!
//! Each case builds a week file of up to 40 items with random `ci`, `!k`,
//! estimate, deadline, dependency, `loc:` and `atomic`, a random subset of the
//! §4.3 routines (windows, a `pref:` anchor, sleep), optionally the two
//! `optional.md` lines, up to two calendar walls, a log with a random number of
//! finished blocks and an optional energy report, and plans at a random instant
//! inside the window. A case may also be **running a block**
//! (`state.active` + the matching `start` in the log), **interrupted**
//! (`state.interrupt`), or a **late day** whose §8.1 window is pushed past the
//! 21:30 wind-down by a six-hour evening wall. Then every invariant of §8.3 is
//! checked:
//!
//! * **purity** — the same input twice gives an identical `DayPlan`;
//! * **stability** — a replan an hour later changes no segment that had ended,
//!   except the ones that had not *finished* ([`SegFlags::open`]: the running
//!   interruption and the running block, which grow rather than move);
//! * **no overbooking** — Σ planned Block minutes ≤ `remaining_budget ×
//!   block_min` (the running block excepted: §9 gives it its minutes whatever
//!   the budget says), no segment overlaps a Wall, nothing is planned after
//!   wind-down, and no two placements overlap;
//! * **energy filter** — every Block the planner *assigned* has `item.ci ≤
//!   slot.energy`, and the one block it did not assign — the one already
//!   running — takes no slot at all;
//! * **monotone rank** — equal `p` and equal `ci`: the lower line order is
//!   never left unassigned while the other is assigned;
//! * **tail-drop** — taking a block off the budget removes a tail and
//!   re-shuffles nothing;
//! * **HOT before queue**, **IMPOSSIBLE never dropped**, **walls never
//!   moved** (exactly where the calendar says, to the minute);
//! * and §8.2 step 8's **diagnostics**, which have to agree with the timeline
//!   they describe.
//!
//! Where a property needs a fair comparison it is restricted to the
//! candidates the rule is written about — a `loc:`-constrained, `atomic` or
//! `max:`-capped item is skipped by §8.2 step 5 for reasons the invariant is
//! not about, and the Active item is excepted by §8.3 itself.
//!
//! # What outlives R3, and what leaves with the fork (stage 6 W-37 track H)
//!
//! R3 deletes `tm-core/src/planner.rs`. Since W-37 this file is two halves, and
//! the line between them is the one R3 draws:
//!
//! * **Outside the region — the kernel, on every generated case.** The
//!   generator is `support/plangen.rs` (README gap 3080: the comparand keyed by
//!   class re-draws its worlds from it). §8.3's invariants above are
//!   [`check_day_invariants`], asked of the kernel as
//!   `day_plan_satisfies_every_invariant` — the planner R3 ships, through the
//!   host's codec — and "the higher-ranked of two" is the planner's own §7.4
//!   order (the owner's D63). The kernel-only checks stay beside it: the
//!   contending routines' kernel half, the P45 checker's bite and `send_order`.
//! * **The `BEGIN THE FORK PLANNER` … `END THE FORK PLANNER` region is gone** —
//!   every arm that planned with the fork, deleted whole at R3 (W-45; README gap
//!   3084: until W-37 34 code lines of them sat outside any region). What each
//!   compares that the frozen comparand (`planner_classes.rs`) covers by value
//!   is README's W-38 track H table: since W-38 that is everything but the
//!   fork's OWN §7 day and P43's fractional rows (D53: no shipped path builds
//!   either), a typed pause over a wall (the owner's D68 redraws it, track T's
//!   number, the same run) and README gap 3281's order (track R's, the same run).
//! * **What the region asked of the kernel ALONE has left it** (W-38, README gap
//!   3282): the kernel's own day through the `plan` section's cells
//!   ([`the_kernel_reads_every_day_it_plans`]), step 8's projections, P45's rule
//!   on generated break days, and the kernel halves of the fixed days.

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

/// **The `plan` section's wire**, shared with `tm/tests/kernel_row_cells.rs`
/// since stage 6 W-25 (step R2): one encoder, two callers (AGENTS §5.3).
#[allow(dead_code)]
#[path = "support/rowwire.rs"]
mod rowwire;

/// The request the host's codec builds, and the kernel's day read back through
/// it — how the arms that survive R3 ask the kernel (W-37 track H).
#[allow(dead_code)]
#[path = "support/planreq.rs"]
mod planreq;

#[allow(dead_code)]
#[path = "support/forkday.rs"]
mod forkday;

/// The comparand keyed by class: its D60 order is the kernel's own §7.4 order
/// (one copy, README gap 3122), and it re-draws its worlds from `plangen`.
#[allow(dead_code)]
#[path = "support/forkclass.rs"]
mod forkclass;

/// The fork's planner as a backend, and the comparand built over any backend (W-39, the
/// owner's D72): the arm below asks `tm-oracle plan`, the region's cross-check the in-tree fork.
#[allow(dead_code)]
#[path = "support/forkplan.rs"]
mod forkplan;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;

use chrono::{DateTime, Duration, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use proptest::prelude::*;
use serde_json::{json, Value};
use tm_core::capacity::{local_dt, Exact, CAP_DEN};
use tm_core::priority::PrioClass;
use tm_core::model::{Id, Loc, Shape};
use tm_core::dayplan::{DayPlan, SegKind, Segment};
use tm_core::planwire;
use tm_core::priority::{self, Candidate, Prio};
use tm_core::store::RuntimeState;

/// **The generator, shared** (stage 6 W-37 track H, README gaps 3080 and 3084):
/// `Case`, `case_strategy`, `build` and the widenings the arms draw live in
/// `support/plangen.rs`, so the comparand keyed by class re-draws its worlds from
/// them and they outlive R3 with the arms that plan with the kernel.
#[allow(dead_code)]
#[path = "support/plangen.rs"]
mod plangen;
use plangen::*;


/// The candidates §8.3's comparisons are written about: plain, splittable,
/// uncapped work with no location constraint and no placement window.
fn comparable(c: &Candidate) -> bool {
    c.eligible()
        && !c.is_wall
        && !c.is_optional
        && c.window.is_none()
        && c.splittable
        && c.cap.is_none()
        && c.loc == Loc::Any
        && c.remaining_min > 0
}

/// The items the plan *proposes* — the blocks the log already holds are not
/// the planner's doing and never count as "assigned" for §8.3.
fn assigned_set(day: &DayPlan, from: DateTime<Tz>) -> BTreeSet<Id> {
    day.assigned_from(from).into_iter().collect()
}

/// The slot layout, as `(start, items)` — what the tail-drop invariant
/// compares.
fn layout(day: &DayPlan) -> Vec<(DateTime<Tz>, Vec<Id>)> {
    day.segments
        .iter()
        .filter(|s| s.kind.is_work())
        .map(|s| (s.start, s.items()))
        .collect()
}


fn overlaps(a: &Segment, b: &Segment) -> bool {
    a.start < b.end && b.start < a.end
}

/// **Which planner §8.3's invariants are asked of** (stage 6 W-37 track H,
/// README gap 3084): the property `day_plan_satisfies_every_invariant`
/// asserted of the FORK's own-§7 day until W-37 — a day no shipped path plans
/// (D53) and one R3 deletes — written once, over this, and asked of the
/// KERNEL (the planner R3 ships) on every generated case; of the fork, in the
/// file's one region, until R3.
trait Planner {
    /// The day planned for `w` at `state` and `now`, or why none was.
    fn day(&self, w: &World, state: &RuntimeState, now: DateTime<Tz>) -> Result<DayPlan, String>;
    /// The candidates re-keyed so `(root_order, own_order)` is the planner's
    /// own §7.4 order (the owner's D63: §8.3's monotone-rank check reads it),
    /// for the day `day` plans for `w` at `w.state` and `w.now`.
    fn rank_view(&self, w: &World, cands: &[Candidate], prios: &[Prio]) -> Vec<Candidate>;
    /// Which one, for a failure message.
    fn name(&self) -> &'static str;
}

/// **The kernel**, through the request the host's codec builds
/// (`support/planreq.rs`) and read back by `tm_core::planwire` — the planner R3
/// swaps into the binary. Its §7.4 order is D60's (`forkclass::d60_cands`):
/// `p = 0` impossible answers by due date and request position, before every
/// other `p = 0` answer.
struct Kernel;

impl Planner for Kernel {
    fn day(&self, w: &World, state: &RuntimeState, now: DateTime<Tz>) -> Result<DayPlan, String> {
        let date = planwire::plan_date(state, now);
        let cands = priority::collect_candidates(&w.tree, &w.replay, &w.cfg, &w.model, date, now);
        let pw = planreq::World {
            docs: &w.docs,
            log: &w.log,
            tree: &w.tree,
            cfg: &w.cfg,
            state,
            now,
            cands: &cands,
            replay: &w.replay,
        };
        planreq::kernel_day(&pw, None).map(|(k, _)| k.day)
    }
    /// **The order the kernel SAYS its step 5 served** (W-38's land step, README gaps 3343 and
    /// 3396): `diagnostics.served`, one `{ix, id, ci}` per answer that entered the order, in the
    /// walk's order (`Planner.PlanReq.dayServed`, `Planner.dayPlan_serves_in_the_walks_order`).
    /// Until W-38 this was `forkclass::d60_cands`, a Rust copy of D63's key with D60's
    /// component, so §8.3's monotone check read the harness's idea of the kernel's order and
    /// not the kernel's; the copy stays, compared with this key by value in
    /// `planner_w38_order.rs`. A candidate the check can compare (`comparable`) is eligible and
    /// not a wall, so it enters the order: one missing from `served` is a finding, by name.
    fn rank_view(&self, w: &World, cands: &[Candidate], prios: &[Prio]) -> Vec<Candidate> {
        let pw = planreq::World {
            docs: &w.docs,
            log: &w.log,
            tree: &w.tree,
            cfg: &w.cfg,
            state: &w.state,
            now: w.now,
            cands,
            replay: &w.replay,
        };
        let (req, order) = planreq::request(&pw, None);
        let resp = planreq::call(&req);
        let served = resp["ok"]["plan"]["diagnostics"]["served"]
            .as_array()
            .unwrap_or_else(|| panic!("the kernel's day carries no `served` order: {resp}"));
        let mut rank: Vec<Option<usize>> = vec![None; cands.len()];
        for (k, e) in served.iter().enumerate() {
            let ix = e["ix"].as_u64().unwrap_or_else(|| panic!("a `served` entry with no `ix`: {e}")) as usize;
            let i = *order.get(ix).unwrap_or_else(|| panic!("`served` names request position {ix}, which was not sent"));
            assert_eq!(e["id"].as_str(), Some(cands[i].id.as_str()), "`served` entry {e} is not the candidate sent at {ix}");
            assert!(rank[i].is_none(), "`served` names {} twice", cands[i].id);
            rank[i] = Some(k);
        }
        // **And the served order is D60's, read INDEPENDENTLY, on every fresh draw** (README
        // gap 3534, the W-38 repair): once the monotone check reads the kernel's own `served`,
        // an order the kernel got wrong would be checked against itself on the generated days.
        // The Rust copy of D63's key (`forkclass::d60_cands`), sorted by the fork's
        // `priority::sorted_candidates`, must serve the same candidates in the same order —
        // `planner_w38_order.rs`' comparison, on plan-basic and the frozen classes there, on
        // this proptest's fresh draws here.
        let d60 = forkclass::d60_cands(cands, prios);
        let copy: Vec<usize> = priority::sorted_candidates(prios, &d60)
            .into_iter()
            .map(|x| d60.iter().position(|y| std::ptr::eq(x, y)).expect("a candidate of the list"))
            .collect();
        let mut kernel: Vec<(usize, usize)> = rank.iter().enumerate().filter_map(|(i, k)| k.map(|k| (k, i))).collect();
        kernel.sort();
        let kernel: Vec<usize> = kernel.into_iter().map(|(_, i)| i).collect();
        assert_eq!(kernel, copy, "the kernel serves {kernel:?}, the Rust copy of its order says {copy:?}");
        cands
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let mut d = c.clone();
                match rank[i] {
                    Some(k) => d.root_order = (0, k),
                    None => {
                        assert!(!comparable(c), "{} is comparable and the kernel did not serve it", c.id);
                        d.root_order = (1, i);
                    }
                }
                d.own_order = (0, 0);
                d
            })
            .collect()
    }
    fn name(&self) -> &'static str {
        "the kernel"
    }
}

/// Whether some candidate's §8.2 step-2 window closes exactly at `t` — the
/// instant README gap 3280's refusal happened at until W-37's land step, read
/// off the fork-point collector the host codec's `routine_instances` reads.
fn routine_window_ends_at(w: &World, state: &RuntimeState, t: DateTime<Tz>) -> bool {
    let date = planwire::plan_date(state, t);
    priority::collect_candidates(&w.tree, &w.replay, &w.cfg, &w.model, date, t)
        .iter()
        .any(|c| c.window.is_some_and(|(_, end)| end == t))
}

/// **§8.3's invariants, of one generated day** — see [`Planner`]. The checks
/// are the ones this file's first arm made of the fork's day since stage 3,
/// unchanged but for two readings: the planner's day is `p.day`, and "the
/// higher-ranked of two" is the planner's own §7.4 order (`p.rank_view`).
fn check_day_invariants(p: &dyn Planner, case: &Case, w: &World) -> Result<(), TestCaseError> {
    let tz = w.cfg.tz;
    let block_min = w.cfg.block_min();
    let day = p.day(w, &w.state, w.now).map_err(TestCaseError::fail)?;

    // --- purity (§8.3, §17.2) ---------------------------------------
    let again = p.day(w, &w.state, w.now).map_err(TestCaseError::fail)?;
    prop_assert_eq!(&day, &again);
    prop_assert_eq!(day.hash(), again.hash());

    // --- the running block (§9) --------------------------------------
    // It is a fact, not a placement: exactly one `▶`, it belongs to
    // `state.active`, it starts at `now`, and it holds no slot.
    let current = day.current_segment();
    prop_assert!(
        day.segments.iter().filter(|s| s.flags.current).count() <= 1,
        "two blocks are running at once"
    );
    if let Some(seg) = current {
        let active = w.state.active.as_ref().expect("a `▶` needs `state.active`");
        prop_assert_eq!(seg.item.as_ref(), Some(&active.id));
        prop_assert!(seg.energy.is_none(), "the running block takes no slot: {:?}", seg);
        // Either the minutes it still needs (from `now`) or — in
        // overtime, when there is nothing left to reserve — the stretch it
        // has already run (up to `now`).
        prop_assert!(seg.start <= w.now && seg.end >= w.now, "{seg:?}");
    }
    let running_min = current.filter(|s| s.start >= w.now).map_or(0, Segment::minutes);

    // --- no overbooking ---------------------------------------------
    // §9 gives the running block its minutes whatever the budget says
    // (that is the state §9.1's overtime prompt runs in); everything the
    // planner *chose* fits the remaining budget.
    // §8.1's remaining budget, `budget − blocks_done` and never below zero (fork
    // `capacity::remaining_budget`'s rule; R3 deletes that function, README gap 4752).
    let remaining = w.state.budget.unwrap_or(6).saturating_sub(w.replay.blocks_done(date()));
    prop_assert!(
        day.planned_block_minutes(w.now) - running_min <= remaining * block_min,
        "{} planned minutes ({running_min} of them running) for {remaining} blocks\n{day:?}",
        day.planned_block_minutes(w.now)
    );

    // No segment overlaps a Wall, and no two placements overlap.
    let placed: Vec<&Segment> = day
        .segments
        .iter()
        .filter(|s| {
            s.start >= w.now
                && !matches!(s.kind, SegKind::Lost | SegKind::WindDown | SegKind::Sleep)
        })
        .collect();
    for (i, a) in placed.iter().enumerate() {
        for b in placed.iter().skip(i + 1) {
            if a.kind == SegKind::Wall && b.kind == SegKind::Wall {
                // §8.2 step 1: overlapping walls are reported, not
                // resolved — and nothing else is placed in the overlap,
                // which the other pairs of this loop check.
                if overlaps(a, b) && a.item != b.item {
                    let (x, y) = (
                        a.item.clone().expect("a wall names its item"),
                        b.item.clone().expect("a wall names its item"),
                    );
                    prop_assert!(
                        day.diagnostics
                            .conflicts
                            .iter()
                            .any(|(p, q)| (*p == x && *q == y) || (*p == y && *q == x)),
                        "unreported wall conflict {x} × {y}"
                    );
                }
                continue;
            }
            prop_assert!(!overlaps(a, b), "overlap: {a:?} / {b:?}");
        }
    }

    // Nothing is planned after wind-down (the strong form of "no Block
    // with ci ≥ 4 after wind-down"). A late day's window reaches past it.
    let wind = at(tz, 21, 30);
    for seg in day.segments.iter().filter(|s| s.kind.is_work()) {
        prop_assert!(seg.end <= wind, "work after wind-down: {seg:?}");
    }
    if case.late {
        prop_assert!(day.window.1 > wind, "the late day runs past the wind-down");
    }

    // --- walls never moved -------------------------------------------
    // Exactly where the calendar says: a wall segment is either the event
    // itself or the `buffer:` in front of it, both clipped to the day.
    for seg in day.segments.iter().filter(|s| s.kind == SegKind::Wall) {
        let id = seg.item.clone().expect("a wall names its item");
        let Shape::Interval { start, end } = w.tree.effective_shape(&id) else {
            prop_assert!(false, "{id} is not an interval");
            unreachable!()
        };
        let buffer = w.tree.get(&id).and_then(|i| i.buffer).map_or(0, |d| d.as_minutes());
        let midnight = at(tz, 0, 0);
        let s = local_dt(tz, start.date(), start.time());
        let e = local_dt(tz, end.date(), end.time());
        let event = (s.max(midnight), e.min(midnight + Duration::days(1)));
        let front = (s - Duration::minutes(i64::from(buffer)), s);
        prop_assert!(
            (seg.start, seg.end) == event
                || (buffer > 0 && (seg.start, seg.end) == (front.0.max(midnight), front.1)),
            "a wall moved: {seg:?} is neither {event:?} nor {front:?}"
        );
    }

    // --- energy filter ------------------------------------------------
    let cands = w.candidates();
    let ci_of = |id: &Id| cands.iter().find(|c| c.id == *id).map_or(0, |c| c.ci);
    for seg in day.segments.iter().filter(|s| s.kind.is_work() && s.start >= w.now) {
        if seg.flags.current {
            continue; // checked above: it is not in a slot at all
        }
        let energy = seg.energy.expect("a planned block has an energy");
        for id in seg.items() {
            prop_assert!(ci_of(&id) <= energy, "{id} ci {} in a slot of {energy}", ci_of(&id));
        }
    }

    // --- the priority-dependent invariants ----------------------------
    let prios: Vec<Prio> = day.priorities.iter().map(|(_, p)| p.clone()).collect();
    prop_assert_eq!(prios.len(), cands.len());
    prop_assert!(
        day.priorities.iter().map(|(id, _)| id).eq(cands.iter().map(|c| &c.id)),
        "{}'s §7 answers are not in the candidates' order", p.name()
    );
    // **The planner's OWN §7.4 order** (the owner's D63): the key its step 5
    // serves by, which is the fork's `(root_order, own_order)` and, on the
    // kernel, D60's order among `p = 0` impossible answers before them.
    let rv = p.rank_view(w, &cands, &prios);
    let done = assigned_set(&day, w.now);
    let max_energy = day
        .segments
        .iter()
        .filter(|s| s.kind.is_work())
        .filter_map(|s| s.energy)
        .max()
        .unwrap_or(0);

    // Monotone rank: equal p and ci → the higher-ranked of the two is never
    // the one left out. The running item is excepted: §9 gave it its slot.
    //
    // **"Higher-ranked" is `(root_order, own_order)`, not `own_order`**
    // (stage 6 W-27). §7.4's key is `priority::sort_key = (p, root_order,
    // own_order)` — the item's ROOT first, its own line second — so a child
    // of an early root outranks an unrelated item written on an earlier
    // line. This loop compared `own_order` alone, which is the same
    // relation **exactly when every item is its own root**, and until this
    // run the generated corpus had no `@parent` token, so it always was.
    // With parents drawn the two relations part company and the fork was
    // failing an invariant the spec does not state: six runs of 256 cases
    // failed here and six of the pre-parent generator passed. The fork is
    // right; this line was wrong. Seed `80a3875…` in
    // `planner_invariants.proptest-regressions` is the one that found it
    // (D46: a new seed is a finding and it stays). README gap 1661.
    let active_id = w.state.active.as_ref().map(|a| a.id.clone());
    for (i, a) in cands.iter().enumerate() {
        if !comparable(a) || Some(&a.id) == active_id.as_ref() {
            continue;
        }
        for (j, b) in cands.iter().enumerate().skip(i + 1) {
            if !comparable(b) || a.ci != b.ci || prios[i].p != prios[j].p {
                continue;
            }
            if Some(&b.id) == active_id.as_ref() {
                continue;
            }
            let rank = |k: usize| (rv[k].root_order, rv[k].own_order);
            let (first, second) = if rank(i) <= rank(j) { (a, b) } else { (b, a) };
            if done.contains(&second.id) {
                prop_assert!(
                    done.contains(&first.id),
                    "{} (later line) is assigned while {} is not",
                    second.id,
                    first.id
                );
            }
        }
    }

    // HOT before queue, slot by slot: wherever a `p > 0` candidate got a
    // block, no `p = 0` candidate that the day left out could have taken
    // that same slot. (The `max_energy` form of this — "a HOT item that
    // fits *some* slot is never left out" — is nearly unfalsifiable,
    // because `max_energy` is measured over the slots that were filled.)
    // §7.5: a batch is won by its leader, and the small items sharing the
    // block ride along whatever their own key says. Those passengers never
    // "took" a slot from anyone.
    let carried = |id: &Id| -> bool {
        day.segments
            .iter()
            .filter(|s| s.kind.is_work() && s.items().contains(id))
            .any(|s| {
                s.items().iter().any(|other| {
                    other != id
                        && cands
                            .iter()
                            .position(|c| c.id == *other)
                            .is_some_and(|j| prios[j].p == 0)
                })
            })
    };
    let hot_left_out: Vec<&Candidate> = cands
        .iter()
        .zip(&prios)
        .filter(|(c, p)| comparable(c) && p.p == 0 && !done.contains(&c.id))
        .map(|(c, _)| c)
        .collect();
    for seg in day
        .segments
        .iter()
        .filter(|s| s.kind.is_work() && s.start >= w.now && !s.flags.current)
    {
        let Some(energy) = seg.energy else { continue };
        // A §7.5 batch is won by its leader and carries the rest of the
        // block with it, so the block counts as `p = 0` work when *any*
        // of its items is `p = 0`.
        let members: Vec<usize> = seg
            .items()
            .iter()
            .filter_map(|id| cands.iter().position(|c| c.id == *id))
            .collect();
        if members.is_empty()
            || members.iter().any(|j| prios[*j].p == 0 || !comparable(&cands[*j]))
        {
            continue;
        }
        for hot in &hot_left_out {
            prop_assert!(
                hot.ci > energy,
                "{:?} (p {}) took the {} slot of energy {energy} that HOT {} (ci {}) fits",
                seg.items(),
                prios[members[0]].p,
                seg.start.format("%H:%M"),
                hot.id,
                hot.ci
            );
        }
    }

    // IMPOSSIBLE never dropped (§7.3: "still scheduled with everything
    // available"). Placement is the HOT rule above — an IMPOSSIBLE
    // candidate is `p = 0`, so it only ever yields to other `p = 0` work.
    // What is checked here is that it is never *silently* dropped: the
    // banner names it and the shortfall.
    for (i, c) in cands.iter().enumerate() {
        if !prios[i].is_impossible() || c.is_wall {
            continue;
        }
        prop_assert!(
            day.diagnostics
                .impossible
                .iter()
                .any(|(id, short, _)| *id == c.id && *short == prios[i].shortfall_min),
            "IMPOSSIBLE {} is not in the diagnostics",
            c.id
        );
        if !done.contains(&c.id) && comparable(c) && c.ci <= max_energy {
            // Everything that took a slot instead was at least as urgent.
            for (j, other) in cands.iter().enumerate() {
                if comparable(other)
                    && done.contains(&other.id)
                    && other.ci >= c.ci
                    && Some(&other.id) != active_id.as_ref()
                    && !carried(&other.id)
                {
                    prop_assert_eq!(
                        prios[j].p,
                        0,
                        "{} (p {}) took a slot the IMPOSSIBLE {} could have used",
                        other.id,
                        prios[j].p,
                        c.id
                    );
                }
            }
        }
    }

    // --- nothing is wasted ---------------------------------------------
    // A Rest slot inside the budget means no candidate could take it: §8.2
    // step 5 turns a slot to Rest only when the first eligible candidate
    // does not fit it.
    // §8.2 step 5 counts *blocks*, not minutes ("while blocks_assigned <
    // remaining_budget"): a slot cut short by a wall costs a block all the
    // same, and so does the block that is running.
    let used_blocks = day
        .segments
        .iter()
        .filter(|s| s.kind.is_work() && s.start >= w.now)
        .count() as u32;
    if used_blocks < remaining {
        for rest in day.segments.iter().filter(|s| s.kind == SegKind::Rest) {
            let energy = rest.energy.unwrap_or(0);
            for c in cands.iter().filter(|c| comparable(c)) {
                prop_assert!(
                    c.ci > energy || done.contains(&c.id),
                    "{} (ci {}) was left out while a Rest slot of energy {energy} stood",
                    c.id,
                    c.ci
                );
            }
        }
    }
    prop_assert!(!day.segments.is_empty());

    // --- §8.2 step 8: the diagnostics describe this timeline ------------
    for (id, energy, ci) in &day.diagnostics.underused {
        prop_assert!(energy >= &(ci + 2), "{id}: gap {energy} − {ci} is not ≥ 2");
        prop_assert!(
            day.segments.iter().any(|s| s.kind.is_work()
                && s.flags.underused
                && s.energy == Some(*energy)
                && s.items().contains(id)),
            "underused {id} belongs to no `↓` block"
        );
    }
    for seg in day.segments.iter().filter(|s| s.kind.is_work() && s.start >= w.now) {
        let Some(energy) = seg.energy else { continue };
        for id in seg.items() {
            let gap = energy.saturating_sub(ci_of(&id));
            prop_assert_eq!(
                seg.flags.underused,
                gap >= 2,
                "{}: gap {} but flag {}",
                id,
                gap,
                seg.flags.underused
            );
        }
    }
    for id in &day.diagnostics.hot {
        let i = cands.iter().position(|c| c.id == *id).expect("a candidate");
        prop_assert_eq!(prios[i].p, 0, "{} is in `hot` with p {}", id, prios[i].p);
    }
    for id in &day.diagnostics.dropped_tail {
        prop_assert!(
            !day.assigned().contains(id),
            "{id} is both dropped and assigned"
        );
    }
    for id in &day.diagnostics.deferred {
        prop_assert!(!day.assigned().contains(id), "{id} is both deferred and assigned");
    }
    for (id, deps) in &day.diagnostics.blocked {
        prop_assert!(!deps.is_empty(), "{id} is blocked by nothing");
        // §9's one exception: a block that is *already running* keeps its
        // minutes even when step 5 would refuse the item.
        prop_assert!(
            day.segments
                .iter()
                .filter(|s| s.kind.is_work() && s.start >= w.now && s.items().contains(id))
                .all(|s| s.flags.current),
            "{id} is blocked and planned"
        );
    }
    for id in &day.diagnostics.waiting {
        let c = cands.iter().find(|c| c.id == *id).expect("a candidate");
        prop_assert!(c.waiting, "{id} is not waiting");
    }
    prop_assert_eq!(
        day.diagnostics.plan_honesty.is_some(),
        remaining > 0,
        "plan honesty is reported exactly when the day has a budget"
    );

    // --- tail-drop -----------------------------------------------------
    if remaining > 1 {
        let short_state = RuntimeState {
            budget: Some(w.state.budget.unwrap_or(6) - 1),
            ..w.state.clone()
        };
        let short = p.day(w, &short_state, w.now).map_err(TestCaseError::fail)?;
        let (long_layout, short_layout) = (layout(&day), layout(&short));
        prop_assert!(short_layout.len() <= long_layout.len());
        prop_assert_eq!(
            &short_layout[..],
            &long_layout[..short_layout.len()],
            "losing a block re-shuffled the day"
        );
        for id in assigned_set(&short, w.now) {
            prop_assert!(done.contains(&id), "{id} appeared when the day got shorter");
        }
    }

    // --- stability -----------------------------------------------------
    // Everything that had *finished* by `now` is untouched; what had not —
    // an open interruption, the block that is running — is still there,
    // from the same minute, only longer.
    let at = w.now + Duration::hours(1);
    let later = match p.day(w, &w.state, at) {
        Ok(d) => d,
        // README gap 3280's declared class (the kernel refusing the replan at the minute a
        // routine's window closes) was set aside here until W-37's land step: track R's host
        // filter (gap 3201) stops `planwire::routine_instances` sending the empty window, so
        // the kernel plans that minute and any refusal fails the arm again.
        Err(e) => return Err(TestCaseError::fail(e)),
    };
    for seg in day.segments.iter().filter(|s| s.end <= w.now) {
        if seg.flags.open {
            let grown = later.segments.iter().find(|s| {
                s.start == seg.start && s.kind == seg.kind && s.item == seg.item
            });
            prop_assert!(
                grown.is_some_and(|g| g.end >= seg.end),
                "an open segment moved or shrank: {seg:?}"
            );
            continue;
        }
        prop_assert!(
            later.segments.contains(seg),
            "a replan moved a settled segment: {seg:?}"
        );
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 256, max_shrink_iters: 2_000, ..ProptestConfig::default() })]

    /// **§8.3's invariants hold of every day the KERNEL plans** (W-37 track H,
    /// README gap 3084): the planner R3 ships, asked on every generated case.
    #[test]
    fn day_plan_satisfies_every_invariant(case in case_strategy()) {
        let w = build(&case);
        check_day_invariants(&Kernel, &case, &w)?;
    }
}


impl World {
    /// **The whole request the kernel plans from — the binary's own** (the W-40
    /// repair, README gap 3907): `planreq::request` over this world, so the
    /// documents, the log through D24's seam, the CAPACITY section
    /// (`tm_core::planwire::capacity_json`, the pure half
    /// `kernel_capacity::request` calls) and the `planner` section
    /// (`tm_core::planwire::planner_json`, the codec R3 swaps in) are each
    /// written by the one encoder the binary writes them with.
    ///
    /// Until the repair this arm spelled the capacity section a fourth time —
    /// `windowHours` 8/1, `budgetRatio` 3/4, the bins, the safety, `batchMaxMin`
    /// 20, the posterior and the sleep as literals, `state.loc` sent raw, and the
    /// candidates' records by hand — so its 287-draw hash arm
    /// and its `TM_ORACLE` arm planned through a request the binary does not
    /// send. Every draw is generated on [`DAY`], so the binary's dating of the
    /// floors and the lookahead by `now`'s date is the hand spelling's `date()`.
    fn plan_request(&self) -> Value {
        let cands = self.candidates();
        let w = planreq::World {
            docs: &self.docs,
            log: &self.log,
            tree: &self.tree,
            cfg: &self.cfg,
            state: &self.state,
            now: self.now,
            cands: &cands,
            replay: &self.replay,
        };
        planreq::request(&w, None).0
    }
}

/// The kernel's own day for a request, or the refusal it answered.
///
/// **The §8.4 answer travels with it under `__grants`** (W-30): one call answers `plan` and
/// `lookahead` together, and the lookahead's per-candidate grants are §7's WHOLE answer — the
/// ten fields the fork region's grant_fields compared until R3 deleted it, and `kernel_prios`
/// reads back. A leading `__` is not a
/// key the wire has: `PlanWire.planKeys` lists the nine the `plan` object carries, so a reader
/// of either side cannot confuse it for one.
fn kernel_plan(req: &Value) -> Result<Value, String> {
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("the response is json");
    if resp["ok"]["plan"]["day"].is_null() {
        return Err(raw);
    }
    let mut p = resp["ok"]["plan"].clone();
    p["__grants"] = resp["ok"]["lookahead"]["grants"].clone();
    Ok(p)
}

/// **The kernel's own §7 answer, read back as the fork's `Prio`** (W-30), so the fork can be
/// asked to plan the day WITH IT — `PlanInput::with_ranking`, which is exactly what the shipped
/// binary does (`planning::build_ranked` → `Ctx::priorities` → `kernel_capacity::rank`, then
/// `with_ranking`).
///
/// **Why a second fork run exists at all.** §8.2 step 5's assignment cannot be asserted against
/// a fork that ran its OWN §7 pass, because the two passes are given different capacity by
/// design — parity **P1** for the future days and parity **P41** for day 0 — and every
/// difference in `p` reaches step 5 as a different rank order. Measured at this commit, over
/// 526 cases, the number of days on which the whole §7 answer agreed row for row was **four**;
/// an assertion gated on that is an assertion that does not run, which is the defect this arm
/// shipped with for one whole run (README gap 2005). Handing the fork the kernel's answer makes
/// step 5 comparable on EVERY day, and it compares the thing the binary actually runs.
///
/// It is `kernel_capacity::parse`'s **third** spelling and README gap **2006** is amended to say
/// so rather than growing one quietly: `tm` is a `[[bin]]` with no library target.
///
/// `None` when the grants cannot be keyed 1:1 onto `cands` — an id naming two rows (§5.3's
/// carried instance), or a candidate the kernel answered nothing for. The census counts those
/// days; a guess would compare the kernel against a ranking neither planner holds.
fn kernel_prios(plan: &Value, cands: &[Candidate]) -> Option<Vec<Prio>> {
    let mut by_id: BTreeMap<&str, Option<&Value>> = BTreeMap::new();
    for g in plan["__grants"].as_array().map(Vec::as_slice).unwrap_or_default() {
        let id = g["id"].as_str()?;
        // A second row under one id poisons the entry rather than overwriting it.
        by_id.entry(id).and_modify(|e| *e = None).or_insert(Some(g));
    }
    let unit = |v: &Value| -> u128 { v.as_str().unwrap_or("0").parse::<u128>().unwrap_or(0) };
    let mut out = Vec::with_capacity(cands.len());
    for c in cands {
        let g = (*by_id.get(c.id.as_str())?)?;
        let class = match g["class"].as_str()? {
            "wall" => PrioClass::Wall,
            "hot" => PrioClass::Hot,
            "impossible" => PrioClass::Impossible,
            "overdue" => PrioClass::Overdue,
            "mandatory" => PrioClass::Mandatory,
            "hotflag" => PrioClass::HotFlag,
            "dated" => PrioClass::Dated,
            "floor" => PrioClass::Floor,
            "rank" => PrioClass::Rank,
            "optional" => PrioClass::Optional,
            _ => return None,
        };
        // A wall is off §7.2's scale on both sides: the kernel writes `p: null` and the fork's
        // own `Prio::wall` is the comparand, so it is built here rather than decoded.
        if class == PrioClass::Wall {
            // `Prio::wall` is private to `tm-core`; this is its body, and §7.2's
            // "off the scale" is what both spellings say (`priority.rs:842`).
            out.push(Prio {
                id: c.id.clone(),
                p: 0,
                class,
                k: c.k,
                u: None,
                bin: None,
                need_min: 0,
                avail_min: 0,
                avail_min_exact: Exact::default(),
                allocation_min: 0,
                allocation_min_exact: Exact::default(),
                shortfall_min: 0,
                shortfall_min_exact: Exact::default(),
                until: None,
                hysteresis_applied: false,
                raw_p: 0,
            });
            continue;
        }
        let avail = Exact::new(unit(&g["avail"]), CAP_DEN);
        let alloc = Exact::new(unit(&g["allocation"]), CAP_DEN);
        let short = Exact::new(unit(&g["shortfall"]), CAP_DEN);
        let need = u32::try_from(g["need"].as_u64()?).ok()?;
        let p = u8::try_from(g["p"].as_u64()?).ok()?;
        let raw_p = u8::try_from(g["rawP"].as_u64()?).ok()?;
        // `u` is the ONE field the grant does not carry, and the shipped reader rebuilds it:
        // `planwire::prio_of` (moved from `kernel_capacity` at W-35 track R, gap 2876) sets it
        // only where the grant has an `until` and is not a
        // wall, as the exact `need / avail` held on the kernel's side of 1 — at or above 1
        // exactly when the grant's `bin` is `null` (HOT), below it otherwise. **W-33, README
        // gap 2518: this spelling used to fill `need / avail` for EVERY grant, a zero capacity
        // infinite**, so every undated candidate — no grant, `avail` 0, a positive `need` —
        // read as HOT here and as not-HOT in the shipped binary. Nothing step 5 reads uses `u`;
        // §8.2 step 8's `hot` and `impossible` do (`Prio::is_hot`, `Prio::is_impossible`), and
        // this arm has compared both against the kernel since W-33, so the spelling is the
        // shipped one now. (Walls never reach here: they are built above.)
        let until = g["until"].as_str().and_then(|d| NaiveDate::parse_from_str(d, "%Y-%m-%d").ok());
        let bin = g["bin"].as_u64().map(|b| b as u8);
        let units = unit(&g["avail"]);
        let uu = until.is_some().then(|| {
            let exact = if units == 0 {
                f64::INFINITY
            } else {
                (u128::from(need) * CAP_DEN) as f64 / units as f64
            };
            match bin {
                None => exact.max(1.0),
                Some(_) => exact.min(1.0 - f64::EPSILON),
            }
        });
        out.push(Prio {
            id: c.id.clone(),
            p,
            class,
            k: u8::try_from(g["k"].as_u64()?).ok()?,
            u: uu,
            bin,
            need_min: need,
            avail_min: avail.floor_u32(),
            avail_min_exact: avail,
            allocation_min: alloc.floor_u32(),
            allocation_min_exact: alloc,
            shortfall_min: short.floor_u32(),
            shortfall_min_exact: short,
            until,
            hysteresis_applied: p != raw_p,
            raw_p,
        });
    }
    Some(out)
}


/// **§8.2 step 2's ORDERING half, drawn** — README gap **2226**.
///
/// The fuzz above cannot reach this case: `ROUTINES`' first five have
/// pairwise-disjoint placeable windows, so the sort `collect_routines` and
/// `Planner.sortRoutines` both perform — mandatory first, then by the moment the
/// window closes, then by id — permutes a list whose placement does not depend
/// on its order. An auditor reversed it at W-31 and **no row of any case moved**
/// (W-31's plant 3).
///
/// Here two mandatory instances contend for one position. `teatime` is a
/// 60-minute job in a 60-minute window, so it has exactly one feasible start;
/// `lunch` is a 30-minute job in a two-hour window that overlaps it. Under the
/// sort the tightest window claims first and **both** are placed, back to back.
/// Under any other order — by id (`lunch` < `teatime`), by the window's OPEN
/// (11:00 < 11:30 is the same order, but reversed it is not), or reversed —
/// `lunch` takes 11:30 and `teatime` never fits: step 2 defers it, and step 6
/// cannot repair it either, because its window holds no free hour and no
/// assigned slot an hour long inside it to displace. So **asserting the two rows
/// asserts the order**, without a second spelling of the comparator here.
///
/// The fork's half — the two rows compared to the fork ranked as the kernel
/// ranked it, gap 2224's comparand — is
/// `two_routines_contend_for_one_position_on_the_fork`, in the region (W-37
/// track H): this half reads the kernel alone and outlives R3.
#[test]
fn two_routines_contend_for_one_position() {
    let w = build(&contending_routines());
    let plan = kernel_plan(&w.plan_request()).expect("the kernel plans the day");
    let krout = kernel_routine_rows(&plan);
    let day = date();
    let tz = w.cfg.tz;
    let sec = |h: u32, m: u32| {
        rowwire::kernel_sec(local_dt(tz, day, NaiveTime::from_hms_opt(h, m, 0).expect("time")))
    };
    // **THE PLACEMENT IS THE ORDER.** `teatime` first because its window closes
    // first, then `lunch` in the next free minute of its own window.
    assert_eq!(
        krout,
        vec![
            (sec(11, 0), sec(12, 0), "teatime".to_string()),
            (sec(12, 0), sec(12, 30), "lunch".to_string()),
        ],
        "§8.2 step 2 placed the contending routines in the wrong order or dropped one"
    );
}

/// The day of [`two_routines_contend_for_one_position`]: one item, and
/// `lunch` (bit 0) and `teatime` (bit 5) and nothing else.
fn contending_routines() -> Case {
    Case {
        items: vec![Spec {
            ci: 0, k: 1, est_b: 2, small: None, due_in: Some(0), dep: None,
            loc_home: false, atomic: false, parent: None, waiting: false, hot: false,
            floor: None,
        }],
        walls: vec![],
        now_idx: 0,
        done_blocks: 0,
        report: None,
        routines: 1 | 32,
        optionals: false,
        home: false,
        active: None,
        interrupt: None,
        late: false,
    }
}

/// The kernel's §8.2 step-2 rows `(start, stop, item)`, in timeline order.
fn kernel_routine_rows(plan: &Value) -> Vec<(i64, i64, String)> {
    plan["segments"]
        .as_array().map(Vec::as_slice).unwrap_or_default().iter()
        .filter(|s| s["kind"] == "routine")
        .map(|s| (s["start"].as_i64().unwrap_or(-1), s["stop"].as_i64().unwrap_or(-1),
                  s["item"].as_str().unwrap_or_default().to_string()))
        .collect()
}


/// **P45's rule bites on a generated day** — a perturbation of the kernel's own day, three ways:
/// the Break row removed, moved by a minute, and a Rest row slid under it. A rule that passed any
/// of them would be asserting nothing on the generated days of
/// [`the_kernel_keeps_a_running_break_on_every_generated_day`]. **One rule since W-38** (README
/// gap 3471): `forkclass::p45_rule` over the day the host's codec decodes; this file's own copy
/// over the raw answer (w35_check_break, the same rule written twice — README gap 3122's family,
/// named by W-37 track R's gap 3202) is deleted.
#[test]
fn the_break_checker_fails_on_a_perturbed_answer() {
    let case = Case {
        items: vec![],
        walls: vec![],
        now_idx: 2,
        done_blocks: 0,
        report: None,
        routines: 0,
        optionals: false,
        home: false,
        active: None,
        interrupt: None,
        late: false,
    };
    let mut w = build(&case);
    let tz = w.cfg.tz;
    let span = (local_dt(tz, date(), NaiveTime::MIN), local_dt(tz, date() + Duration::days(1), NaiveTime::MIN));
    let t = w.now - Duration::minutes(5);
    w.state.break_ = Some(tm_core::store::BreakState {
        started: Some(t.time()),
        planned_min: 20,
        place: Some("walk".to_string()),
    });
    let day = Kernel.day(&w, &w.state, w.now).expect("the kernel plans the break day");
    let check = |d: &DayPlan| forkclass::p45_rule(d, t, 20, Some("walk"), w.now, span);
    let (lo, hi, open) = check(&day).expect("the kernel's own day passes");
    assert_eq!((lo, hi, open), (t, t + Duration::minutes(20), false));
    // 1. the row removed
    let mut gone = day.clone();
    gone.segments.retain(|s| s.kind != SegKind::Break);
    assert!(check(&gone).is_err(), "a day with no Break row passed P45's rule");
    // 2. the row moved by a minute
    let mut moved = day.clone();
    for s in moved.segments.iter_mut().filter(|s| s.kind == SegKind::Break) {
        s.end += Duration::minutes(1);
    }
    assert!(check(&moved).is_err(), "a Break row a minute long passed P45's rule");
    // 3. a Rest row slid under the break
    let mut over = day.clone();
    over.segments.push(Segment {
        start: w.now,
        end: w.now + Duration::minutes(10),
        kind: SegKind::Rest,
        energy: Some(3),
        item: None,
        instance: None,
        flags: tm_core::dayplan::SegFlags::default(),
    });
    assert!(check(&over).is_err(), "a Rest row scheduled over the break passed P45's rule");
}


/// **`send_order` is the fork's `priority::compute` sort** — `(no due last, due, own_order,
/// index)`, the kernel's REQUEST POSITION, which `Look.sortDueIx` breaks a date's ties by and
/// D60's key reads. Nothing else in this file can tell it from the collection order: the kernel
/// and the D60 comparand both read it, so W-36's plant that made it the identity SURVIVED every
/// arm. It is pinned here on a day whose collection order is not the served order: an undated
/// line, one due tomorrow, one due today, in that order in the file.
#[test]
fn send_order_is_the_forks_compute_order() {
    let item = |due_in: Option<u8>| Spec {
        ci: 2, k: 3, est_b: 1, small: None, due_in, dep: None, loc_home: false,
        atomic: false, parent: None, waiting: false, hot: false, floor: None,
    };
    let case = Case {
        items: vec![item(None), item(Some(1)), item(Some(0))],
        walls: vec![],
        now_idx: 0,
        done_blocks: 0,
        report: None,
        routines: 0,
        optionals: false,
        home: false,
        active: None,
        interrupt: None,
        late: false,
    };
    let w = build(&case);
    let cvec = w.candidates();
    let file: Vec<String> = cvec.iter().map(|c| c.id.to_string()).collect();
    let sent: Vec<String> = planreq::send_order(&cvec).iter().map(|&i| cvec[i].id.to_string()).collect();
    assert_eq!(file.len(), 3, "three candidates: {file:?}");
    assert_eq!(sent, vec![file[2].clone(), file[1].clone(), file[0].clone()],
        "due today, then due tomorrow, then the undated line: {file:?}");
}

/// **The reversed day** (README gap 2801): two IMPOSSIBLE items of one `ci`, the one due
/// tomorrow on the first line and the one due today on the second — so D60's order and the
/// file's disagree.
fn reversed_day() -> Case {
    let item = |due: u8| Spec {
        ci: 2, k: 3, est_b: 60, small: None, due_in: Some(due), dep: None, loc_home: false,
        atomic: false, parent: None, waiting: false, hot: false, floor: None,
    };
    Case {
        items: vec![item(1), item(0)],
        walls: vec![],
        now_idx: 0,
        done_blocks: 0,
        report: None,
        routines: 0,
        optionals: false,
        home: false,
        active: None,
        interrupt: None,
        late: false,
    }
}

/// **§8.3's monotone rank reads the planner's OWN order** (the owner's D63; W-37 track H): on
/// the reversed day the kernel serves the item due today, on the second line, and leaves the
/// first — `check_day_invariants` passes over it with the kernel's order, and the same day read
/// with the FILE's order as "the higher-ranked of two" (the fork's reading, which D63 replaced
/// for a planner that orders by D60) fails the monotone-rank check by name. So the rank view is
/// load-bearing, and the kernel arm's pass is not a pass because the check was blind to it.
#[test]
fn the_kernels_monotone_rank_is_its_own_order() {
    /// The kernel's day, read in the file's order.
    struct FileOrder;
    impl Planner for FileOrder {
        fn day(&self, w: &World, state: &RuntimeState, now: DateTime<Tz>) -> Result<DayPlan, String> {
            Kernel.day(w, state, now)
        }
        fn rank_view(&self, _w: &World, cands: &[Candidate], _prios: &[Prio]) -> Vec<Candidate> {
            cands.to_vec()
        }
        fn name(&self) -> &'static str {
            "the kernel read in file order"
        }
    }
    let case = reversed_day();
    let w = build(&case);
    check_day_invariants(&Kernel, &case, &w).unwrap_or_else(|e| panic!("the kernel's own order: {e}"));
    let e = check_day_invariants(&FileOrder, &case, &w).expect_err("the file's order passed the reversed day");
    assert!(e.to_string().contains("(later line) is assigned"), "{e}");
}

/// **An impossible answer with no `until` keys as every other answer** (W-37 repair, README gap
/// 3337). The harness's copy of D60's key (`forkclass::d60_cands`) read `until` as `0` when it was
/// absent, putting such an answer FIRST, while the kernel's `Planner.Ranked.imp` is
/// `(answerUntil x.out).map …` — `none` for an answer with neither a floor nor a grant, which then
/// keys as every other. On the reversed day the impossible tie keys `(0, until)`; the same answer
/// with its `until` taken away keys as every other candidate does (its root one file down).
#[test]
fn an_impossible_answer_with_no_until_keys_as_every_other() {
    let case = reversed_day();
    let w = build(&case);
    let cvec = w.candidates();
    // The kernel's §7 answers as the BINARY reads them (`planwire::read_capacity_answer`, through
    // `planreq::kernel_day`) — until W-38 this read them with the fork region's own `kernel_prios`,
    // so R3's deletion of the region would have left this test, outside it, unbuildable (README
    // gap 3472, found by W-38's deletion simulation).
    let pw = planreq::World { docs: &w.docs, log: &w.log, tree: &w.tree, cfg: &w.cfg, state: &w.state, now: w.now, cands: &cvec, replay: &w.replay };
    let (_, ans) = planreq::kernel_day(&pw, None).unwrap_or_else(|e| panic!("the kernel refused: {e}"));
    let ps = ans.prios;
    let i = ps.iter().position(forkclass::is_impossible_tie).expect("the reversed day has an impossible tie");
    assert!(ps[i].until.is_some(), "the tie has an until");
    assert_eq!(forkclass::d60_cands(&cvec, &ps)[i].root_order.0, 0, "an impossible tie keys first");
    let mut bare = ps.clone();
    bare[i].until = None;
    let k = cvec.iter().position(|c| c.id == ps[i].id).expect("the answer's candidate");
    assert_eq!(
        forkclass::d60_cands(&cvec, &bare)[k].root_order,
        (cvec[k].root_order.0 + 1, cvec[k].root_order.1),
        "an impossible answer with no until keyed as an impossible tie"
    );
}

/// **README gap 3280, CLOSED at W-37's land step, and pinned**: at the minute a routine's §8.2
/// step-2 window closes, `planwire::routine_instances` used to send it an EMPTY window and the
/// kernel refused the whole planner section, where the fork plans the day. Track R's filter (gap
/// 3201) sends no instance with nothing left of its span, so the kernel plans that minute: on a
/// late day with `lunch` (11:30-13:30) it plans 13:29, 13:30 and 13:31, and the case is real —
/// [`routine_window_ends_at`] names 13:30 and only 13:30.
#[test]
fn a_routine_window_s_close_is_planned_by_the_kernel() {
    let mut case = contending_routines();
    case.routines = 1;
    case.late = true;
    case.now_idx = 1;
    let w = build(&case);
    for (h, m, closes) in [(13, 29, false), (13, 30, true), (13, 31, false)] {
        let t = at(w.cfg.tz, h, m);
        assert_eq!(routine_window_ends_at(&w, &w.state, t), closes, "a window closes at {h}:{m:02}: {closes}");
        if let Err(e) = Kernel.day(&w, &w.state, t) {
            panic!("the kernel refused {h}:{m:02} (README gap 3280): {e}");
        }
    }
}

/// **The cells the kernel is allowed to disagree with the fork about on a
/// GENERATED day, with the gap that records why.**
///
/// The same two holes `tm/tests/kernel_row_cells.rs` declares on its fixture
/// day, and no others — a third name appearing here would be a finding, not a
/// widening:
///
/// * **`note`** (gap **1102**, and the `note: null` decision in `seg_json`) —
///   `SegFlags::note` is a `String` the fork's planner wrote as prose and
///   `Planner.Note` is eleven names with their arguments, so a host whose
///   planner produced text has nothing to send. The kernel **derives** the
///   column and cannot derive the `⚠` branch, which needs the fork's
///   `effective_due`.
/// * **`est`** (gap **1101**) — the fork's `est_cell` reads `est_original`
///   first and this kernel has one estimate view, `Core.est`, which is `est:`
///   then the leading estimate. A line carrying both makes the two readers pick
///   different numbers.
///
/// Every other cell — `time`, `ci`, `p`, `mark`, `title`, `parent`, `actual`
/// and `batchNames` — is compared **exactly**, on every row of every case.
///
/// **And `parent` is now compared at a value** (W-27). It was in this list
/// before, and the list was true and empty of content for that one cell: the
/// generated corpus had no `@` token, so both readers wrote `""` on every row
/// and the cell asserted nothing. [`CENSUS`]'s fifth counter and the
/// `parents > 0` assertion are what make the membership load-bearing.
const CELL_HOLES: [&str; 2] = ["note", "est"];

// ===========================================================================
// **W-38 (track H): what the fork region compared that needs no fork, moved out of it**
// (README gap 3282).
//
// R3 deletes the region below whole. Several of its arms asserted things of the KERNEL alone —
// the kernel's rendering of a day through the `plan` section, the projections of step 8's
// tuples on the kernel's own wire, P45's rule on a generated break day, and the kernel halves
// of the fixed days — and so would have left with the fork although no fork was needed to
// ask them. They are asked here, of the kernel, and the region keeps only what compares
// with the fork. What the region compares WITH the fork is frozen by value in
// `planner_classes.rs`' comparand; README's W-38 track H table says which line holds each.
// ===========================================================================

/// **The kernel's reservation**, when it placed one: the energy-less `▶` Block row starting at
/// `now` — its `stop`.
fn w35_reservation(plan: &Value, now_sec: i64) -> Option<i64> {
    plan["segments"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default()
        .iter()
        .find(|s| {
            s["kind"] == "block"
                && s["energy"].is_null()
                && s["flags"]["current"] == true
                && s["start"].as_i64() == Some(now_sec)
        })
        .map(|s| s["stop"].as_i64().unwrap_or(-1))
}

/// The kernel's Block/Batch rows from `now` on, in the same shape.
fn w36_kernel_work_rows(plan: &Value, now_sec: i64) -> Vec<(i64, i64, Vec<String>)> {
    plan["segments"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default()
        .iter()
        .filter(|s| (s["kind"] == "block" || s["kind"] == "batch")
            && s["start"].as_i64().unwrap_or(-1) >= now_sec
            && s["flags"]["current"] != true)
        .map(|s| {
            let mut it: Vec<String> = match s["kind"].as_str() {
                Some("batch") => s["batch"].as_array().map(Vec::as_slice).unwrap_or_default()
                    .iter().filter_map(|v| v.as_str().map(ToString::to_string)).collect(),
                _ => s["item"].as_str().map(|x| vec![x.to_string()]).unwrap_or_default(),
            };
            it.sort();
            (s["start"].as_i64().unwrap_or(-1), s["stop"].as_i64().unwrap_or(-1), it)
        })
        .collect()
}


/// `(rows compared, cases, note-hole firings, est-hole firings, non-empty parent cells, kernel rows
/// digested at a multiplier other than 1.0)` — what [`the_kernel_reads_every_day_it_plans`] looked
/// at, read inside the arm that fills it (as `CENSUS`, the fork arm's, is).
static KERNEL_CELL_CENSUS: Mutex<[u64; 6]> = Mutex::new([0; 6]);

/// `[cases, impossible tuples, underused tuples, blocked tuples, blocked deps]` — what
/// [`the_kernels_step_8_ids_are_the_projections_of_its_tuples`] compared.
static PROJECTION_CENSUS: Mutex<[u64; 5]> = Mutex::new([0; 5]);

/// `[cases, break days, still running, overrun, open rows of a paused block]` — what
/// [`the_kernel_keeps_a_running_break_on_every_generated_day`] asked.
static BREAK_CENSUS: Mutex<[u64; 5]> = Mutex::new([0; 5]);

/// **Step 8's id lists on the kernel's own wire are the projections of its tuples**: `impossible`
/// of `impossibleUntil`, `underused` of `underusedLevels`, `blocked` of `blockedDeps`, as multisets.
/// `Ok` carries the tuple counts `(impossible, underused, blocked, deps)`; `Err` names the list.
fn step8_projections(kd: &Value) -> Result<(usize, usize, usize, usize), String> {
    let arr = |v: &Value| -> Vec<Value> { v.as_array().cloned().unwrap_or_default() };
    let s = |v: &Value| -> String { v.as_str().unwrap_or("<not a string>").to_string() };
    let sorted = |mut x: Vec<String>| {
        x.sort();
        x
    };
    let imp: Vec<(String, u64)> = arr(&kd["impossibleUntil"]).iter()
        .map(|o| (s(&o["id"]), o["shortMin"].as_u64().unwrap_or(u64::MAX))).collect();
    let mut pairs: Vec<(String, u64)> = arr(&kd["impossible"]).iter()
        .map(|o| (s(&o["id"]), o["shortMin"].as_u64().unwrap_or(u64::MAX))).collect();
    let mut proj = imp.clone();
    pairs.sort();
    proj.sort();
    if proj != pairs {
        return Err(format!("`impossible` is not `impossibleUntil`'s projection: {pairs:?} against {proj:?}"));
    }
    let und: Vec<String> = arr(&kd["underusedLevels"]).iter().map(|o| s(&o["id"])).collect();
    if sorted(und.clone()) != sorted(arr(&kd["underused"]).iter().map(s).collect()) {
        return Err(format!("`underused` is not `underusedLevels`' projection: {}", kd["underused"]));
    }
    let blk: Vec<(String, usize)> = arr(&kd["blockedDeps"]).iter()
        .map(|o| (s(&o["id"]), arr(&o["deps"]).len())).collect();
    if sorted(blk.iter().map(|b| b.0.clone()).collect()) != sorted(arr(&kd["blocked"]).iter().map(s).collect()) {
        return Err(format!("`blocked` is not `blockedDeps`' projection: {}", kd["blocked"]));
    }
    Ok((imp.len(), und.len(), blk.len(), blk.iter().map(|b| b.1).sum()))
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(64),
        max_shrink_iters: 2_000,
        ..ProptestConfig::default()
    })]

    /// **The kernel reads every day IT plans, and writes the host's cells for it** (W-38,
    /// README gap 3282) — `the_kernel_reads_every_day_the_fork_planned`'s two claims, asked of
    /// the day R3 ships instead of the fork's: (1) no day the kernel plans is refused by the
    /// `plan` section's wire (every R10 bound it carries is one a real day could exceed); (2)
    /// cell for cell, row for row, against the host's `emit::row_cells` over the SAME decoded
    /// day, with [`CELL_HOLES`]'s two declared exceptions and no others. The day is drawn at a
    /// learned multiplier too (the hash arm's values), so the host codec's digest check —
    /// `planwire::read_plan` refuses a day whose rows do not hash to the kernel's `hash` —
    /// asks the EMITTER of zmij's spellings on generated days, which the region's hash arm
    /// asked of the fork's rows.
    #[test]
    fn the_kernel_reads_every_day_it_plans(
        case in case_strategy(),
        mult in prop::sample::select(vec![
            None, Some(1.6), Some(0.25), Some(2.0), Some(1.125), Some(0.3), Some(0.1 + 0.2), Some(123.456),
        ]),
    ) {
        let mut w = build(&case);
        w.set_multiplier(mult);
        let day = Kernel.day(&w, &w.state, w.now).map_err(TestCaseError::fail)?;
        let lean = match rowwire::kernel_rows(w.docs_json(), &day, &w.cfg) {
            Ok(rows) => rows,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the wire refused a day the kernel planned: {head}");
                unreachable!()
            }
        };
        let host = rowwire::fork_cells(&day, &w.tree, &w.cfg);
        prop_assert_eq!(lean.len(), host.len(), "the kernel answered {} rows for {} segments", lean.len(), host.len());
        let mut seen = [0u64; 6];
        seen[0] = host.len() as u64;
        seen[1] = 1;
        seen[5] = day.segments.iter().filter(|s| s.flags.multiplier.is_some_and(|m| m != 1.0)).count() as u64;
        for (i, (f, l)) in host.iter().zip(&lean).enumerate() {
            if !f.parent.is_empty() {
                seen[4] += 1;
            }
            for (cell, hosted, kernelled) in rowwire::differences(f, l) {
                prop_assert!(
                    CELL_HOLES.contains(&cell),
                    "row {i}: the two readers disagree on an UNDECLARED cell {cell:?} — host {hosted:?}, kernel {kernelled:?}"
                );
                if cell == "note" {
                    seen[2] += 1;
                } else {
                    seen[3] += 1;
                }
            }
        }
        let [rows, cases, notes, ests, parents, mults] = {
            let mut c = KERNEL_CELL_CENSUS.lock().expect("census");
            for (a, b) in c.iter_mut().zip(seen) {
                *a += b;
            }
            *c
        };
        prop_assert!(rows >= 4 * cases, "only {rows} rows over {cases} cases");
        if cases >= 32 {
            prop_assert!(notes > 0, "the `note` hole has not fired in {cases} cases (gap 1102)");
            prop_assert!(ests > 0, "the `est` hole has not fired in {cases} cases (gap 1101)");
            prop_assert!(parents > 0, "no row's `parent` cell was non-empty in {cases} cases");
            prop_assert!(mults > 0, "no row was digested at a multiplier other than 1.0 in {cases} cases");
        }
        eprintln!(
            "planner_invariants kernel-day census: {cases} cases, {rows} rows compared, note-hole {notes}, \
             est-hole {ests}, parent-cells {parents}, rows digested at a multiplier other than 1.0 {mults}"
        );
    }

    /// **Step 8's id lists are the projections of the kernel's tuples** (W-38, README gap 3282):
    /// the check the region's step-8 arm made of the kernel's own wire before it compared with
    /// the fork, on the same widened days (a travel day and a spent budget drawn).
    #[test]
    fn the_kernels_step_8_ids_are_the_projections_of_its_tuples(
        case in case_strategy(),
        travel in prop_oneof![3 => Just(false), 1 => Just(true)],
        spent in prop_oneof![3 => Just(false), 1 => Just(true)],
    ) {
        let mut w = build(&case);
        let _ = widen_for_notes(&mut w, &case, travel, spent);
        let plan = kernel_plan(&w.plan_request()).map_err(TestCaseError::fail)?;
        let (imp, und, blk, deps) = step8_projections(&plan["diagnostics"]).map_err(TestCaseError::fail)?;
        let c = {
            let mut c = PROJECTION_CENSUS.lock().expect("census");
            for (a, b) in c.iter_mut().zip([1, imp, und, blk, deps]) {
                *a += b as u64;
            }
            *c
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(64);
        if c[0] >= generated {
            prop_assert!(c[1] > 0, "no IMPOSSIBLE tuple was projected in {} cases", c[0]);
            prop_assert!(c[2] > 0, "no UNDERUSED tuple was projected in {} cases", c[0]);
            prop_assert!(c[3] > 0 && c[4] > 0, "no BLOCKED tuple or dep was projected in {} cases", c[0]);
        }
        eprintln!(
            "planner_invariants step-8 projection census: {} cases; impossible {}, underused {}, blocked {} ({} deps)",
            c[0], c[1], c[2], c[3], c[4]
        );
    }

    /// **P45 on every generated break day, of the kernel alone** (W-38, README gap 3282): the
    /// W-35 arm's rule check, which needs no fork — `forkclass::p45_rule` over the kernel's day
    /// — and the open row of a paused block: it ends where the break began (or before) and
    /// carries no `▶` (`tm break` pauses the block).
    #[test]
    fn the_kernel_keeps_a_running_break_on_every_generated_day(
        case in case_strategy(),
        brk in prop::option::of((0u32..=40, 5u32..=30, prop::sample::select(vec!["walk", "seat", "bed", "phone"]))),
    ) {
        let mut w = build(&case);
        let tz = w.cfg.tz;
        let mut row = [1u64, 0, 0, 0, 0];
        if let (Some(t), Some((_, planned, place))) = (w.run_a_break(&case, brk), brk) {
            let day = Kernel.day(&w, &w.state, w.now).map_err(TestCaseError::fail)?;
            let span = (local_dt(tz, date(), NaiveTime::MIN), local_dt(tz, date() + Duration::days(1), NaiveTime::MIN));
            let (_, _, open) = forkclass::p45_rule(&day, t, planned, Some(place), w.now, span)
                .map_err(|e| TestCaseError::fail(format!("P45: {e}")))?;
            row[1] = 1;
            row[2] = u64::from(!open);
            row[3] = u64::from(open);
            for s in day.segments.iter().filter(|s| s.kind == SegKind::Block && s.flags.open) {
                prop_assert!(!s.flags.current, "a block paused by a running break is drawn running: {s:?}");
                prop_assert!(s.start >= t || s.end <= t, "the paused block's open row runs past the break's start {t}: {s:?}");
                row[4] += 1;
            }
        }
        let c = {
            let mut c = BREAK_CENSUS.lock().expect("census");
            for (a, b) in c.iter_mut().zip(row) {
                *a += b;
            }
            *c
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(64);
        if c[0] >= generated {
            prop_assert!(c[2] > 0 && c[3] > 0, "P45 was asked of no running and no overrun break in {} cases: {c:?}", c[0]);
            prop_assert!(c[4] > 0, "no paused block's open row was asked in {} cases", c[0]);
        }
        eprintln!(
            "planner_invariants break census: {} cases, {} break days (running {}, overrun {}), open rows of a paused block {}",
            c[0], c[1], c[2], c[3], c[4]
        );
    }
}

/// **`step8_projections` bites, and does not over-bite** (AGENTS §5.8): three tuples and
/// their three projections pass; each projection with one entry dropped, or one id changed,
/// is refused, naming its list.
#[test]
fn step8_projections_bites() {
    let good = json!({
        "impossibleUntil": [{"id": "zaa", "shortMin": 30, "until": "2026-09-07"}],
        "impossible": [{"id": "zaa", "shortMin": 30}],
        "underusedLevels": [{"id": "zab", "energy": 5, "ci": 2}],
        "underused": ["zab"],
        "blockedDeps": [{"id": "zac", "deps": ["^zaa"]}],
        "blocked": ["zac"],
    });
    assert_eq!(step8_projections(&good), Ok((1, 1, 1, 1)));
    for (list, bent) in [
        ("`impossible`", json!([{"id": "zaa", "shortMin": 31}])),
        ("`underused`", json!([])),
        ("`blocked`", json!(["zzz"])),
    ] {
        let mut x = good.clone();
        let key = list.trim_matches('`');
        x[key] = bent;
        let e = step8_projections(&x).expect_err("a bent projection passed");
        assert!(e.starts_with(list), "{e}");
    }
}

/// **A P46 day reserves to the end of its block** (W-38, README gap 3282) — the kernel half of
/// the region's `a_p46_day_is_compared_on_every_run`, stated outright: one item running 70
/// minutes against a 30-minute estimate, one-hour blocks, so the block the item is in ends two
/// blocks after it started — fifty minutes from now.
#[test]
fn a_p46_day_reserves_to_the_end_of_its_block() {
    let w = build(&p46_day());
    assert_eq!(w.cfg.block_min(), 60, "the rule below is stated for one-hour blocks");
    let plan = kernel_plan(&w.plan_request()).expect("the kernel plans the P46 day");
    let now_sec = rowwire::kernel_sec(w.now);
    assert_eq!(w35_reservation(&plan, now_sec), Some(now_sec + 50 * 60), "the block the item is in ends fifty minutes from now");
}

/// The fixed P46 day: one item, running 70 minutes against a 30-minute estimate, no wall, no
/// routine, no break.
fn p46_day() -> Case {
    Case {
        items: vec![Spec {
            ci: 2, k: 3, est_b: 1, small: None, due_in: None, dep: None,
            loc_home: false, atomic: false, parent: None, waiting: false, hot: false,
            floor: None,
        }],
        walls: vec![],
        now_idx: 2,
        done_blocks: 0,
        report: None,
        routines: 0,
        optionals: false,
        home: false,
        active: Some((0, 70, 30)),
        interrupt: None,
        late: false,
    }
}

/// **The reversed day is served by due date** (W-38, README gap 3282) — the kernel half of the
/// region's `the_reversed_day_is_served_by_due_date_on_every_run`: of two impossible items of one
/// `ci`, the kernel serves the one due TODAY, on the second line, first (the owner's D60, P51).
///
/// **Its two preconditions, of the kernel alone** (W-45 track C, README gap 4682): both answers are
/// `p = 0` impossible ties and D60's key moves the order — so "the item due today first" is D60's
/// doing and not a ranking that put it first anyway. Until W-45 they were asserted only in the
/// region's `_on_every_run` twin, beside the fork's half, and R3 would have deleted them with it.
#[test]
fn the_reversed_day_is_served_by_due_date() {
    let w = build(&reversed_day());
    let plan = kernel_plan(&w.plan_request()).expect("the kernel plans the reversed day");
    let cvec = w.candidates();
    let ps = kernel_prios(&plan, &cvec).expect("the kernel ranks the reversed day");
    let ids: Vec<String> = cvec.iter().map(|c| c.id.to_string()).collect();
    assert_eq!(ids.len(), 2, "two candidates: {ids:?}");
    assert!(ps.iter().all(forkclass::is_impossible_tie), "both are p = 0 and impossible: {ps:?}");
    assert!(forkclass::is_p51(&cvec, &ps), "D60 moves the order on the reversed day");
    let k = w36_kernel_work_rows(&plan, rowwire::kernel_sec(w.now));
    assert!(!k.is_empty(), "the kernel assigns work on the reversed day");
    assert_eq!(k[0].2, vec![ids[1].clone()], "the kernel serves the item due today first: {k:?}");
}

/// **A batch row, digested** (W-38, README gap 3282) — the kernel half of the region's
/// `a_batch_row_is_digested_on_every_run`: three twenty-minute errands of one `ci`, and the
/// kernel's day, decoded by the host's codec (which refuses a day whose rows do not hash to the
/// kernel's `hash`), holds a batch row.
#[test]
fn a_batch_row_is_digested() {
    let w = build(&errand_day());
    let day = Kernel.day(&w, &w.state, w.now).expect("the kernel plans the errand day and its digest reads back");
    assert!(
        day.segments.iter().any(|s| matches!(s.kind, SegKind::Batch(_))),
        "the kernel's day holds no batch row: {:?}", day.segments
    );
}

/// The fixed errand day: three twenty-minute errands of one `ci`, nothing else.
fn errand_day() -> Case {
    let errand = Spec {
        ci: 2, k: 3, est_b: 1, small: Some(20), due_in: None, dep: None,
        loc_home: false, atomic: false, parent: None, waiting: false, hot: false, floor: None,
    };
    Case {
        items: vec![errand.clone(), errand.clone(), errand],
        walls: vec![],
        now_idx: 0,
        done_blocks: 0,
        report: None,
        routines: 0,
        optionals: false,
        home: false,
        active: None,
        interrupt: None,
        late: false,
    }
}

/// **A sub-second `now` does not move the kernel's day** (W-38, README gap 3282) — the kernel
/// half of parity P43, which the region's `a_sub_second_now_moves_the_forks_day_and_not_the_kernels`
/// states against the fork: the kernel plans every row on `now`'s whole second, so the day planned
/// half a second past a minute is the day planned on it, row for row and digest for digest. (The
/// fork's half — its fractional rows — leaves with the fork: D53.)
#[test]
fn a_sub_second_now_does_not_move_the_kernels_day() {
    let w = build(&Case {
        items: vec![Spec {
            ci: 2, k: 1, est_b: 1, small: None, due_in: None, dep: None, loc_home: false,
            atomic: false, parent: None, waiting: false, hot: false, floor: None,
        }],
        walls: vec![],
        now_idx: 1,
        done_blocks: 0,
        report: None,
        routines: 0,
        optionals: false,
        home: false,
        active: None,
        interrupt: None,
        late: false,
    });
    let at = w.now + Duration::minutes(20);
    let whole = Kernel.day(&w, &w.state, at).expect("the kernel plans the minute");
    let half = Kernel.day(&w, &w.state, at + Duration::milliseconds(500)).expect("the kernel plans half a second past it");
    assert_eq!(whole.hash(), half.hash(), "half a second moved the kernel's digest");
    assert_eq!(whole.segments, half.segments, "half a second moved the kernel's rows");
}

/// **The fork oracle at `TM_ORACLE`, running** (W-39, the owner's D72) — `None`, and every
/// arm that asks it inert, when `TM_ORACLE` is not set. Its `plan` mode is refused by name
/// if the binary lacks it (README gap 196: provenance is not freshness).
fn the_oracle() -> Option<&'static forkplan::Oracle> {
    static ORACLE: std::sync::OnceLock<Option<forkplan::Oracle>> = std::sync::OnceLock::new();
    ORACLE.get_or_init(|| forkplan::oracle_path().map(forkplan::Oracle::new)).as_ref()
}

/// **A fresh draw's seed**: the class draw's own protocol (`forkclass::class_draws`) from a
/// seed the proptest draws, spelled as hex so a failure names a draw anyone can repeat.
fn fresh_seed(bytes: &[u8; 12]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// A fresh draw and its world, and whether the shipped binary holds it (D64(b)).
fn fresh_draw(bytes: &[u8; 12]) -> (String, forkclass::Draw, forkclass::ClassWorld, Result<(), Vec<String>>) {
    let seed = fresh_seed(bytes);
    let draw = forkclass::class_draws(&seed, None).next().expect("a draw");
    let world = forkclass::world_of(&draw);
    let holds = forkclass::binary_holds(&forkclass::Built::of(world.clone()));
    (seed, draw, world, holds)
}

/// **The oracle arm's census** (W-39): `[cases, drawn worlds the binary refuses, lines
/// compared, what-ifs compared, P45 days, P46, P47, P51, P52, P55, P56 lines, oracle requests]`.
/// (Its thirteenth count, the break days README gap 3480's declared class explained, went with
/// the class at the W-40 land step: README gap 3783.)
static ORACLE_CENSUS: Mutex<[u64; 12]> = Mutex::new([0; 12]);

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256),
        max_shrink_iters: 16,
        ..ProptestConfig::default()
    })]

    /// **The kernel plans every fresh draw as fork 4748911 plans it** (W-39, the owner's D72,
    /// README gap 3533) — the exploring differential that outlives R3. Each case is draw 0 of
    /// the class draw from a fresh seed (every arm's widenings, as the frozen batch draws them);
    /// a world the shipped binary cannot hold is counted and set aside (D64(b)); the rest are
    /// answered by `tm-oracle plan` — fork 4748911's planner out of the tree, ranked by the
    /// kernel's grants as the shipped binary ranks it (D53) — with every registered departure
    /// applied by `forkplan::comparand_answers`, the frozen lines' one definition, and the
    /// kernel held to the line by `forkclass::compare_line`, the frozen lines' one comparison.
    /// Inert without `TM_ORACLE`; nothing of the in-tree planner is reached.
    ///
    /// **No declared class since the W-40 land step** (README gap 3783): W-39 declared README
    /// gap 3480's — a difference after a running break explained by the fork planned with the
    /// break UNLOGGED — while the kernel read a running break as a rest of the cut. The owner's
    /// D77 (parity P67) made the kernel's running break reset the cut's counter exactly as the
    /// same break once logged, which is the comparand's reading, so every difference fails.
    #[test]
    #[ignore]
    fn the_kernel_plans_every_fresh_draw_as_the_forks_oracle_plans_it(bytes in any::<[u8; 12]>()) {
        let Some(oracle) = the_oracle() else { return Ok(()) };
        let (seed, draw, world, holds) = fresh_draw(&bytes);
        let mut c = [0u64; 12];
        c[0] = 1;
        if holds.is_err() {
            c[1] = 1;
        } else {
            let b = forkclass::Built::of(world.clone());
            let prios = forkclass::kernel_answer_with_grants(&b)
                .map_err(|e| TestCaseError::fail(format!("seed {seed}: the kernel did not plan the day: {e}")))?
                .1;
            let answers = forkplan::comparand_answers(&b, &prios, oracle)
                .map_err(|e| TestCaseError::fail(format!("seed {seed}: the fork oracle did not answer: {e}")))?;
            let class = forkclass::class_of(&b).key();
            let mut line = forkclass::drawn_line(format!("fresh seed {seed}"), &seed, 0, &draw, &world, &class);
            for key in forkclass::ANSWERS {
                forkclass::set_answer(&mut line, key, answers[key].clone());
            }
            let mut t = forkclass::ClassTally::default();
            let findings = forkclass::compare_line(&line, &mut t);
            prop_assert!(
                findings.is_empty(),
                "{} disagreement(s) with fork 4748911 on a fresh draw (repeat it: class_draws({seed:?}, None).next()):\n  {}",
                findings.len(),
                findings.join("\n  ")
            );
            c[2] = 1;
            c[3] = t.whatifs as u64;
            c[4] = t.p45 as u64;
            c[5] = t.p46 as u64;
            c[6] = t.p47 as u64;
            c[7] = t.p51 as u64;
            c[8] = t.p52 as u64;
            c[9] = t.p55 as u64;
            c[10] = t.p56 as u64;
        }
        let asked = *oracle.asked.lock().expect("census");
        let [cases, refused, compared, whatifs, p45, p46, p47, p51, p52, p55, p56, requests] = {
            let mut g = ORACLE_CENSUS.lock().expect("census");
            for (a, x) in g.iter_mut().zip(c) {
                *a += x;
            }
            g[11] = asked;
            *g
        };
        let asked_now = requests;
        let generated: u64 = std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(256);
        if cases >= generated {
            // THE FLOORS (AGENTS §9.2): the comparison ran, and on the departures it carries.
            prop_assert!(compared > generated / 2, "only {compared} of {cases} fresh draws were compared with the oracle");
            prop_assert!(whatifs > 0 && p45 > 0 && p51 > 0, "a what-if, a running break and D60's order: {whatifs}, {p45}, {p51}");
        }
        eprintln!(
            "planner_invariants oracle census: {cases} fresh draws, {refused} the binary cannot hold, {compared} compared with \
             fork 4748911's planner out of the tree ({asked_now} oracle requests): what-ifs {whatifs}; P45 days {p45}, P46 {p46}, \
             P47 {p47}, P51 {p51}, P52 {p52}, P55 {p55}, P56 {p56}"
        );
    }
}

/// **The plain arm's census** (W-45 track C): `[cases, drawn worlds the binary refuses, worlds the
/// kernel planned, what-ifs asked and answered, base, hash, w35 and step-8 arms, days with no
/// candidate]`.
static KERNEL_DRAW_CENSUS: Mutex<[u64; 9]> = Mutex::new([0; 9]);

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(64),
        max_shrink_iters: 16,
        ..ProptestConfig::default()
    })]

    /// **The kernel plans every fresh class draw, and answers §9.1's what-if exactly where it is
    /// asked — of the kernel alone, in a plain run** (W-45 track C, README gap 4682). The region's
    /// generated arms each assert, beside their fork comparisons, that the kernel PLANS the world
    /// they drew (`the kernel refused a day the fork planned`), that it answers `overtime` on a
    /// request that asked one and on no other, and that a request with no candidate assigns no
    /// work — none of which compares a fork, and all of which R3 would delete with the region. After
    /// it the fork's half meets fresh draws only under `TM_ORACLE`
    /// ([`the_kernel_plans_every_fresh_draw_as_the_forks_oracle_plans_it`]); this keeps the kernel's
    /// half on fresh draws in every `cargo test` run. Each case is draw 0 of the class draw from a
    /// fresh seed (`fresh_draw`: every arm's widenings — a multiplier and a logged break, a running
    /// break and forced overtime, a travel or spent day — as the frozen batch draws them); a world
    /// the shipped binary cannot hold is counted and set aside (D64(b)); the rest are asked as R3's
    /// host asks them (`forkclass::kernel_answer_with_grants`: the host's worked minutes, the
    /// what-if with its grown facts on a running block), decoded by the host's codec, which refuses
    /// a day whose rows do not hash to the kernel's digest.
    #[test]
    fn the_kernel_plans_every_fresh_class_draw(bytes in any::<[u8; 12]>()) {
        let (seed, draw, world, holds) = fresh_draw(&bytes);
        let mut c = [0u64; 9];
        c[0] = 1;
        if holds.is_err() {
            c[1] = 1;
        } else {
            let b = forkclass::Built::of(world);
            let (k, _) = forkclass::kernel_answer_with_grants(&b).map_err(|e| {
                TestCaseError::fail(format!("seed {seed}: the kernel refused a world the binary holds (repeat it: class_draws({seed:?}, None).next()): {e}"))
            })?;
            let asked = forkclass::whatif_json(&b).is_some();
            prop_assert_eq!(
                k.overtime.is_some(), asked,
                "seed {}: the kernel answered `overtime` {} a request that asked {}", seed,
                if k.overtime.is_some() { "to" } else { "nothing to" }, if asked { "one" } else { "none" }
            );
            if b.cands.is_empty() {
                let assigned: Vec<String> = k.day.segments.iter().filter(|s| s.kind.is_work() && s.energy.is_some()).flat_map(|s| s.items()).map(|i| i.to_string()).collect();
                prop_assert!(assigned.is_empty(), "seed {}: the kernel assigned {:?} from a request carrying no candidates", seed, assigned);
                c[8] = 1;
            }
            c[2] = 1;
            c[3] = u64::from(asked);
            c[4 + usize::from(forkclass::Widening::number_of(draw.widening.arm()).unwrap_or(0))] = 1;
        }
        let [cases, refused, planned, whatifs, base, hash, w35, step8, empty] = {
            let mut g = KERNEL_DRAW_CENSUS.lock().expect("census");
            for (a, x) in g.iter_mut().zip(c) {
                *a += x;
            }
            *g
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(64);
        if cases >= generated {
            // THE FLOORS (AGENTS §9.2): the kernel was asked most draws, on every arm's widening, and
            // a what-if was answered.
            prop_assert!(planned > generated / 2, "only {planned} of {cases} fresh draws were planned by the kernel");
            prop_assert!(base > 0 && hash > 0 && w35 > 0 && step8 > 0, "an arm drew nothing the kernel planned: {base}, {hash}, {w35}, {step8}");
            prop_assert!(whatifs > 0, "no what-if was asked in {cases} fresh draws");
        }
        eprintln!(
            "planner_invariants kernel draw census: {cases} fresh draws, {refused} the binary cannot hold, {planned} planned by \
             the kernel (base {base}, hash {hash}, w35 {w35}, step-8 {step8}); what-ifs asked and answered {whatifs}; days \
             with no candidate {empty}"
        );
    }
}

/// What [`log_a_break_into_the_running_block`] drew: whether a break was logged inside the running
/// block (`drew`), whether nothing else stops the block's clock so the host's reading and the
/// replay's are ONE (`one_reading`), whether the log holds a timer mark from the block's start on
/// (`marked`, P84), whether an interruption ended the break (`d90`, D90), and whether a
/// clock-STARTING mark is stamped strictly inside the break (`starting_inside`, README gap 4501).
#[derive(Clone, Copy, Debug, Default)]
struct BreakDraw {
    drew: bool,
    one_reading: bool,
    marked: bool,
    d90: bool,
    starting_inside: bool,
}

/// **A break LOGGED inside the running block, as the binary writes it** — the world the D87 arm
/// plans and the one-reading arm reads (README gap 4491, the W-43 repair: lifted out of the fork
/// region, because the assertion that the host's worked minutes and the replay's are one reads no
/// fork and must outlive R3).  `logged` places the break, `interrupted` ends it with an
/// interruption (D90), `walled` puts D61's wall pause before it and its unpause inside it.
fn log_a_break_into_the_running_block(
    w: &mut World,
    logged: Option<(u32, u32)>,
    interrupted: Option<(u32, u32)>,
    walled: Option<(u32, u32)>,
) -> BreakDraw {
    let tz = w.cfg.tz;
    // A break LOGGED inside the running block, begun `into` minutes after it started and
    // ended at or before `now` — written as `tm break` writes it, at its end and stamped at
    // its start, so the kernel and the fork replay the same bytes.
    let mut drew = false;
    let mut one_reading = false;
    let mut marked = false;
    // A clock-STARTING mark stamped strictly inside the logged break (README gap 4501).
    let mut starting_inside = false;
    let mut d90 = false;
    if let (Some((into, len)), Some(a)) = (logged, w.state.active.clone()) {
        let started = local_dt(tz, date(), a.started);
        let t = started + Duration::minutes(i64::from(into));
        let end = t + Duration::minutes(i64::from(len));
        if end <= w.now {
            // **The break line goes where `tm break` writes it** — at the break's END, stamped
            // at its start (the W-42 repair, README gap 4332).  It was appended LAST, so every
            // pause, unpause, interrupt and resume the log held after the break preceded it in
            // the file, a world no binary writes; and the one-reading assertion below then had
            // to skip every world with such a mark, which is exactly the world W-42's reuse
            // critic drove the host and the kernel apart in (a break inside a typed pause).
            let at = |l: &str| {
                serde_json::from_str::<Value>(l).ok().and_then(|e| {
                    e["t"].as_str().and_then(|s| DateTime::parse_from_rfc3339(s).ok())
                })
            };
            let stamp = |m: DateTime<Tz>| m.format("%Y-%m-%dT%H:%M:%S%:z").to_string();
            // **D90 (README gaps 4340 and 4390, the W-43 land): an interruption taken during
            // the break ENDS it.**  `tm interrupt` ends a running break first, as `tm break`'s
            // ending arm does (`day::end_break`, P86): the break's line carries the minutes up
            // to the interruption and is written at that instant, before the `interrupt` line,
            // and `tm resume` writes its `resume` later.  So gap 4340's world — a timer mark
            // inside a logged break, which this arm used to leave out by name — is drawn as the
            // binary now writes it, on a stretch of the log nothing else is stamped in, and held
            // to the one reading below like every other logged break.
            let d90_world = interrupted
                .map(|(k, lost)| (1 + (k - 1) % (len - 1), lost))
                .map(|(k, lost)| {
                    let m = t + Duration::minutes(i64::from(k));
                    (m, m + Duration::minutes(i64::from(lost)), k, lost)
                })
                .filter(|&(_, r, _, _)| {
                    r <= w.now
                        && w.log.lines().all(|l| {
                            at(l).is_none_or(|x| x < t.fixed_offset() || x > r.fixed_offset())
                        })
                });
            // **A clock-STARTING mark inside the break, as the binary writes one (README gap
            // 4501, the W-43 repair).**  D61's wall: a meeting that began `b` minutes before the
            // break paused the block there, and ended `i` minutes into the break — the
            // housekeeping of the verb that ended the break logged its `unpause` at the wall's
            // end, INSIDE the break, before the break's own line (`WallTimer.unpauseIfDone`
            // withholds nothing for a running break, and needs to withhold nothing: the
            // kernel's clock runs from the unpause until the break's line moves it to the
            // break's end, `Replay.brkFx`, and the host's union nets the same span).  Drawn
            // only where the block's timer was the user's untouched since its start, on a
            // stretch of the log nothing else is stamped in, and held to the one reading below.
            let walled_world = if d90_world.is_none() && len >= 2 && !a.paused && w.state.interrupt.is_none() {
                walled
                    .map(|(b, i)| {
                        (
                            t - Duration::minutes(i64::from(b)),
                            t + Duration::minutes(i64::from(1 + (i - 1) % (len - 1))),
                        )
                    })
                    .filter(|&(p, _)| {
                        p > started
                            && w.log.lines().filter_map(|l| serde_json::from_str::<Value>(l).ok()).all(|e| {
                                !matches!(e["ev"].as_str(), Some("pause" | "unpause" | "interrupt" | "resume"))
                                    || e["t"].as_str().and_then(|s| DateTime::parse_from_rfc3339(s).ok()).is_some_and(|m| m < started.fixed_offset())
                            })
                            && w.log.lines().all(|l| {
                                at(l).is_none_or(|x| x < p.fixed_offset() || x > end.fixed_offset())
                            })
                    })
            } else {
                None
            };
            let (line, end) = match d90_world {
                Some((m, r, k, lost)) => (
                    format!(
                        "{{\"t\":\"{}\",\"ev\":\"break\",\"planned_min\":{len},\"actual_min\":{k}}}\n\
                         {{\"t\":\"{}\",\"ev\":\"interrupt\",\"id\":\"{}\"}}\n\
                         {{\"t\":\"{}\",\"ev\":\"resume\",\"lost_min\":{lost},\"dropped\":[]}}\n",
                        stamp(t),
                        stamp(m),
                        a.id,
                        stamp(r)
                    ),
                    m,
                ),
                None => (
                    walled_world
                        .map(|(p, u)| {
                            format!(
                                "{{\"t\":\"{}\",\"ev\":\"pause\",\"id\":\"{}\"}}\n\
                                 {{\"t\":\"{}\",\"ev\":\"unpause\",\"id\":\"{}\"}}\n",
                                stamp(p),
                                a.id,
                                stamp(u),
                                a.id
                            )
                        })
                        .unwrap_or_default()
                        + &format!(
                            "{{\"t\":\"{}\",\"ev\":\"break\",\"planned_min\":{len},\"actual_min\":{len}}}\n",
                            stamp(t)
                        ),
                    end,
                ),
            };
            d90 = d90_world.is_some();
            let mut before = String::new();
            let mut after = String::new();
            for l in w.log.split_inclusive('\n') {
                // A line stamped at the break's end follows it: `tm break` ended the break
                // first and the verb at that instant came after.
                if after.is_empty() && at(l).is_none_or(|m| m < end.fixed_offset()) {
                    before.push_str(l);
                } else {
                    after.push_str(l);
                }
            }
            w.log = before + &line + &after;
            // D87's one reading, since P84 (README gap 4332), holds with every pause, unpause,
            // interrupt and resume the log holds — the host's idle minutes are the union of
            // its spans and a break leaves the timer as it found it, as the kernel's
            // `Replay.brkFx` reads it.  Three worlds are left out, each by name: an
            // interruption still OPEN in the cache (the generator may hold one the log does
            // not); an interruption RESUMED while a typed `tm pause` held the block — the
            // kernel keeps such a block paused (`close_pause_does_not_clear_paused`) where `tm
            // resume` runs it, README gap 3521's divergence, which is not a break's; and a
            // clock-STOPPING mark (a `pause` or an `interrupt`) stamped strictly INSIDE the
            // break — the kernel steps the break at its line, after that mark, so it would
            // credit the break's head before the mark to the block where the host's union nets
            // it: README gaps 4340 and 4501, which the binary no longer writes — since D90 `tm
            // interrupt` ENDS the break first (that world is drawn above, the D90 world), since
            // the W-43 repair a typed `tm pause` inside a running break is REFUSED (P89; it
            // logged `unpause` then `pause` there until then, which this sentence said it did
            // not), and D61 writes no wall pause while a break runs (`WallTimer.step`'s
            // `stoppedAt`).  A clock-STARTING mark inside the break (an `unpause` or a `resume`)
            // is NOT left out: the kernel's clock runs from it until the break's line moves it
            // to the break's end (`Replay.brkFx`), the host's union nets the same span, and the
            // binary writes one — D61's unpause at a wall's end while a break runs.
            let mut held = false;
            let mut resumed_held = false;
            let mut inside = false;
            for e in w.log.lines().filter_map(|l| serde_json::from_str::<Value>(l).ok()) {
                let m = e["t"].as_str().and_then(|s| DateTime::parse_from_rfc3339(s).ok());
                if !m.is_some_and(|m| m >= started.fixed_offset()) {
                    continue;
                }
                if matches!(e["ev"].as_str(), Some("pause" | "interrupt"))
                    && m.is_some_and(|m| t.fixed_offset() < m && m < end.fixed_offset())
                {
                    inside = true;
                }
                if matches!(e["ev"].as_str(), Some("unpause" | "resume"))
                    && m.is_some_and(|m| t.fixed_offset() < m && m < end.fixed_offset())
                {
                    starting_inside = true;
                }
                match e["ev"].as_str() {
                    Some("pause") if e["id"].as_str() == Some(a.id.as_str()) => held = true,
                    Some("unpause") if e["id"].as_str() == Some(a.id.as_str()) => held = false,
                    Some("resume") if held => resumed_held = true,
                    _ => {}
                }
            }
            one_reading = !resumed_held && !inside && w.state.interrupt.is_none();
            marked = w.log.lines().filter_map(|l| serde_json::from_str::<Value>(l).ok()).any(|e| {
                matches!(e["ev"].as_str(), Some("pause" | "unpause" | "interrupt" | "resume"))
                    && e["t"].as_str().and_then(|s| DateTime::parse_from_rfc3339(s).ok()).is_some_and(|m| m >= started.fixed_offset())
            });
            w.replay = chokepoint::replay_of_text(&w.log, tz);
            drew = true;
        }
    }
    BreakDraw { drew, one_reading, marked, d90, starting_inside }
}

/// **A case every one of whose days admits the clock-starting world** (README gap 4509, W-44 track
/// C): the case with nothing else stamped over its running block — no meeting (the walls go, and the
/// late day's evening wall with them, which would pause the block at 15:00), no interruption, no
/// energy report — planned at least ninety minutes after the arrival with one block done, and a
/// block running since a minute after that block: `active_block` starts it at the arrival plus
/// 56 minutes, so it has run 34, 124 or 244 minutes at `now`.  Everything else is the case's
/// own draw (its items, routines, home or lounge, estimate).  A day the binary writes: a block
/// started after one done block, on a day with no calendar.
fn clock_starting_case(case: &Case) -> Case {
    let mut c = case.clone();
    c.walls.clear();
    c.late = false;
    c.interrupt = None;
    c.report = None;
    c.now_idx = 1 + c.now_idx % 3;
    c.done_blocks = 1;
    let (idx, _, est) = c.active.unwrap_or((0, 0, 60));
    c.active = Some((idx, 24 * 60, est));
    c
}

/// **The replay's worked minutes of the running block** — the log's own open block when it is this
/// item's (`OpenBlock::worked_min_at`), `None` otherwise: the reading the kernel's replay gives, which
/// the one-reading arm holds to the host's.
fn replay_worked(w: &World, st: &RuntimeState) -> Option<u32> {
    let a = st.active.as_ref()?;
    w.replay
        .open_block
        .as_ref()
        .filter(|b| b.id == a.id.as_str())
        .map(|b| chokepoint::open_worked_min_at(b, w.now.fixed_offset()))
}

/// **The host's worked minutes of the running block** — `day::worked_min`'s reading, the very call
/// `tm done` makes: `Replay::running_worked_min`, from the INSTANT of the log's own `start` line, the
/// running break included (D75, parity P65). `None` where the log holds no open block for the running
/// block, as `day::worked_min` answers then (no draw here builds one: measured at W-41, 132 of 132
/// calls a number, each the old reading's). Until W-41 this read `Replay::active_worked_min` from the
/// cache's `HH:MM` on `date()` (README gaps 3825, 3941 and 4042).
fn w36_host_worked(w: &World, st: &RuntimeState) -> Option<u32> {
    // The binary's one reading (`planwire::running_worked_min`, README gap 4875): the running
    // break where every host site places it, its LOGGED start since D105 (track T's P73
    // composed at W-41's land step, README gap 4121).
    planwire::running_worked_min(st, &w.replay, w.cfg.tz, w.now, w.now.date_naive(), w.now.fixed_offset())
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256),
        max_shrink_iters: 2_000,
        ..ProptestConfig::default()
    })]

    /// **A break logged inside the running block is read ONE way by the host and the replay** — the
    /// owner's D87 (parity P81), with P84's union, D90's interruption that ends the break, and since
    /// the W-43 repair (README gap 4501) D61's wall unpause stamped inside the break.  `tm stop`'s
    /// and `tm done`'s minutes are the host's (`Replay::running_worked_min`, the union of idle
    /// spans); `tm review`'s, the heat grid's and the planner's are the replay's (`OpenBlock::
    /// worked_min_at`); on every generated day where nothing else stops the block's clock they are
    /// one number.  **Outside the fork region** (README gap 4491): this was the D87 arm's own
    /// assertion, inside a region R3 deletes though it compares no fork; lifted here with its census
    /// and floors, it outlives the deletion.  **Since W-44 track C (README gap 4509) the clock-starting
    /// member is PLACED on every case** (`clock_starting_case`) as well as drawn, so its count has a
    /// floor no run can miss.
    #[test]
    fn the_host_and_the_replay_read_a_logged_break_one_way(
        case in case_strategy(),
        logged in prop::option::of((0u32..=60, 5u32..=30)),
        interrupted in prop::option::weighted(0.5, (1u32..=29, 1u32..=20)),
        walled in prop::option::weighted(0.5, (1u32..=20, 1u32..=29)),
        placed in (1u32..=10, 1u32..=10, 2u32..=13, 1u32..=12),
    ) {
        /// `[cases, logged-break days held to one reading, of them with a timer mark from the block's
        /// start on (P84), of them whose break an interruption ended (D90), of them with a
        /// clock-starting mark inside the break (gap 4501), logged-break days drawn, clock-starting
        /// days PLACED on every case and held to one reading (gap 4509)]`.
        static ONE_READING: Mutex<[u64; 7]> = Mutex::new([0; 7]);
        let mut w = build(&case);
        let draw = log_a_break_into_the_running_block(&mut w, logged, interrupted, walled);
        let host = w36_host_worked(&w, &w.state);
        let held = draw.drew && draw.one_reading && host.is_some();
        if held {
            prop_assert_eq!(host, replay_worked(&w, &w.state), "D87: a break logged inside the running block left the host's reading and the log's apart (P81); now {}, the log:\n{}", w.now, w.log);
        }
        // **The clock-starting world on EVERY case** (README gap 4509, W-44 track C).  The draw above
        // reaches D61's wall unpause inside a break only where the case's own log leaves the block's
        // timer untouched and a stretch of it quiet — 2, 0, 3, 2, 2 and 3 days over six runs of the
        // W-43 repair, so a floor on that count would fail a run in six.  So the world is also PLACED,
        // through the same builder, on a case built to admit it (`clock_starting_case`): the wall's
        // pause `b` minutes before a break begun `b + into` minutes into the block, the break `len`
        // minutes long, its unpause inside it — 1 ≤ b ≤ 10, 2 ≤ b + into ≤ 20, 2 ≤ len ≤ 13, which
        // fits the shortest such block (34 minutes) — and held to the one reading.  THIS IS THE FLOOR,
        // and it is per case: a case the world is not placed on fails here by name (and shrinks), so
        // the count is the case count and a run cannot hold the claim on no day.  A count-floor at the
        // end beside it could fail on no input — a disguised gap (AGENTS §9.2) — so there is none.
        let (b, into, len, i) = placed;
        let mut w2 = build(&clock_starting_case(&case));
        let placed_draw = log_a_break_into_the_running_block(&mut w2, Some((b + into, len)), None, Some((b, i)));
        prop_assert!(
            placed_draw.drew && placed_draw.one_reading && placed_draw.starting_inside,
            "gap 4509: the clock-starting world was not drawn on a case built to admit it ({:?}); now {}, the log:\n{}",
            placed_draw, w2.now, w2.log
        );
        let host2 = w36_host_worked(&w2, &w2.state);
        prop_assert!(host2.is_some(), "gap 4509: the host reads no running block on the placed world; the log:\n{}", w2.log);
        prop_assert_eq!(host2, replay_worked(&w2, &w2.state), "D61's unpause inside a running break: the host's reading and the log's apart; now {}, the log:\n{}", w2.now, w2.log);
        let r = {
            let mut r = ONE_READING.lock().expect("census");
            r[0] += 1;
            r[1] += u64::from(held);
            r[2] += u64::from(held && draw.marked);
            r[3] += u64::from(held && draw.d90);
            r[4] += u64::from(held && draw.starting_inside);
            r[5] += u64::from(draw.drew);
            r[6] += 1;
            *r
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        if r[0] >= generated {
            // **Floors** (AGENTS §9.2), moved here with the assertion: a reading compared on no day
            // compares nothing.  D90's is a probability (README gap 4492): red is a finding about the
            // draw, re-run and reported, never reverted (D46).
            prop_assert!(r[5] > 0, "no break was logged inside a running block in {} cases", r[0]);
            prop_assert!(r[1] > 0, "no logged-break day held the two readings equal (D87's one reading)");
            prop_assert!(r[3] > 0, "no logged-break day whose break an interruption ended was held to one reading (D90)");
        }
        eprintln!(
            "planner_invariants one-reading census (D87): {} cases, {} logged-break days drawn, {} held to one reading \
             ({} with a timer mark, P84; {} whose break an interruption ended, D90; {} with a clock-starting mark inside \
             the break, gap 4501); {} clock-starting days placed and held (gap 4509)",
            r[0], r[5], r[1], r[2], r[3], r[4], r[6]
        );
    }
}




