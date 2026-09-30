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
//! * **Inside the one `BEGIN THE FORK PLANNER` … `END THE FORK PLANNER` region —
//!   every arm that plans with the fork**, which R3 deletes whole (README gap
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

use std::collections::BTreeSet;
use std::sync::Mutex;

use chrono::{DateTime, Duration, NaiveTime, Timelike};
use chrono_tz::Tz;
use proptest::prelude::*;
use serde_json::{json, Value};
use tm_core::capacity::{self, local_dt};
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
    let remaining = capacity::remaining_budget(
        w.state.budget.unwrap_or(6),
        w.replay.blocks_done(date()),
    );
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


/// **A configured double as the exact decimal pair the wire carries** (D17).
///
/// The kernel holds no `Float`, so every `[energy]` and `[expected]` decimal
/// crosses as `num/den`. This is `kernel_capacity::written_pair` restricted to
/// the shortest round-trip text of a `f64` — the shipped reader lives in the
/// `tm` binary and an integration test cannot link it, which is README gap
/// 2006: one concept, two readings, and the move belongs with R3's deletion.
fn dec(x: f64) -> Value {
    let t = format!("{x}");
    let (int, frac) = t.split_once('.').unwrap_or((t.as_str(), ""));
    json!({"num": format!("{int}{frac}"), "den": format!("1{}", "0".repeat(frac.len()))})
}

/// The same pair as JSON naturals, for the sections whose reader is `natAt`
/// rather than a digit string (the prior's step bounds).
fn decn(x: f64) -> Value {
    let v = dec(x);
    json!({"num": v["num"].as_str().unwrap_or("0").parse::<u64>().unwrap_or(0),
           "den": v["den"].as_str().unwrap_or("1").parse::<u64>().unwrap_or(1)})
}

/// A `NaiveTime` as the wire's `HH:MM`.
fn hhmm(t: NaiveTime) -> String {
    format!("{:02}:{:02}", t.hour(), t.minute())
}

impl World {
    /// **`capacity.candidates.items`, the fork's own list** (W-29 repair,
    /// README gap 2005 — it closes gap 1905's first half).
    ///
    /// Gap 1905 said no honest encoder for `Look.Cand` existed on this side.
    /// One does, and it ships: `tm/src/cli/kernel_capacity.rs`'s `send_order`,
    /// `cand_json` and `plan_json` are what the `tm` binary sends on every
    /// `tm plan`. **They cannot be linked from here** — `tm` is a `[[bin]]`
    /// with no library target, so an integration test cannot `use` them — so
    /// this is that encoder's second spelling and README gap **2006** records
    /// the move (into `tm-core`, or out with R3) rather than pretending it is
    /// not one. Everything it reads is the FORK's: `collect_candidates` builds
    /// the records, `Tree::root`/`priority` the written `!k`, and the order is
    /// the fork's own `(effective_due, own_order, index)`.
    ///
    /// `yesterday` is `None` on every record because `RuntimeState::default()`
    /// leaves `priorities_yesterday` empty and the fork reads exactly that map
    /// (`planner.rs:988`) — the two sides agree by construction, not by luck.
    fn candidate_items(&self) -> Vec<Value> {
        let cands = self.candidates();
        // `kernel_capacity::send_order`: the fork's `priority::compute` sort, so
        // the kernel's stable sort by due date serves a date's deadlines in the
        // fork's order.  One spelling of it here since W-36: `send_order`, which
        // D60's comparand reads too (the kernel's request position).
        let order = planreq::send_order(&cands);
        order
            .iter()
            .map(|&i| {
                let c = &cands[i];
                let root_prio = self.tree.get(&self.tree.root(&c.id)).and_then(|r| r.priority);
                let floor = c.floor.as_ref().map(|r| {
                    json!({"left": r.amount.as_minutes().saturating_sub(c.floor_done_min),
                           "until": priority::period_range(r.per, date()).1.to_string()})
                });
                json!({
                    "id": c.id.as_str(), "ci": c.ci, "rootPrio": root_prio,
                    "remaining": c.remaining_min,
                    "due": c.effective_due.map(|d| d.date_naive().to_string()),
                    "window": c.window.is_some(), "wall": c.is_wall,
                    "optional": c.is_optional, "overdue": c.overdue,
                    "mandatory": c.mandatory, "hot": c.hot,
                    "yesterday": Option::<u8>::None,
                    "floor": floor,
                    // §8.2 step 5's nine (`Look.PlanFacts`), as `plan_json` sends them.
                    "plan": {"plannedMin": c.planned_min,
                             "multiplier": decn(c.multiplier),
                             "loc": c.loc.as_str(), "splittable": c.splittable,
                             "cap": c.cap.as_ref().map(|r| json!({
                                 "capMin": r.amount.as_minutes(), "doneMin": c.cap_done_min})),
                             "state": c.state.glyph().to_string(),
                             "blockedBy": c.blocked_by.iter().map(ToString::to_string)
                                 .collect::<Vec<String>>(),
                             "wallToday": c.wall_today}})
            })
            .collect()
    }

    /// **§8.2 step 2's instances** — `tm_core::planwire::routine_instances`, the collector the
    /// binary's encoder uses, over this world's candidates and tree (W-31 put the fork's
    /// `collect_routines` here as a SECOND spelling, README gap 2221; the W-35 repair made it a
    /// call, README gap 2922).
    fn routine_items(&self) -> Vec<planwire::RoutineInst> {
        planwire::routine_instances(&self.candidates(), &self.tree, self.now, date(), self.cfg.tz)
    }

    /// **The whole request the kernel plans from**: the generated documents,
    /// the generated log through D24's seam, the capacity section over
    /// `Config::default()`, and the `planner` section §9's runtime rows live in.
    ///
    /// The lookahead's own inputs — `pLounge`, `arrival`, `prior`, `homeMaxCi`,
    /// `posterior`, `sleep`, `priority` and `days` — are the shipped defaults
    /// spelled here rather than read off `Config`, and **none of them reaches
    /// what this arm compares**: §8.1's window is `[day]`, the stored window and
    /// the walls, and the walls are the documents'. They are here because the
    /// capacity section must decode for the planner section to be read at all.
    fn plan_request(&self) -> Value {
        let tz = self.cfg.tz;
        let week = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
        // **READ OFF `Config`, NEVER SPELLED** (W-29 repair, README gap 2005).
        // These three tables were hand-written literals said to be "the shipped
        // defaults"; they were not. `Config::default()` puts the lounge prior at
        // `0-1:4, 1-5:5, 5-8:4, 8-10:3, 10+:2` and the home prior at
        // `0-1:3, 1-4:4, 4-8:3, 8+:2`, `p_lounge` at 0.9/0.8/0.5/0.4 and the
        // expected arrival at 07:00 (10:00 at the weekend) — the literals said
        // `5/3/1`, `3/2`, 1.0 everywhere and `state.arrival` (00:00 when unset).
        // Nothing before this step read them: §8.1's window is `[day]` and the
        // walls, so the window and budget halves of this arm agreed anyway, and
        // §8.2 step 5's ENERGY FILTER — the one reader of the prior — was never
        // compared. DRIVEN: with the literals 2 of 19 routine-free cases cut the
        // day into different assigned slots; read off `Config`, 26 of 26 agree.
        let wds = [chrono::Weekday::Mon, chrono::Weekday::Tue, chrono::Weekday::Wed,
                   chrono::Weekday::Thu, chrono::Weekday::Fri, chrono::Weekday::Sat,
                   chrono::Weekday::Sun];
        let p_config: serde_json::Map<String, Value> = week
            .iter()
            .zip(wds)
            .map(|(k, wd)| ((*k).to_string(), dec(*self.cfg.expected.p_lounge.get(wd))))
            .collect();
        let arrival_tbl: serde_json::Map<String, Value> = week
            .iter()
            .zip(wds)
            .map(|(k, wd)| ((*k).to_string(), json!(hhmm(*self.cfg.expected.arrival.get(wd)))))
            .collect();
        let curve = |loc: &str| -> Value {
            Value::Array(
                self.cfg.energy.prior[loc]
                    .0
                    .iter()
                    .map(|s| json!({"from": decn(s.from), "to": s.to.map(decn), "level": s.level}))
                    .collect(),
            )
        };
        let d = &self.cfg.day;
        let capacity = json!({
            // **`wake` CROSSES** (W-30). `kernel_capacity::request` sends
            // `{"sec", "ns"}` when `state.wake` is set and `"log"` otherwise; this
            // arm sent NEITHER, so `Boundary.readWake` answered `.absent` and the
            // kernel measured §8.5's `hsw` from the weekday's expected arrival
            // while the fork measured it from the day's own wake. Every slot's
            // energy level rides on that.
            "wake": match self.state.wake {
                Some(t) => json!({"sec": t.num_seconds_from_midnight(), "ns": t.nanosecond()}),
                None => json!("log"),
            },
            "pLounge": {"config": p_config},
            "arrival": {"config": arrival_tbl},
            "prior": {"lounge": curve("lounge"), "home": curve("home")},
            "homeMaxCi": self.cfg.location.home_max_ci,
            "day": {"breakMin": d.break_min, "breakAfterBlocks": d.break_after_blocks,
                    "minLastBlockMin": d.min_last_block_min,
                    "windowHours": {"num": 8, "den": 1}, "windowCap": hhmm(d.window_cap),
                    "budgetRatio": {"num": 3, "den": 4},
                    "windDown": hhmm(d.wind_down), "bed": hhmm(d.bed)},
            "priority": {"bins": [{"num": 1, "den": 2}, {"num": 1, "den": 4},
                                  {"num": 1, "den": 10}],
                         "safety": {"num": 13, "den": 10}, "defaultPriority": 3,
                         "batchMaxMin": 20},
            "days": priority::lookahead_days(&self.candidates(), date()),
            "at": self.now.to_rfc3339(),
            "state": {
                "date": self.state.date.map(|x| x.to_string()),
                "window": self.state.window.map(|(f, t)| json!({"from": hhmm(f), "to": hhmm(t)})),
                "budget": self.state.budget,
                "arrival": self.state.arrival.map(hhmm),
                "loc": self.state.loc,
                "allowHome": false},
            "posterior": {"fullHours": {"num": 3, "den": 1}, "zeroHours": {"num": 6, "den": 1}},
            "sleep": {"shiftModel": null, "shiftConfig": {"neg": false, "num": 1, "den": 1},
                      "underHours": {"num": 7, "den": 1}},
            "candidates": {"hysteresis": self.cfg.priority.hysteresis,
                           "items": self.candidate_items()},
        });
        // **THE `planner` SECTION IS THE BINARY'S OWN ENCODER** (W-35 repair, README gap
        // 2922): `tm_core::planwire::planner_json` over `routine_instances`, the codec R3 swaps
        // in.  Until the repair this arm spelled `state.active`, `state.interrupt` and the
        // routines by hand (and the W-35 arm `state.break`), so the 279-day generated comparison
        // never ran the encoder R3 will ship — and the two spellings differed on an interruption
        // with no start, which the hand spelling dropped and `state_json` sends as `null`.
        json!({
            "docs": self.docs_json(),
            "now": DAY,
            "blockMin": self.cfg.block_min(),
            "tz": rowwire::tz_table::wire_for(None, tz),
            "log": {"ckpt": null, "from": 1,
                    "lines": self.log.lines().collect::<Vec<_>>(),
                    "terminated": true, "reseal": null,
                    "want": {"facts": true, "headersFrom": null, "render": []},
                    "sealed": null},
            "capacity": capacity,
            "planner": planwire::planner_json(
                &self.state,
                self.now,
                tz,
                &self.routine_items(),
                None,
            ),
        })
    }
}

/// The kernel's own day for a request, or the refusal it answered.
///
/// **The §8.4 answer travels with it under `__grants`** (W-30): one call answers `plan` and
/// `lookahead` together, and the lookahead's per-candidate grants are §7's WHOLE answer — the
/// ten fields `grant_fields` compares and `kernel_prios` reads back. A leading `__` is not a
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
    let pw = planreq::World { docs: &w.docs, log: &w.log, tree: &w.tree, cfg: &w.cfg, state: &w.state, now: w.now, cands: &cvec };
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
#[test]
fn the_reversed_day_is_served_by_due_date() {
    let w = build(&reversed_day());
    let plan = kernel_plan(&w.plan_request()).expect("the kernel plans the reversed day");
    let ids: Vec<String> = w.candidates().iter().map(|c| c.id.to_string()).collect();
    assert_eq!(ids.len(), 2, "two candidates: {ids:?}");
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
/// compared, what-ifs compared, P45 days, P46, P47, P51, P52, P55, P56 lines, oracle requests,
/// break days README gap 3480's declared class explained]`.
static ORACLE_CENSUS: Mutex<[u64; 13]> = Mutex::new([0; 13]);

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
    /// **ONE DECLARED CLASS, README gap 3480's, and it is exact.** On a running-break day the
    /// comparand plans the fork after the break with the break LOGGED once it has run
    /// `break_min`, which resets the fork's cut counter wherever the break ends; the kernel
    /// reads the running break as a rest that resets it only where a free stretch begins
    /// (`Look.restfulEnd`) — two readings of one span, an open question P45's owner has to
    /// decide. The frozen lines hold only break days where the two agree; fresh draws reach the
    /// others (found by this arm's first run in W-39's R3 simulation, seed
    /// `96e7339b0c1745683b47728b`, `break/home`). So a difference AFTER the running break is
    /// explained only when the kernel's rows from there are, row for row, the fork's own
    /// planned with the break UNLOGGED (`forkplan::p45_rows`) — the other reading, asked of the
    /// fork itself — and counted; any other difference fails.
    #[test]
    #[ignore]
    fn the_kernel_plans_every_fresh_draw_as_the_forks_oracle_plans_it(bytes in any::<[u8; 12]>()) {
        let Some(oracle) = the_oracle() else { return Ok(()) };
        let (seed, draw, world, holds) = fresh_draw(&bytes);
        let mut c = [0u64; 13];
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
            let (after_break, mut findings): (Vec<String>, Vec<String>) =
                forkclass::compare_line(&line, &mut t).into_iter().partition(|f| f.contains("after the running break (P45"));
            if !after_break.is_empty() {
                let explained = forkplan::gap_3480_explains(&b, &prios, oracle)
                    .map_err(|e| TestCaseError::fail(format!("seed {seed}: {e}")))?;
                if explained {
                    c[12] = 1;
                } else {
                    findings.extend(after_break);
                }
            }
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
        let [cases, refused, compared, whatifs, p45, p46, p47, p51, p52, p55, p56, requests, gap3480] = {
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
             P47 {p47}, P51 {p51}, P52 {p52}, P55 {p55}, P56 {p56}; break days README gap 3480's declared class explained \
             {gap3480}"
        );
    }
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gaps 3084, 3080, 2722)
//
// **Everything below reaches the fork's planner, and R3 deletes it whole** (W-37 track H,
// README gap 3084). Until W-37 these arms sat outside any region — 34 code lines naming
// `planner::` — so R3 could not delete them mechanically and the region guard carried a dated
// exemption for this file. Each is kept here rather than deleted because it compares the kernel
// with the LIVE fork on every generated case, which the frozen comparand keyed by class
// (`planner_classes.rs`) does on its 45 lines: what each arm compares that the frozen lines
// cover by value, and what they do not, is README's W-37 track H table — the part they do not
// cover is lost at R3 and is named there.
use std::collections::BTreeMap;

use chrono::NaiveDate;
use tm_core::capacity::{Exact, CAP_DEN};
use tm_core::planner::{self, PlanInput};
use tm_core::priority::PrioClass;

/// **The fork oracle IS the in-tree fork, on every fresh draw** (W-39, the owner's D72; README
/// gap 3533) — while both exist, `tm-oracle plan` (fork 4748911 with `09d38fa`'s ranking seam
/// grafted, `plan-seam.patch`) and the in-tree fork answer every fresh draw alike: the raw day
/// both draw (the shipped ask and the comparand's, with D60's key), fork 4748911's drawing, the
/// §7.4 order, and every answer `forkplan::comparand_answers` builds over each. So the oracle arm
/// above, which R3 leaves standing, compares the kernel with the planner the shipped binary ran
/// and not with a copy that drifted — and P56's rule applied by its property on the oracle's
/// drawing (`forkplan::p56_cut`) is the in-tree fork's cut, measured. Deleted with the region.
static ORACLE_CROSS: Mutex<[u64; 4]> = Mutex::new([0; 4]);

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256),
        max_shrink_iters: 16,
        ..ProptestConfig::default()
    })]

    #[test]
    #[ignore]
    fn the_forks_oracle_answers_as_the_in_tree_fork_on_every_fresh_draw(bytes in any::<[u8; 12]>()) {
        let Some(oracle) = the_oracle() else { return Ok(()) };
        let (seed, _draw, world, holds) = fresh_draw(&bytes);
        let b = forkclass::Built::of(world);
        let prios = forkclass::kernel_answer_with_grants(&b)
            .map_err(|e| TestCaseError::fail(format!("seed {seed}: the kernel did not plan the day: {e}")))?
            .1;
        let mut cut = 0u64;
        for d60 in [false, true] {
            let ask = forkplan::ForkAsk { state: &b.world.state, now: b.world.now, d60, prios: &prios, extend: None, log_line: None };
            let i = forkplan::ForkPlan::plan(&forkplan::InTree, &b, &ask).map_err(TestCaseError::fail)?;
            let o = forkplan::ForkPlan::plan(oracle, &b, &ask)
                .map_err(|e| TestCaseError::fail(format!("seed {seed}: the fork oracle did not answer: {e}")))?;
            for (what, x, y) in [("fork 4748911's drawing", &i.fork_day, &o.fork_day), ("the shipped fork's day", &i.day, &o.day)] {
                if let Some(d) = forkplan::first_difference("day", x, y) {
                    prop_assert!(false, "seed {seed} (D60's key {d60}): {what} differs, in-tree against the oracle: {d}");
                }
            }
            prop_assert_eq!(&i.ranked, &o.ranked, "seed {}: the fork's §7.4 order differs", seed);
            cut += u64::from(i.day != i.fork_day);
        }
        let a = forkplan::comparand_answers(&b, &prios, &forkplan::InTree).map_err(TestCaseError::fail)?;
        let z = forkplan::comparand_answers(&b, &prios, oracle)
            .map_err(|e| TestCaseError::fail(format!("seed {seed}: the fork oracle did not answer: {e}")))?;
        for key in forkclass::ANSWERS {
            if let Some(d) = forkplan::first_difference(key, &a[key], &z[key]) {
                prop_assert!(false, "seed {seed}: the comparand's `{key}` differs, in-tree against the oracle: {d}");
            }
        }
        let [cases, held, cuts, whatifs] = {
            let mut g = ORACLE_CROSS.lock().expect("census");
            g[0] += 1;
            g[1] += u64::from(holds.is_ok());
            g[2] += cut;
            g[3] += u64::from(!a["whatif"].is_null());
            *g
        };
        eprintln!(
            "planner_invariants oracle cross-check: {cases} fresh draws ({held} the binary holds), in-tree and oracle \
             equal on every raw day, drawing, order and answer; P56's cut applied on {cuts} raw day(s); what-ifs {whatifs}"
        );
    }
}

/// **The fork's planner, with its OWN §7 pass** — the day
/// `day_plan_satisfies_every_invariant` asked §8.3's invariants of until W-37. No shipped
/// path plans it (D53: the binary hands the fork the kernel's ranking), so it stays beside the
/// kernel's only until R3; its §7.4 order is the fork's own `(root_order, own_order)`.
struct Fork;

impl Planner for Fork {
    fn day(&self, w: &World, state: &RuntimeState, now: DateTime<Tz>) -> Result<DayPlan, String> {
        Ok(planner::plan(&w.input(state, now)))
    }
    fn rank_view(&self, _w: &World, cands: &[Candidate], _prios: &[Prio]) -> Vec<Candidate> {
        cands.to_vec()
    }
    fn name(&self) -> &'static str {
        "the fork"
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 256, max_shrink_iters: 2_000, ..ProptestConfig::default() })]

    /// **§8.3's invariants of the fork's own-§7 day** — the arm as it stood until W-37,
    /// kept while the fork is here.
    #[test]
    fn day_plan_satisfies_every_invariant_on_the_fork(case in case_strategy()) {
        let w = build(&case);
        check_day_invariants(&Fork, &case, &w)?;
    }
}

impl World {
    fn input<'a>(&'a self, state: &'a RuntimeState, now: DateTime<Tz>) -> PlanInput<'a> {
        PlanInput::new(
            &self.tree,
            &self.replay,
            &self.cfg,
            &self.model,
            state,
            now,
        )
    }
}

/// `(rows compared, cases compared, note-hole firings, est-hole firings,
/// rows whose `parent` cell was NON-EMPTY)` — what
/// [`the_kernel_reads_every_day_the_fork_planned`] actually looked at.
///
/// **The fifth number is W-27's** and it is the one that makes the `parent`
/// comparison mean something. Until this run the generated corpus carried no
/// `@` token, so every row's `parent` cell was `""` on both sides and the
/// comparison could not fail whatever the kernel wrote; the arm is now asserted
/// to have seen the cell at a real value.
///
/// A proptest case body returns only a verdict, so the census is a side
/// channel — but it is read **inside the arm that fills it**, on every case,
/// and not by a separate `#[test]`. A separate test would race the arm in
/// cargo's default parallel run and pass by seeing nothing, which is the very
/// defect it exists to catch: "every cell of every row agreed" is a sentence a
/// fuzz comparing **no** rows also produces — AGENTS §9.2's "a check no input
/// can fail", which this campaign has met at five different levels.
static CENSUS: Mutex<[u64; 5]> = Mutex::new([0; 5]);

// ===========================================================================
// STEP R2 (stage 6 W-25): the generated days go through the KERNEL.
//
// §14.4's R2 says this file must exercise "the kernel's `dayPlan` through the
// FFI".  **When this arm was written at W-25 it could not**: `dayPlan` was not
// reachable through the FFI, because the `plan` REQUEST section carried the
// day's rows and not the planner's inputs, and `EmitWire.lean`'s own header
// assigned that section to step R3 (README gap **1431**, which priced what R3
// then needed, field by field).
//
// **THAT IS NO LONGER TRUE, AND THIS PARAGRAPH IS THE LAND STEP'S.**  D48 moved
// the wire into R2, W-27 landed its REQUEST half and W-28 its RESPONSE half, so
// `Planner.dayPlan` IS reachable through the FFI now and the section at the
// **THE KERNEL PLANS THE DAY** banner below exercises it.  This arm is kept
// because it is a *different* claim, not a superseded one: it sends the FORK's
// day in and checks the kernel's RENDERING of it, where the arm below asks the
// kernel to PLAN.  Read the two banners together; neither is the whole.
//
// What this arm covers, said plainly so the remainder is not mistaken for the
// whole: every day this file's generators produce — 40 random items, five routines, calendar walls, a random log, a
// running block, an open interruption, a late day — is handed to the kernel's
// `plan` section, and the kernel's nine cells for every row are compared
// against `emit::row_cells`'s.  Before W-25 that comparison existed on ONE
// hand-built fixture day (`tm/tests/kernel_row_cells.rs`); this makes it
// thousands of generated ones, and the two files share the encoder.
//
// It is NOT the tail-drop or stability half of R2: those are about a plan the
// kernel made.  The kernel DOES make one now (the banner below), but only §8.2
// steps 1 and 2 of it, so those two halves are still unclaimed — README gap
// **1670**, and the land step re-read this sentence rather than leaving it to
// read as though nothing had changed.
// ===========================================================================


proptest! {
    #![proptest_config(ProptestConfig {
        // Each case is an FFI call over a whole generated tree, so the count is
        // its own: `TM_PROPTEST_CASES` raises it and W-25's README block records
        // what it was run at (D46 — one run of a randomised test is a weak
        // claim).
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(64),
        max_shrink_iters: 2_000,
        ..ProptestConfig::default()
    })]

    /// **The kernel reads every day the fork planned, and writes the fork's
    /// cells for it.**
    ///
    /// Two claims, and the first is the one nothing else makes:
    ///
    /// 1. **No day the fork's planner produces is refused by the wire.** Every
    ///    `R10` bound the `plan` section carries — `Planner.maxCands` on the
    ///    segment list, `CapWire.maxCandId` on every id, `Look.maxPlanMinutes`
    ///    on `planned`, `Fin 6` on the energy, `maxBatch` on a batch — is a
    ///    number a real day could exceed, and a bound that is too tight refuses
    ///    a legitimate plan. `kernel_rows` returns the refusal instead of
    ///    panicking so this can be asserted rather than assumed.
    /// 2. **Cell for cell, row for row**, against `emit::row_cells`, with
    ///    [`CELL_HOLES`]'s two declared exceptions and no others. The kernel is
    ///    told no title, no `ci`, no estimate and no parent: those four come
    ///    from its own parse of the same generated bytes.
    #[test]
    fn the_kernel_reads_every_day_the_fork_planned(case in case_strategy()) {
        let w = build(&case);
        let day = planner::plan(&w.input(&w.state, w.now));
        let lean = match rowwire::kernel_rows(w.docs_json(), &day, &w.cfg) {
            Ok(rows) => rows,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the wire refused a day the fork planned: {head}");
                unreachable!()
            }
        };
        let fork = rowwire::fork_cells(&day, &w.tree, &w.cfg);
        prop_assert_eq!(
            lean.len(), fork.len(),
            "the kernel answered {} rows for {} segments (`Emit.rowsOf_length`'s wire half)",
            lean.len(), fork.len()
        );
        let mut seen = [0u64; 5];
        seen[0] = fork.len() as u64;
        seen[1] = 1;
        for (i, (f, l)) in fork.iter().zip(&lean).enumerate() {
            // **The `parent` cell, counted where it is not the default** (W-27).
            // Counted off the FORK's cell: the kernel's is the value under
            // test, and a census read off the value under test would report
            // whatever a broken kernel wrote.
            if !f.parent.is_empty() {
                seen[4] += 1;
            }
            for (cell, forked, kernelled) in rowwire::differences(f, l) {
                prop_assert!(
                    CELL_HOLES.contains(&cell),
                    "row {i}: the two readers disagree on an UNDECLARED cell {cell:?} \
                     — fork {forked:?}, kernel {kernelled:?}"
                );
                if cell == "note" {
                    seen[2] += 1;
                } else {
                    seen[3] += 1;
                }
            }
        }
        // **The fuzz compared something, asserted inside the fuzz.**
        //
        // A proptest arm runs its cases in sequence, so a cumulative claim here
        // is deterministic — where a separate `#[test]` reading the same census
        // would race the arm that fills it and pass by seeing nothing. "Every
        // cell agreed" is a sentence a fuzz comparing NO rows also produces
        // (AGENTS §9.2's "a check no input can fail"), and a declared hole that
        // has stopped firing is a claim that has changed (gaps 1101, 1102).
        let [rows, cases, notes, ests, parents] = {
            let mut c = CENSUS.lock().expect("census");
            for (a, b) in c.iter_mut().zip(seen) {
                *a += b;
            }
            *c
        };
        prop_assert!(rows >= 4 * cases, "only {rows} rows over {cases} cases");
        if cases >= 32 {
            prop_assert!(notes > 0, "the `note` hole has not fired in {cases} cases (gap 1102)");
            prop_assert!(ests > 0, "the `est` hole has not fired in {cases} cases (gap 1101)");
            // **The `parent` cell was compared at a real value** (W-27). Without
            // this the cell is in `differences`' nine and still asserts nothing:
            // `"" == ""` on every row of every case is the shape AGENTS §9.2
            // calls a check no input can fail, and an auditor's perturbation of
            // `Emit.parentCell` passed through it. A generator that stops
            // drawing parents now fails here instead of going quietly green.
            prop_assert!(
                parents > 0,
                "no row's `parent` cell was non-empty in {cases} cases — the `parent` \
                 comparison is vacuous (gap 1437's neighbour)"
            );
        }
        // **THE CENSUS IS PRINTED, so the README's figure can be RE-DERIVED.**
        //
        // It was write-only: asserted on and never shown, while the W-25 block
        // quoted "1,035 cases, 11,611 rows compared, note-hole 2,311, est-hole
        // 571" as a MEASUREMENT that no command in the committed tree produced
        // — it can only have come from a temporary print. AGENTS §5.11's own
        // rule is one measurement per number, from the committed harness.
        //
        // It prints on EVERY case, to stderr, and that is deliberate: this is
        // the one place the census can be read without racing the arm that
        // fills it (the sibling file's
        // `zz_the_declared_refusals_are_all_reachable` shape needs `--test-threads=1`, and this
        // arm's own comment above says why a separate `#[test]` would pass by
        // seeing nothing). Every line is a running prefix and the LAST is the
        // total. libtest captures it, so a green run is silent; read it with
        //
        //     cargo test --test planner_invariants -- --nocapture \
        //       the_kernel_reads_every_day_the_fork_planned
        eprintln!(
            "planner_invariants census: {cases} cases, {rows} rows compared, \
             note-hole {notes}, est-hole {ests}, parent-cells {parents}"
        );
    }
}

// ===========================================================================
// **THE KERNEL PLANS THE DAY** — stage 6 W-28, step R2's RESPONSE half (D48).
//
// The arm above sends the FORK's day through the `plan` section and compares
// the kernel's rendering of it. This one asks the kernel to **plan**, through
// `PlanWire.callExport`, and compares two planners.
//
// **What is compared, and why not everything, measured rather than assumed.**
// `Planner.dayRows` is §8.2 steps 1 and 2 and nothing else; steps 3 to 7 are
// P3..P7 and unwritten, and README gap **1670** records that the kernel's day
// therefore holds no step-5 assignment at all. Asserting segment-for-segment
// equality would be asserting something untrue of a half-built planner, and
// narrowing the generator until it came out true is what **D46** forbids. So
// this compares the answers the kernel is *complete* for:
//
//   * `plan.day`, the date it planned;
//   * `plan.window`, §8.1's working window — `Look.day0Window` on one side and
//     `Planner::window_and_budget` on the other, two readers README gap **320**
//     says can disagree, so a disagreement here is a **finding owed a parity
//     number** and not a hole to widen;
//   * `plan.budgetBlocks`;
//   * and **the walls**, the one row class step 1 completes, which §8.3's own
//     "walls are never moved" invariant is about — compared to the minute, both
//     ways, so a wall the kernel invents fails as loudly as one it drops.
//
// Everything else the kernel places (the routine rows, the replayed past, the
// rest/wind-down/sleep filler) is COUNTED and reported and asserted on only
// through the refusal claim, because the fork's day for those rows is the
// output of steps this kernel has not written.
//
// **The `routines` key CARRIES THE FORK'S OWN INSTANCES SINCE W-31**, and the
// sentence that stood here — "this arm has no honest collector" — was false.
// `Planner::collect_routines` reads the candidate list and the item's `shape`
// and nothing else, and both were already in this arm's hands; see
// [`World::routine_items`] (a call of `tm_core::planwire::routine_instances` since the W-35
// repair, README gap 2922) and README gap **2220**. F2's recurrence expansion
// is still not built and D27 is still not done early: the expansion happened in
// `priority::collect_candidates` before the list existed. So the kernel places
// §8.2 step 2's rows here now, they are compared to the second, both ways, and
// the assigned-row comparison no longer exempts a day for holding one.
// ===========================================================================


/// `(cases, walls compared, kernel rows seen, window disagreements, budget
/// disagreements, assigned rows compared, cases EXEMPT from the assigned
/// comparison, cases whose §7 answers differ, compared cases whose slots agree
/// and whose items do not (gap 2007), and the two clock-based work-row
/// counts)`, then W-30's four §7-row counters: rows compared, rows whose
/// capacity (`avail`) differs and whose `until` is TODAY (parity **P41**), the
/// same with `until` beyond today (parity **P1**), rows an id could not key
/// because it named two rows on one side, and the days on which §7's whole
/// answer agreed so that step 5's assignment could be ASSERTED.
///
/// **W-31 adds four**: the days on which the FORK placed a §8.2 step-2 routine
/// row (the population the old exemption removed from the assigned-row
/// comparison, kept as a counter so a run that stopped drawing routines is
/// visible), the step-2 routine rows COMPARED, and the two candidate-set
/// counters README gap **2222** is about — fork-assigned row ids the kernel was
/// sent no candidate for, and fork-assigned row ids the kernel returned no §7
/// grant for.
static PLAN_CENSUS: Mutex<[u64; 44]> = Mutex::new([0; 44]);

/// **The `SegKind` words this run actually compared** — README gap **2227**.
///
/// `planner::kind_label` and `PlanWire.kindName` are two spellings of one table
/// (the kernel's carries an eleventh arm, `ghost`, which the fork keeps as a
/// `SegFlags` bit). `kernel_row_cells.rs`'s
/// `the_kernel_and_the_fork_agree_on_every_kind_of_row` sweeps all ten words
/// through the kernel's **reader** (`EmitWire.readKind`) and compares nine
/// rendered cells, so the reader is pinned. The **writer** was not: this arm
/// read `s["kind"]` against one string literal, `"routine"`, and against nothing
/// else in the file. Here the kernel's own word for a row is compared to
/// `kind_label`'s for the fork row at the same minutes carrying the same item.
///
/// **The table is never spelled here.** The words come out of `kind_label` on
/// one side and out of the kernel on the other; a third copy in this file would
/// be the very defect the comparison is for (AGENTS §5.3). Coverage is therefore
/// a SET that grows, not a checklist, and the floor is on its size.
static KIND_WORDS: Mutex<BTreeSet<String>> = Mutex::new(BTreeSet::new());

/// `(start, stop)` of every Wall row of a kernel day, in the day's order.
fn kernel_walls(plan: &Value) -> Vec<(i64, i64)> {
    plan["segments"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default()
        .iter()
        .filter(|s| s["kind"] == "wall")
        .map(|s| (s["start"].as_i64().unwrap_or(-1), s["stop"].as_i64().unwrap_or(-1)))
        .collect()
}

/// **(start, stop, items) of every row §8.2 step 5 ASSIGNED**, on both sides, by the property
/// that distinguishes them and not by a list of the rows that are not them: a step-5 row is a
/// work row (Block or Batch) that carries a **slot energy**.
///
/// The three other sources of a work row each carry `energy: None` and each does so for a
/// reason a reader can check: §8.2 choice 5b's reservation *"is a reservation, not a slot, so
/// it carries no slot energy"* (fork `emit_segments`; kernel
/// `Planner.PlanReq.activeRow_is_an_energyless_block`), and the replayed past is played back
/// off the log, which has no slots in it (`Planner.pastRows`). Only the assign fold puts a row
/// in an energised slot, on either side.
///
/// **This was a `start >= now` restriction for one run of this arm and the clock was the wrong
/// subject** — driven: the arm failed with *"the kernel assigned [(63924379200, 63924380760,
/// [\"zaa\"])] from a request carrying no candidates"*, and with no candidates on the wire the
/// only work row the kernel can draw at or after `now` is §8.2 choice 5b's reservation. The
/// energy property names step 5's rows; the clock names "whatever has not started yet", which
/// is a different set. **No asymmetry between the two planners is claimed from that failure**
/// — the census counts the clock-based set on both sides, and it is 25 and 25. README gap
/// 1906.
fn kernel_assigned(plan: &Value, _now_sec: i64) -> Vec<(i64, i64, Vec<String>)> {
    plan["segments"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default()
        .iter()
        .filter(|s| {
            (s["kind"] == "block" || s["kind"] == "batch") && !s["energy"].is_null()
        })
        .map(|s| {
            // **THE KEY IS `batch`, AND THIS READ `ids`** (W-29 repair, README
            // gap 2015). `PlanWire.segJson` writes `batch` for a Batch row's
            // members and `item` for a Block's; `s["ids"]` is a key the kernel
            // has never written, so every Batch row read as EMPTY and fell
            // through to a null `item`. Nothing caught it because this function's
            // result was never compared with the fork's until this step — the
            // reader of a comparison that does not run is not a tested reader.
            let ids: Vec<String> = match s["batch"].as_array() {
                Some(a) if !a.is_empty() => {
                    a.iter().filter_map(|x| x.as_str().map(str::to_string)).collect()
                }
                _ => s["item"].as_str().map(str::to_string).into_iter().collect(),
            };
            (s["start"].as_i64().unwrap_or(-1), s["stop"].as_i64().unwrap_or(-1), ids)
        })
        .collect()
}

/// The same, off the fork's day, by the same property.
fn fork_assigned(day: &DayPlan, _from: DateTime<Tz>) -> Vec<(i64, i64, Vec<String>)> {
    day.segments
        .iter()
        .filter(|s| matches!(s.kind, SegKind::Block | SegKind::Batch(_)))
        .filter(|s| s.energy.is_some())
        .map(|s| {
            let ids: Vec<String> = match &s.kind {
                SegKind::Batch(ids) => ids.iter().map(ToString::to_string).collect(),
                _ => s.item.iter().map(ToString::to_string).collect(),
            };
            (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end), ids)
        })
        .collect()
}

/// **§7's WHOLE ANSWER for one candidate, kernel beside fork** (W-30) — the ten fields
/// `Look.FloorOut` carries and `kernel_capacity::parse` decodes into a `Prio`, not the `p`
/// alone the W-29 repair step compared.
///
/// It returns two lists: the fields of the **capacity** — what the §8.4 lookahead handed §7 —
/// that differ, and the fields **downstream** of it that differ. The split is the whole point.
/// Both registered divergences of this pass are capacity divergences and nothing else: parity
/// **P1** (the kernel mixes `w·L + (capDen − w)·H` over the two locations where the fork picks
/// one at the `p_lounge ≥ 0.5` threshold, so a future day's minutes land on different levels)
/// and parity **P41** (the kernel reads day 0 off the capacity section's own window cut, since
/// D24/L9 keeps every §9 row off that wire, where the fork point reads it off §8.2 step 3's
/// cut — walls, the running block, today's placed routines and the night already removed).
/// **Everything downstream is asserted to agree**, which is the statement P1's own register row
/// makes (*"future-day capacity **and everything downstream**"*) read as a test rather than as
/// a sentence: `allocation`, `shortfall`, `bin`, the HOT/IMPOSSIBLE class, `p` and `rawP` are
/// one function of `(k, need, avail, until)` and the two planners must compute it alike.
///
/// A wall carries no `p` on either side (`Planner.prioRow`, fork `sorted_candidates`' `7`), so
/// only its class is compared.
fn grant_fields(k: &Value, f: &Prio) -> (Vec<String>, Vec<String>) {
    let unit = |v: &Value| -> u128 {
        v.as_str().unwrap_or("0").parse::<u128>().unwrap_or(0) / 1_000_000_000_000_000_000
    };
    let cls = |c: PrioClass| -> &'static str {
        match c {
            PrioClass::Wall => "wall",
            PrioClass::Hot => "hot",
            PrioClass::Impossible => "impossible",
            PrioClass::Overdue => "overdue",
            PrioClass::Mandatory => "mandatory",
            PrioClass::HotFlag => "hotflag",
            PrioClass::Dated => "dated",
            PrioClass::Floor => "floor",
            PrioClass::Rank => "rank",
            PrioClass::Optional => "optional",
        }
    };
    let mut cap = Vec::new();
    let mut down = Vec::new();
    let say = |v: &mut Vec<String>, name: &str, a: String, b: String| {
        if a != b {
            v.push(format!("{name} kernel {a}, fork {b}"));
        }
    };
    // Is it a wall on both sides?  That half is compared for every row.
    say(&mut down, "class", k["class"].as_str().unwrap_or("?").to_string(), cls(f.class).to_string());
    if f.class == PrioClass::Wall {
        return (cap, down);
    }
    // The capacity §8.4 handed §7, and the two facts that are the candidate's own.
    say(&mut cap, "avail", unit(&k["avail"]).to_string(), f.avail_min.to_string());
    say(&mut cap, "until", format!("{:?}", k["until"].as_str()),
        format!("{:?}", f.until.map(|d| d.to_string()).as_deref()));
    say(&mut cap, "need", format!("{:?}", k["need"].as_u64()), f.need_min.to_string());
    say(&mut cap, "k", format!("{:?}", k["k"].as_u64()), f.k.to_string());
    // Everything §7 computes FROM that.
    say(&mut down, "allocation", unit(&k["allocation"]).to_string(), f.allocation_min.to_string());
    say(&mut down, "shortfall", unit(&k["shortfall"]).to_string(), f.shortfall_min.to_string());
    say(&mut down, "bin", format!("{:?}", k["bin"].as_u64()), format!("{:?}", f.bin));
    say(&mut down, "p", format!("{:?}", k["p"].as_u64()), f.p.to_string());
    say(&mut down, "rawP", format!("{:?}", k["rawP"].as_u64()), f.raw_p.to_string());
    (cap, down)
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

/// The same, off the fork's day.
fn fork_walls(day: &DayPlan) -> Vec<(i64, i64)> {
    day.segments
        .iter()
        .filter(|s| matches!(s.kind, SegKind::Wall))
        .map(|s| (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end)))
        .collect()
}

proptest! {
    #![proptest_config(ProptestConfig {
        // **256, RAISED FROM 128 AT W-31** (128 from 64 at W-30) — the search,
        // not the generator (D46: narrowing a generator to lose a disagreement
        // is forbidden; widening the search to find one is the opposite move).
        // W-30 raised it because 64 cases had never found the slot-geometry
        // disagreement README gap **2062** carries and a 512-case run found it
        // on the fourth try. W-31 raises it because the population the run
        // compares grew by 4.6x in the same edit — `routines` crossing the wire
        // took `cases exempt` from 102 of 143 to 0 and `assigned-rows compared`
        // from 84 to 390 — so a case is worth more than it was, and the two
        // step-2 floors below want a count that reliably draws a routine.
        // Measured on this tree: the whole file costs 67.6 s at 256. The
        // comparison test alone costs 35.9 s at 128 with `routines` on the wire
        // against 24.2 s at the 128 W-30 shipped without them, so the key is
        // half again as expensive per case and the raise is the other half.
        // `TM_PROPTEST_CASES` still takes an auditor higher.
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256),
        max_shrink_iters: 2_000,
        ..ProptestConfig::default()
    })]

    /// **The kernel plans the same day the fork plans**, as far as the kernel
    /// is built to plan it — see this section's header for exactly how far, and
    /// why the line is where it is.
    #[test]
    fn the_kernel_plans_the_day_the_fork_plans(case in case_strategy()) {
        let w = build(&case);
        let fork = planner::plan(&w.input(&w.state, w.now));
        let req = w.plan_request();
        let plan = match kernel_plan(&req) {
            Ok(p) => p,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the kernel refused a day the fork planned: {head}");
                unreachable!()
            }
        };

        // **The date.**
        let fork_date = fork.date.to_string();
        prop_assert_eq!(
            plan["day"].as_str(), Some(fork_date.as_str()),
            "the two planners planned different days"
        );

        // **§8.1's window and budget**, the two readers README gap 320 is about.
        let (klo, khi) = (
            plan["window"]["lo"].as_i64().unwrap_or(-1),
            plan["window"]["hi"].as_i64().unwrap_or(-1),
        );
        let (flo, fhi) = (
            rowwire::kernel_sec(fork.window.0),
            rowwire::kernel_sec(fork.window.1),
        );
        let window_differs = (klo, khi) != (flo, fhi);
        let budget_differs =
            plan["budgetBlocks"].as_u64() != Some(u64::from(fork.budget_blocks));

        // **The walls, to the minute, both ways.**
        let kw = kernel_walls(&plan);
        let fw = fork_walls(&fork);
        prop_assert_eq!(
            &kw, &fw,
            "the two planners disagree about §8.2 step 1's walls \
             (kernel {:?}, fork {:?})", kw, fw
        );

        // **§8.2 step 5's rows, compared — and the exemption is a PROPERTY, not a list.**
        // P9 put `Planner.PlanReq.assignedRows` in the kernel's day, and since the W-29
        // repair step this arm SENDS the fork's candidates (`candidate_items`), so a
        // kernel day carries assigned Block and Batch rows on every case whose tree
        // generated one. What is still not sent is §10.2's `routines`, and that is the
        // exemption below — stated over the fork's own day, counted, and not universal.
        let now_sec = rowwire::kernel_sec(w.now);
        let ka = kernel_assigned(&plan, now_sec);
        // **Measured, not asserted**: the energy-less work rows at or after `now` — the set a
        // clock-based subject would have called "assigned". It is here because the first
        // version of this comparison used that subject and caught the reservation with it;
        // the counter is what says whether the two planners' clock-based sets even have the
        // same size, rather than a sentence claiming they do not. README gap 1906.
        let k_res = plan["segments"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .filter(|s| {
                (s["kind"] == "block" || s["kind"] == "batch")
                    && s["energy"].is_null()
                    && s["start"].as_i64().unwrap_or(-1) >= now_sec
            })
            .count() as u64;
        let f_res = fork
            .segments
            .iter()
            .filter(|s| {
                matches!(s.kind, SegKind::Block | SegKind::Batch(_))
                    && s.energy.is_none()
                    && s.start >= w.now
            })
            .count() as u64;
        let fa = fork_assigned(&fork, w.now);
        let cands = req["capacity"]["candidates"]["items"]
            .as_array()
            .map_or(0, Vec::len);
        // **A request with no candidates must produce no assigned row**, and
        // that is a consequence of the kernel's own definitions rather than of
        // this arm's input: `Planner.rankedCands.length ≤ cands.length`, so
        // `dayBatches` and `rawGroups` are empty and `assignedRows`' `groups[gi]?`
        // can never return one. It is asserted anyway because it is cheap, and
        // it is NO LONGER the whole of this comparison: the request above now
        // carries the fork's candidates and `cands` is 0 only for a case whose
        // tree generated nothing.
        if cands == 0 {
            prop_assert!(
                ka.is_empty(),
                "the kernel assigned {:?} from a request carrying no candidates", ka
            );
        }
        // **THE EXEMPTION'S `routines` HALF IS GONE, BECAUSE THE KEY CROSSES THE
        // WIRE** (W-31, README gap 2220). The clause read `fork_routines > 0`
        // and its own comment ended *"the day `routines` crosses the wire the
        // exemption empties with no edit here"* — that day is this one, and the
        // edit is the clause's deletion. It was firing on **102 of 143** cases,
        // which is 71% of the population, and it took §8.2 step 5's whole
        // assignment comparison with it: `assigned-rows compared` was 84 of the
        // 368 rows the kernel drew.
        //
        // What is left is `cands == 0`, and that is a property of the REQUEST,
        // not of the fork's day. The count is kept as a census figure so that a
        // run which stopped drawing routines — and therefore stopped exercising
        // step 2 at all — is visible rather than silently green.
        let fork_routines = fork
            .segments
            .iter()
            .filter(|s| matches!(s.kind, SegKind::Routine))
            .count();
        // **§7's WHOLE ANSWER, compared row by row, and the capacity half is told
        // apart from everything downstream of it** (W-30; the W-29 repair step
        // compared `(id, p)` and could say only *that* the two disagreed).
        //
        // `PlanWire.priosJson` writes `Planner.dayPriorities` into the `plan`
        // object and `kernel_plan` carries the lookahead's own `grants` beside
        // it — the ten fields `kernel_capacity::parse` turns into a `Prio` — so
        // the comparison can name WHICH field moved. Driven at this commit, over
        // 526 cases: **every** divergence of this pass is a divergence of the
        // capacity `avail`, and `allocation`, `shortfall`, `bin`, the class, `p`
        // and `rawP` follow it. That is asserted below, per row, which is P1's
        // own register row (*"future-day capacity **and everything downstream**"*)
        // read as a test instead of as a sentence.
        //
        // **Keyed by an id that names ONE row on each side.** §5.3's carried
        // instance can put an id in the list twice; such a row is not compared
        // and is COUNTED (`§7 rows unkeyable`) rather than silently collapsed
        // into a map, which is what the `(id, p)` `BTreeMap` did.
        let mut kg: BTreeMap<String, Vec<&Value>> = BTreeMap::new();
        for g in plan["__grants"].as_array().map(Vec::as_slice).unwrap_or_default() {
            kg.entry(g["id"].as_str().unwrap_or_default().to_string()).or_default().push(g);
        }
        let mut fg: BTreeMap<String, Vec<&Prio>> = BTreeMap::new();
        for (id, pr) in &fork.priorities {
            fg.entry(id.to_string()).or_default().push(pr);
        }
        let (mut g7, mut gcap0, mut gcapn, mut gdup) = (0u64, 0u64, 0u64, 0u64);
        let mut prios_differ = false;
        for (id, fl) in &fg {
            let Some(kl) = kg.get(id) else { continue };
            if kl.len() != 1 || fl.len() != 1 {
                gdup += 1;
                continue;
            }
            let (kr, fr) = (kl[0], fl[0]);
            let (cap, down) = grant_fields(kr, fr);
            g7 += 1;
            // **THE ASSERTION**: §7 is one function of the capacity it is given.
            // A field downstream of the capacity may differ only where the
            // capacity does, and where the capacity agrees nothing downstream
            // may move. Neither P1 nor P41 can reach this; a change to §7's own
            // arithmetic on either side fails here, naming the field.
            prop_assert!(
                !cap.is_empty() || down.is_empty(),
                "§7 answered differently for {id} while the capacity it was given AGREED: {}",
                down.join("; ")
            );
            if !cap.is_empty() {
                prios_differ = true;
                // **Which registered divergence it is, by the row's OWN `until`**:
                // a row summed to today alone is P41's (day 0's cut); a row that
                // reaches a later day is P1's (the mixture). Both are properties
                // of the row, not a list of case shapes.
                if fr.until.is_none_or(|d| d <= date()) {
                    gcap0 += 1;
                } else {
                    gcapn += 1;
                }
            } else if !down.is_empty() {
                prios_differ = true;
            }
        }
        // **§8.2 STEP 2's ROWS, COMPARED TO THE SECOND AND BOTH WAYS** (W-31),
        // **AGAINST THE DAY THE KERNEL WAS ASKED ABOUT** (W-32, README gap 2224
        // settled). The kernel places these, and a row it places that nothing
        // compares is this campaign's third shape — a part built correctly and
        // never joined to the thing it is part of (D50, gap 501, `Tree.lean`). So
        // they are asserted: start, end and item, in timeline order, which is the
        // same statement the walls have had since W-29 and which a routine the
        // kernel invents or drops fails as loudly as one placed at the wrong
        // minute.
        //
        // **W-31 WITHDREW THIS ASSERTION TO A COUNTER AND THE REASON IT GAVE WAS
        // FALSE IN BOTH HALVES.** The reason on record was: seed `af6b8c79…`
        // (kept, D46) places `shower` at 21:00 on the fork and nowhere on the
        // kernel, because *"the fork then places it at §8.2 step 6, which the
        // kernel has not written"*.
        //
        //   * **The kernel has had a step 6 since `0d52a4d`** (2026-09-19, step
        //     P6): `Planner.PlanReq.deferOne` / `deferWalk` / `deferFold`, with
        //     `finalRoutines` and `finalAssign` its two projections, and
        //     `dayRows` reads `dayRoutineSegs` = `routineRows r r.finalRoutines`.
        //     It is composed, not orphaned. Driven on the kept seed: the kernel's
        //     step 6 RAN and reported `{"note":"noPosition","id":"shower"}` in
        //     `diagnostics.notes`, which only `PlanReq.noPositionNotes` over
        //     `finalRoutines` can write.
        //   * **The comparand was the wrong day.** `frout` below reads the fork
        //     day ranked by the FORK's own §7 pass. Two registered divergences —
        //     **P1** (the future days' mixture) and **P41** (day 0's cut) — put a
        //     different `p` into step 5, so that day assigns different slots; on
        //     the kept seed it leaves 21:00–21:30 free and the kernel's step 5
        //     fills it, after which the kernel's step 6 correctly finds no
        //     20-minute position anywhere in 11:00–21:30 and says so. Asked the
        //     question the kernel was asked — `with_ranking(cands, kernel_prios)`,
        //     the shipped `planning::build_ranked` wiring — the fork ALSO leaves
        //     `shower` unplaced and ALSO fills 21:00–21:30.
        //
        // This is the same defect the assigned-row comparison below names in
        // capital letters (*"`ka != fa` above is not a step-5 statement and this
        // arm spent a run pretending it was"*), one section up, in rows added
        // after that repair and never given its comparand. Measured over 272
        // cases: against the fork's OWN-§7 day, only the fork placed **1** of
        // 293; against the kernel-ranked fork, **292 rows on both sides, 0 only
        // the kernel, 0 only the fork**. So the statement is restored as an
        // assertion, the old pair of counters stays in the census as gap 2224's
        // record, and the perturbation W-31 said was caught by nothing — a step-2
        // rename at identical minutes — is caught again.
        //
        // **The first restatement of all, kept because the measurement and not
        // the intention is what settles it**: telling a step-2 row from a step-6
        // row by the fork's own `deferred` flag — set by all three of step 6's
        // branches (`planner.rs:1657`, `:1673`, `:1694`) and left false by step
        // 2's — is a true split, and comparing the kernel against the fork's
        // NON-deferred rows alone made **107 of 301** rows differ, because what
        // the fork defers to step 6 the kernel may place at step 2 and the two
        // land on the same minute anyway. A 35% disagreement rate is the
        // signature of the wrong comparand; so is 1 in 293, and this arm has now
        // met that signature three times (the `days: 7` / `wake` pair, `ka != fa`,
        // and this). The comparison is the WHOLE routine row list on both sides.
        // **THE SECOND FORK DAY, THE SAME REQUEST RANKED BY THE KERNEL'S OWN §7
        // ANSWER** — hoisted here at W-32 because the routine rows below need it
        // as much as the assigned rows do (README gap 2224).
        let cvec = w.candidates();
        let kprios = kernel_prios(&plan, &cvec);
        let day2 = kprios
            .as_ref()
            .map(|ps| w35_fork_plan(&w, &w.state, &cvec, ps));
        let routine_rows = |segs: &[Segment]| -> Vec<(i64, i64, String)> {
            segs.iter()
                .filter(|s| matches!(s.kind, SegKind::Routine))
                .map(|s| (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end),
                          s.item.as_ref().map(ToString::to_string).unwrap_or_default()))
                .collect()
        };
        let krout: Vec<(i64, i64, String)> = plan["segments"]
            .as_array().map(Vec::as_slice).unwrap_or_default().iter()
            .filter(|s| s["kind"] == "routine")
            .map(|s| (s["start"].as_i64().unwrap_or(-1), s["stop"].as_i64().unwrap_or(-1),
                      s["item"].as_str().unwrap_or_default().to_string()))
            .collect();
        let fdefer = fork.segments.iter()
            .filter(|s| matches!(s.kind, SegKind::Routine) && s.flags.deferred)
            .count() as u64;
        let frout: Vec<(i64, i64, String)> = routine_rows(&fork.segments);
        let ronly = krout.iter().filter(|r| !frout.contains(r)).count() as u64;
        let fonly = frout.iter().filter(|r| !krout.contains(r)).count() as u64;
        // **W-32 DRIVE**: the same two counters against the day the kernel was
        // asked about.
        let (mut kindcmp, mut kindskip) = (0u64, 0u64);
        let frout2: Vec<(i64, i64, String)> =
            day2.as_ref().map(|d| routine_rows(&d.segments)).unwrap_or_default();
        let ronly2 = krout.iter().filter(|r| !frout2.contains(r)).count() as u64;
        let fonly2 = frout2.iter().filter(|r| !krout.contains(r)).count() as u64;
        // **THE KERNEL'S OWN `SegKind` WORD, AGAINST `kind_label`'s** (W-32,
        // README gap 2227). Every row of the kernel-ranked fork day is keyed by
        // `(start, stop, item)`; a key that names one row on each side is a row
        // the two planners agree is there, and its two kind words must be the
        // same word. A key that names two rows on one side is not compared and
        // is counted as unkeyable, the shape §7's row comparison already uses.
        if let Some(d) = day2.as_ref() {
            let mut fkinds: BTreeMap<(i64, i64, String), Vec<&'static str>> = BTreeMap::new();
            for seg in &d.segments {
                fkinds
                    .entry((rowwire::kernel_sec(seg.start), rowwire::kernel_sec(seg.end),
                            seg.item.as_ref().map(ToString::to_string).unwrap_or_default()))
                    .or_default()
                    .push(planner::kind_label(&seg.kind));
            }
            let mut kkinds: BTreeMap<(i64, i64, String), Vec<String>> = BTreeMap::new();
            for seg in plan["segments"].as_array().map(Vec::as_slice).unwrap_or_default() {
                kkinds
                    .entry((seg["start"].as_i64().unwrap_or(-1), seg["stop"].as_i64().unwrap_or(-2),
                            seg["item"].as_str().unwrap_or_default().to_string()))
                    .or_default()
                    .push(seg["kind"].as_str().unwrap_or_default().to_string());
            }
            for (key, ks) in &kkinds {
                let Some(fs) = fkinds.get(key) else { continue };
                if ks.len() != 1 || fs.len() != 1 {
                    kindskip += 1;
                    continue;
                }
                prop_assert_eq!(
                    ks[0].as_str(), fs[0],
                    "the kernel and the fork name one row's kind differently at {:?}", key
                );
                kindcmp += 1;
                KIND_WORDS.lock().expect("kinds").insert(ks[0].clone());
            }
        }
        if day2.is_some() {
            prop_assert_eq!(
                &krout, &frout2,
                "§8.2 step 2's routine rows differ from the fork ranked by the kernel's own \
                 §7 answer (kernel {:?}, fork {:?})", krout, frout2
            );
        }

        // **§8.2 STEP 8: THE KERNEL'S DIAGNOSTICS AGAINST THE KERNEL-RANKED FORK'S** (W-33,
        // README gaps 2403 and 2321). Since W-33 the kernel writes seven of the twelve fields
        // off its own answers — `impossible`, `hot`, `waiting`, `blocked`, `droppedTail`,
        // `underused`, `planHonesty` — and the fork's `diagnose` computes all twelve for the
        // very question the kernel was asked: `day2` is `with_ranking(cands, kernel_prios)`,
        // the shipped wiring (D53). Each field is compared as a MULTISET, because the fork
        // pushes in its candidate order and the kernel in the wire's and neither order is
        // §8.2's contract; `impossible` compares the SHORTFALL too — the value, not the
        // presence; `planHonesty` compares the ratio the fork prints, `None` at a zero budget.
        // The other five fields are not written by this kernel yet (`conflicts`, `notes` and
        // `aCapacityLost` are, since P1/P7, and are not this arm's question) and are not
        // compared here: `deferred` and `restDebtMin` are README gap 2511.
        let (mut dcmp, mut dimp, mut dhot, mut dmore, mut d554) = (0u64, 0u64, 0u64, 0u64, 0u64);
        // **EVERY COMPARED FIELD HAS ITS OWN FLOOR** (W-33 repair, README gap 2568). The
        // floors below were two -- `impossible` and `hot` non-empty on some day -- and the
        // other five shared one sum, `dmore`, so `waiting` could be `[]` against `[]` on
        // every day with the sum carried by `droppedTail`. A list of two checks where the
        // rule is "every compared field", the fifteenth counted instance. Each field is
        // counted alone now, and so are the two ARMS track P added to the kernel's writers:
        // the FLOOR answers of `impossible` (`PlanReq.dayImpossible` over `candAnswers`,
        // `PlannerWit.the_day_names_an_impossible_floor`) and the HOT-FLAG answers of `hot`.
        let (mut dwait, mut dblock, mut dund, mut ddrop, mut dhon, mut dimpfl, mut dhotfl) =
            (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        if let Some(d2) = day2.as_ref() {
            let kd = &plan["diagnostics"];
            let ids_of = |v: &Value| -> Vec<String> {
                let mut x: Vec<String> = v
                    .as_array()
                    .map(Vec::as_slice)
                    .unwrap_or_default()
                    .iter()
                    .map(|s| s.as_str().unwrap_or("<not a string>").to_string())
                    .collect();
                x.sort();
                x
            };
            let sorted = |mut x: Vec<String>| -> Vec<String> {
                x.sort();
                x
            };
            let mut kimp: Vec<(String, u64)> = kd["impossible"]
                .as_array()
                .map(Vec::as_slice)
                .unwrap_or_default()
                .iter()
                .map(|o| {
                    (o["id"].as_str().unwrap_or("<no id>").to_string(),
                     o["shortMin"].as_u64().unwrap_or(u64::MAX))
                })
                .collect();
            kimp.sort();
            let mut fimp: Vec<(String, u64)> = d2
                .diagnostics
                .impossible
                .iter()
                .map(|(id, short, _)| (id.to_string(), u64::from(*short)))
                .collect();
            fimp.sort();
            prop_assert_eq!(
                &kimp, &fimp,
                "§8.2 step 8's `impossible` (id, shortfall minutes) differs from the \
                 kernel-ranked fork's"
            );
            let fhot = sorted(d2.diagnostics.hot.iter().map(ToString::to_string).collect());
            prop_assert_eq!(ids_of(&kd["hot"]), fhot.clone(), "§8.2 step 8's `hot` differs");
            let fwait = sorted(d2.diagnostics.waiting.iter().map(ToString::to_string).collect());
            prop_assert_eq!(ids_of(&kd["waiting"]), fwait.clone(), "§8.2 step 8's `waiting` differs");
            let fblock =
                sorted(d2.diagnostics.blocked.iter().map(|(id, _)| id.to_string()).collect());
            prop_assert_eq!(ids_of(&kd["blocked"]), fblock.clone(), "§8.2 step 8's `blocked` differs");
            // **`droppedTail` and `planHonesty` read the day's ASSIGNED set**, and until W-34 on
            // one class of day the two planners' sets differed for the reason README gap **554**
            // names: fork `open_block_segment` draws the worked stretch of the block the log
            // holds OPEN (`[since, now)`, `SegFlags::open`), and the kernel did not port it.
            // Where no reservation was placed (a wall covering `now`, overtime) only the fork's
            // set held the running item. Those days were COUNTED, not compared, by the property
            // that defined them: the fork's day carries gap 554's row for an item no kernel work
            // row names. DRIVEN (W-33): the first run of this comparison found exactly this,
            // `droppedTail` kernel `["zaa"]`, fork `[]`, at a running block whose `now` is a
            // wall's start; the seed is kept (D46).
            //
            // **W-34 PORTED THE ROW AND THE COUNTER IS AN ASSERTION** (README gap 2519, closed):
            // `Planner.openBlockRows`, composed into `Planner.dayRows` through `replayedRows`. So
            // the property that defined the exemption is asserted FALSE on every day — a fork
            // open-block row whose item no kernel work row names is a failure by name — and
            // both fields are compared on every day. `d554` now counts the days the fork DREW
            // an open-block row at all, which is the population the two assertions below were
            // exempt on, and it has a floor.
            let kwork: BTreeSet<String> = plan["segments"]
                .as_array()
                .map(Vec::as_slice)
                .unwrap_or_default()
                .iter()
                .filter(|s| s["kind"] == "block" || s["kind"] == "batch")
                .flat_map(|s| {
                    let mut ids: Vec<String> = s["batch"]
                        .as_array()
                        .map(Vec::as_slice)
                        .unwrap_or_default()
                        .iter()
                        .filter_map(|x| x.as_str().map(str::to_string))
                        .collect();
                    ids.extend(s["item"].as_str().map(str::to_string));
                    ids
                })
                .collect();
            let gap554 = d2.segments.iter().any(|s| {
                matches!(s.kind, SegKind::Block)
                    && s.flags.open
                    && s.start < w.now
                    && s.item.as_ref().is_some_and(|i| !kwork.contains(i.as_str()))
            });
            prop_assert!(
                !gap554,
                "the fork drew gap 554's open-block row for an item no kernel work row names \
                 (kernel work rows name {:?})", kwork
            );
            let fdrop =
                sorted(d2.diagnostics.dropped_tail.iter().map(ToString::to_string).collect());
            prop_assert_eq!(
                ids_of(&kd["droppedTail"]), fdrop.clone(),
                "§8.2 step 8's `droppedTail` differs"
            );
            let fund =
                sorted(d2.diagnostics.underused.iter().map(|(id, _, _)| id.to_string()).collect());
            prop_assert_eq!(
                ids_of(&kd["underused"]), fund.clone(),
                "§8.2 step 8's `underused` differs"
            );
            let planned = kd["planHonesty"]["planned"].as_u64().unwrap_or(u64::MAX);
            let total = kd["planHonesty"]["total"].as_u64().unwrap_or(u64::MAX);
            let kratio = (total != 0).then(|| planned as f64 / total as f64);
            prop_assert_eq!(
                kratio, d2.diagnostics.plan_honesty,
                "§8.2 step 8's `planHonesty` differs (kernel {}/{})", planned, total
            );
            dcmp = 1;
            dimp = kimp.len() as u64;
            dhot = fhot.len() as u64;
            dwait = fwait.len() as u64;
            dblock = fblock.len() as u64;
            dund = fund.len() as u64;
            ddrop = fdrop.len() as u64;
            dhon = u64::from(kratio.is_some());
            let floored = |id: &str| cvec.iter().any(|c| c.id.as_str() == id && c.floor.is_some());
            let flagged = |id: &str| cvec.iter().any(|c| c.id.as_str() == id && c.hot);
            dimpfl = kimp.iter().filter(|(id, _)| floored(id)).count() as u64;
            dhotfl = fhot.iter().filter(|id| flagged(id)).count() as u64;
            dmore = (fwait.len() + fblock.len() + fund.len() + fdrop.len()) as u64
                + u64::from(kratio.is_some());
            d554 = u64::from(d2.segments.iter().any(|s| {
                matches!(s.kind, SegKind::Block) && s.flags.open && s.start < w.now
            }));
        }

        // **AND EVERY ROW THE FORK ASSIGNED IS A ROW THE KERNEL ANSWERED FOR**
        // (W-31, README gap 2222). W-29 measured *"the fork assigned 184-209
        // rows the kernel had no candidate for"* (gap 1905) and W-30 reported
        // the figure closed — but the measurement it offered for that was
        // `rows unkeyable`, which counts a §7 row an id could not KEY because it
        // named two rows on one side. That is a different quantity, and this
        // campaign's commonest shape is a claim of having checked that was never
        // made. So the quantity the sentence is about is measured here.
        //
        // **The candidate half is 0 BY CONSTRUCTION and is therefore counted,
        // not asserted**: `fork_assigned` reads ids off the fork's own day and
        // `candidate_items` sends the fork's own candidate list, so the first is
        // a subset of the second and no draw can make it otherwise. A counter
        // that cannot move is not an instrument, and saying so is the point of
        // printing it.
        //
        // **The GRANT half can move and is asserted.** The kernel may answer
        // nothing for a candidate the capacity section refused by name, or for
        // one dropped past `Planner.maxCands` — `Planner.PlanReq.rankedCands`
        // is bounded by the candidate list's own length and nothing makes it
        // meet it. A day on which either happened would be a day where the two
        // planners were handed different work, which is exactly what gap 1905's
        // sentence warned bounds any comparison. It names the id.
        let wire_ids: BTreeSet<&str> = req["capacity"]["candidates"]["items"]
            .as_array().map(Vec::as_slice).unwrap_or_default().iter()
            .filter_map(|c| c["id"].as_str()).collect();
        let f_uncand = fa.iter().flat_map(|r| r.2.iter())
            .filter(|id| !wire_ids.contains(id.as_str())).count() as u64;
        let ungranted: Vec<&String> = fa.iter().flat_map(|r| r.2.iter())
            .filter(|id| !kg.contains_key(id.as_str())).collect();
        prop_assert!(
            ungranted.is_empty(),
            "the fork assigned {:?}, which the kernel's §7 answered nothing for",
            ungranted
        );

        let exempt = cands == 0;
        let kslots: Vec<(i64, i64)> = ka.iter().map(|r| (r.0, r.1)).collect();
        let fslots: Vec<(i64, i64)> = fa.iter().map(|r| (r.0, r.1)).collect();
        // **§8.2 step 5's SLOT GEOMETRY: asserted, DRIVEN, and found FALSE at a
        // larger case count — so it is COUNTED and the seed is kept** (W-30, D46).
        //
        // The W-29 repair step counted 1 to 6 slot disagreements per 64-case run.
        // Two of the causes were this arm asking the two planners two different
        // questions, and both are named and fixed above: the request spelled
        // `days: 7` where `kernel_capacity::rank` sends the fork's own
        // `priority::lookahead_days`, and it sent no `wake` at all, so
        // `Boundary.readWake` answered `.absent` and §8.5's `hsw` — which every
        // slot's energy level rides on — was measured from the weekday's expected
        // arrival on one side and from the day's own wake on the other. With both
        // sent, three 512-case runs counted **0** slot disagreements and the
        // assertion was written.
        //
        // **It then failed on the fourth**, and the case is in
        // `planner_invariants.proptest-regressions` (`3a39ad72…`): three items —
        // an `atomic` four-block one, a plain one and a batchable — on a LATE day
        // at home with one wall and the workout routine, where the kernel assigns
        // **two** consecutive hours and the fork assigns **one**. It is not a
        // different cut of the same day; it is one more slot taken, so the
        // subject is step 5's own budget-and-commitment walk and not §8.4.
        // README gap **2062** carries it. The count stays in the census line, at
        // 0 on most runs, so the step that settles it sees the number and the
        // seed replays on every run from here.
        let slots_differ = !exempt && kslots != fslots;
        // **AND THE ITEM COUNTER IS THE COMPLEMENT OF THE SLOT ONE, NOT A SUBSET
        // OF IT** — it requires that the slots AGREE — so the census label read "of
        // those" said the opposite of what it counted, exactly like the two labels
        // gap 2123 repaired one line of prose earlier. This run printed `slots
        // differ .. 1, of those .. ITEMS differ 3`, and 3 cannot be a subset of 1.
        // The antecedent is the NON-EXEMPT days, which is what both counters are
        // taken over; README gap 2131 (W-30 repair) carries the correction.
        let ids_differ = !exempt && !slots_differ && ka != fa;
        // The second fork day: the same request, ranked by the KERNEL's §7 answer.
        let fa2 = day2.as_ref().map(|day| fork_assigned(day, w.now));
        // **AND NOW THE ITEM IN THE SLOT IS ASSERTED — against the fork ranked by
        // the KERNEL, which is the wiring the binary ships** (W-30).
        //
        // `ka != fa` above is not a step-5 statement and this arm spent a run
        // pretending it was. The fork it compares there ran its OWN §7 pass over
        // its OWN lookahead, and the two lookaheads differ by two REGISTERED
        // divergences — **P1** for the future days' mixture and **P41** for day
        // 0's cut — so a different `p` reaches step 5 as a different rank order
        // and the assignment follows it. Measured over 527 cases: the whole §7
        // answer agreed on **four** days. An assertion gated on that is an
        // assertion that does not run.
        //
        // So the fork is asked the question the kernel was asked:
        // `PlanInput::with_ranking(cands, kernel_prios)`, which is exactly
        // `planning::build_ranked` → `Ctx::priorities` → `kernel_capacity::rank`
        // → `with_ranking` in the shipped binary. Then §8.2 step 5 is the only
        // thing left that can differ, and **it does not**: over three 512-case
        // runs, 167/167, 167/167 and 168/168 non-exempt days agree on every
        // assigned row, slot AND item.
        //
        // **This is the assertion the W-29 audit's perturbation has to get
        // past**: reversing `emit_segments`' slot→group map leaves the geometry
        // alone and moves the occupant, which `ka != fa`'s COUNTER could only
        // watch rise. Driven again at this commit in a clone — see the README
        // block — and it fails here now, naming both rows.
        let same_question = !exempt && fa2.is_some();
        if let (false, Some(fa2)) = (exempt, fa2.as_ref()) {
            prop_assert_eq!(
                &ka, fa2,
                "§8.2 step 5 assigned differently from the fork ranked by the kernel's own \
                 §7 answer (kernel {:?}, fork {:?})", ka, fa2
            );
        }

        let rows = plan["segments"].as_array().map(Vec::len).unwrap_or(0) as u64;
        let [cases, walls, seen, wdiff, bdiff, acmp, aexempt, pdiff, sdiff, iddiff, kres, fres,
             grows, gday0, gdays, gdups, gsame, frdays, krows, funcand, fungrant, rdefer, ronlyc,
             fonlyc, frows, rboth, ronlyc2, fonlyc2, frows2, rboth2, kindc, kindsk, dcmpc, dimpc,
             dhotc, dmorec, d554c, dwaitc, dblockc, dundc, ddropc, dhonc, dimpflc, dhotflc] = {
            let mut c = PLAN_CENSUS.lock().expect("census");
            c[0] += 1;
            c[1] += kw.len() as u64;
            c[2] += rows;
            c[3] += u64::from(window_differs);
            c[4] += u64::from(budget_differs);
            c[5] += if exempt { 0 } else { ka.len() as u64 };
            c[6] += u64::from(exempt);
            c[7] += u64::from(prios_differ);
            c[8] += u64::from(slots_differ);
            c[9] += u64::from(ids_differ);
            c[10] += k_res;
            c[11] += f_res;
            c[12] += g7;
            c[13] += gcap0;
            c[14] += gcapn;
            c[15] += gdup;
            c[16] += u64::from(same_question);
            c[17] += u64::from(fork_routines > 0);
            c[18] += krout.len() as u64;
            c[19] += f_uncand;
            c[20] += ungranted.len() as u64;
            c[21] += fdefer;
            c[22] += ronly;
            c[23] += fonly;
            c[24] += frout.len() as u64;
            c[25] += krout.iter().filter(|r| frout.contains(r)).count() as u64;
            c[26] += ronly2;
            c[27] += fonly2;
            c[28] += frout2.len() as u64;
            c[29] += krout.iter().filter(|r| frout2.contains(r)).count() as u64;
            c[30] += kindcmp;
            c[31] += kindskip;
            c[32] += dcmp;
            c[33] += dimp;
            c[34] += dhot;
            c[35] += dmore;
            c[36] += d554;
            c[37] += dwait;
            c[38] += dblock;
            c[39] += dund;
            c[40] += ddrop;
            c[41] += dhon;
            c[42] += dimpfl;
            c[43] += dhotfl;
            *c
        };
        // **THE COMPARISON IS NOT VACUOUS**, asserted inside the fuzz: a run
        // that planned nothing on either side produces "every wall agreed" too
        // (AGENTS §9.2).
        // **THE FLOOR IS ABOUT A RUN, NOT ABOUT A PREFIX** (W-29 repair, README
        // gap 2016). It used to fire at 32 cases, and the census counts
        // proptest's PERSISTED REGRESSION replays first — shrunk cases, which
        // carry no wall BY CONSTRUCTION, because shrinking removes everything
        // the failure did not need. D46 keeps a drawn seed, so the replay list
        // only ever grows, and the 19th entry pushed the wall-less prefix past
        // 32: DRIVEN, three consecutive runs failed `no wall was compared in 35
        // cases` while the same runs compared 108-120 walls over their full 76.
        // The floor now fires once the GENERATED phase has run, which is what
        // "a run that planned nothing on either side" was always about.
        let generated: u64 = std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        if cases >= generated {
            prop_assert!(walls > 0, "no wall was compared in {cases} cases");
            prop_assert!(seen >= cases, "the kernel answered {seen} rows over {cases} cases");
            // **AND NEITHER IS THE ASSIGNED COMPARISON** (W-29 repair, README
            // gap 2005). This is the assertion whose absence let the arm ship
            // green while `assigned-rows compared` was 0 in every run: an
            // exemption every case satisfies is not an exemption, and it fails
            // HERE rather than in an auditor's census.
            prop_assert!(
                aexempt < cases,
                "every one of {cases} cases was exempt from the assigned-row comparison"
            );
            prop_assert!(acmp > 0, "no assigned row was compared in {cases} cases");
            // **AND NEITHER IS §7's** (W-30). `grant_fields` is the reader of a
            // comparison, and this campaign's own lesson is that the reader of a
            // comparison that does not run is not a tested reader (README gap
            // 2015). A run in which no §7 row was keyable compares nothing.
            prop_assert!(grows > 0, "no §7 row was compared in {cases} cases");
            // **AND THE ASSIGNMENT'S OWN COMPARISON HAS A FLOOR** (W-30). The
            // population is a third of the cases (167 of 527, measured), so a run
            // in which it is empty is a run in which the second fork call stopped
            // happening — and an assertion that does not run is the defect this
            // arm shipped with (README gap 2005).
            prop_assert!(
                gsame > 0,
                "step 5's assignment was asserted on no day of {cases} cases"
            );
            // **AND STEP 2 HAS ITS OWN THREE FLOORS** (W-31, repaired W-31 —
            // README gap 2265). The sentence here used to open "the routine rows
            // are asserted equal above", and they are NOT: two hundred lines up,
            // in the same commit, the equality was withdrawn to a counter and
            // says so — "IT IS A COUNTER AND NOT AN ASSERTION". So the floors
            // were guarding the vacuity of an assertion that does not exist.
            //
            // AND THE QUANTITY THEY TESTED WAS NOT THE ONE THE CAPTION NAMED.
            // `c[18] += krout.len()` is the number of routine rows THE KERNEL
            // placed, and the census line printed it as "routine rows compared":
            // nothing is compared into it, and on a planted run it read 279
            // while 279 kernel rows and 281 fork rows disagreed. The caption
            // names what is counted now — `krows` and `frows`, one per side —
            // and a third figure, `rboth`, is the rows that are on BOTH sides,
            // which is the only one of the three the word "compared" fits.
            //
            // The floor is `rboth`, because a run in which the `routines` key
            // silently stopped decoding gives `krows > 0` on the kernel side and
            // agrees with nothing (AGENTS §5.2's vacuous theorem, one layer in).
            // Four floors and not one: any one of the others alone would let the
            // rest rot.
            //
            // **W-32 ADDS THE FOURTH, AND IT IS THE ONE THE ASSERTION NEEDS.**
            // `rboth` counts rows the kernel and the fork's OWN-§7 day share, and
            // the restored equality is against the KERNEL-RANKED day, so `rboth`
            // could stay positive while the asserted comparison ran on nothing —
            // `day2` is `None` on a case with no kernel `p` answers, and an
            // assertion inside `if day2.is_some()` is an assertion that can be
            // skipped for every case in the run. `rboth2` is the rows the
            // assertion actually compared.
            prop_assert!(krows > 0, "the kernel placed no §8.2 step 2 routine row in {cases} cases");
            prop_assert!(
                rboth > 0,
                "not one §8.2 step 2 routine row agreed with the fork's in {cases} cases, \
                 so the comparison the counters below report is over two disjoint lists"
            );
            prop_assert!(
                rboth2 > 0,
                "not one §8.2 step 2 routine row was compared against the kernel-ranked fork \
                 in {cases} cases, so the equality asserted above ran on nothing"
            );
            // **AND THE KIND-WORD COMPARISON HAS ITS OWN FLOOR, ON THE SET AND
            // NOT ON THE COUNT** (gap 2227). A run that compared ten thousand
            // `block` rows and nothing else would satisfy any count; what makes
            // the comparison a comparison of a TABLE is how many of its arms it
            // reached. Six is what this generator draws — `block`, `routine`,
            // `wall`, `rest`, `sleep`, `wind-down`, and `batch`, `break` and
            // `optional` when the draw has them; `lost` needs an interruption
            // that ended and `ghost` is the kernel's alone. The floor is stated
            // below the observed number on purpose: it is a floor, not a band
            // (README gap 2267).
            let words = KIND_WORDS.lock().expect("kinds").len();
            prop_assert!(
                words >= 5,
                "only {words} distinct `SegKind` words were compared in {cases} cases, \
                 so `kind_label` and the kernel's own table were checked on almost no arm"
            );
            prop_assert!(
                frdays > 0,
                "the fork placed no routine on any of {cases} cases, so the days the \
                 `routines` exemption used to remove are not being drawn"
            );
            // **AND §8.2 STEP 8's COMPARISON HAS ITS FLOORS** (W-33). The comparison sits
            // inside `if let Some(d2) = day2`, which a run can skip on every case; and a run
            // that compared seven empty lists on every day compared nothing.
            prop_assert!(dcmpc > 0, "§8.2 step 8 was compared on no day of {cases} cases");
            prop_assert!(
                dimpc > 0,
                "no IMPOSSIBLE row was compared in {cases} cases, so `impossible` and its \
                 shortfall were checked against nothing"
            );
            prop_assert!(dhotc > 0, "no HOT id was compared in {cases} cases");
            // W-33 repair (gap 2568): one floor per compared field, and one per arm.
            for (n, what) in [
                (dwaitc, "WAITING id"),
                (dblockc, "BLOCKED id"),
                (dundc, "UNDERUSED id"),
                (ddropc, "DROPPED-TAIL id"),
                (dhonc, "planHonesty ratio"),
                (dimpflc, "IMPOSSIBLE row for a FLOOR (`min:`) candidate"),
                (dhotflc, "HOT id for a `hot`-FLAGGED candidate"),
            ] {
                prop_assert!(n > 0, "no {} was compared in {} cases", what, cases);
            }
            // **AND THE DAYS THE EXEMPTION USED TO REMOVE ARE DRAWN** (W-34, README gap 2519):
            // an assertion that `droppedTail` and `planHonesty` agree on the open-block days
            // is only an assertion if such days occur.
            prop_assert!(
                d554c > 0,
                "the fork drew an open-block row on none of {cases} cases, so gap 2519's \
                 assertion ran on nothing"
            );
        }
        eprintln!(
            "planner_invariants plan census: {cases} cases, {walls} walls compared, \
             {seen} kernel rows, window-differs {wdiff}, budget-differs {bdiff}, \
             assigned-rows compared {acmp}, cases exempt {aexempt}, \
             cases whose §7 answers differ {pdiff}, \
             NON-exempt days whose slots differ from the fork's OWN-§7 day {sdiff}, \
             of the NON-EXEMPT days, whose slots agree and whose ITEMS differ {iddiff}, \
             §7 rows compared {grows}, capacity differs to TODAY (P41) {gday0}, \
             beyond today (P1) {gdays}, rows unkeyable {gdups}, \
             days whose assignment was ASSERTED against the kernel-ranked fork {gsame}, \
             §8.2 step 2 routine rows the kernel placed {krows}, the fork placed \
             {frows}, on BOTH sides {rboth}, on {frdays} days the fork \
             placed one, fork-assigned ids with no kernel CANDIDATE {funcand} \
             (0 by construction), with no kernel §7 GRANT {fungrant}, \
             fork routine rows the fork's OWN-§7 day DEFERRED to §8.2 step 6 \
             {rdefer}, against that day step-2 rows only the kernel placed \
             {ronlyc}, only the fork placed {fonlyc} (gap 2224's record), \
             AGAINST THE KERNEL-RANKED FORK, WHICH IS WHAT IS ASSERTED: it \
             placed {frows2}, on BOTH sides {rboth2}, only the kernel {ronlyc2}, \
             only the fork {fonlyc2}, \
             `SegKind` words compared against `kind_label` {kindc} over {} \
             distinct words, rows unkeyable for that comparison {kindsk}, \
             energy-less work rows from now: kernel {kres}, fork {fres}, \
             §8.2 step 8 compared on {dcmpc} days: IMPOSSIBLE rows {dimpc}, HOT ids {dhotc}, \
             waiting/blocked/droppedTail/underused ids and planHonesty ratios {dmorec} \
             (waiting {dwaitc}, blocked {dblockc}, underused {dundc}, droppedTail {ddropc}, \
             planHonesty {dhonc}; IMPOSSIBLE rows of floor candidates {dimpflc}, HOT ids of \
             hot-flagged candidates {dhotflc}), \
             days the fork drew gap 554's open-block row on, where `droppedTail` and \
             `planHonesty` are now ASSERTED (W-34; counted and not compared until then) {d554c}",
            KIND_WORDS.lock().expect("kinds").len()
        );
        // **THE TWO DISAGREEMENTS ARE KEPT, NOT HIDDEN** (D46). A window or a
        // budget that differs is a finding: README gap 320's two readers, one of
        // them wrong, and the parity register is where a deliberate divergence
        // goes (check 10 says the next free number). They are asserted LAST so
        // the wall comparison above is reached on every case.
        prop_assert!(!window_differs, "§8.1's window: kernel ({klo}, {khi}), fork ({flo}, {fhi})");
        prop_assert!(
            !budget_differs,
            "§8.1's budget: kernel {:?}, fork {}", plan["budgetBlocks"], fork.budget_blocks
        );
    }
}

/// **The fork's half of [`two_routines_contend_for_one_position`]**: asked
/// the question the kernel was asked — the kernel's own §7 answer handed to
/// `with_ranking`, gap 2224's comparand — the fork places the two contending
/// routines row for row as the kernel does. Split out at W-37 track H so the
/// kernel's half outlives R3; this one leaves with the fork.
#[test]
fn two_routines_contend_for_one_position_on_the_fork() {
    let w = build(&contending_routines());
    let plan = kernel_plan(&w.plan_request()).expect("the kernel plans the day");
    let krout = kernel_routine_rows(&plan);
    let cvec = w.candidates();
    let kprios = kernel_prios(&plan, &cvec).expect("the kernel answers §7 for this day");
    let fork = planner::plan(&w.input(&w.state, w.now).with_ranking(&cvec, &kprios));
    let frout: Vec<(i64, i64, String)> = fork.segments.iter()
        .filter(|s| matches!(s.kind, SegKind::Routine))
        .map(|s| (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end),
                  s.item.as_ref().map(ToString::to_string).unwrap_or_default()))
        .collect();
    assert_eq!(krout, frout, "the two planners ordered the contending routines differently");
}

/// **W-34's census**: `[cases, open rows compared, days with an open row, overtime days
/// compared, overtime ids compared (removed, added and moved), overtime days where the fork's
/// `extra_min` override moved the answer beyond the estimate's own, overtime drops on those
/// days (fork, full what-if), cases with no kernel §7 answer]`.
static W34_CENSUS: Mutex<[u64; 8]> = Mutex::new([0; 8]);

/// The worked minutes a fork `open_block_segment` row carries in its note, `"<n>m so far"`.
fn so_far(note: Option<&str>) -> Option<u64> {
    note?.strip_suffix("m so far")?.parse().ok()
}

/// One `planner::PlanDiff`, on the kernel's absolute seconds: `(removed, added, moved, drift)`.
type DiffRow = (Vec<String>, Vec<String>, Vec<(String, i64, i64)>, u64);

fn fork_diff(d: &planner::PlanDiff) -> DiffRow {
    (
        d.removed.iter().map(ToString::to_string).collect(),
        d.added.iter().map(ToString::to_string).collect(),
        d.moved
            .iter()
            .map(|(id, a, b)| (id.to_string(), rowwire::kernel_sec(*a), rowwire::kernel_sec(*b)))
            .collect(),
        u64::from(d.drift_min),
    )
}

fn kernel_diff(v: &Value) -> DiffRow {
    let ids = |k: &str| -> Vec<String> {
        v[k].as_array()
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .map(|x| x.as_str().unwrap_or("<not a string>").to_string())
            .collect()
    };
    (
        ids("removed"),
        ids("added"),
        v["moved"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .map(|m| {
                (m["id"].as_str().unwrap_or("<no id>").to_string(),
                 m["from"].as_i64().unwrap_or(-1), m["to"].as_i64().unwrap_or(-1))
            })
            .collect(),
        v["driftMin"].as_u64().unwrap_or(u64::MAX),
    )
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

    /// **W-34: the open block's worked stretch and §9.1's overtime what-if, by value, against
    /// the fork ranked as the kernel ranked it** (D53; README gaps 554, 2519, 2680-2682).
    ///
    /// **The open row.** Fork `open_block_segment` draws `[since, now)` for the block the log
    /// holds open, clipped at the day's end and at an interruption that began after it, `▶`
    /// when nothing is reserved and nothing interrupts, and `"<n>m so far"`. The kernel's
    /// `Planner.openBlockRows` is compared row for row — start, stop, item, the `▶` and the
    /// minutes — on every case, both ways.
    ///
    /// **The what-if.** On a case with a running block the request carries `planner.overtime`
    /// = one block on the running item, which is `App::extend_drops`' only reachable branch
    /// (the TUI asks it of `state.active.id` and nothing else). The kernel answers
    /// `Planner.overtimeDiff` — `diff` of its day and the day with the running estimate grown
    /// — and it is ASSERTED equal, every field, to `planner::diff` of the fork's two days AS
    /// THE SHIPPED TUI BUILDS THEM (estimate grown and `extending` applied, D53). The one
    /// class it is not is **parity P44**, defined by its property: the fork's
    /// `PlanOverrides::apply` also grows the running candidate's `remaining_min`,
    /// `planned_min` and `need_min` (a candidate fact, D34), and on a day where that moves
    /// `diff` beyond what the estimate alone moved, the kernel's answer is ASSERTED to be the
    /// estimate's and the day is counted as P44 (README gaps 2680, 2731). *(Until the W-34
    /// repair this arm asserted against the estimate-only what-if on every day — a
    /// configuration no shipped path builds — and only counted the shipped one.)*
    #[test]
    fn the_kernel_draws_the_open_block_and_answers_the_overtime_what_if_the_fork_answers(
        case in case_strategy()
    ) {
        let w = build(&case);
        let mut req = w.plan_request();
        let active = w.state.active.clone();
        if let Some(a) = &active {
            req["planner"]["overtime"] = planwire::overtime_json(&a.id, 1, None);
        }
        let plan = match kernel_plan(&req) {
            Ok(p) => p,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the kernel refused a day the fork planned: {head}");
                unreachable!()
            }
        };
        let cvec = w.candidates();
        let Some(ps) = kernel_prios(&plan, &cvec) else {
            W34_CENSUS.lock().expect("census")[7] += 1;
            return Ok(());
        };
        let base = w35_fork_plan(&w, &w.state, &cvec, &ps);

        // **The open row, by value, both ways.**
        let kopen: Vec<(i64, i64, String, bool, Option<u64>)> = plan["segments"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .filter(|s| s["kind"] == "block" && s["flags"]["open"] == true)
            .map(|s| (s["start"].as_i64().unwrap_or(-1), s["stop"].as_i64().unwrap_or(-1),
                      s["item"].as_str().unwrap_or_default().to_string(),
                      s["flags"]["current"].as_bool().unwrap_or(false),
                      s["note"]["workedMin"].as_u64()))
            .collect();
        let fopen: Vec<(i64, i64, String, bool, Option<u64>)> = base
            .segments
            .iter()
            .filter(|s| matches!(s.kind, SegKind::Block) && s.flags.open)
            .map(|s| (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end),
                      s.item.as_ref().map(ToString::to_string).unwrap_or_default(),
                      s.flags.current, so_far(s.flags.note.as_deref())))
            .collect();
        prop_assert_eq!(
            &kopen, &fopen,
            "the open block's worked stretch differs from fork `open_block_segment`'s"
        );

        // **The overtime what-if, by value.**
        let (mut otc, mut otids, mut otextra, mut otdrops) = (0u64, 0u64, 0u64, 0u64);
        if let Some(a) = &active {
            let bm = w.cfg.block_min();
            let mut rt = w.state.clone();
            if let Some(x) = rt.active.as_mut() {
                x.est_min = x.est_min.saturating_add(bm);
            }
            let ov = planner::PlanOverrides::new().extending(&a.id, bm);
            // W-35 (D57): the what-if days read the kernel's P46/P47 rule as the base does.
            let rt = w35_p46_state(&w, &rt);
            // W-36 (D60, parity P51): the what-if days run D60's key as the base does.
            let dvec = forkclass::d60_cands(&cvec, &ps);
            let mut alt_est = planner::plan(&w.input(&rt, w.now).with_ranking(&dvec, &ps));
            let mut alt_full = planner::plan(
                &w.input(&rt, w.now).with_ranking(&dvec, &ps).with_overrides(&ov),
            );
            w35_p47_day(&w, &mut alt_est);
            w35_p47_day(&w, &mut alt_full);
            let f_est = fork_diff(&planner::diff(&base, &alt_est));
            let f_full = fork_diff(&planner::diff(&base, &alt_full));
            prop_assert!(!plan["overtime"].is_null(), "the kernel did not answer `overtime`");
            let k = kernel_diff(&plan["overtime"]);
            // THE COMPARAND IS THE SHIPPED CONFIGURATION (D53; W-34 repair, README gap 2731).
            // The shipped what-if is what `App::extend_drops` builds for the running block — the estimate
            // grown AND `PlanOverrides::extending` applied — and until the repair this arm
            // ASSERTED against the estimate-only what-if, which no shipped path builds, while the shipped one was only
            // counted. The one class where the kernel answers otherwise is registered as
            // **parity P44** and defined by its property, never by a list: the fork's
            // `PlanOverrides::apply` grows the running candidate's `remaining_min`,
            // `planned_min` and `need_min`, a CANDIDATE FACT the kernel may not derive (D34), so
            // on a day where that growth moves `diff` beyond what the estimate alone moved
            // (the two fork what-ifs differ) the kernel's answer is the estimate's — asserted, not assumed.
            if f_full == f_est {
                prop_assert_eq!(
                    &k, &f_full,
                    "the kernel's overtime `diff` differs from the shipped TUI's what-if"
                );
            } else {
                prop_assert_eq!(
                    &k, &f_est,
                    "on a parity-P44 day the kernel's overtime `diff` is not the estimate's"
                );
                otextra = 1;
                otdrops = f_full.0.len() as u64;
            }
            otc = 1;
            otids = (k.0.len() + k.1.len() + k.2.len()) as u64;
        } else {
            prop_assert!(
                plan["overtime"].is_null(),
                "the kernel answered `overtime` to a request that asked none"
            );
        }

        let [cases, orows, odays, ocmp, oids, oextra, odrops, noprio] = {
            let mut c = W34_CENSUS.lock().expect("census");
            c[0] += 1;
            c[1] += kopen.len() as u64;
            c[2] += u64::from(!kopen.is_empty());
            c[3] += otc;
            c[4] += otids;
            c[5] += otextra;
            c[6] += otdrops;
            *c
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        if cases >= generated {
            // **Floors** (AGENTS §9.2): a comparison that ran on nothing compared nothing.
            prop_assert!(orows > 0, "no open-block row was compared in {cases} cases");
            prop_assert!(ocmp > 0, "no overtime what-if was compared in {cases} cases");
            prop_assert!(oids > 0, "every overtime `diff` compared was empty in {cases} cases");
        }
        eprintln!(
            "planner_invariants W-34 census: {cases} cases, open-block rows compared {orows} on \
             {odays} days, overtime what-ifs ASSERTED against the shipped TUI's `diff` {ocmp} \
             (ids compared {oids}), of which parity-P44 days (the fork's `extra_min` override \
             moved the answer beyond the estimate's; asserted equal to the estimate's) {oextra}, with \
             {odrops} fork drops on them, cases with no kernel §7 answer {noprio}"
        );
    }
}

// ===========================================================================
// **THE PLAN HASH, COMPARED BY VALUE** — stage 6 W-34 track H (P8's emitter).
//
// `Planner.dayPlan` carries `Planner.planDigest` since W-34: FNV-1a/64 of the
// bytes of `serde_json::to_string(&Vec<Placement>)`, which is what fork
// `DayPlan::hash` digests. Two claims, kept apart because they fail for
// different reasons:
//
//   1. **THE EMITTER** — on EVERY generated day, the kernel's `plan.hash`
//      equals the fork's OWN `DayPlan::hash` run over the KERNEL's rows, rebuilt
//      as `planner::Segment`s. No exemption: this is the bytes, the zone, the
//      instance keys and the multiplier's spelling, whatever the planner did.
//   2. **THE DAY** — the kernel's `plan.hash` equals `day2.hash()`, the fork's
//      day ranked by the kernel's own §7 answer (the shipped wiring, D53). A day
//      whose rows do not agree is classified ROW BY ROW, by a PROPERTY of the
//      fork's row, into the row classes this kernel is recorded as not
//      porting — README gap 554 (`open_block_segment`: the row `open` marks)
//      UNTIL W-34's LAND STEP, which removed it when track D's port made it
//      count zero; gap 550 (the reservation's multiplier: the `current` Block whose kernel
//      twin differs in `multiplier` alone) and gap 551 (the cut's kept breaks: a
//      Break row starting at or after `now`, which the log cannot have written).
//      That is an enumeration a row must JOIN to be exempt, never a list of days
//      (W-27's shape): a row outside the three FAILS by name, a day whose rows
//      agree must agree in its hash too — order included — and each class is
//      counted so the day its gap closes is the day its count reaches zero.
//
// The multiplier is DRAWN as well as left at the default: `Model::default()`
// sizes every candidate at `1.0`, which would test one of zmij's spellings
// (`1.0`) and none of its other layouts (`1.6`, `0.3`, `123.456`).  `1e-6` and
// `1e-5` are drawn too and are NEVER DIGESTED here: a candidate sized that
// small plans to zero minutes and no row carries it (W-34's reuse critic, 52
// of 273 days; README gap 2742).  This comment said the arm tested `1e-6`
// until the W-34 repair; the scientific layouts are pinned in Lean only.
// Setting `model.duration["_default"]` is a WIDENING of what this arm sees
// (D46); the arms above are untouched.
// ===========================================================================


/// The census: cases; days with no kernel §7 answer; days compared with the
/// kernel-ranked fork; of those, equal hashes; equal rows; rows the emitter
/// digested; drawn multipliers; fork open-block rows the kernel's day holds
/// (gap 554's class until W-34's land step removed it); reservation multipliers
/// (550); kept breaks (551); days a class explained; batch rows digested;
/// days `deferred` was compared; deferred ids compared; days `deferred` was
/// compared whole on a day carrying an open-block row; days with a drawn break;
/// days whose rest debt was non-zero; kernel rows digested with a multiplier other
/// than `1.0` (W-34 repair, README gap 2742 -- a DRAW is not a DIGEST).
/// (W-37 track H added a nineteenth, the days README gap 3281's declared class explained; W-38's
/// land step deleted it with the class, because track R's `Planner.stepOneOrder` draws an
/// interruption among the walls where fork `collect_walls` sorts it and the class counted 0 on
/// every run -- README gap 3394. The seed that found it, `ef4f4091…`, stays in the regressions
/// file, where it now asks for EQUAL hashes.)
static HASH_CENSUS: Mutex<[u64; 18]> = Mutex::new([0; 18]);

/// Fork `parse_instance_key` (`planner.rs:2375`, private to `tm-core::planner`),
/// for the `inst` text a kernel row carries.
fn instance_key_of(s: &str) -> Option<tm_core::model::InstanceKey> {
    if let Some(n) = s.strip_prefix('#') {
        return n.parse::<u32>().ok().map(tm_core::model::InstanceKey::Nth);
    }
    NaiveDate::parse_from_str(s, "%Y-%m-%d").ok().map(tm_core::model::InstanceKey::Date)
}

/// A kernel `{num, den}` multiplier as the double it was written from: the host
/// sends the double's shortest `Display` digits over `10^places` (`dec` above),
/// so the decimal is rebuilt digit for digit and parsed — correctly rounded —
/// back to that double.
fn f64_of_pair(v: &Value) -> Option<f64> {
    let num = v["num"].as_u64()?;
    let den = v["den"].as_u64()?;
    let places = den.to_string().len() - 1;
    if den != 10u64.pow(places as u32) {
        return Some(num as f64 / den as f64);
    }
    let digits = format!("{num:0>width$}", width = places + 1);
    let (int, frac) = digits.split_at(digits.len() - places);
    format!("{int}.{frac}0").parse::<f64>().ok()
}

/// **The kernel's rows as the fork's own `Segment`s**, so the FORK's
/// `DayPlan::hash` can be run over them. Every digested field is carried; the
/// marks are left at their defaults because the fork does not digest them.
fn fork_rows_of_kernel(plan: &Value, tz: Tz) -> Vec<Segment> {
    use chrono::TimeZone;
    let at = |v: &Value| {
        tz.timestamp_opt(v.as_i64().expect("a second") - rowwire::EPOCH_FROM_CE, 0)
            .single()
            .expect("an instant the zone reads")
    };
    plan["segments"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default()
        .iter()
        .map(|s| {
            let kind = match s["kind"].as_str().expect("a kind") {
                "block" => SegKind::Block,
                "batch" => SegKind::Batch(
                    s["batch"].as_array().map(Vec::as_slice).unwrap_or_default().iter()
                        .map(|v| Id::new(v.as_str().expect("an id"))).collect(),
                ),
                "break" => SegKind::Break,
                "routine" => SegKind::Routine,
                "wall" => SegKind::Wall,
                "rest" => SegKind::Rest,
                "optional" => SegKind::Optional,
                "wind-down" => SegKind::WindDown,
                "sleep" => SegKind::Sleep,
                "lost" => SegKind::Lost,
                other => panic!("the kernel placed a `{other}` row, which no fork kind is"),
            };
            Segment {
                start: at(&s["start"]),
                end: at(&s["stop"]),
                kind,
                energy: s["energy"].as_u64().map(|e| e as u8),
                item: s["item"].as_str().map(Id::new),
                instance: s["inst"]["inst"].as_str().and_then(instance_key_of),
                flags: planner::SegFlags {
                    planned_min: s["planned"].as_u64().map(|p| p as u32),
                    multiplier: if s["mult"].is_null() { None } else { f64_of_pair(&s["mult"]) },
                    ..planner::SegFlags::default()
                },
            }
        })
        .collect()
}

/// One row's digested fields, as serde spells them (`Placement`'s eight, in its
/// order) — the key two rows are matched by.
fn placement_key(s: &Segment) -> String {
    serde_json::to_string(&(
        &s.start, &s.end, &s.kind, s.energy, &s.item, &s.instance, s.flags.planned_min,
        s.flags.multiplier,
    ))
    .expect("a placement serialises")
}

/// The rows of `a` that `b` does not hold, as a MULTISET difference: a row two
/// sides both hold twice is matched twice, and a third copy is left over.
fn rows_not_in<'a>(a: &'a [Segment], b: &[Segment]) -> Vec<&'a Segment> {
    let mut left: BTreeMap<String, usize> = BTreeMap::new();
    for s in b {
        *left.entry(placement_key(s)).or_default() += 1;
    }
    a.iter()
        .filter(|s| match left.get_mut(&placement_key(s)) {
            Some(n) if *n > 0 => {
                *n -= 1;
                false
            }
            _ => true,
        })
        .collect()
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

    /// **The kernel's plan hash is the fork's `DayPlan::hash`**, by value.
    #[test]
    fn the_kernel_hashes_the_day_the_fork_hashes(
        case in case_strategy(),
        mult in prop::sample::select(vec![
            None, Some(1.6), Some(0.25), Some(2.0), Some(1.125), Some(0.3), Some(0.000001),
            Some(0.00001), Some(0.1 + 0.2), Some(123.456),
        ]),
        brk in prop::option::of((5u32..=30, 0u32..=40)),
        errands in any::<bool>(),
    ) {
        // **ERRANDS, DRAWN** (W-36 land, README gap 3126; gap 2935's named fix): the batch
        // floor below counted 0, 5 and 3 batch rows over three ~280-case runs of this arm and
        // failed on the 0 -- the generator reaches a batch only when two small items of one
        // `ci` land unplaced together. On half the cases with at least two items the first two
        // are made twenty-minute errands of the first item's `ci` (a day the generator could
        // already draw, drawn more often). No assertion, floor or shared generator changes.
        let mut case = case;
        if errands && case.items.len() >= 2 {
            let ci = 2 + case.items[0].ci % 2;
            for sp in case.items.iter_mut().take(2) {
                sp.small = Some(20);
                sp.ci = ci;
            }
        }
        let mut w = build(&case);
        w.set_multiplier(mult);
        let tz = w.cfg.tz;
        // **A BREAK IN TODAY'S LOG** (W-34, README gap 2511) — planned 5-30 minutes, taken 0-40,
        // so it can run short, exact or long; `plangen`'s `World::log_a_break` says where and why
        // (one definition since W-37, shared with the class draw).
        let drew_break = w.log_a_break(&case, brk);
        let req = w.plan_request();
        let plan = match kernel_plan(&req) {
            Ok(p) => p,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the kernel refused a day the fork planned: {head}");
                unreachable!()
            }
        };
        let khash = plan["hash"].as_str().expect("plan.hash").to_string();
        let fork = planner::plan(&w.input(&w.state, w.now));
        let krows = fork_rows_of_kernel(&plan, tz);
        let mut kday = DayPlan::empty(fork.date, fork.window, fork.budget_blocks);
        kday.segments = krows.clone();
        // **1. THE EMITTER**, on every day.
        prop_assert_eq!(
            &khash, &kday.hash(),
            "the kernel's digest of its own {} rows is not the fork's `DayPlan::hash` of \
             them — the BYTES differ, not the day", krows.len()
        );
        // **2. THE DAY**, against the kernel-ranked fork (D53).
        let cvec = w.candidates();
        let day2 = kernel_prios(&plan, &cvec)
            .map(|ps| w35_fork_plan(&w, &w.state, &cvec, &ps));
        let (mut compared, mut same, mut rows_agree, mut explained) = (0u64, 0u64, 0u64, 0u64);
        let (mut c554, mut c550, mut c551) = (0u64, 0u64, 0u64);
        let (mut set_aside, mut def_ids, mut rest_debt) = (0u64, 0u64, false);
        if let Some(d2) = day2.as_ref() {
            compared = 1;
            let fonly = rows_not_in(&d2.segments, &krows);
            let konly = rows_not_in(&krows, &d2.segments);
            // **GAP 554's CLASS IS GONE** (W-34's land step). Track D composed fork
            // `open_block_segment` into `Planner.dayRows`, and on the merged tree the
            // class counted ZERO rows; so a fork open-block row the kernel's day lacks is
            // no longer explained by anything and FAILS below by name. `c554` counts the
            // fork's open-block rows the kernel's day HOLDS, so the census can show the case
            // ran (`n554 > 0` is a floor).
            c554 = d2.segments.iter()
                .filter(|s| s.flags.open && matches!(s.kind, SegKind::Block))
                .count() as u64
                - fonly.iter()
                    .filter(|f| f.flags.open && matches!(f.kind, SegKind::Block))
                    .count() as u64;
            // **GAPS 551 AND 550 ARE NO LONGER CLASSES EITHER** (W-37's land step, README gap
            // 3206). Until W-37 a fork Break row from `now` (the cut's kept breaks, gap 551)
            // and a fork current Block whose kernel twin differed only in its multiplier (gap
            // 550) were passed over here; track R drew both, three runs counted each class
            // ZERO, and so neither is explained by anything now: every row of either day must
            // be a row of the other. `c551` and `c550` count the rows of the two kinds the
            // kernel's day HOLDS — compared by value, as `c554` counts its own.
            c551 = d2.segments.iter()
                .filter(|s| matches!(s.kind, SegKind::Break) && s.start >= w.now)
                .count() as u64;
            c550 = d2.segments.iter()
                .filter(|s| s.flags.current && matches!(s.kind, SegKind::Block) && s.flags.multiplier.is_some())
                .count() as u64;
            for f in &fonly {
                prop_assert!(
                    false,
                    "the fork's day holds a row the kernel's does not (no class explains one \
                     since W-37): {}", placement_key(f)
                );
            }
            for k in &konly {
                prop_assert!(
                    false,
                    "the kernel's day holds a row the fork's does not: {}", placement_key(k)
                );
            }
            // **§8.2 STEP 8's LAST TWO FIELDS, BY VALUE** (W-34, README gap 2511). `deferred`
            // is a set of ids (the fork pushes each once); it reads the day's `assigned`, which
            // the fork's open-block row adds its item to. Until W-34's land step that item was
            // set aside from the kernel's list, because the kernel drew no open-block row; the
            // kernel draws it now (the loop above fails if it does not), so NOTHING is set
            // aside and the two lists are compared whole. The counter below counts the days the
            // compared lists read an open-block row's item on both sides. `restDebtMin` reads
            // no row and is compared on every day.
            let kd = &plan["diagnostics"];
            let mut kdef: Vec<String> = kd["deferred"].as_array().map(Vec::as_slice)
                .unwrap_or_default().iter()
                .map(|v| v.as_str().unwrap_or("<not a string>").to_string())
                .collect();
            set_aside = u64::from(c554 > 0);
            let mut fdef: Vec<String> =
                d2.diagnostics.deferred.iter().map(ToString::to_string).collect();
            kdef.sort();
            fdef.sort();
            prop_assert_eq!(
                &kdef, &fdef,
                "§8.2 step 8's `deferred` differs from the kernel-ranked fork's"
            );
            def_ids = kdef.len() as u64;
            prop_assert_eq!(
                kd["restDebtMin"].as_u64(), Some(u64::from(d2.diagnostics.rest_debt_min)),
                "§8.2 step 8's `restDebtMin` differs from the kernel-ranked fork's"
            );
            rest_debt = d2.diagnostics.rest_debt_min > 0;
            if fonly.is_empty() && konly.is_empty() {
                rows_agree = 1;
                // **Rows that agree must hash alike — in the same ORDER** (since W-38's land
                // step on every day: README gap 3281's interruption among the walls is drawn
                // where the fork sorts it, and its declared class is gone, gap 3394).
                prop_assert_eq!(
                    &khash, &d2.hash(),
                    "the two days hold the same rows and hash differently: the order differs"
                );
            } else {
                explained = 1;
            }
            same = u64::from(khash == d2.hash());
        }
        let batches = krows.iter().filter(|s| matches!(s.kind, SegKind::Batch(_))).count() as u64;
        let [cases, noprio, cmp, eq, agree, digested, drawn, n554, n550, n551, nexpl, nbatch,
             ndefdays, ndefids, naside, nbrk, nrest, nmult] = {
            let mut c = HASH_CENSUS.lock().expect("census");
            c[0] += 1;
            c[1] += 1 - compared;
            c[2] += compared;
            c[3] += same;
            c[4] += rows_agree;
            c[5] += krows.len() as u64;
            c[6] += u64::from(mult.is_some());
            c[7] += c554;
            c[8] += c550;
            c[9] += c551;
            c[10] += explained;
            c[11] += batches;
            c[12] += compared;
            c[13] += def_ids;
            c[14] += set_aside;
            c[15] += u64::from(drew_break);
            c[16] += u64::from(rest_debt);
            c[17] += krows
                .iter()
                .filter(|s| s.flags.multiplier.is_some_and(|m| m != 1.0))
                .count() as u64;
            *c
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        if cases >= generated {
            // **THE FLOORS** — every comparison above sits behind something a run
            // can skip, so each is shown to have run (AGENTS §9.2).
            prop_assert!(digested > cases, "the emitter digested {digested} rows in {cases} cases");
            prop_assert!(cmp > 0, "no day was compared with the kernel-ranked fork in {cases} cases");
            prop_assert!(eq > 0, "no kernel hash equalled the fork's in {cases} cases");
            prop_assert!(agree > 0, "no day's rows agreed with the fork's in {cases} cases");
            prop_assert!(drawn > 0, "no multiplier was drawn in {cases} cases");
            // A DRAW IS NOT A DIGEST (W-34 repair, README gap 2742): W-34's reuse critic found
            // that on every day drawing `1e-5` or `1e-6` no kernel row carried a multiplier --
            // a candidate sized that small plans to zero minutes and is placed nowhere -- so
            // `drawn > 0` held while zmij's scientific layout reached no digest. This floor
            // counts what the emitter DIGESTED; the scientific layouts are pinned in Lean
            // (`Planner.multText_is_zmijs`, `Planner.the_placement_bytes_are_the_forks`).
            prop_assert!(nmult > 0, "no row was digested at a multiplier other than 1.0 in {cases} cases");
            prop_assert!(nbatch > 0, "no batch row was digested in {cases} cases");
            prop_assert!(ndefids > 0, "no DEFERRED id was compared in {cases} cases");
            prop_assert!(nbrk > 0, "no break was drawn in {cases} cases");
            prop_assert!(nrest > 0, "no non-zero REST DEBT was compared in {cases} cases");
            prop_assert!(n554 > 0, "no fork open-block row was matched by a kernel row in {cases} cases");
        }
        eprintln!(
            "planner_invariants hash census: {cases} cases; the EMITTER compared on all \
             {cases} ({digested} kernel rows digested, {nbatch} of them batches, {drawn} \
             days at a drawn multiplier, {nmult} rows DIGESTED at a multiplier other than 1.0); the DAY compared with the kernel-ranked fork on \
             {cmp} ({noprio} with no kernel §7 answer): hashes EQUAL {eq}, rows agree {agree}, \
             days whose rows differ {nexpl} (every one fails since W-37) — reservation multipliers \
             (gap 550, NO LONGER A CLASS) the kernel's day holds {n550}, kept breaks (gap 551, NO \
             LONGER A CLASS) {n551}; open-block rows (gap 554, NO LONGER A \
             CLASS) the kernel's day holds {n554}; STEP 8's `deferred` compared on {ndefdays} \
             days ({ndefids} ids, whole, on {naside} days carrying an open-block row), \
             `restDebtMin` on {ndefdays} ({nrest} non-zero, {nbrk} days with a drawn break)"
        );
    }
}

/// **The P56 arm's census** (W-37 repair, README gap 3332): `[cases, days a meeting was
/// logged as passed (D61's marks), of them with a typed pause longer than the wall, days
/// compared, Pause segments the replay holds on those days, of them overlapping a wall,
/// paused rows the kernel-ranked fork drew on those days, cases with no kernel §7 answer]`.
static P56_CENSUS: Mutex<[u64; 8]> = Mutex::new([0; 8]);

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256),
        max_shrink_iters: 2_000,
        ..ProptestConfig::default()
    })]

    /// **P56, differentially: the kernel's `Planner.pastSpans` and the fork's `cut_out` draw
    /// the same rows on a day whose log holds a meeting's pause** (W-37 repair, README gap
    /// 3332). Track T wrote the kernel's cut and changed the in-tree fork to agree (P56), and
    /// until this arm the two were never run on one day: the generator logged no `pause`, so
    /// each was tested only against itself — the W-37 critic's finding, a claim of having
    /// checked (README W-37 track T §1) that was never made. Here a running block passes a
    /// meeting, logged as the binary's housekeeping logs it (`plangen`'s
    /// `timer_marks`, which since README gap 3340 every generated world logs) — on half the
    /// draws with a typed pause ten minutes
    /// longer than the wall at each end, so the cut leaves two pieces — and EVERY row of
    /// either day must be a row of the other, against the kernel-ranked fork (D53).
    #[test]
    fn the_kernel_cuts_a_meeting_out_of_a_pause_as_the_fork_does(
        case in case_strategy(),
        typed in any::<bool>(),
        force in any::<bool>(),
    ) {
        // **A PASSED MEETING, DRAWN** (the errands move, README gap 3126): the shared generator
        // runs a block across a meeting that has ended on ~6 of 256 cases. On half the cases the
        // running block is started half an hour before a wall that begins after the last `done`
        // and ends at least eleven minutes before `now` (a one-hour wall on the hour, added when
        // the calendar has none there) — a day the generator can already draw (it draws `ago`
        // and walls freely), drawn more often. An interruption drawn on the same case is left
        // out of THIS draw (§9's other event); the shared generator is untouched.
        let mut case = case;
        if force && !case.items.is_empty() {
            let tz = tm_core::config::Config::default().tz;
            let now = case.now(tz);
            let floor = case.arrival(tz) + Duration::minutes(i64::from(case.done(tz)) * 60 - 5) + Duration::minutes(1);
            // The first whole hour at least eleven minutes after `floor` whose hour-long wall
            // ends eleven minutes before `now`: an existing wall there is used as it is, and
            // otherwise a one-hour wall is added to the calendar (a wall the generator draws).
            let first = (floor + Duration::minutes(11 + 59)).format("%H").to_string().parse::<u32>().unwrap_or(24);
            for h in first..23 {
                let lo = local_dt(tz, date(), NaiveTime::from_hms_opt(h, 0, 0).expect("time"));
                if lo + Duration::minutes(60 + 11) > now {
                    break;
                }
                if !case.walls.iter().any(|x| x.hour == h) {
                    case.walls.push(WallSpec { hour: h, hours: 1 });
                }
                let start = (lo - Duration::minutes(30)).max(floor);
                let ago = u32::try_from((now - start).num_minutes()).unwrap_or(0);
                let est = case.active.map_or(60, |a| a.2);
                case.active = Some((0, ago, est));
                case.interrupt = None;
                break;
            }
        }
        let w = build_with(&case, tm_core::config::Config::default(), typed);
        let tz = w.cfg.tz;
        // Every generated world logs the meetings its running block passed, as the
        // binary does (`plangen::timer_marks`, README gap 3340); `typed` draws the pause
        // longer than the first meeting.
        let marks = timer_marks(&case, &w.walls_today(), tz, typed);
        let drew = (!marks.marks.is_empty()).then_some(marks.typed);
        let (mut logged, mut longer, mut compared, mut pauses, mut over, mut paused_rows, mut noprio) =
            (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        if let Some(t) = drew {
            logged = 1;
            longer = u64::from(t);
            let req = w.plan_request();
            let plan = match kernel_plan(&req) {
                Ok(p) => p,
                Err(raw) => {
                    let head: String = raw.chars().take(400).collect();
                    prop_assert!(false, "the kernel refused a day the fork planned: {head}");
                    unreachable!()
                }
            };
            let cvec = w.candidates();
            match kernel_prios(&plan, &cvec) {
                None => noprio = 1,
                Some(ps) => {
                    compared = 1;
                    let d2 = w35_fork_plan(&w, &w.state, &cvec, &ps);
                    let krows = fork_rows_of_kernel(&plan, tz);
                    for f in rows_not_in(&d2.segments, &krows) {
                        prop_assert!(false, "P56: the fork's day holds a row the kernel's does not: {}", placement_key(f));
                    }
                    for k in rows_not_in(&krows, &d2.segments) {
                        prop_assert!(false, "P56: the kernel's day holds a row the fork's does not: {}", placement_key(k));
                    }
                    let walls = w.walls_today();
                    let segs: Vec<(DateTime<Tz>, DateTime<Tz>)> = w
                        .replay
                        .day(date())
                        .map(|d| {
                            d.segments
                                .iter()
                                .filter(|g| matches!(g.kind, tm_core::log::SegmentKind::Pause { .. }))
                                .map(|g| (g.start.with_timezone(&tz), g.end.with_timezone(&tz)))
                                .collect()
                        })
                        .unwrap_or_default();
                    pauses = segs.len() as u64;
                    over = segs.iter().filter(|(a, b)| walls.iter().any(|(lo, hi)| a < hi && lo < b)).count() as u64;
                    paused_rows = d2
                        .segments
                        .iter()
                        .filter(|g| matches!(g.kind, SegKind::Lost) && g.flags.note.as_deref() == Some("paused"))
                        .count() as u64;
                }
            }
        }
        let [cases, nlogged, nlonger, ncmp, npause, nover, nrows, nnoprio] = {
            let mut c = P56_CENSUS.lock().expect("census");
            for (i, v) in [1, logged, longer, compared, pauses, over, paused_rows, noprio].into_iter().enumerate() {
                c[i] += v;
            }
            *c
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        if cases >= generated {
            // **Floors** (AGENTS §9.2): the cut compared on no day is compared on nothing.
            prop_assert!(ncmp > 0, "no day with a logged meeting was compared in {cases} cases");
            prop_assert!(nover > 0, "no Pause segment over a wall reached the comparison in {cases} cases");
            prop_assert!(nlonger > 0, "no typed pause longer than its wall was drawn in {cases} cases");
            prop_assert!(nrows > 0, "no paused row the cut LEFT was compared in {cases} cases");
        }
        eprintln!(
            "planner_invariants P56 census: {cases} cases; a passed meeting logged on {nlogged} ({nlonger} \
             with a typed pause longer than the wall); compared with the kernel-ranked fork on {ncmp} \
             ({nnoprio} with no kernel §7 answer); the replay's Pause segments on them {npause}, {nover} \
             over a wall; paused rows both days drew {nrows}"
        );
    }
}

/// **A sub-second `now` moves the fork's day, and the kernel's does not move**
/// (W-34, parity **P43**).
///
/// `Planner.Seg` is on whole seconds — `Look.Slot`'s representation since P0
/// (README gap 256) — and the kernel reads the request's `at` to the nanosecond
/// but cuts and places every row from `now`'s second. The fork carries `now` as it
/// is: `Local::now()` in the shipped binary has a fraction, the cut starts there
/// and carries the fraction to every slot boundary after it, and chrono
/// serialises it (SecondsFormat::AutoSi), so `DayPlan::hash` digests bytes the
/// kernel's digest cannot write. The generator above draws `now` on the minute
/// and so never sees this; here `now` is half a second past one.
///
/// **DRIVEN, and it is more than bytes**: the first version of this test asserted
/// that the fork's rows, truncated to the second, ARE the kernel's — and it failed.
/// The fork's last slot runs `15:30:00.5`–`16:00`, half a second short of
/// `min_last_block_min`, and §8.2 step 3 drops it; the kernel's runs `15:30`–`16:00`,
/// exactly the minimum, and keeps it as Rest. So a half second of the verb's clock
/// changes the fork's SLOT GEOMETRY. Asserted exactly as found: the fork has
/// fractional rows; every fork row, truncated, is a kernel row; the kernel's only
/// other row is that one last Rest slot, ending at the window's end and as long as
/// the minimum; and the two hashes differ.
#[test]
fn a_sub_second_now_moves_the_forks_day_and_not_the_kernels() {
    let case = Case {
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
    };
    let mut w = build(&case);
    // **Twenty minutes later than the case's `now`** (W-37 repair, README gap 3340): the
    // finding needs the day's LAST slot to be exactly `min_last_block_min` long. Until the
    // repair the world stored `[07:00, 16:00]` while its log's `arrive` said `[07:00, 15:00]`
    // (a cache the binary does not hold), and 08:30's cut ended in a 15:30–16:00 slot; in the
    // world `tm arrive` leaves, the window ends at 15:00, and it is 08:50's cut that ends in
    // 14:30–15:00. The phenomenon asserted below is unchanged.
    w.now += Duration::minutes(20) + Duration::milliseconds(500);
    let tz = w.cfg.tz;
    let plan = kernel_plan(&w.plan_request()).expect("the kernel plans the day");
    let khash = plan["hash"].as_str().expect("plan.hash").to_string();
    let krows = fork_rows_of_kernel(&plan, tz);
    let cvec = w.candidates();
    let ps = kernel_prios(&plan, &cvec).expect("the kernel answers §7 for this day");
    let day2 = planner::plan(&w.input(&w.state, w.now).with_ranking(&cvec, &ps));
    let fractional = day2
        .segments
        .iter()
        .filter(|s| s.start.nanosecond() != 0 || s.end.nanosecond() != 0)
        .count();
    assert!(fractional > 0, "the fork's day held no row at the sub-second `now`");
    let ftrunc: Vec<Segment> = day2
        .segments
        .iter()
        .map(|s| {
            let mut t = s.clone();
            t.start = t.start.with_nanosecond(0).expect("a whole second");
            t.end = t.end.with_nanosecond(0).expect("a whole second");
            t
        })
        .collect();
    let fonly = rows_not_in(&ftrunc, &krows);
    let konly = rows_not_in(&krows, &ftrunc);
    assert!(
        fonly.is_empty(),
        "a fork row, truncated to its second, is not a kernel row: {:?}",
        fonly.iter().map(|s| placement_key(s)).collect::<Vec<_>>()
    );
    let min_last = i64::from(w.cfg.day.min_last_block_min);
    assert!(
        konly.len() == 1
            && matches!(konly[0].kind, SegKind::Rest)
            && konly[0].end == day2.window.1
            && (konly[0].end - konly[0].start).num_minutes() == min_last,
        "the kernel's extra rows are not the one last slot the fork's fractional cut left \
         short: {:?}",
        konly.iter().map(|s| placement_key(s)).collect::<Vec<_>>()
    );
    assert_ne!(khash, day2.hash(), "the fork's fraction reached no digested byte");
    eprintln!(
        "planner_invariants sub-second now: {} of the fork's {} rows carry the fraction; the \
         kernel's one extra row {}; kernel {khash}, fork {}",
        fractional, day2.segments.len(), placement_key(konly[0]), day2.hash()
    );
}

// ===========================================================================
// **W-35 (track K): D57 — §9's running break, the overtime block and a wall on `now`**
//
// The owner's D57 (README gap 2740) fixes three §9 behaviours in the KERNEL before R3, each a
// registered divergence from fork 4748911: **P45** a running break (`state.break`) is a Break row
// nothing is scheduled over; **P46** in overtime the running block keeps its block (the fork's
// `active_run` refused to reserve); **P47** a wall on `now` pauses the running block (the fork drew
// the worked stretch across it).  The fork now disagrees BY DESIGN on those days, so they are
// asserted against the KERNEL's own rule, which this block states once as a comparand —
// `w35_fork_plan`: the fork as the shipped binary runs it (D53, kernel-ranked) with P46 and P47
// applied by their PROPERTIES, never by a list of cases.  The earlier arms call it in place of
// `planner::plan` wherever they compare a day; on every day that is neither P46 nor P47 it is
// `planner::plan` exactly.  P45 has no fork analogue at all (fork `planner::plan` reads no
// `runtime.break_`), so the arm below asserts its rule directly and counts the fork's disagreement.
// ===========================================================================


/// **The fork's `worked` for the running block** — fork `active_run`'s own reading: the log's open
/// block when it is this item's (`OpenBlock::worked_min_at`), the clock since `started` otherwise.
fn w35_fork_worked(w: &World, st: &RuntimeState) -> Option<u32> {
    let a = st.active.as_ref()?;
    let started = local_dt(w.cfg.tz, date(), a.started);
    Some(
        w.replay
            .open_block
            .as_ref()
            .filter(|b| b.id == a.id.as_str())
            .map(|b| b.worked_min_at(w.now.fixed_offset()))
            .unwrap_or_else(|| (w.now - started).num_minutes().max(0) as u32),
    )
}

/// **P46, by its property**: the running block is in overtime — not paused, no break running,
/// its worked minutes at or past its estimate, which is fork `active_run`'s `left == 0` refusal.
///
/// **Decided off the STATE, never off the kernel's answer** (W-35 repair, README gap 2921).  This
/// read `plan` until the repair and required the KERNEL to have reserved: on an overtime day where
/// the kernel regressed to the fork's refusal the day was not P46, and it was compared with plain
/// `planner::plan`, which agreed with the regression.  Both the fork and the kernel refuse a
/// paused block, and the kernel refuses under a running break (P45 pauses it), so neither is a
/// P46 day by this property either.
fn w35_is_p46(w: &World, st: &RuntimeState) -> bool {
    let (Some(a), Some(worked)) = (st.active.as_ref(), w35_fork_worked(w, st)) else {
        return false;
    };
    let breaking = st.break_.as_ref().is_some_and(|b| b.started.is_some());
    !a.paused && !breaking && worked >= a.est_min
}

/// **P46's comparand state**: `state.active`'s estimate raised by a whole day of minutes, so fork
/// `active_run`'s `left` binds nowhere and the FORK reserves `min(free stretch end,
/// current_block_end)` from its own walls, wind-down and block boundary — the P46 rule
/// (`Planner.PlanReq.activeStop_in_overtime`), computed by the other implementation.  Unchanged
/// off P46.
///
/// **It used to raise the estimate to the KERNEL'S reservation stop** — `worked + ⌈(stop − now) /
/// 60⌉` with `stop` read out of the answer under test — so the comparand reproduced whatever span
/// the kernel emitted, and a kernel reservation cut short could not fail it: the W-35 auditor cut
/// every P46 reservation to `now + 60 s` and the P46 assertion fired on none of 67 (README gap
/// 2921).  The day's length is `Look.maxDayMin`'s bound on an estimate, and no block boundary or
/// free stretch lies further from `now` than the end of the day.
fn w35_p46_state(w: &World, st: &RuntimeState) -> RuntimeState {
    let mut out = st.clone();
    if w35_is_p46(w, st) {
        let worked = w35_fork_worked(w, st).unwrap_or(0);
        if let Some(a) = out.active.as_mut() {
            a.est_min = worked.saturating_add(24 * 60);
        }
    }
    out
}

/// **P46's row, as the kernel writes it**: the reservation's `planned` and note carry the fork's
/// own saturating `left`, which is 0 in overtime (`running · 0m left`), not the raised estimate's.
fn w35_p46_row(w: &World, day: &mut DayPlan) {
    for s in day.segments.iter_mut().filter(|s| {
        matches!(s.kind, SegKind::Block) && s.flags.current && s.energy.is_none() && s.start == w.now
    }) {
        s.flags.planned_min = Some(0);
        s.flags.note = Some("running · 0m left".to_string());
    }
}

/// **P47, by its property, on the fork's own day**: when a wall's blocked span (its run-up and its
/// event, joined by item) covers `now`, every open Block row loses its `▶` and is clipped at the
/// earliest start, after its own, of that wall's rows — `Planner.PlanReq.pauseRows`' wall half.
/// Returns whether the day is a P47 day: a wall on `now` and an open row.
fn w35_p47_day(w: &World, day: &mut DayPlan) -> bool {
    let now = w.now;
    let mut spans: BTreeMap<String, (DateTime<Tz>, DateTime<Tz>)> = BTreeMap::new();
    for s in day.segments.iter().filter(|s| matches!(s.kind, SegKind::Wall)) {
        let id = s.item.as_ref().map(ToString::to_string).unwrap_or_default();
        let e = spans.entry(id).or_insert((s.start, s.end));
        e.0 = e.0.min(s.start);
        e.1 = e.1.max(s.end);
    }
    let on_now: Vec<DateTime<Tz>> = day
        .segments
        .iter()
        .filter(|s| matches!(s.kind, SegKind::Wall))
        .filter(|s| {
            let id = s.item.as_ref().map(ToString::to_string).unwrap_or_default();
            spans.get(&id).is_some_and(|(a, b)| *a <= now && now < *b)
        })
        .map(|s| s.start)
        .collect();
    if on_now.is_empty() {
        return false;
    }
    w35_pause_open_rows(day, &on_now)
}

/// **What pausing does to the worked stretch** — `Planner.PlanReq.openStop` over
/// `Planner.PlanReq.pauseRows`, and `interrupted`'s `▶`: every open Block row loses its `▶` and is
/// clipped at the earliest of `starts` after its own.  Returns whether any open row was paused.
fn w35_pause_open_rows(day: &mut DayPlan, starts: &[DateTime<Tz>]) -> bool {
    let mut hit = false;
    for s in day.segments.iter_mut().filter(|s| matches!(s.kind, SegKind::Block) && s.flags.open) {
        hit = true;
        s.flags.current = false;
        if let Some(cut) = starts.iter().filter(|a| **a > s.start).min().copied() {
            if cut < s.end {
                s.end = cut;
            }
        }
    }
    hit
}

/// **The fork, as the kernel's D57 rule reads it**: `planner::plan` over the kernel's ranking
/// (D53), with P46's comparand state and row and P47's pause — each applied only where its
/// property holds, so on every other day this IS `planner::plan`.
fn w35_fork_plan(
    w: &World,
    st: &RuntimeState,
    cvec: &[Candidate],
    ps: &[Prio],
) -> DayPlan {
    let st2 = w35_p46_state(w, st);
    // W-36 (D60, parity P51): the fork runs D60's key through its own two order fields.
    let dvec = forkclass::d60_cands(cvec, ps);
    let mut d = planner::plan(&w.input(&st2, w.now).with_ranking(&dvec, ps));
    let is46 = w35_is_p46(w, st);
    if is46 {
        w35_p46_row(w, &mut d);
    }
    let is47 = w35_p47_day(w, &mut d);
    let mut c = W35_COMPARAND.lock().expect("census");
    c[0] += 1;
    c[1] += u64::from(is46);
    c[2] += u64::from(is47);
    d
}

/// **How often the comparand departed from `planner::plan`**, over every arm that calls it —
/// `[days, P46 days, P47 days]`.  Read by the W-35 census line, so the earlier arms' share of the
/// three classes is printed rather than assumed.
static W35_COMPARAND: Mutex<[u64; 3]> = Mutex::new([0; 3]);

/// **W-35's census**: `[cases, break days (P45), of them still running at now, of them overrun,
/// P45 days where the SHIPPED fork scheduled over the break, overtime days (P46), P46 days whose
/// shipped fork day differs from the kernel's rule, wall-on-now days (P47), P47 days whose shipped
/// fork open row runs past the wall's start, assigned rows compared against the D57 comparand,
/// cases with no kernel §7 answer]`.
static W35_CENSUS: Mutex<[u64; 11]> = Mutex::new([0; 11]);

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256),
        max_shrink_iters: 2_000,
        ..ProptestConfig::default()
    })]

    /// **D57's three rows, on generated days, against the kernel's own rule** (W-35 track K,
    /// parity P45-P47, README gap 2740).  Every case also asserts that the kernel's assigned rows
    /// are the D57 comparand's, so the rest of the day is still compared against the fork.
    #[test]
    fn the_kernel_keeps_the_break_the_overtime_block_and_the_wall_pause(
        case in case_strategy(),
        brk in prop::option::of((0u32..=40, 5u32..=30, prop::sample::select(vec!["walk", "seat", "bed", "phone"]))),
        over in prop_oneof![1 => Just(false), 1 => Just(true)],
    ) {
        let mut w = build(&case);
        // **P46, drawn and not only met** (W-35 land step, README gap 2910): the `n46 > 0` floor
        // below failed at the merge on a run that drew none — `plangen`'s `World::force_overtime`.
        w.force_overtime(&case, over, brk.is_some());
        let tz = w.cfg.tz;
        let now_sec = rowwire::kernel_sec(w.now);
        // **P45: a running break**, drawn `ago` minutes before `now` for `planned` minutes — the
        // host's `tm break` pauses a running block, so this does too; since W-37 it starts after
        // the last `start`/`done` the log holds, which is when `tm break` can have run
        // (`plangen`'s `World::run_a_break`, owner D64(b)).
        let mut drew = None;
        let drew_at: Option<DateTime<Tz>> = w.run_a_break(&case, brk);
        if let (Some(t), Some((_, planned, place))) = (drew_at, brk) {
            drew = Some((rowwire::kernel_sec(t), i64::from(planned), place));
        }
        // `state.break` and the paused block reach the request through `planwire::state_json`,
        // off `w.state` — never spelled here (W-35 repair, README gap 2922).
        let req = w.plan_request();
        let plan = match kernel_plan(&req) {
            Ok(p) => p,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the kernel refused a day the fork planned: {head}");
                unreachable!()
            }
        };
        let cvec = w.candidates();
        let Some(ps) = kernel_prios(&plan, &cvec) else {
            W35_CENSUS.lock().expect("census")[10] += 1;
            return Ok(());
        };
        let shipped = planner::plan(&w.input(&w.state, w.now).with_ranking(&cvec, &ps));
        let d57 = w35_fork_plan(&w, &w.state, &cvec, &ps);

        // **P45** — the rule, asserted (one rule since W-38, `forkclass::p45_rule` over the day
        // the host's codec decodes); the fork's disagreement, counted.
        let (mut p45, mut p45run, mut p45over, mut p45fork) = (0u64, 0u64, 0u64, 0u64);
        if let (Some(at), Some((_, planned, place))) = (drew_at, drew) {
            let kday = planwire::read_plan(&plan, &planwire::DayCtx { tz, cands: &cvec, prios: &ps })
                .map_err(|e| TestCaseError::fail(format!("the kernel's day does not decode: {e:?}")))?;
            let span = (local_dt(tz, date(), NaiveTime::MIN), local_dt(tz, date() + Duration::days(1), NaiveTime::MIN));
            let got = forkclass::p45_rule(&kday.day, at, u32::try_from(planned).unwrap_or(0), Some(place), w.now, span);
            prop_assert!(got.is_ok(), "P45: {}", got.clone().err().unwrap_or_default());
            let (lo, hi, open) = got
                .map(|(a, z, o)| (rowwire::kernel_sec(a), rowwire::kernel_sec(z), o))
                .unwrap_or((0, 0, false));
            p45 = 1;
            p45run = u64::from(!open);
            p45over = u64::from(open);
            // The shipped fork has no Break row and places from `now` into the break.
            p45fork = u64::from(shipped.segments.iter().any(|s| {
                let (a, z) = (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end));
                matches!(s.kind, SegKind::Block | SegKind::Batch(_) | SegKind::Rest
                    | SegKind::Routine | SegKind::Optional)
                    && a >= now_sec && a < hi && lo < z
            }));
        }

        // **P46** — the kernel's overtime reservation IS the comparand fork's reservation.
        let is46 = w35_is_p46(&w, &w.state);
        let (mut p46diff, mut p46res) = (0u64, 0u64);
        if is46 {
            let k = w35_reservation(&plan, now_sec);
            let f = d57.segments.iter()
                .find(|s| matches!(s.kind, SegKind::Block) && s.flags.current && s.energy.is_none()
                    && rowwire::kernel_sec(s.start) == now_sec)
                .map(|s| rowwire::kernel_sec(s.end));
            prop_assert_eq!(k, f, "P46: the kernel's overtime reservation is not the comparand's");
            // Counted only where the comparand placed one: a P46 day with no free stretch at
            // `now` is compared (both refuse) but reserves nothing to compare.
            p46res = u64::from(f.is_some());
            let kleft = plan["segments"].as_array().map(Vec::as_slice).unwrap_or_default().iter()
                .find(|s| s["kind"] == "block" && s["flags"]["current"] == true)
                .map(|s| (s["planned"].as_u64(), s["note"]["leftMin"].as_u64()));
            if f.is_some() {
                prop_assert_eq!(kleft, Some((Some(0), Some(0))), "P46: the reservation's left is not the fork's 0");
            }
            p46diff = u64::from(!shipped.segments.iter().any(|s| {
                matches!(s.kind, SegKind::Block) && s.flags.current && s.energy.is_none()
                    && rowwire::kernel_sec(s.start) == now_sec
            }));
        }

        // **P47** — the kernel's open row stops at the wall on `now` — and, on a break day, at the
        // running break's start too: P45 pauses the block as the wall does (`pauseRows`).
        let mut probe = shipped.clone();
        let is47 = w35_p47_day(&w, &mut probe);
        let paused45 = drew_at.is_some_and(|t| w35_pause_open_rows(&mut probe, &[t]));
        let mut p47diff = 0u64;
        if is47 || paused45 {
            let kopen: Vec<(i64, i64, bool)> = plan["segments"].as_array().map(Vec::as_slice)
                .unwrap_or_default().iter()
                .filter(|s| s["kind"] == "block" && s["flags"]["open"] == true)
                .map(|s| (s["start"].as_i64().unwrap_or(-1), s["stop"].as_i64().unwrap_or(-1),
                          s["flags"]["current"].as_bool().unwrap_or(true)))
                .collect();
            let fopen: Vec<(i64, i64, bool)> = probe.segments.iter()
                .filter(|s| matches!(s.kind, SegKind::Block) && s.flags.open)
                .map(|s| (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end), s.flags.current))
                .collect();
            prop_assert_eq!(&kopen, &fopen, "P47: the kernel's open row is not the wall-paused one");
            let shipped_open: Vec<(i64, i64, bool)> = shipped.segments.iter()
                .filter(|s| matches!(s.kind, SegKind::Block) && s.flags.open)
                .map(|s| (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end), s.flags.current))
                .collect();
            // The shipped fork drew it across the wall or marked it `▶`.
            p47diff = u64::from(is47 && shipped_open != kopen);
        }

        // **Everything else, against the D57 comparand** — §8.2 step 5's rows, both ways; a
        // break day is not compared here (P45 has no fork analogue: the comparand plans over it).
        let mut acmp = 0u64;
        if drew.is_none() {
            let ka = kernel_assigned(&plan, now_sec);
            let fa = fork_assigned(&d57, w.now);
            prop_assert_eq!(&ka, &fa, "§8.2 step 5 differs from the D57 comparand");
            acmp = ka.len() as u64;
        }

        let [cases, n45, n45run, n45over, n45fork, n46, n46diff, n47, n47diff, nacmp, noprio] = {
            let mut c = W35_CENSUS.lock().expect("census");
            c[0] += 1;
            c[1] += p45;
            c[2] += p45run;
            c[3] += p45over;
            c[4] += p45fork;
            c[5] += p46res;
            c[6] += p46diff;
            c[7] += u64::from(is47);
            c[8] += p47diff;
            c[9] += acmp;
            *c
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        if cases >= generated {
            // **Floors** (AGENTS §9.2): a divergence asserted on no day is asserted on nothing.
            prop_assert!(n45run > 0, "no running break that had not overrun was drawn in {cases} cases");
            prop_assert!(n45over > 0, "no overrun break was drawn in {cases} cases");
            prop_assert!(n45fork > 0, "the shipped fork never scheduled over a break in {cases} cases");
            prop_assert!(n46 > 0, "no overtime reservation (P46) was compared in {cases} cases");
            prop_assert!(n46diff > 0, "on no P46 day did the shipped fork reserve nothing in {cases} cases");
            prop_assert!(n47 > 0, "no wall on `now` paused a running block (P47) in {cases} cases");
            prop_assert!(n47diff > 0, "on no P47 day did the shipped fork's open row differ in {cases} cases");
            prop_assert!(nacmp > 0, "no assigned row was compared against the D57 comparand in {cases} cases");
        }
        let [cdays, c46, c47] = *W35_COMPARAND.lock().expect("census");
        eprintln!(
            "planner_invariants W-35 comparand, over every arm that calls it: {cdays} days, P46 \
             applied on {c46}, P47 on {c47}"
        );
        eprintln!(
            "planner_invariants W-35 census: {cases} cases; P45 break days {n45} (running {n45run}, \
             overrun {n45over}; the SHIPPED fork scheduled over the break on {n45fork}); P46 overtime \
             reservations compared {n46} (on {n46diff} overtime days the shipped fork reserved nothing); P47 wall-on-now days \
             {n47} (the shipped fork drew the open row across the wall or marked it current on {n47diff}); assigned rows \
             compared against the D57 comparand {nacmp}; cases with no kernel §7 answer {noprio}"
        );
    }
}

/// **A batch row, digested on every run** (W-35 repair, README gap 2935).  The hash arm's
/// `nbatch > 0` floor counts batch rows the EMITTER digested on generated days, and a run of this
/// step's acceptance drew none in 307 cases and FAILED it (its seed is kept, D46) — the generator
/// reaches a batch on 3-5 days of ~280.  This day is fixed: three twenty-minute errands of one
/// `ci`, nothing else.  The kernel's day holds a batch row, its digest is the fork's
/// `DayPlan::hash` of its own rows, and the batch row is the kernel-ranked fork's too.
#[test]
fn a_batch_row_is_digested_on_every_run() {
    let w = build(&errand_day());
    let tz = w.cfg.tz;
    let plan = kernel_plan(&w.plan_request()).expect("the kernel plans the errand day");
    let krows = fork_rows_of_kernel(&plan, tz);
    let batches: Vec<&Segment> =
        krows.iter().filter(|s| matches!(s.kind, SegKind::Batch(_))).collect();
    assert!(!batches.is_empty(), "the kernel's day holds no batch row: {:?}",
        krows.iter().map(placement_key).collect::<Vec<_>>());
    let fork = planner::plan(&w.input(&w.state, w.now));
    let mut kday = DayPlan::empty(fork.date, fork.window, fork.budget_blocks);
    kday.segments = krows.clone();
    assert_eq!(
        plan["hash"].as_str().expect("plan.hash"),
        kday.hash(),
        "the kernel's digest of a day with a batch row is not the fork's `DayPlan::hash` of it"
    );
    let cvec = w.candidates();
    let ps = kernel_prios(&plan, &cvec).expect("the kernel ranks the day");
    let day2 = w35_fork_plan(&w, &w.state, &cvec, &ps);
    let fkeys: Vec<_> = day2.segments.iter().map(placement_key).collect();
    for b in batches {
        assert!(fkeys.contains(&placement_key(b)),
            "the kernel's batch row {:?} is not the kernel-ranked fork's", placement_key(b));
    }
}

/// **A P46 day, compared on every run** (W-35 repair, README gaps 2910 and 2934).  The arm above
/// reaches an overtime reservation only when the shared generator happens to draw one — 2 and 12
/// were compared on this repair's two runs — so its `n46 > 0` floor is a probability.  This day is
/// fixed: one item, running 70 minutes against a 30-minute estimate, no wall, no routine, no break.
/// P46 holds by its property, the kernel reserves, and the reservation is the one the FORK places
/// with its `left` out of the way — which is also the rule stated outright: the block the item is
/// in ends two blocks after it started (70 minutes run, one-hour blocks), fifty minutes from now.
#[test]
fn a_p46_day_is_compared_on_every_run() {
    let w = build(&p46_day());
    assert_eq!(w.cfg.block_min(), 60, "the rule below is stated for one-hour blocks");
    assert!(w35_is_p46(&w, &w.state), "a block run 70 minutes against 30 is P46 by its property");
    let plan = kernel_plan(&w.plan_request()).expect("the kernel plans the P46 day");
    let cvec = w.candidates();
    let ps = kernel_prios(&plan, &cvec).expect("the kernel ranks the day");
    let now_sec = rowwire::kernel_sec(w.now);
    let k = w35_reservation(&plan, now_sec);
    let d57 = w35_fork_plan(&w, &w.state, &cvec, &ps);
    let f = d57.segments.iter()
        .find(|s| matches!(s.kind, SegKind::Block) && s.flags.current && s.energy.is_none()
            && rowwire::kernel_sec(s.start) == now_sec)
        .map(|s| rowwire::kernel_sec(s.end));
    assert_eq!(k, Some(now_sec + 50 * 60), "the block the item is in ends fifty minutes from now");
    assert_eq!(k, f, "P46: the kernel's overtime reservation is not the comparand's");
    let shipped = planner::plan(&w.input(&w.state, w.now).with_ranking(&cvec, &ps));
    assert!(
        !shipped.segments.iter().any(|s| matches!(s.kind, SegKind::Block) && s.flags.current
            && s.energy.is_none() && rowwire::kernel_sec(s.start) == now_sec),
        "the shipped fork refuses to reserve in overtime — that is what P46 diverges from"
    );
}

// ===========================================================================
// **§8.2 STEP 8, THE REST OF IT, BY VALUE** — stage 6 W-35 track E (README
// gaps 2723, 2640 and 2743).
//
// The step-8 arm above compares nine of the twelve fields and says why it does
// not compare the other three: `conflicts`, `notes` and `aCapacityLost` "are
// not this arm's question". They reach `--json plan` at R3, so they are this
// block's: each against the kernel-ranked fork's (`day2`, the shipped wiring,
// D53), by VALUE —
//
//   * `conflicts` as a multiset of `(a, b)` pairs;
//   * `aCapacityLost` as the number;
//   * `notes` IN ORDER, each kernel note rendered to the fork's own prose
//     (`planner.rs:927`, `:1056` and `:2218`, `fmt_clock` on the zone's clock);
//
// and the three TUPLE COMPONENTS the kernel did not carry until this step —
// `impossible`'s `until`, `underused`'s `(energy, ci)` and `blocked`'s deps —
// each whole tuple as a multiset, the dates as `YYYY-MM-DD`, the deps as their
// `after:` spelling (`Dep`'s `Display`). And on the kernel's own wire, each
// pair/id field is the projection of its tuple field. Every comparison has its
// own floor below, so no field passes by being empty on every day (AGENTS §9.2).
// ===========================================================================


/// cases; days compared; conflicts pairs compared; days with conflicts; notes
/// compared; days with a note; days with `aCapacityLost > 0`; impossible tuples;
/// underused tuples; blocked tuples; deps compared; days with no kernel §7 answer;
/// and the notes compared BY KIND — travel day, no position, budget spent — so the
/// census says which of the three kinds a run actually compared.
static REST_CENSUS: Mutex<[u64; 15]> = Mutex::new([0; 15]);

/// A kernel `notes` entry, in the fork's prose (`planner.rs`), `None` for a
/// note kind the fork's `Diagnostics.notes` never carries.
fn note_text(n: &Value, tz: Tz) -> Option<String> {
    use chrono::TimeZone;
    let clock = |v: &Value| -> String {
        let t = tz
            .timestamp_opt(v.as_i64().expect("a second") - rowwire::EPOCH_FROM_CE, 0)
            .single()
            .expect("an instant the zone reads");
        planner::fmt_clock(t)
    };
    match n["note"].as_str()? {
        "travelDay" => Some("travel day: no blocks planned (`travel-day` wall today)".to_string()),
        "noPosition" => Some(format!(
            "{}: no free {}m position in {}–{}; not planned today",
            n["id"].as_str()?,
            n["durMin"].as_u64()?,
            clock(&n["lo"]),
            clock(&n["hi"]),
        )),
        "budgetSpent" => Some(format!(
            "budget spent: {} blocks done, the rest of the day is rest",
            n["blocksDone"].as_u64()?
        )),
        _ => None,
    }
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

    /// **The rest of §8.2 step 8, by value**, against the kernel-ranked fork.
    #[test]
    fn the_kernel_writes_the_rest_of_step_8_as_the_fork_does(
        case in case_strategy(),
        travel in prop_oneof![3 => Just(false), 1 => Just(true)],
        spent in prop_oneof![3 => Just(false), 1 => Just(true)],
    ) {
        let mut w = build(&case);
        let _ = widen_for_notes(&mut w, &case, travel, spent);
        let tz = w.cfg.tz;
        let req = w.plan_request();
        let plan = match kernel_plan(&req) {
            Ok(p) => p,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the kernel refused a day the fork planned: {head}");
                unreachable!()
            }
        };
        let kd = &plan["diagnostics"];
        let arr = |v: &Value| -> Vec<Value> { v.as_array().cloned().unwrap_or_default() };
        let s = |v: &Value| -> String { v.as_str().unwrap_or("<not a string>").to_string() };

        // The projections of the kernel's own tuples are asked of the kernel alone, outside this
        // region, since W-38 (`step8_projections`, README gap 3282); the tuples are compared here.
        let mut kimp: Vec<(String, u64, String)> = arr(&kd["impossibleUntil"]).iter()
            .map(|o| (s(&o["id"]), o["shortMin"].as_u64().unwrap_or(u64::MAX), s(&o["until"])))
            .collect();
        let mut kund: Vec<(String, u64, u64)> = arr(&kd["underusedLevels"]).iter()
            .map(|o| (s(&o["id"]), o["energy"].as_u64().unwrap_or(99), o["ci"].as_u64().unwrap_or(99)))
            .collect();
        let mut kblk: Vec<(String, Vec<String>)> = arr(&kd["blockedDeps"]).iter()
            .map(|o| (s(&o["id"]), arr(&o["deps"]).iter().map(s).collect()))
            .collect();

        let cvec = w.candidates();
        // **The D57 comparand, not `planner::plan`** (W-35 land step, README gap 2910): on an
        // overtime day (P46) or a wall on `now` (P47) the kernel's day differs from the fork's BY
        // DESIGN, so step 8's rest is compared with `w35_fork_plan` — which IS `planner::plan`,
        // kernel-ranked (D53), on every other day — as track K's merge made every earlier arm do.
        // Found by the merge: an overtime day (`active: (0, 59 min, est 30)`) failed `underused`
        // against the raw fork, which placed a second item at `now`.
        let day2 = kernel_prios(&plan, &cvec)
            .map(|ps| w35_fork_plan(&w, &w.state, &cvec, &ps));
        let mut row = [0u64; 15];
        row[0] = 1;
        match day2.as_ref() {
            None => row[11] = 1,
            Some(d2) => {
                row[1] = 1;
                // `conflicts`: a multiset of pairs.
                let mut kc: Vec<(String, String)> = arr(&kd["conflicts"]).iter()
                    .map(|o| (s(&o["a"]), s(&o["b"]))).collect();
                let mut fc: Vec<(String, String)> = d2.diagnostics.conflicts.iter()
                    .map(|(a, b)| (a.to_string(), b.to_string())).collect();
                kc.sort();
                fc.sort();
                prop_assert_eq!(&kc, &fc, "§8.2 step 8's `conflicts` differs from the fork's");
                row[2] = kc.len() as u64;
                row[3] = u64::from(!kc.is_empty());
                // `notes`: in order, in the fork's prose.
                let kn: Vec<Option<String>> = arr(&kd["notes"]).iter().map(|n| note_text(n, tz)).collect();
                prop_assert!(
                    kn.iter().all(Option::is_some),
                    "the kernel's diagnostics carry a note kind the fork's never does: {}", kd["notes"]
                );
                for n in arr(&kd["notes"]) {
                    match n["note"].as_str() {
                        Some("travelDay") => row[12] += 1,
                        Some("noPosition") => row[13] += 1,
                        Some("budgetSpent") => row[14] += 1,
                        _ => {}
                    }
                }
                let kn: Vec<String> = kn.into_iter().flatten().collect();
                prop_assert_eq!(&kn, &d2.diagnostics.notes, "§8.2 step 8's `notes` differ from the fork's");
                row[4] = kn.len() as u64;
                row[5] = u64::from(!kn.is_empty());
                // `aCapacityLost`: the number.
                prop_assert_eq!(
                    kd["aCapacityLost"].as_u64(), Some(u64::from(d2.diagnostics.a_capacity_lost)),
                    "§8.2 step 8's `aCapacityLost` differs from the fork's"
                );
                row[6] = u64::from(d2.diagnostics.a_capacity_lost > 0);
                // The three whole tuples.
                let mut fimp: Vec<(String, u64, String)> = d2.diagnostics.impossible.iter()
                    .map(|(id, short, until)| (id.to_string(), u64::from(*short), until.to_string()))
                    .collect();
                kimp.sort();
                fimp.sort();
                prop_assert_eq!(&kimp, &fimp, "`impossible`'s whole tuple (with `until`) differs");
                row[7] = kimp.len() as u64;
                let mut fund: Vec<(String, u64, u64)> = d2.diagnostics.underused.iter()
                    .map(|(id, e, c)| (id.to_string(), u64::from(*e), u64::from(*c))).collect();
                kund.sort();
                fund.sort();
                prop_assert_eq!(&kund, &fund, "`underused`'s whole tuple (energy, ci) differs");
                row[8] = kund.len() as u64;
                let mut fblk: Vec<(String, Vec<String>)> = d2.diagnostics.blocked.iter()
                    .map(|(id, deps)| (id.to_string(), deps.iter().map(ToString::to_string).collect()))
                    .collect();
                kblk.sort();
                fblk.sort();
                prop_assert_eq!(&kblk, &fblk, "`blocked`'s whole tuple (deps) differs");
                row[9] = kblk.len() as u64;
                row[10] = kblk.iter().map(|t| t.1.len() as u64).sum();
            }
        }
        let c = {
            let mut c = REST_CENSUS.lock().expect("census");
            for (i, v) in row.iter().enumerate() {
                c[i] += v;
            }
            *c
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        if c[0] >= generated {
            // **THE FLOORS**, one per comparison (AGENTS §9.2).
            prop_assert!(c[1] > 0, "no day was compared with the kernel-ranked fork");
            prop_assert!(c[3] > 0, "no day carried a wall conflict: `conflicts` was compared only empty");
            prop_assert!(c[5] > 0, "no day carried a note: `notes` was compared only empty");
            prop_assert!(c[12] > 0, "no TRAVEL-DAY note was compared");
            prop_assert!(c[13] > 0, "no NO-POSITION note was compared");
            prop_assert!(c[14] > 0, "no BUDGET-SPENT note was compared");
            prop_assert!(c[6] > 0, "no day lost A-capacity: `aCapacityLost` was compared only at 0");
            prop_assert!(c[7] > 0, "no IMPOSSIBLE tuple was compared, so no `until`");
            prop_assert!(c[8] > 0, "no UNDERUSED tuple was compared, so no `(energy, ci)`");
            prop_assert!(c[10] > 0, "no BLOCKED dep was compared");
        }
        eprintln!(
            "planner_invariants step-8 rest census: {} cases, {} compared with the kernel-ranked \
             fork ({} with no kernel §7 answer); conflicts {} pairs on {} days; notes {} on {} \
             days (by kind: travel day {}, no position {}, budget spent {}); aCapacityLost > 0 on \
             {} days; impossible tuples {}; underused tuples {}; blocked tuples {} ({} deps)",
            c[0], c[1], c[11], c[2], c[3], c[4], c[5], c[12], c[13], c[14], c[6], c[7], c[8], c[9],
            c[10]
        );
    }
}

// ===========================================================================
// **W-36 (track K): D60 — IMPOSSIBLE ties at `p = 0` go by DUE DATE (parity P51)**
//
// The owner's D60 (README gap 2801): every impossible item is HOT (`p = 0`), fork
// `sorted_candidates`/`build_groups` break ties by `(root_order, own_order)` — its place in the
// file — while §7.3's pass served them by due date, so the item whose grant held the day's
// minutes could be dropped for one whose grant is tomorrow's. The kernel's step-5 key carries
// D60's component since W-36 (`Planner.Ranked.imp`): a `p = 0` answer with a positive shortfall
// sorts by its `until` and then its request position, before every other `p = 0` answer.
//
// **The comparand runs D60's key in the FORK, by its property and never by a list.** Both fork
// sorts read the candidate's own `root_order`/`own_order`, and nothing else of the fork's
// `with_ranking` day reads them (its §7 pass, which uses `own_order` as an EDF tie-break, is
// bypassed), so `forkclass::d60_cands` rewrites those two fields and changes nothing else: an impossible
// `p = 0` candidate gets `root_order = (0, until)` and `own_order = (0, index)`, every other
// candidate's `root_order` moves one file down — a uniform shift, which keeps the fork's order
// among them. `w35_fork_plan` and the what-if days call it, so every earlier arm compares the
// kernel with the fork as D60 reads it; on a day with no `p = 0` impossible candidate the shift
// is uniform and the day is `planner::plan`'s exactly.
// ===========================================================================


/// `[cases, days with a kernel §7 answer, P51 days, P51 days whose SHIPPED fork's assigned
/// rows differ from the D60 comparand's, P51 days whose kernel rows equal the comparand's]`.
static W36_CENSUS: Mutex<[u64; 5]> = Mutex::new([0; 5]);

/// The Block/Batch rows of a day from `now` on, as `(start, stop, sorted items)`.
fn w36_work_rows(d: &DayPlan, now: DateTime<Tz>) -> Vec<(i64, i64, Vec<String>)> {
    d.segments
        .iter()
        .filter(|s| s.kind.is_work() && s.start >= now && !s.flags.current)
        .map(|s| {
            let mut it: Vec<String> = s.items().iter().map(ToString::to_string).collect();
            it.sort();
            (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end), it)
        })
        .collect()
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

    /// **D60 on every generated day, by value.** The kernel's work rows from `now` equal the
    /// D60 comparand's (the fork running D60's key), and on a P51 day — where D60 moved the
    /// order — the SHIPPED fork's rows are counted where they differ: that difference is the
    /// registered divergence, and the kernel is on the comparand's side of it.
    #[test]
    fn the_kernel_serves_impossible_ties_by_due_date(case in case_strategy()) {
        let w = build(&case);
        let plan = match kernel_plan(&w.plan_request()) {
            Ok(p) => p,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the kernel refused a day the fork planned: {head}");
                unreachable!()
            }
        };
        let cvec = w.candidates();
        let Some(ps) = kernel_prios(&plan, &cvec) else {
            W36_CENSUS.lock().expect("census")[0] += 1;
            return Ok(());
        };
        let now_sec = rowwire::kernel_sec(w.now);
        let d60 = w35_fork_plan(&w, &w.state, &cvec, &ps);
        let k = w36_kernel_work_rows(&plan, now_sec);
        let c = w36_work_rows(&d60, w.now);
        prop_assert_eq!(&k, &c, "§8.2 step 5 differs from the D60 comparand");
        let p51 = forkclass::is_p51(&cvec, &ps);
        let mut shipped_differs = false;
        if p51 {
            let shipped = planner::plan(&w.input(&w35_p46_state(&w, &w.state), w.now)
                .with_ranking(&cvec, &ps));
            shipped_differs = w36_work_rows(&shipped, w.now) != c;
        }
        let row = {
            let mut t = W36_CENSUS.lock().expect("census");
            t[0] += 1;
            t[1] += 1;
            t[2] += u64::from(p51);
            t[3] += u64::from(shipped_differs);
            t[4] += u64::from(p51 && k == c);
            *t
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        if row[0] >= generated {
            // **Floors** (AGENTS §9.2): the D60 order was exercised, and it was VISIBLE — a day
            // where the shipped fork's rows differ from the comparand's is a day this arm could
            // have failed on.
            prop_assert!(row[2] > 0, "no P51 day in {} cases: D60's order was never exercised", row[0]);
            prop_assert!(row[3] > 0, "no P51 day moved a work row in {} cases", row[0]);
        }
        eprintln!(
            "planner_invariants W-36 census: {} cases, {} with a kernel §7 answer; P51 days (D60 \
             moved the fork's order) {}, of them the SHIPPED fork's work rows differ from the D60 \
             comparand's {}, and the kernel's equal the comparand's {}",
            row[0], row[1], row[2], row[3], row[4]
        );
    }
}

/// **The reversed day, driven** (README gap 2801): two impossible items of one `ci`, the first
/// line due TOMORROW and the second due TODAY. D60 serves the second first; the SHIPPED fork
/// serves the first, by line; the D60 comparand agrees with the kernel. Compared on every run,
/// so the P51 arm above never rests on the generator drawing such a day.
#[test]
fn the_reversed_day_is_served_by_due_date_on_every_run() {
    let w = build(&reversed_day());
    let plan = kernel_plan(&w.plan_request()).expect("the kernel plans the reversed day");
    let cvec = w.candidates();
    let ps = kernel_prios(&plan, &cvec).expect("the kernel ranks the reversed day");
    let ids: Vec<String> = cvec.iter().map(|c| c.id.to_string()).collect();
    assert_eq!(ids.len(), 2, "two candidates: {ids:?}");
    assert!(ps.iter().all(forkclass::is_impossible_tie), "both are p = 0 and impossible: {ps:?}");
    assert!(forkclass::is_p51(&cvec, &ps), "D60 moves the order on the reversed day");
    let now_sec = rowwire::kernel_sec(w.now);
    let k = w36_kernel_work_rows(&plan, now_sec);
    assert!(!k.is_empty(), "the kernel assigns work on the reversed day");
    assert_eq!(k[0].2, vec![ids[1].clone()], "the kernel serves the item due today first: {k:?}");
    let d60 = w35_fork_plan(&w, &w.state, &cvec, &ps);
    assert_eq!(k, w36_work_rows(&d60, w.now), "the kernel's rows are the D60 comparand's");
    let shipped = planner::plan(&w.input(&w.state, w.now).with_ranking(&cvec, &ps));
    let f = w36_work_rows(&shipped, w.now);
    assert_eq!(f[0].2, vec![ids[0].clone()], "the SHIPPED fork serves the first line: {f:?}");
    assert_ne!(k, f, "parity P51: the kernel and the shipped fork differ on the reversed day");
}

// ---------------------------------------------------------------------------
// **W-36 (track K): D58's kernel half — the what-if reads the HOST's grown facts (gap 2873)**
//
// Since W-36 `PlanWire.readOvertime` reads `overtime.grown` — fork `PlanOverrides::apply`'s
// `remaining_min` and `planned_min`, which `planwire::grown` computes with the two functions
// `collect_candidates` derives the originals with — and `Planner.overtimeDiff` plans the grown
// request (`Planner.PlanReq.growing`). The arm below sends them exactly as the binary's encoder
// writes them and compares the kernel's `diff` BY VALUE with the shipped TUI's what-if.
//
// **What is left of parity P44 is defined by its property, never by a list.** The kernel's
// what-if day ranks the GROWN request — its §7 pass reads the extended record's `remaining` —
// while the shipped TUI's `with_ranking` keeps the reload's ranking (README gap 114). So the
// comparand is the fork's full what-if run with the kernel's OWN ranking of the grown request
// (that request's `lookahead.grants`, which is the day's `candAnswers` —
// `Planner.PlanReq.candAnswers_is_the_lookaheads`), ASSERTED on every day; a day where that
// ranking differs from the reload's is where the kernel may differ from the shipped TUI, and
// the census counts it. The host's `need_min` is sent and not read: no reader of a
// `with_ranking` day reads it (README gap 3004).
// ---------------------------------------------------------------------------


/// `[cases, what-ifs compared (a running block and a kernel §7 answer), of them the running item
/// is a candidate the extension grows, of them the grown facts moved the kernel's §7 answer,
/// parity-P44 days (the shipped fork's full what-if differs from its estimate-only one), of them
/// the kernel's `diff` now equals the shipped TUI's, days where the kernel's `diff` differs from
/// the shipped TUI's, ids compared]`.
static W36_GROWN: Mutex<[u64; 8]> = Mutex::new([0; 8]);

/// **The request the kernel ranks the what-if day with**: `req` with every candidate record
/// named `id` carrying the grown `remaining` and `plannedMin` — `Planner.PlanReq.growing`'s
/// rewrite, read back through `lookahead.grants`.
fn w36_grown_request(req: &Value, id: &Id, g: &planwire::Grown) -> Value {
    let mut out = req.clone();
    if let Some(items) = out["capacity"]["candidates"]["items"].as_array_mut() {
        for it in items.iter_mut().filter(|it| it["id"] == id.as_str()) {
            it["remaining"] = json!(g.remaining_min);
            it["plan"]["plannedMin"] = json!(g.planned_min);
        }
    }
    out
}

/// **What of a §7 answer a `with_ranking` day reads**: the sort's `p` (`sorted_candidates`), and
/// the class, `until` and shortfall step 8's diagnostics and D60's key read. `need_min` is not
/// in it — it moves on every grown day and no reader of the day reads it (README gap 3004).
fn w36_rank_view(ps: &[Prio]) -> Vec<(String, u8, String, Option<NaiveDate>, bool)> {
    ps.iter()
        .map(|p| (p.id.to_string(), p.p, format!("{:?}", p.class), p.until,
                  p.shortfall_min_exact.num > 0))
        .collect()
}

/// **The fork's what-if day as the shipped TUI builds it** (estimate grown, P46/P47 read as the
/// base reads them, D60's key), ranked by `ps`, with `PlanOverrides::extending` applied when
/// `full` — and its `diff` against `base`.
fn w36_fork_whatif(
    w: &World,
    base: &DayPlan,
    cvec: &[Candidate],
    ps: &[Prio],
    id: &Id,
    full: bool,
) -> DiffRow {
    let bm = w.cfg.block_min();
    let mut rt = w.state.clone();
    if let Some(x) = rt.active.as_mut() {
        x.est_min = x.est_min.saturating_add(bm);
    }
    let rt = w35_p46_state(w, &rt);
    let dvec = forkclass::d60_cands(cvec, ps);
    let ov = planner::PlanOverrides::new().extending(id, bm);
    let mut day = if full {
        planner::plan(&w.input(&rt, w.now).with_ranking(&dvec, ps).with_overrides(&ov))
    } else {
        planner::plan(&w.input(&rt, w.now).with_ranking(&dvec, ps))
    };
    w35_p47_day(w, &mut day);
    fork_diff(&planner::diff(base, &day))
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

    /// **§9.1's what-if WITH the host's grown facts, by value** (D58, README gap 2873). On a
    /// case with a running block the request carries `overtime` = one block on the running item
    /// and, when the extension grows a candidate, `grown`; the kernel's `diff` is ASSERTED equal
    /// to the fork's full what-if ranked by the kernel's answer for the grown request, and a day
    /// where it differs from the shipped TUI's is ASSERTED to be one the grown facts re-ranked.
    #[test]
    fn the_kernel_answers_the_what_if_with_the_hosts_grown_facts(case in case_strategy()) {
        let w = build(&case);
        let cvec = w.candidates();
        let bm = w.cfg.block_min();
        let active = w.state.active.clone();
        let grown = active.as_ref().and_then(|a| {
            cvec.iter().find(|c| c.id == a.id).and_then(|c| planwire::grown(c, None, bm, &w.cfg))
        });
        let mut req = w.plan_request();
        if let Some(a) = &active {
            req["planner"]["overtime"] = planwire::overtime_json(&a.id, 1, grown.as_ref());
        }
        let plan = match kernel_plan(&req) {
            Ok(p) => p,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the kernel refused a day the fork planned: {head}");
                unreachable!()
            }
        };
        let mut add = [1u64, 0, 0, 0, 0, 0, 0, 0];
        if let (Some(a), Some(ps)) = (&active, kernel_prios(&plan, &cvec)) {
            let ps_g = match &grown {
                None => Some(ps.clone()),
                Some(g) => match kernel_plan(&w36_grown_request(&req, &a.id, g)) {
                    Ok(pg) => kernel_prios(&pg, &cvec),
                    Err(raw) => {
                        let head: String = raw.chars().take(400).collect();
                        prop_assert!(false, "the kernel refused the grown request: {head}");
                        unreachable!()
                    }
                },
            };
            if let Some(ps_g) = ps_g {
                let base = w35_fork_plan(&w, &w.state, &cvec, &ps);
                let f_est = w36_fork_whatif(&w, &base, &cvec, &ps, &a.id, false);
                let f_full = w36_fork_whatif(&w, &base, &cvec, &ps, &a.id, true);
                let f_grown = w36_fork_whatif(&w, &base, &cvec, &ps_g, &a.id, true);
                prop_assert!(!plan["overtime"].is_null(), "the kernel did not answer `overtime`");
                let k = kernel_diff(&plan["overtime"]);
                prop_assert_eq!(
                    &k, &f_grown,
                    "the kernel's what-if differs from the fork's, ranked as the kernel ranks the \
                     grown request"
                );
                let reranked = w36_rank_view(&ps_g) != w36_rank_view(&ps);
                let p44 = f_full != f_est;
                let differs = k != f_full;
                prop_assert!(
                    !differs || reranked,
                    "the kernel's what-if differs from the shipped TUI's on a day the grown facts \
                     did not re-rank"
                );
                add[1] = 1;
                add[2] = u64::from(grown.is_some());
                add[3] = u64::from(reranked);
                add[4] = u64::from(p44);
                add[5] = u64::from(p44 && !differs);
                add[6] = u64::from(differs);
                add[7] = (k.0.len() + k.1.len() + k.2.len()) as u64;
            }
        } else if active.is_none() {
            prop_assert!(
                plan["overtime"].is_null(),
                "the kernel answered `overtime` to a request that asked none"
            );
        }
        let row = {
            let mut t = W36_GROWN.lock().expect("census");
            for (x, d) in t.iter_mut().zip(add) {
                *x += d;
            }
            *t
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        if row[0] >= generated {
            // **Floors** (AGENTS §9.2): the grown facts were sent, and the what-ifs compared
            // said something.
            prop_assert!(row[1] > 0, "no what-if was compared in {} cases", row[0]);
            prop_assert!(row[2] > 0, "no what-if carried grown facts in {} cases", row[0]);
            prop_assert!(row[7] > 0, "every what-if compared was empty in {} cases", row[0]);
        }
        eprintln!(
            "planner_invariants W-36 grown census: {} cases, what-ifs compared {}, carrying grown \
             facts {}, re-ranked by them {}; parity-P44 days (the shipped fork's full what-if \
             differs from its estimate-only one) {}, of them the kernel's `diff` now equals the \
             shipped TUI's {}; days the kernel's `diff` differs from the shipped TUI's {}; ids \
             compared {}",
            row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7]
        );
    }
}

/// **One what-if, driven**: the kernel's `diff` for `overtime` with and without the host's grown
/// facts, the shipped TUI's what-if (`PlanOverrides::extending` applied) and its estimate-only
/// one, the fork's full what-if ranked as the kernel ranks the grown request, and the two rank
/// views — for the fixed days below.
struct W36Whatif {
    kernel_grown: DiffRow,
    kernel_est: DiffRow,
    shipped: DiffRow,
    estimate: DiffRow,
    grown_ranked: DiffRow,
    reranked: bool,
}

fn w36_whatif(case: &Case) -> W36Whatif {
    let w = build(case);
    let cvec = w.candidates();
    let a = w.state.active.clone().expect("the day has a running block");
    let c = cvec.iter().find(|c| c.id == a.id).expect("the running item is a candidate");
    let g = planwire::grown(c, None, w.cfg.block_min(), &w.cfg).expect("the extension grows it");
    let ask = |grown: Option<&planwire::Grown>| -> (Value, DiffRow) {
        let mut req = w.plan_request();
        req["planner"]["overtime"] = planwire::overtime_json(&a.id, 1, grown);
        let plan = kernel_plan(&req).expect("the kernel plans the day");
        let d = kernel_diff(&plan["overtime"]);
        (plan, d)
    };
    let (plan, kernel_grown) = ask(Some(&g));
    let (_, kernel_est) = ask(None);
    let ps = kernel_prios(&plan, &cvec).expect("the kernel ranks the day");
    let req = w.plan_request();
    let pg = kernel_plan(&w36_grown_request(&req, &a.id, &g)).expect("the kernel plans the grown request");
    let ps_g = kernel_prios(&pg, &cvec).expect("the kernel ranks the grown request");
    let base = w35_fork_plan(&w, &w.state, &cvec, &ps);
    W36Whatif {
        kernel_grown,
        kernel_est,
        shipped: w36_fork_whatif(&w, &base, &cvec, &ps, &a.id, true),
        estimate: w36_fork_whatif(&w, &base, &cvec, &ps, &a.id, false),
        grown_ranked: w36_fork_whatif(&w, &base, &cvec, &ps_g, &a.id, true),
        reranked: w36_rank_view(&ps_g) != w36_rank_view(&ps),
    }
}

/// A generated item, spelled.
#[allow(clippy::too_many_arguments)]
fn w36_spec(ci: u8, k: u8, est_b: u32, small: Option<u32>, due_in: Option<u8>, dep: Option<usize>,
            loc_home: bool, atomic: bool, waiting: bool, floor: Option<u32>, parent: Option<usize>) -> Spec {
    Spec { ci, k, est_b, small, due_in, dep, loc_home, atomic, waiting, hot: false, floor, parent }
}

/// **A parity-P44 day, driven on every run** (README gap 2873): three items of `ci:0` due today,
/// the second running. The shipped TUI's what-if differs from its estimate-only one — fork
/// `PlanOverrides::apply` grew the running candidate — so until W-36 the kernel answered the
/// estimate's and the day was P44's. With the host's grown facts the kernel answers the shipped
/// TUI's what-if, on a day the grown facts do not re-rank. Drawn by the generator (W-36's third
/// census run) and fixed here, so the closure never rests on the generator drawing one.
#[test]
fn a_p44_day_is_answered_as_the_shipped_tui_answers_it_on_every_run() {
    let case = Case {
        items: vec![
            w36_spec(0, 3, 4, None, Some(0), None, false, true, false, None, None),
            w36_spec(0, 2, 2, None, Some(0), None, true, false, false, None, None),
            w36_spec(0, 2, 2, None, Some(0), Some(34), false, true, false, None, None),
        ],
        walls: vec![],
        now_idx: 0,
        done_blocks: 2,
        report: Some(1),
        routines: 28,
        optionals: false,
        home: true,
        active: Some((1, 31, 106)),
        interrupt: Some(19),
        late: true,
    };
    let x = w36_whatif(&case);
    assert_ne!(x.shipped, x.estimate, "a P44 day: the fork's `apply` moved its own what-if");
    assert_eq!(x.kernel_est, x.estimate, "without `grown` the kernel answers the estimate's (P44)");
    assert!(!x.reranked, "the grown facts do not re-rank this day");
    assert_eq!(x.kernel_grown, x.shipped, "with `grown` the kernel answers the shipped TUI's what-if");
}

/// **A parity-P52 day, driven on every run**: the running `^zaa`'s grown need takes today's
/// capacity from two items due today, which §7.3's pass over the GROWN request names IMPOSSIBLE
/// (`p = 0`). The kernel's what-if ranks them so and keeps `^zad`, moving it; the shipped TUI's
/// `with_ranking` keeps the reload's ranking and drops it (README gap 114). The kernel's answer is
/// the fork's full what-if ranked by the kernel's own answer for the grown request. Drawn by the
/// generator and fixed here.
#[test]
fn a_re_ranked_what_if_is_answered_by_the_grown_ranking_on_every_run() {
    let case = Case {
        items: vec![
            w36_spec(1, 3, 1, None, Some(0), None, false, true, false, Some(8), None),
            w36_spec(1, 4, 3, None, None, None, false, false, false, None, None),
            w36_spec(2, 4, 4, Some(15), Some(0), None, false, true, true, None, None),
            w36_spec(3, 3, 3, Some(20), Some(0), None, false, false, false, None, Some(19)),
            w36_spec(4, 3, 3, None, Some(0), Some(23), true, false, false, None, None),
            w36_spec(5, 3, 3, None, Some(0), Some(10), true, false, false, None, None),
        ],
        walls: vec![WallSpec { hour: 15, hours: 1 }],
        now_idx: 3,
        done_blocks: 3,
        report: None,
        routines: 6,
        optionals: true,
        home: false,
        active: Some((0, 78, 138)),
        interrupt: Some(46),
        late: false,
    };
    let x = w36_whatif(&case);
    assert!(x.reranked, "the grown facts re-rank this day");
    assert_eq!(x.kernel_grown, x.grown_ranked,
        "the kernel's what-if is the fork's, ranked as the kernel ranks the grown request");
    assert_ne!(x.kernel_grown, x.shipped,
        "parity P52: the kernel's what-if differs from the shipped TUI's on a re-ranked day");
}

// ===========================================================================
// **W-36 (track T): ONE reading of worked minutes — README gap 2920**
//
// Since W-36 the kernel's planner reads the running block's worked minutes off the request
// (`Planner.PlanReq.workedOf`): `state.active.workedMin`, the host's `Replay::active_worked_min`,
// which `tm now` prints and `tm done` logs.  A request that carries none gets the log's own reading
// (fork `active_run`'s), which is why every arm above — none of them sends it — still compares
// against the fork exactly as it did.  THIS arm sends it (`planwire::add_worked_min`, the one host
// encoder of the key) and draws what makes the two readings differ: a BREAK LOGGED INSIDE the
// running block, which the replay's open block never sees (`Replay.dayArm`) and the host's rule
// nets out — the class README gap 2920 said the generator never drew.  Its comparand is
// `w35_fork_plan` with the new rule applied by its PROPERTY, as P46 is: fork `active_run`'s estimate
// moved by the difference of the two readings, so the FORK computes a `left` of `est − host` and
// its own reservation from it, and the running block's open row reads the host's `so far`.  On a
// day where the two readings agree the comparand is `w35_fork_plan` exactly.
// ===========================================================================


/// **The host's worked minutes of the running block** — `Replay::active_worked_min`, the very call
/// `tm done` makes (`tm/src/cli/day.rs`' `worked_min`), the running break included.
fn w36_host_worked(w: &World, st: &RuntimeState) -> Option<u32> {
    let a = st.active.as_ref()?;
    let tz = w.cfg.tz;
    let started = local_dt(tz, date(), a.started);
    let running_break = st
        .break_
        .as_ref()
        .and_then(|b| b.started)
        .map(|t| local_dt(tz, date(), t).fixed_offset());
    Some(w.replay.active_worked_min(date(), started.fixed_offset(), w.now.fixed_offset(), running_break))
}

/// **The comparand, with the host's reading**: `w35_fork_plan` over a state whose running estimate
/// is moved by the difference of the two readings (`fork + (est − host)`, saturating, so the fork's
/// overtime property is the kernel's `host ≥ est`), and the running block's open row carrying the
/// host's minutes.  Nothing is copied out of the kernel's answer.
fn w36_fork_plan(w: &World, st: &RuntimeState, cvec: &[Candidate], ps: &[Prio], host: u32) -> DayPlan {
    let fork = w35_fork_worked(w, st).unwrap_or(0);
    let mut st2 = st.clone();
    if let Some(a) = st2.active.as_mut() {
        a.est_min = fork.saturating_add(a.est_min.saturating_sub(host));
    }
    let mut d = w35_fork_plan(w, &st2, cvec, ps);
    let running = st.active.as_ref().map(|a| a.id.clone());
    for s in d.segments.iter_mut().filter(|s| matches!(s.kind, SegKind::Block) && s.flags.open) {
        if s.item == running {
            s.flags.note = Some(format!("{host}m so far"));
        }
    }
    d
}

/// **W-36's census**: `[cases, days with a running block, days where the host's reading and the
/// fork's differ, open rows compared, open rows compared on a differing day, reservations compared,
/// reservations compared on a differing day, assigned rows compared, cases with no kernel §7
/// answer, logged breaks drawn inside a running block]`.
static W36_WORKED: Mutex<[u64; 10]> = Mutex::new([0; 10]);

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256),
        max_shrink_iters: 2_000,
        ..ProptestConfig::default()
    })]

    /// **The kernel reads the host's worked minutes, and the day agrees with the fork that reads
    /// them too** (W-36 track T, README gap 2920).  Every case with a running block sends the
    /// host's reading; the open row (start, stop, item, `▶`, `so far`), the reservation (its stop
    /// and its `left`) and §8.2 step 5's rows are compared with the comparand both ways.
    #[test]
    fn the_kernel_reads_the_hosts_worked_minutes(
        case in case_strategy(),
        logged in prop::option::of((0u32..=60, 5u32..=30)),
    ) {
        let mut w = build(&case);
        let tz = w.cfg.tz;
        // A break LOGGED inside the running block, begun `into` minutes after it started and
        // ended at or before `now` — written as `tm break` writes it, at its end and stamped at
        // its start, so the kernel and the fork replay the same bytes.
        let mut drew = 0u64;
        if let (Some((into, len)), Some(a)) = (logged, w.state.active.clone()) {
            let started = local_dt(tz, date(), a.started);
            let t = started + Duration::minutes(i64::from(into));
            if t + Duration::minutes(i64::from(len)) <= w.now {
                w.log.push_str(&format!(
                    "{{\"t\":\"{}\",\"ev\":\"break\",\"planned_min\":{len},\"actual_min\":{len}}}\n",
                    t.format("%Y-%m-%dT%H:%M:%S%:z")
                ));
                w.replay = chokepoint::replay_of_text(&w.log, tz);
                drew = 1;
            }
        }
        let host = w36_host_worked(&w, &w.state);
        let fork = w35_fork_worked(&w, &w.state);
        let mut req = w.plan_request();
        if let Some(h) = host {
            planwire::add_worked_min(&mut req["planner"], h);
        }
        let plan = match kernel_plan(&req) {
            Ok(p) => p,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the kernel refused a day the fork planned: {head}");
                unreachable!()
            }
        };
        let cvec = w.candidates();
        let Some(ps) = kernel_prios(&plan, &cvec) else {
            W36_WORKED.lock().expect("census")[8] += 1;
            return Ok(());
        };
        let d = match host {
            Some(h) => w36_fork_plan(&w, &w.state, &cvec, &ps, h),
            None => w35_fork_plan(&w, &w.state, &cvec, &ps),
        };
        let now_sec = rowwire::kernel_sec(w.now);
        let differs = host.is_some() && host != fork;

        // **The open row, by value, both ways** — its `so far` is the host's minutes.
        let kopen: Vec<(i64, i64, String, bool, Option<u64>)> = plan["segments"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .filter(|s| s["kind"] == "block" && s["flags"]["open"] == true)
            .map(|s| (s["start"].as_i64().unwrap_or(-1), s["stop"].as_i64().unwrap_or(-1),
                      s["item"].as_str().unwrap_or_default().to_string(),
                      s["flags"]["current"].as_bool().unwrap_or(false),
                      s["note"]["workedMin"].as_u64()))
            .collect();
        let fopen: Vec<(i64, i64, String, bool, Option<u64>)> = d
            .segments
            .iter()
            .filter(|s| matches!(s.kind, SegKind::Block) && s.flags.open)
            .map(|s| (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end),
                      s.item.as_ref().map(ToString::to_string).unwrap_or_default(),
                      s.flags.current, so_far(s.flags.note.as_deref())))
            .collect();
        prop_assert_eq!(&kopen, &fopen, "the open row does not read the host's worked minutes");

        // **The reservation** — its stop, and its `left`, which is the estimate less the host's.
        let k = w35_reservation(&plan, now_sec);
        let fres = d.segments.iter().find(|s| {
            matches!(s.kind, SegKind::Block) && s.flags.current && s.energy.is_none()
                && rowwire::kernel_sec(s.start) == now_sec
        });
        prop_assert_eq!(k, fres.map(|s| rowwire::kernel_sec(s.end)),
            "the reservation is not the comparand's");
        if let Some(f) = fres {
            let kleft = plan["segments"].as_array().map(Vec::as_slice).unwrap_or_default().iter()
                .find(|s| s["kind"] == "block" && s["flags"]["current"] == true
                    && s["start"].as_i64() == Some(now_sec))
                .and_then(|s| s["planned"].as_u64());
            prop_assert_eq!(kleft, f.flags.planned_min.map(u64::from),
                "the reservation's `left` is not the estimate less the host's worked minutes");
        }

        // **Everything else** — §8.2 step 5's rows, against the same comparand.
        let ka = kernel_assigned(&plan, now_sec);
        let fa = fork_assigned(&d, w.now);
        prop_assert_eq!(&ka, &fa, "§8.2 step 5 differs from the comparand");

        let c = {
            let mut c = W36_WORKED.lock().expect("census");
            c[0] += 1;
            c[1] += u64::from(host.is_some());
            c[2] += u64::from(differs);
            c[3] += kopen.len() as u64;
            c[4] += if differs { kopen.len() as u64 } else { 0 };
            c[5] += u64::from(fres.is_some());
            c[6] += u64::from(differs && fres.is_some());
            c[7] += ka.len() as u64;
            c[9] += drew;
            *c
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        if c[0] >= generated {
            // **Floors** (AGENTS §9.2): a reading compared only where the two agree compares nothing.
            prop_assert!(c[9] > 0, "no break was logged inside a running block in {} cases", c[0]);
            prop_assert!(c[2] > 0, "on no day did the host's reading differ from the log's in {} cases", c[0]);
            prop_assert!(c[4] > 0, "no open row was compared on a day the two readings differ");
            prop_assert!(c[6] > 0, "no reservation was compared on a day the two readings differ");
            prop_assert!(c[7] > 0, "no assigned row was compared");
        }
        eprintln!(
            "planner_invariants W-36 worked census: {} cases, {} with a running block, {} with a break \
             logged inside it; the host's reading differed from the log's on {} days; open rows \
             compared {} ({} on a differing day); reservations compared {} ({} on a differing day); \
             assigned rows compared {}; cases with no kernel §7 answer {}",
            c[0], c[1], c[9], c[2], c[3], c[4], c[5], c[6], c[7], c[8]
        );
    }
}
// END THE FORK PLANNER



/// **README gap 3480's declared class has its witness** (W-39): on the fresh draw the oracle arm's
/// first run found it on (`96e7339b0c1745683b47728b`, `break/home`: a 25-minute walk begun 09:46,
/// planned at 10:00), the kernel differs from P45's comparand after the break, and its rows from
/// there are the fork's own planned with the break UNLOGGED (`forkplan::gap_3480_explains`) — so the
/// class the arm declares is not vacuous, and it is not wider than that. Inert without `TM_ORACLE`.
#[test]
#[ignore]
fn gap_3480s_declared_class_holds_on_the_draw_that_found_it() {
    let Some(oracle) = the_oracle() else { return };
    let seed = "96e7339b0c1745683b47728b";
    let draw = forkclass::class_draws(seed, None).next().expect("a draw");
    let world = forkclass::world_of(&draw);
    let b = forkclass::Built::of(world.clone());
    assert_eq!(forkclass::class_of(&b).key(), "break/home");
    let prios = forkclass::kernel_answer_with_grants(&b).expect("the kernel plans the day").1;
    let answers = forkplan::comparand_answers(&b, &prios, oracle).expect("the fork answers");
    let mut line = forkclass::drawn_line(format!("fresh seed {seed}"), seed, 0, &draw, &world, "break/home");
    for key in forkclass::ANSWERS {
        forkclass::set_answer(&mut line, key, answers[key].clone());
    }
    let findings = forkclass::compare_line(&line, &mut forkclass::ClassTally::default());
    assert!(
        !findings.is_empty() && findings.iter().all(|f| f.contains("after the running break (P45")),
        "the draw that found gap 3480 differs otherwise now: {findings:?}"
    );
    assert!(forkplan::gap_3480_explains(&b, &prios, oracle).expect("the fork answers"), "the unlogged reading no longer explains the draw");
    // And it is not wider: on the frozen `overrun` lines — break days where the kernel agrees with
    // the LOGGED comparand (the class arm holds them to it) — the unlogged reading explains a line
    // exactly when logging the break moves none of the fork's rows (W-38's
    // `the_overrun_lines_witness_p45s_reset`: it moves them on five of the six).
    let tz = tm_core::config::Config::default().tz;
    let mut refuted = 0;
    for l in forkclass::frozen_lines().iter().filter(|l| l["secondary"] == "overrun") {
        let b = forkclass::Built::of(forkclass::ClassWorld::of_json(&l["world"], tz).expect("a stored world"));
        let prios = forkclass::kernel_answer_with_grants(&b).expect("the kernel plans the day").1;
        let rows = |logged| forkplan::p45_rows(&b, &prios, oracle, Some(logged)).expect("the fork answers").expect("a break").1;
        let moved = rows(true) != rows(false);
        let explains = forkplan::gap_3480_explains(&b, &prios, oracle).expect("the fork answers");
        assert_eq!(explains, !moved, "{}: the unlogged reading explains it {explains} and logging moves its rows {moved}", l["class"]);
        refuted += usize::from(!explains);
    }
    assert!(refuted >= 1, "the unlogged reading explains every frozen overrun line: it explains everything");
}
