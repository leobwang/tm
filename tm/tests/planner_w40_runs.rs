//! **D74 through the FFI: §7.5's batches are split into RUNS** — stage 6 W-40,
//! track K (the owner's D74, parity P64; README gaps 3546 and 3714).
//!
//! # What the owner decided, and what each test here shows
//!
//! §7.5 gathers small equal-`ci` candidates into a batch and §8.2 step 5 splits
//! the batch by `loc:`, atomicity and the running block. Fork 4748911's
//! `split_by_filters` is a GROUP-BY: a member joins the first bucket with its
//! key wherever it sits, so `[^t3, ^t1, ^t2]` with `^t1` atomic was split
//! `{^t3, ^t2}`, `{^t1}`, the pair keyed by `^t3` and served first — and `^t1`,
//! ranked ahead of `^t2`, got nothing while `^t2` was placed (README gap 3546).
//! The owner's D74: a bucket closes where the next ranked candidate cannot join
//! it, so the split is the batch's RUNS (`Planner.splitPush`), and step 5 serves
//! each `ci`'s entries in the candidate order
//! (`PlanFold.a_same_ci_entry_ahead_is_served_no_later`).
//!
//! * [`the_kernel_serves_the_split_batch_in_runs`] — the KERNEL's day (the
//!   planner R3 swaps in, through `tm_kernel_call`) on the split world, at one,
//!   two and three blocks of budget: `^t3`, then `^t1`, then `^t2`, each its own
//!   Block row, and never a Batch row holding `^t2` while `^t1` waits.
//! * [`the_kernel_batches_across_a_ci_on_the_riding_day`] — the day
//!   `PlannerWit.theRidingRequest` mirrors: §7.5 still gathers PAST an entry of
//!   another `ci` (the fork's `continue`, untouched by D74), so `^j1` rides with
//!   `^l1` into the one block and `^i1` — HOT, ranked ahead of `^j1` — gets
//!   nothing. It is why `PlanCheck.plan_is_monotone_in_rank` needs one `ci` and
//!   `PlanCheck.plan_puts_hot_before_the_queue` a row of queue items only.
//!
//! The fork's half is one `BEGIN THE FORK PLANNER` region, which R3 deletes: the
//! fork as the shipped binary runs it (kernel-ranked, D53) splits the batch as a
//! group-by — the behaviour P64 departs from — and batches across a `ci` exactly
//! as the kernel does, so the riding day is shipped behaviour, not a kernel
//! defect (W-39's lesson: a refutation standing on a defect is no discharge).
//!
//! * [`every_day_the_kernel_plans_unlike_the_fork_carries_p64s_precondition`] —
//!   what D74 MOVES on generated days, measured by value: the class draw from a
//!   seed no frozen file draws from, each world the shipped binary holds planned
//!   by the kernel and compared with the comparand (`forkplan::comparand_answers`,
//!   the frozen lines' one definition) by `forkclass::compare_line`. Every day the
//!   kernel plans unlike the fork must carry P64's precondition — a batch whose
//!   members, keyed as fork `split_by_filters` keys them, show one key again after
//!   another — the one shape on which a group-by and the runs differ.
//!   Since the W-40 land step the comparand runs P64 itself, so the kernel must
//!   differ from it on no day, and the census holds the comparand's `p64` flag
//!   (the runs moved the fork's day) to that precondition instead.

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
#[path = "support/forkplan.rs"]
mod forkplan;

/// Fork 4748911's §7.5 batches, by value (W-46 track C; README gap 4752, the class).
#[allow(dead_code)]
#[path = "support/forkcap.rs"]
mod forkcap;

use chrono::NaiveTime;
use tm_core::dayplan::{DayPlan, SegKind};
use tm_core::model::Id;
use forkclass::Built;
use tm_core::priority::{self, Candidate, Prio};
use tm_core::store::RuntimeState;

use planner_common::{at, date, of_texts, DayPlanner, Fixture, Kernel};

/// The split world: three siblings at `ci 2`, ten minutes each (small enough to
/// share a block), `^t1` atomic, written `^t3`, `^t1`, `^t2` — the batch store
/// of `PlannerWit.theOneBlockSplitRequest`.
const SPLIT_WEEK: &str = "# Tasks\n\
- [ ] 2 10m Third task ^t3\n\
- [ ] 2 10m First task ^t1 atomic\n\
- [ ] 2 10m Second task ^t2\n";

/// The riding world: `^l1` (HOT, `ci 1`), `^i1` (HOT, `ci 2`), `^j1` (`ci 1`),
/// written in that order — `PlannerWit.ridingWitness`' store.
const RIDING_WEEK: &str = "# Tasks\n\
- [ ] 1 10m Lead the batch ^l1 hot\n\
- [ ] 2 10m Another level ^i1 hot\n\
- [ ] 1 10m Ride along ^j1\n";

fn world(week: &str) -> Fixture {
    of_texts(&[("week/2026-W37.md", week)], "")
}

/// Monday of the week, woken at 07:00, arrived at 09:00, `budget` blocks left.
fn state(budget: u32) -> RuntimeState {
    RuntimeState {
        date: Some(date("2026-09-07")),
        wake: Some(NaiveTime::from_hms_opt(7, 0, 0).expect("time")),
        arrival: Some(NaiveTime::from_hms_opt(9, 0, 0).expect("time")),
        loc: Some("lounge".to_string()),
        budget: Some(budget),
        ..RuntimeState::default()
    }
}

/// The day's work rows in order: `(batch?, items)`.
fn work(day: &DayPlan) -> Vec<(bool, Vec<String>)> {
    day.segments
        .iter()
        .filter(|s| s.kind.is_work())
        .map(|s| {
            (
                matches!(s.kind, SegKind::Batch(_)),
                s.items().iter().map(|i| i.as_str().to_string()).collect(),
            )
        })
        .collect()
}

fn ids(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| (*s).to_string()).collect()
}

/// The drive's record (`--nocapture`): every row the day draws.
fn show(label: &str, day: &DayPlan) {
    println!("{label}:");
    for s in &day.segments {
        println!(
            "  {} {:?} {:?}",
            tm_core::dayplan::fmt_clock(s.start),
            s.kind,
            s.items().iter().map(|i| i.as_str().to_string()).collect::<Vec<_>>()
        );
    }
}

/// **The kernel serves the split batch in runs** (D74, P64): one block goes to
/// `^t3` alone; two give `^t1`, ranked second, the second; three serve all
/// three, each in a Block row of its own — the batch the fork forms,
/// `{^t3, ^t2}`, is not formed (D74's accepted cost).
#[test]
fn the_kernel_serves_the_split_batch_in_runs() {
    let fx = world(SPLIT_WEEK);
    let now = at("2026-09-07", 9, 0);
    let want: [&[&str]; 3] = [&["t3"], &["t3", "t1"], &["t3", "t1", "t2"]];
    for (n, want) in want.iter().enumerate() {
        let day = Kernel.day(&fx, &state(n as u32 + 1), now);
        show(&format!("the kernel, {} block(s)", n + 1), &day);
        let rows = work(&day);
        assert!(rows.iter().all(|(batch, _)| !batch), "{} block(s): a Batch row {rows:?}", n + 1);
        let held: Vec<String> = rows.into_iter().flat_map(|(_, items)| items).collect();
        assert_eq!(held, ids(want), "{} block(s)", n + 1);
    }
}

/// **§7.5 still gathers across a `ci`** (the riding day): `{^l1, ^j1}` takes the
/// one block as a Batch row and the HOT `^i1`, of another `ci`, gets nothing —
/// so the candidate-order rank law needs one `ci`, and the HOT law a row of
/// queue items only (`PlannerWit.monotone_rank_in_the_candidate_order_needs_one_ci`,
/// `PlannerWit.plan_puts_hot_before_the_queue_needs_a_row_of_queue_items`).
#[test]
fn the_kernel_batches_across_a_ci_on_the_riding_day() {
    let fx = world(RIDING_WEEK);
    let day = Kernel.day(&fx, &state(1), at("2026-09-07", 9, 0));
    show("the kernel, the riding day", &day);
    assert_eq!(work(&day), vec![(true, ids(&["l1", "j1"]))]);
}

/// **P64's precondition over one ranked order, by its property**: a batch §7.5 forms
/// over `ranked` (fork `priority::batches`, `groups`) whose plain members — the ones fork
/// `build_groups` keeps — keyed as fork `split_by_filters` keys them (`loc:`,
/// splittability, the running block), show one key AGAIN after another key. That is
/// the one shape on which the fork's group-by and D74's runs split a batch
/// differently; on every other batch the two are the same buckets in the same order.
///
/// **`groups` is fork 4748911's own answer, out of the tree since W-46 track C**
/// (`forkcap::batches`, frozen by value; `forkcap::batches_live` for the census's fresh
/// draws): until then it was tm-core's in-tree copy of `batches`, which R3 leaves with no
/// shipped caller and deletes.
fn a_key_reappears(ranked: &[&Candidate], groups: &[forkcap::ForkBatch], active: Option<&Id>) -> bool {
    groups.iter().any(|batch| {
        let keys: Vec<_> = batch
            .ids
            .iter()
            .filter_map(|id| ranked.iter().find(|c| c.id == *id && !c.is_wall && !c.is_optional && c.window.is_none()))
            .map(|c| (c.loc.clone(), c.splittable, active == Some(&c.id)))
            .collect();
        let mut closed = Vec::new();
        let mut run = None;
        keys.into_iter().any(|k| {
            if run.as_ref() == Some(&k) {
                return false;
            }
            if let Some(r) = run.replace(k.clone()) {
                closed.push(r);
            }
            closed.contains(&k)
        })
    })
}

/// **P64's precondition bites, both ways** (AGENTS §5.8): the split world's one batch,
/// `[^t3, ^t1, ^t2]` with `^t1` atomic, shows the splittable key again after the atomic
/// one; the same three with `^t1` written last, `[^t3, ^t2, ^t1]`, do not — the group-by
/// and the runs are then the same two buckets. **It reads no fork** — the kernel's ranking and
/// `tm_core::priority`'s batches — so it sits outside the region since W-45 track C (README gap
/// 4682), with the precondition and the census that reads it.  Since W-46 track C those batches
/// are fork 4748911's own, frozen by value (`forkcap::batches`), because R3 deletes the in-tree
/// copy (README gap 4752, the class).
#[test]
fn p64s_precondition_sees_a_key_again_and_only_then() {
    let mut lines = vec![("t3", ""), ("t1", " atomic"), ("t2", "")];
    for (expect, order) in [(true, "t3 t1 t2"), (false, "t3 t2 t1")] {
        if !expect {
            lines.swap(1, 2);
        }
        let week: String = std::iter::once("# Tasks\n".to_string())
            .chain(lines.iter().map(|(id, flag)| format!("- [ ] 2 10m Task {id} ^{id}{flag}\n")))
            .collect();
        let fx = world(&week);
        let now = at("2026-09-07", 9, 0);
        let st = state(1);
        let day = tm_core::planwire::plan_date(&st, now);
        let cands = priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, day, now);
        let w = planner_common::planreq::World {
            docs: &fx.docs,
            log: &fx.log,
            tree: &fx.tree,
            cfg: &fx.cfg,
            state: &st,
            now,
            cands: &cands,
            replay: &fx.replay,
        };
        let (_, ans) = planner_common::planreq::kernel_day(&w, None).expect("the kernel ranks the day");
        let ranked = priority::sorted_candidates(&ans.prios, &cands);
        let order_seen: Vec<&str> = ranked.iter().map(|c| c.id.as_str()).collect();
        assert_eq!(order_seen.join(" "), order, "the ranked order of the {order} world");
        let groups = forkcap::batches(forkcap::store(), &ranked, &fx.cfg);
        assert_eq!(a_key_reappears(&ranked, &groups, None), expect, "the {order} world");
    }
}

/// The census's seed — one no frozen file draws from — and its size.
const CENSUS_SEED: &str = "w40-k D74 runs census";
const CENSUS_DRAWS: usize = 128;

/// **P64's precondition for one world**: over every order the comparand plans it in —
/// the kernel's ranking as shipped and with D60's key run in the fork (P51), and on a
/// running-block day the kernel's ranking of the GROWN request (P52's what-if).
fn p64_precondition(b: &Built, prios: &[Prio]) -> bool {
    let active = b.world.state.active.as_ref().map(|a| &a.id);
    let mut rankings = vec![prios.to_vec()];
    rankings.extend(forkplan::grown_prios(b));
    rankings.iter().any(|ps| {
        let d60 = forkclass::d60_cands(&b.cands, ps);
        [&b.cands, &d60]
            .iter()
            .any(|cs| {
                let ranked = priority::sorted_candidates(ps, cs);
                a_key_reappears(&ranked, &forkcap::batches_live(forkcap::store(), &ranked, &b.cfg), active)
            })
    })
}

/// **What D74 moves on generated days, by value** (README gap 3546; parity P64). The class
/// draw from [`CENSUS_SEED`], [`CENSUS_DRAWS`] draws: each world the shipped binary holds
/// (`forkclass::binary_holds`, as the seeded batch is chosen) is planned by the kernel and
/// compared with the comparand — fork 4748911 as the shipped binary runs it, kernel-ranked
/// (D53), with the registered departures applied by their properties
/// (`forkplan::comparand_answers`) — by `forkclass::compare_line`, the frozen lines' own
/// comparison. **Every day the kernel plans unlike the fork carries P64's precondition**
/// ([`p64_precondition`]); the census prints how many days carry it, how many of those the
/// kernel plans unlike the fork, and the values that differ. On the kernel before D74 the
/// same draws differ on no day (README, W-40 track K).
///
/// **Since the W-40 land step (README gap 3740 closed) the comparand RUNS P64** — the fork's
/// `PlanInput::with_runs`, the oracle's `p64-runs.patch` — so the kernel is held to it on
/// EVERY day and must differ on none, and what D74 moves is the comparand's own `p64` flag
/// (the runs moved the fork's day): the census asserts that flag is set only on a day that
/// carries P64's precondition. At the land: 128 held, the precondition on 2, the runs moving
/// the fork's day on the count it prints, the kernel unlike the comparand on 0.
///
/// **A measurement, and `#[ignore]`d for its cost**: every draw is planned live by both
/// planners and the comparand's departures are re-derived, about five minutes on this
/// machine; it runs with `--include-ignored`, as the oracle arms do.
///
/// **Since W-45 track C the comparand is asked of `tm-oracle plan`** (README gap 4682; the owner's
/// D72) — fork 4748911 out of the tree, as every comparand is built after R3 — so the census
/// outlives R3 and sits outside the fork region; inert without `TM_ORACLE`. Until W-45 it asked the
/// in-tree fork, and R3 would have deleted it with the region.
#[test]
#[ignore]
fn every_day_the_kernel_plans_unlike_the_fork_carries_p64s_precondition() {
    let Some(bin) = forkplan::oracle_path() else {
        eprintln!("inert: set TM_ORACLE to an oracle built by kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh");
        return;
    };
    let oracle = forkplan::Oracle::new(bin);
    let mut t = forkclass::ClassTally::default();
    let (mut held, mut refused, mut pre, mut moved, mut values) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let mut p64_moved = 0usize;
    let mut bad = Vec::new();
    let mut shown = Vec::new();
    for draw in forkclass::class_draws(CENSUS_SEED, None).take(CENSUS_DRAWS) {
        let world = forkclass::world_of(&draw);
        let b = Built::of(world.clone());
        if forkclass::binary_holds(&b).is_err() {
            refused += 1;
            continue;
        }
        held += 1;
        let (_, prios) =
            forkclass::kernel_answer_with_grants(&b).unwrap_or_else(|e| panic!("draw {}: the kernel: {e}", draw.index));
        let answers = forkplan::comparand_answers(&b, &prios, &oracle)
            .unwrap_or_else(|e| panic!("draw {}: the oracle: {e}", draw.index));
        let class = forkclass::class_of(&b).key();
        let mut line =
            forkclass::drawn_line(format!("census draw {}", draw.index), CENSUS_SEED, draw.index, &draw, &world, &class);
        for key in forkclass::ANSWERS {
            forkclass::set_answer(&mut line, key, answers[key].clone());
        }
        let findings = forkclass::compare_line(&line, &mut t);
        let p = p64_precondition(&b, &prios);
        pre += usize::from(p);
        // Since the W-40 land step the comparand RUNS P64 (`forkplan::comparand_answers`: the
        // fork's `PlanInput::with_runs`), so the kernel is held to it on every day, and what
        // D74 moves is the comparand's own `p64` flag: set where the runs move the fork's day.
        let runs_moved = answers["p64"]["p64"] == true;
        p64_moved += usize::from(runs_moved);
        if runs_moved && !p {
            bad.push(format!("draw {} ({class}): the runs moved the fork's day without P64's precondition", draw.index));
        }
        if findings.is_empty() {
            continue;
        }
        moved += 1;
        values += findings.len();
        bad.push(format!("draw {} ({class}): {}", draw.index, findings.join("; ")));
        if shown.len() < 8 {
            shown.push(format!("draw {} ({class}): {}", draw.index, findings.join("; ")));
        }
    }
    println!(
        "D74 census ({CENSUS_SEED:?}, {CENSUS_DRAWS} draws): {held} held by the binary, {refused} refused; \
         P64's precondition on {pre} day(s); the runs move the fork's day on {p64_moved}; the kernel plans unlike \
         the comparand on {moved} day(s), {values} value(s); {}",
        t.line(values)
    );
    for s in &shown {
        println!("  {s}");
    }
    assert!(held > 0, "the census held no world");
    assert!(
        bad.is_empty(),
        "{} day(s) the kernel plans unlike the comparand, or the runs move the fork's day without P64's precondition:\n  {}",
        bad.len(),
        bad.join("\n  ")
    );
}

