//! **The decoder's three completions, measured** — stage 6 W-40 track E
//! (README gap 2877).
//!
//! `tm_core::planwire::read_plan` reads the kernel's day into the host's
//! `DayPlan`, and three of `Diagnostics`' fields are NARROWER on the wire than
//! in the host's type, so the decoder completes them from what the host already
//! holds — and checks the kernel's half against it, failing by name where the
//! two disagree:
//!
//! * `underused`: the kernel names the ids; the slot energy and the item's `ci`
//!   are rebuilt from the decoded rows and the candidates;
//! * `impossible`: the kernel names the ids; the date is the grant's `until`
//!   (README gap 2640: the kernel does not write it);
//! * `blocked`: the kernel names the ids; the dependencies are the candidate's
//!   own (`Candidate::ineligible_reason`).
//!
//! Gap 2877 asked whether R3 keeps that route. This file is the measurement
//! the call stands on: a seeded draw of the generator every planning suite
//! draws from (`support/plangen.rs`), each day asked of the kernel through the
//! harness's request (`support/planreq.rs`, whose capacity section is the
//! binary's own encoder since W-40) and read back by the decoder R3 swaps in.
//! It asserts that EVERY day the kernel plans decodes — so on every drawn day
//! the host's completion and the kernel's id lists agree — and it prints how
//! often each completion actually had something to complete, because a
//! completion that never fires is checked by nothing here. The draw is
//! deterministic (a fixed ChaCha seed), so the counts are a measurement of the
//! generator and not of the clock (D46).

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[allow(dead_code)]
#[path = "support/planreq.rs"]
mod planreq;

#[allow(dead_code)]
#[path = "support/plangen.rs"]
mod plangen;

use proptest::strategy::{Strategy, ValueTree};
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use tm_core::planwire;
use tm_core::priority;

/// How many days are drawn: half of D72's frozen batch, to keep the suite's wall time
/// off `cli_latency`'s load (README gap 1333); W-40 measured 128 once (gap 2877's block).
const DRAWS: usize = 64;

#[test]
fn every_drawn_day_decodes_and_each_completion_is_counted() {
    let rng = TestRng::from_seed(RngAlgorithm::ChaCha, &[40u8; 32]);
    let mut runner = TestRunner::new_with_rng(Config::default(), rng);
    let strategy = plangen::case_strategy();
    let (mut planned, mut refused) = (0usize, 0usize);
    let (mut underused, mut impossible, mut blocked) = (0usize, 0usize, 0usize);
    let mut defects = Vec::new();
    for draw in 0..DRAWS {
        let case = strategy.new_tree(&mut runner).expect("a case").current();
        let w = plangen::build(&case);
        let date = planwire::plan_date(&w.state, w.now);
        let cands = priority::collect_candidates(&w.tree, &w.replay, &w.cfg, &w.model, date, w.now);
        let world = planreq::World {
            docs: &w.docs,
            log: &w.log,
            tree: &w.tree,
            cfg: &w.cfg,
            state: &w.state,
            now: w.now,
            cands: &cands,
        };
        let (req, order) = planreq::request(&world, None);
        let resp = planreq::call(&req);
        if resp.get("ok").is_none() || planwire::planner_refusal(&resp).is_some() {
            refused += 1;
            continue;
        }
        let d = &resp["ok"]["plan"]["diagnostics"];
        let named = |k: &str| d[k].as_array().is_some_and(|a| !a.is_empty());
        match planreq::kernel_day_of(&resp, &world, &order) {
            Ok((k, _)) => {
                planned += 1;
                underused += usize::from(named("underused") && !k.day.diagnostics.underused.is_empty());
                impossible += usize::from(named("impossible") && !k.day.diagnostics.impossible.is_empty());
                blocked += usize::from(named("blocked") && !k.day.diagnostics.blocked.is_empty());
            }
            Err(e) => defects.push(format!("draw {draw}: {e}")),
        }
    }
    eprintln!(
        "{DRAWS} drawn days: {planned} planned and decoded, {refused} refused by the kernel, {} not \
         decoded; the completion had something to complete on {underused} (underused), {impossible} \
         (impossible's date) and {blocked} (blocked's dependencies)",
        defects.len()
    );
    assert!(
        defects.is_empty(),
        "the decoder refused a day the kernel planned -- the host's completion and the kernel's \
         ids disagree (README gap 2877):\n  {}",
        defects.join("\n  ")
    );
    assert!(planned > DRAWS / 2, "the draw planned {planned} of {DRAWS}: the measurement measured little");
}
