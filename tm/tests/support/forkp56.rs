//! **Seeded P56 days: P56's rule, the comparand's, checked against the in-tree fork's cut
//! before R3 and by value after it** (stage 6 W-40 track H, README gap 3719).
//!
//! # The finding this answers
//!
//! The comparand applies P56 two ways, one per backend (`support/forkplan.rs`): the in-tree
//! backend takes it from `tm-core/src/planner.rs`' `cut_out` (W-37 track T changed the fork's
//! `past_segments` to agree with the kernel), the oracle backend from `forkplan::p56_cut` over
//! fork 4748911's own drawing and `forkclass`' own wall reader. Their cross-check
//! (`planner_invariants.rs`' region, 43 and 91 fresh draws at W-39) met NO P56 day: the class
//! draw rarely runs a block across a meeting. R3 deleted the in-tree backend, and then
//! `p56_cut` is the comparand's only P56, held by a few frozen lines whose mutants die only
//! under `TM_ORACLE`.
//!
//! # What this adds
//!
//! P56 days drawn ON PURPOSE ([`p56_days`]): the class draw's case with a meeting passed by the
//! running block (`plangen::pass_a_meeting`, the P56 arm's own draw, one definition), typed
//! wider than the wall on half the draws (`plangen::timer_marks`' `typed`), kept where the
//! shipped binary holds the world (`forkclass::binary_holds`, D64(b)) and its replay holds a
//! Pause a wall of the day covers ([`is_p56_day`]). Each frozen line
//! (`tests/fixtures/fork-4748911-planner-p56.jsonl`) is a class line — the world, its
//! provenance and `forkclass::ANSWERS`, compared with the kernel by `forkclass::compare_line` —
//! plus `cut`: the SHIPPED fork's day as the in-tree fork drew it (`cut_out`'s answer). Since
//! `shipped` on such a line is fork 4748911's own drawing (taken from `tm-oracle plan` at the
//! bless, and held there equal to the in-tree reconstruction), `p56_cut(shipped) = cut` is the
//! in-tree cut against the comparand's rule, frozen BY VALUE: after R3 a mutant of `p56_cut`
//! dies in plain `cargo test`, with no oracle and no in-tree fork.

#![allow(dead_code)]

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config as ProptestConfig, RngAlgorithm, TestRng, TestRunner};
use serde_json::Value;

use tm_core::config::Config;
use tm_core::log::SegmentKind;

use crate::forkclass::{self, Built, ClassWorld, Draw, Widening};
use crate::plangen;

/// The seeded P56 days' ChaCha seed text (the class draw's convention).
pub const P56_SEED: &str = "W-40 track H P56 days, gap 3719";

/// How many seeded P56 days the frozen file holds.
pub const P56_FROZEN: usize = 24;

/// How many the live cross-check walks while the in-tree fork is here.
pub const P56_LIVE: usize = 64;

/// The frozen file.
pub const FROZEN_P56: &str = "fork-4748911-planner-p56.jsonl";

/// Where it lives.
pub fn p56_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(FROZEN_P56)
}

/// The frozen lines, in file order; a draw carried twice FAILS ([`p56_lines_of`]).
pub fn p56_lines() -> Vec<Value> {
    let path = p56_path();
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e} — see support/forkp56.rs", path.display()));
    p56_lines_of(&text)
}

/// **A frozen P56 file's text, read**: one JSON line per seeded day, blank lines skipped — and
/// a draw carried twice FAILS.
pub fn p56_lines_of(text: &str) -> Vec<Value> {
    let mut seen = std::collections::BTreeSet::new();
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Value = serde_json::from_str(l).expect("a frozen P56 line is JSON");
            let d = v["draw"].as_u64().expect("a P56 line names its draw");
            assert!(seen.insert(d), "two P56 lines for draw {d}");
            v
        })
        .collect()
}

/// **One seeded draw**: the class draw's case with a meeting passed, and whether the pause over
/// it is typed ten minutes wider than the wall at each end.
#[derive(Clone, Debug)]
pub struct P56Draw {
    pub index: usize,
    pub case: plangen::Case,
    pub typed: bool,
}

/// **The draws from `seed`** — `plangen::case_strategy`'s case and a `typed` coin per draw,
/// from a ChaCha seeded by the text's bytes space-padded to 32 (`forkclass::class_draws`'
/// convention), each case run through `plangen::pass_a_meeting`.
pub fn p56_draws(seed: &str) -> impl Iterator<Item = P56Draw> {
    let mut bytes = [b' '; 32];
    for (d, s) in bytes.iter_mut().zip(seed.bytes()) {
        *d = s;
    }
    let mut runner = TestRunner::new_with_rng(ProptestConfig::default(), TestRng::from_seed(RngAlgorithm::ChaCha, &bytes));
    let case_s = plangen::case_strategy();
    let typed_s = any::<bool>();
    (0usize..).map(move |index| {
        let mut case = case_s.new_tree(&mut runner).expect("a case").current();
        let typed = typed_s.new_tree(&mut runner).expect("a coin").current();
        plangen::pass_a_meeting(&mut case);
        P56Draw { index, case, typed }
    })
}

/// The world a draw builds: `plangen::build_with` at the default configuration, typed as drawn.
pub fn world_of(d: &P56Draw) -> ClassWorld {
    let w = plangen::build_with(&d.case, Config::default(), d.typed);
    ClassWorld { docs: w.docs, log: w.log, state: w.state, now: w.now, mult: None, ratio: None }
}

/// **A P56 day**: the planned date's replay holds a Pause that a wall of the day — the walls
/// `forkplan::p56_cut` reads, `forkclass::Built::walls` — covers in part, so P56's drawing and
/// fork 4748911's differ there.
pub fn is_p56_day(b: &Built) -> bool {
    let tz = b.cfg.tz;
    let walls = b.walls();
    b.replay.day(b.date()).is_some_and(|d| {
        d.segments.iter().filter(|g| matches!(g.kind, SegmentKind::Pause { .. })).any(|g| {
            let (s, e) = (g.start.with_timezone(&tz), g.end.with_timezone(&tz));
            walls.iter().any(|(_, lo, hi, _)| s < *hi && *lo < e)
        })
    })
}

/// **The seeded P56 days**: draws whose world the shipped binary holds and that are P56 days,
/// in draw order, with their worlds.
pub fn p56_days(seed: &str) -> impl Iterator<Item = (P56Draw, ClassWorld)> {
    p56_draws(seed).filter_map(|d| {
        let w = world_of(&d);
        let b = Built::of(w.clone());
        // The cheap test first: `binary_holds` runs the binary twice.
        (is_p56_day(&b) && forkclass::binary_holds(&b).is_ok()).then_some((d, w))
    })
}

/// **A frozen P56 line's shape** — `forkclass::drawn_line` (the class line's world and
/// provenance, arm `base`) named `p56 draw <index>`, with `typed` beside the case; the caller
/// writes the answers and `cut`.
pub fn p56_line(d: &P56Draw, w: &ClassWorld, class: &str) -> Value {
    let draw = Draw { index: d.index, case: d.case.clone(), widening: Widening::Base };
    let mut line = forkclass::drawn_line(format!("p56 draw {}", d.index), P56_SEED, d.index, &draw, w, class);
    line["typed"] = Value::Bool(d.typed);
    line
}
