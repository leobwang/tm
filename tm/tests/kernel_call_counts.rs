//! **The per-verb kernel-call count** — design §14.6's instrument beside T11
//! ("the per-verb kernel-call count against R14's baseline table"), built here
//! against the **unswitched** binary so that the switch commit is the body swap
//! and nothing else (the owner's D19).
//!
//! # What it counts, and where from
//!
//! Two counters, both already opt-in in shipped code, both read off stderr:
//!
//! * `tm_kernel_ffi::TRACE_CALLS_ENV` (`TM_TRACE_KERNEL_CALLS`) — one
//!   `kernel call: <kind>` line per call through the FFI. It sits at the FFI
//!   because that is the **one door**: `kernel_bridge.rs` and `kernel_log.rs`
//!   each reach the kernel on their own, so a counter in either would miss the
//!   other.
//! * `tm::cli::ctx::TRACE_SCOPE_ENV` (`TM_TRACE_REPLAY_SCOPE`) — one
//!   `replay scope: <scope>` line per `Ctx::replay_with`, which is the call
//!   whose body becomes `kernel_log::replay_scoped` at the switch. **Every one
//!   of these becomes a kernel `log` call at S**, so this column is what S's
//!   own count must be compared with.
//!
//! # What the baseline is, and what bites today
//!
//! Before the switch **no verb makes a single `log` call** — nothing under
//! `tm/src` calls `kernel_log::` at all — so the assertion this file turns on
//! today is `log == 0` for every verb. That is not a formality: it is the guard
//! against a **half-switched binary** (some verbs reading through the kernel,
//! some through the Rust reader), which is the exact failure D19's
//! all-or-nothing rule exists to prevent. At S the switch updates
//! [`EXPECTED_LOG_CALLS`] to the real per-verb count and the same harness
//! starts guarding the other direction.
//!
//! # What it does NOT count, said plainly
//!
//! The undo recorder's reads (`Recorder::start` / `Recorder::finish`, and
//! `Ctx::log_tail_of`) do **not** pass through `Ctx::replay_with`, so they do
//! not appear in the replay column. README R14 measured 4–5 whole-log reads per
//! writing verb and named those two as part of them; only the `replay_with`
//! share is visible here. Counting the rest would mean instrumenting
//! `Ctx::replay_of`, which this step is forbidden to touch (it is the switch's
//! own body). At S every one of those reads becomes a kernel call and the FFI
//! column counts them all with no change to this file.

mod cli_common;

use std::collections::BTreeMap;

use cli_common::Tm;

/// The per-verb `log`-call count this binary must show. **All zero before the
/// switch**; S replaces this table with the counts it measures.
const EXPECTED_LOG_CALLS: u32 = 0;

/// `tm/src/cli/ctx.rs`'s `TRACE_SCOPE_ENV`, spelled out rather than imported:
/// `tm` is a **binary-only** package (its `Cargo.toml` declares `[[bin]]` and
/// no `[lib]`), so an integration test cannot name anything inside it. The FFI
/// constant beside it *is* imported, because `tm-kernel-ffi` is a real library
/// dependency. If the constant in `ctx.rs` is ever renamed, this test goes
/// vacuous — which is why the assertions below check that the trace is live
/// rather than only that the counts are zero.
const TRACE_SCOPE_ENV: &str = "TM_TRACE_REPLAY_SCOPE";

/// What one traced run reported.
#[derive(Debug, Default, Clone)]
struct Counts {
    /// `kernel call: log` — the replay op. 0 until S.
    log: u32,
    /// `kernel call: apply` — a command call through `kernel_bridge`.
    apply: u32,
    /// `kernel call: capacity` — D10's lookahead call.
    capacity: u32,
    /// Any other request shape reaching the FFI.
    other: u32,
    /// `replay scope: …` — one per `Ctx::replay_with`.
    replays: u32,
    /// The scopes asked for, in order (§11.1).
    scopes: Vec<String>,
}

impl Counts {
    fn kernel_calls(&self) -> u32 {
        self.log + self.apply + self.capacity + self.other
    }
}

/// Run one verb with both traces on and count what it reported.
fn traced(tm: &Tm, now: &str, args: &[&str]) -> (i32, Counts) {
    let out = tm.run_env_at(
        now,
        &[
            (tm_kernel_ffi::TRACE_CALLS_ENV, "1"),
            (TRACE_SCOPE_ENV, "1"),
        ],
        args,
    );
    let mut c = Counts::default();
    for line in out.stderr.lines() {
        if let Some(kind) = line.strip_prefix("kernel call: ") {
            match kind.trim() {
                "log" => c.log += 1,
                "apply" => c.apply += 1,
                "capacity" => c.capacity += 1,
                _ => c.other += 1,
            }
        } else if let Some(scope) = line.strip_prefix("replay scope: ") {
            c.replays += 1;
            c.scopes.push(scope.trim().to_string());
        }
    }
    (out.code, c)
}

/// The verbs R14's table timed, in an order each one's preconditions allow:
/// the day's clock verbs, then a write verb, then the three read verbs.
const VERBS: &[(&str, &[&str])] = &[
    ("wake", &["wake", "06:05", "--slept", "8h10m"]),
    ("arrive", &["arrive", "lounge"]),
    ("start", &["start", "^t4", "--energy", "4"]),
    ("pause", &["pause"]),
    ("done", &["done", "--went", "1"]),
    ("energy", &["energy", "3"]),
    ("break", &["break", "20m"]),
    ("drop", &["drop", "^t3"]),
    ("undo", &["undo"]),
    ("review day", &["review", "day"]),
    ("log", &["log", "--tail", "5"]),
    ("check", &["check"]),
];

#[test]
fn no_verb_makes_a_kernel_log_call_before_the_switch() {
    let tm = Tm::new();
    let mut table: BTreeMap<&str, Counts> = BTreeMap::new();
    for (name, args) in VERBS {
        let (code, c) = traced(&tm, cli_common::NOW, args);
        assert_eq!(code, 0, "`tm {}` failed under tracing", args.join(" "));
        table.insert(name, c);
    }

    // The table, for the README block and for S to compare against.
    eprintln!("per-verb kernel calls (unswitched binary)");
    eprintln!("{:<12} {:>4} {:>6} {:>9} {:>6} {:>8}  scopes", "verb", "log", "apply", "capacity", "other", "replays");
    for (name, c) in &table {
        eprintln!(
            "{:<12} {:>4} {:>6} {:>9} {:>6} {:>8}  {}",
            name, c.log, c.apply, c.capacity, c.other, c.replays, c.scopes.join(",")
        );
    }

    // **The assertion S turns around.** Today every one of these is 0: nothing
    // under `tm/src` calls `kernel_log::`, so a non-zero count here means some
    // verb has begun reading through the kernel while others have not — the
    // half-switched binary D19 forbids.
    for (name, c) in &table {
        assert_eq!(
            c.log, EXPECTED_LOG_CALLS,
            "`tm {name}` made {} kernel `log` call(s) before the switch; \
             the switch is all-or-nothing (D19) and this binary is half-switched",
            c.log
        );
    }

    // **The harness is not vacuous** (README gap 16's lesson: a check no input
    // can fail is not a check). Both traces must actually be live: the run as a
    // whole reached the kernel, and every verb asked for at least one replay.
    let calls: u32 = table.values().map(Counts::kernel_calls).sum();
    assert!(calls > 0, "no kernel call was traced at all — the FFI counter is not live");
    for (name, c) in &table {
        assert!(c.replays >= 1, "`tm {name}` traced no replay at all — the scope counter is not live");
        assert!(
            c.scopes.iter().all(|s| s == "hot" || s == "all" || s.starts_with("dates ")),
            "`tm {name}` named a scope this harness does not know: {:?}",
            c.scopes
        );
    }
}
