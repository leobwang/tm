//! **The per-verb kernel-call count** — design §14.6's instrument beside T11
//! ("the per-verb kernel-call count against R14's baseline table"), landed
//! against the **unswitched** binary under D19 and **turned around at S**.
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
//!   `replay scope: <scope>` line per `Ctx::replay_with`, which **is**
//!   `kernel_log::replay_scoped` since S.
//!
//! # What bites, before and after
//!
//! Before the switch no verb's replay came from the kernel, so this file
//! asserted `log == 0` for every verb but `tm check`. That was the guard
//! against a **half-switched binary** — some verbs reading through the kernel,
//! some through the Rust reader — which is the exact failure D19's
//! all-or-nothing rule exists to prevent.
//!
//! S turns it around and the guard is the same shape: now every verb must make
//! **at least one** `log` call, because a verb making none would be a verb that
//! found some other way to its facts. The counts are also pinned **exactly**
//! ([`expected_log_calls`]), so an extra whole-log read per verb is a finding
//! rather than a silent regression. Both halves are asserted, separately and on
//! purpose: the "at least 1" survives a future re-measurement of the table.
//!
//! **`tm check` carries one more than its replay** (gap 134): a read-only sweep
//! for the log's unreadable lines, because an answer's `warnings` array is per
//! call and genesis returns only its last chunk's — so a `tm check` reading
//! warnings off an answer would silently name the final chunk's lines alone.
//!
//! # What the numbers include, said plainly
//!
//! Every host-side read of `.tm/log.jsonl` is now a kernel call, so this column
//! counts all of them: a verb's `Ctx::replay_with` calls, the undo recorder's
//! two tail reads (`Recorder::start` / `Recorder::finish`, through
//! `Ctx::log_tail_of`), and `tm log`'s `render` op for the selected lines'
//! bytes. README R14 measured 4-5 whole-log *reads* per writing verb before the
//! switch and only the `replay_with` share was visible here; after it, the FFI
//! column sees the lot — which is why `wake` reads 3 where its replay column
//! reads 2.

mod cli_common;

use std::collections::BTreeMap;

use cli_common::Tm;

/// **The per-verb `log`-call count this binary must show** — measured at S and
/// pinned here, the table design §14.6 asks for beside T11.
///
/// Before the switch every entry was **0** except `tm check`'s sweep, and that
/// zero was the half-switch guard: a verb reading through the kernel while
/// others read through Rust would have fired it. S turns the guard around
/// without weakening it. Every verb is now **at least 1** — that is the
/// all-or-nothing gate (D19), and it is asserted separately below so a future
/// half-switch is caught even if someone re-measures this table — and each
/// count is **exact**, so a verb that grows an extra whole-log read is a
/// finding rather than a silent regression.
///
/// Reading the numbers: a verb's count is its `Ctx::replay_with` calls plus the
/// undo recorder's two tail reads (`Recorder::start` and `Recorder::finish`,
/// through `Ctx::log_tail_of`) plus, for `tm log`, the `render` op that reads
/// the selected lines' bytes (§11.4 step 3). `tm check` carries one more than
/// its replay: gap 134's read-only sweep, which is how it names **every**
/// unreadable line rather than the last chunk's.
fn expected_log_calls(verb: &str) -> u32 {
    match verb {
        "wake" => 3,
        "arrive" => 4,
        "start" => 3,
        "pause" => 3,
        "done" => 3,
        "energy" => 4,
        "break" => 2,
        "drop" => 3,
        "undo" => 2,
        "review day" => 1,
        "log" => 2,
        "check" => 2,
        other => panic!("`tm {other}` is not in the measured table"),
    }
}

/// **The per-verb `emit`-call count** — the writer S2 added (**D16**), measured
/// at S2 and pinned here beside the reader's.
///
/// One call per event a verb appends, because the kernel now renders every line
/// the binary writes. Reading the numbers: `arrive` and `energy` make **two**
/// because each also appends the `plan` event its replan writes (`planning.rs`);
/// `tm break 20m` makes **none**, because the `break` entry is appended when the
/// break *ends*, not when it starts; and the three read-only verbs append
/// nothing at all.
///
/// Pinned exactly, for the reason the `log` column is: a verb that starts
/// appending — or quietly stops — is a behaviour change, and this is the column
/// it shows up in. Before S2 every entry here was 0, because the binary wrote
/// its own bytes.
fn expected_emit_calls(verb: &str) -> u32 {
    match verb {
        "wake" => 1,
        "arrive" => 2,
        "start" => 1,
        "pause" => 1,
        "done" => 1,
        "energy" => 2,
        "break" => 0,
        "drop" => 1,
        "undo" => 1,
        "review day" => 0,
        "log" => 0,
        "check" => 0,
        other => panic!("`tm {other}` is not in the measured table"),
    }
}

/// `tm/src/cli/ctx.rs`'s `TRACE_SCOPE_ENV`, spelled out rather than imported:
/// `tm` is a **binary-only** package (its `Cargo.toml` declares `[[bin]]` and
/// no `[lib]`), so an integration test cannot name anything inside it. The FFI
/// constant beside it *is* imported, because `tm-kernel-ffi` is a real library
/// dependency. If the constant in `ctx.rs` is ever renamed, this test goes
/// vacuous — which is why the assertions below check that the trace is live
/// rather than only that the counts match.
const TRACE_SCOPE_ENV: &str = "TM_TRACE_REPLAY_SCOPE";

/// What one traced run reported.
#[derive(Debug, Default, Clone)]
struct Counts {
    /// `kernel call: log` — the replay op. At least 1 a verb since S.
    log: u32,
    /// `kernel call: apply` — a command call through `kernel_bridge`.
    apply: u32,
    /// `kernel call: capacity` — D10's lookahead call.
    capacity: u32,
    /// `kernel call: emit` — the writer S2 added (**D16**): one per event a verb
    /// appends, because the kernel now renders every line the binary writes.
    emit: u32,
    /// Any other request shape reaching the FFI.
    other: u32,
    /// `replay scope: …` — one per `Ctx::replay_with`.
    replays: u32,
    /// The scopes asked for, in order (§11.1).
    scopes: Vec<String>,
}

impl Counts {
    fn kernel_calls(&self) -> u32 {
        self.log + self.apply + self.capacity + self.emit + self.other
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
                "emit" => c.emit += 1,
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
fn every_verb_reads_the_log_through_the_kernel_after_the_switch() {
    let tm = Tm::new();
    let mut table: BTreeMap<&str, Counts> = BTreeMap::new();
    for (name, args) in VERBS {
        let (code, c) = traced(&tm, cli_common::NOW, args);
        assert_eq!(code, 0, "`tm {}` failed under tracing", args.join(" "));
        table.insert(name, c);
    }

    // The table, for the README block and for S to compare against.
    eprintln!("per-verb kernel calls (switched binary)");
    eprintln!(
        "{:<12} {:>4} {:>5} {:>6} {:>9} {:>6} {:>8}  scopes",
        "verb", "log", "emit", "apply", "capacity", "other", "replays"
    );
    for (name, c) in &table {
        eprintln!(
            "{:<12} {:>4} {:>5} {:>6} {:>9} {:>6} {:>8}  {}",
            name, c.log, c.emit, c.apply, c.capacity, c.other, c.replays, c.scopes.join(",")
        );
    }

    // **The gate, in the direction that matters after S.** Every verb reads the
    // log through the kernel: a zero here is a verb that found some other way
    // to its facts, which is the half-switched binary D19 forbids. This is
    // stated over the whole table rather than per verb, so it keeps biting even
    // if the exact counts below are ever re-measured.
    for (name, c) in &table {
        assert!(
            c.log >= 1,
            "`tm {name}` made no kernel `log` call at all — it is not reading through the kernel, \
             and the switch is all-or-nothing (D19)"
        );
    }

    // **The exact counts** (design §14.6's table beside T11): a verb that grows
    // an extra whole-log read is a finding, not a new baseline.
    for (name, c) in &table {
        let want = expected_log_calls(name);
        assert_eq!(
            c.log, want,
            "`tm {name}` made {} kernel `log` call(s), expected {want}",
            c.log
        );
    }

    // **The writer's exact counts** (S2, owner decision D16). Every line the
    // binary appends is one kernel `emit` call, so this column *is* the writer
    // swap, made countable. Before S2 it was 0 everywhere.
    for (name, c) in &table {
        let want = expected_emit_calls(name);
        assert_eq!(
            c.emit, want,
            "`tm {name}` made {} kernel `emit` call(s), expected {want}",
            c.emit
        );
    }

    // **And the swap is real**, so this column cannot go quietly back to zero:
    // a binary that wrote its own bytes again would pass every count above and
    // fail here.
    let written: u32 = table.values().map(|c| c.emit).sum();
    assert!(
        written > 0,
        "no verb wrote a line through the kernel — the binary is writing its own bytes again (D16)"
    );

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
