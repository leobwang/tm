//! **The per-verb kernel-call count** — design §14.6's instrument beside T11
//! ("the per-verb kernel-call count against R14's baseline table"), landed
//! against the **unswitched** binary under D19 and **turned around at S**.
//!
//! # What it counts, and where from
//!
//! Two counters, both already opt-in in shipped code, both read off stderr:
//!
//! * `tm_kernel_ffi::TRACE_CALLS_ENV` (`TM_TRACE_KERNEL_CALLS`) — one
//!   `kernel call: <kind>[+<kind>…]` line per call through the FFI, naming
//!   **every section that call carries**. It sits at the FFI because that is
//!   the **one door**: `kernel_bridge.rs` and `kernel_log.rs` each reach the
//!   kernel on their own, so a counter in either would miss the other.
//!
//!   **Counting lines counts calls; counting names counts sections**, and since
//!   L9 those are different numbers (README **gap 278**, closed by W-14). A
//!   capacity request carries a `log` section too — D24's seam — so it traces
//!   `kernel call: capacity+log` and it is a **second replay of the log inside
//!   the verb's own call** (README **gap 275**). Before W-14 the trace tested
//!   `"capacity":` first and stopped, so that replay was invisible here while
//!   this file pinned the `log` column *exactly* and said it had not moved.
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
///
/// **And, since L9, the `log` section every capacity request carries** — the
/// second replay README **gap 275** names. `arrive` and `energy` replan
/// (`planning.rs`) and `review day` ranks, so each of those three is **one
/// higher than it was at S2**: 5, 5 and 2 where the table read 4, 4 and 1. The
/// numbers did not change at W-14 — the *instrument* did (**gap 278**); the
/// replay was always there and this column could not see it. When gap 275's
/// one-call shape lands these three go back down by one, and that is the
/// measurement that proves it landed.
fn expected_log_calls(verb: &str) -> u32 {
    match verb {
        "wake" => 3,
        "arrive" => 5,
        "start" => 3,
        "pause" => 3,
        "done" => 3,
        "energy" => 5,
        "break" => 2,
        "drop" => 3,
        "undo" => 2,
        "review day" => 2,
        "log" => 2,
        "check" => 2,
        other => panic!("`tm {other}` is not in the measured table"),
    }
}

/// **The per-verb whole-tree `apply`-section count** — pinned for the first
/// time at W-17, because the owner's **D35** made it the column that says what
/// the write gate costs (gap 584).
///
/// An `apply` section is one whole-tree load: every plan file's lines cross the
/// FFI and the kernel runs `planWf` over the lot. Until D35 this column was
/// printed and asserted about by nothing, and the gate — one such load added to
/// every host-only write path — moved five of the twelve rows while the whole
/// suite stayed green. That is **gap 577's shape** (a fact on the wire pinned
/// by no test), one column over, and the fix is the same: pin the value.
///
/// Read the numbers against the run's order — all twelve verbs run in sequence
/// on **one** tree, so §6.3's automatic close fires on the **first** verb and
/// finds nothing to do afterwards:
///
/// * `wake` **2** = the automatic close's own apply, plus the gate;
/// * `start`, `pause`, `done`, `break` **1** = the gate alone (they came after
///   the sweep, so no automatic close);
/// * `arrive`, `energy` **1** = `day::preflight`, which was already a whole-tree
///   call before D35 (gap 115) and is now the gate — the same one call, so these
///   two rows did **not** move;
/// * `drop` **1** = its own kernel-backed write, which is why `tm drop`'s T11
///   row is what one whole-tree load costs, and why D35's measurement is
///   compared against it;
/// * `check` **1** = `kernel_bridge::tree_refusal`, D32's load-the-tree sweep,
///   which is now the same function the gate calls;
/// * `undo` **0**, deliberately — it is the way *out* of a tree the kernel
///   refuses, and a gate on it would lock the user inside one;
/// * `review day`, `log` **0** — they do not write.
///
/// So a change that adds a second whole-tree load to a verb, or that quietly
/// drops the gate from one, fails here **by name**.
fn expected_apply_calls(verb: &str) -> u32 {
    match verb {
        "wake" => 2,
        "arrive" => 1,
        "start" => 1,
        "pause" => 1,
        "done" => 1,
        "energy" => 1,
        "break" => 1,
        "drop" => 1,
        "undo" => 0,
        "review day" => 0,
        "log" => 0,
        "check" => 1,
        other => panic!("`tm {other}` is not in the measured table"),
    }
}

/// **The per-verb `capacity`-section count**, pinned exactly beside the `log`
/// column for the first time at W-14 (**gap 278**).
///
/// Three of R14's verbs compute capacity: `arrive` and `energy` because their
/// replan calls `Ctx::priorities`, and `review day` because it ranks. The other
/// nine make none — which is why `tm drop`'s T11 row is the *reliable* one
/// (README gap 240): it is the row that pays no capacity call.
///
/// Pinned exactly, and not merely "at least", because the pairing below
/// (`each capacity section is a second replay`) turns this column into gap
/// 275's denominator: one extra whole-log replay per capacity call.
fn expected_capacity_calls(verb: &str) -> u32 {
    match verb {
        "arrive" | "energy" | "review day" => 1,
        "wake" | "start" | "pause" | "done" | "break" | "drop" | "undo" | "log" | "check" => 0,
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
///
/// Every field but [`Counts::calls`] counts **sections**, not calls: one traced
/// line can name several (`capacity+log`), and since L9 one does. `calls` is
/// the line count, which is the number of times the binary crossed the FFI.
#[derive(Debug, Default, Clone)]
struct Counts {
    /// `log` sections — the replay op. At least 1 a verb since S.
    log: u32,
    /// `apply` sections — a command call through `kernel_bridge`.
    apply: u32,
    /// `capacity` sections — D10's lookahead call.
    capacity: u32,
    /// `emit` sections — the writer S2 added (**D16**): one per event a verb
    /// appends, because the kernel now renders every line the binary writes.
    emit: u32,
    /// Any other request shape reaching the FFI.
    other: u32,
    /// **Calls**, not sections: one per `kernel call:` line.
    calls: u32,
    /// Calls that named more than one section — since L9, the capacity calls
    /// (README gaps 275 and 278).
    multi: u32,
    /// `replay scope: …` — one per `Ctx::replay_with`.
    replays: u32,
    /// The scopes asked for, in order (§11.1).
    scopes: Vec<String>,
    /// Every traced line, verbatim, for the failure messages.
    lines: Vec<String>,
}

impl Counts {
    /// Sections of every kind — deliberately **not** the call count any more.
    fn sections(&self) -> u32 {
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
        if let Some(kinds) = line.strip_prefix("kernel call: ") {
            let kinds = kinds.trim();
            c.calls += 1;
            c.lines.push(kinds.to_string());
            let named: Vec<&str> = kinds.split('+').collect();
            if named.len() > 1 {
                c.multi += 1;
            }
            // **Every name on the line**, because one call can carry several
            // sections: a capacity request carries a `log` section too (D24's
            // seam), and counting only the first is what made that second
            // replay invisible here (gap 278).
            for kind in named {
                match kind {
                    "log" => c.log += 1,
                    "apply" => c.apply += 1,
                    "capacity" => c.capacity += 1,
                    "emit" => c.emit += 1,
                    _ => c.other += 1,
                }
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

    // The table, for the README block and for S to compare against. `calls` is
    // FFI crossings; every other column is **sections** (W-14, gap 278).
    eprintln!("per-verb kernel sections (switched binary)");
    eprintln!(
        "{:<12} {:>4} {:>5} {:>6} {:>9} {:>6} {:>6} {:>8}  scopes",
        "verb", "log", "emit", "apply", "capacity", "other", "calls", "replays"
    );
    for (name, c) in &table {
        eprintln!(
            "{:<12} {:>4} {:>5} {:>6} {:>9} {:>6} {:>6} {:>8}  {}",
            name, c.log, c.emit, c.apply, c.capacity, c.other, c.calls, c.replays,
            c.scopes.join(",")
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

    // **The whole-tree column, pinned exactly** — new at W-17, and the
    // instrument the owner's D35 is measured by: one `apply` section is one
    // whole-tree kernel load, which is exactly what the write gate adds.
    for (name, c) in &table {
        let want = expected_apply_calls(name);
        assert_eq!(
            c.apply, want,
            "`tm {name}` made {} whole-tree kernel load(s), expected {want} — a verb that grew \
             one is paying a second tree load, and a verb that lost one is writing without asking \
             whether the tree still loads (D35, gap 584)",
            c.apply
        );
    }

    // **The capacity column, pinned exactly** — new at W-14. Before it, a
    // capacity request answered `capacity` and nothing else; now it names every
    // section it carries, so this column and the `log` column above are read
    // from the same lines.
    for (name, c) in &table {
        let want = expected_capacity_calls(name);
        assert_eq!(
            c.capacity, want,
            "`tm {name}` sent {} kernel `capacity` section(s), expected {want}",
            c.capacity
        );
    }

    // **Gap 275, made countable.** Every capacity section travels in a call
    // that also carries a `log` section — that is D24's seam, and it is a
    // second whole-log replay inside the verb's own call. The equality is the
    // instrument: when the one-call shape lands, a verb's capacity section stops
    // bringing a replay with it and this assertion fails **by name**, which is
    // how the fix announces itself instead of being noticed in a latency row.
    for (name, c) in &table {
        let paired = c
            .lines
            .iter()
            .filter(|l| l.split('+').any(|k| k == "capacity") && l.split('+').any(|k| k == "log"))
            .count() as u32;
        assert_eq!(
            paired,
            expected_capacity_calls(name),
            "`tm {name}` traced {paired} call(s) carrying both a capacity and a log section, \
             expected {} — gap 275 is that every capacity call replays the log a second time; if \
             this is now lower, the one-call shape has landed and this table is owed a \
             re-measurement (and gap 275 a closing line)",
            expected_capacity_calls(name)
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
    let sections: u32 = table.values().map(Counts::sections).sum();
    assert!(sections > 0, "no kernel call was traced at all — the FFI counter is not live");
    // And the *multi-section* half of the trace is live too: at least one call
    // must name more than one section, or the `+` join has been lost and every
    // column silently went back to counting first-literal-wins (gap 278).
    let multi: u32 = table.values().map(|c| c.multi).sum();
    assert!(
        multi > 0,
        "no traced call named more than one section — the FFI trace is back to naming only the \
         first literal it finds, and a capacity request's log section is invisible again (gap 278)"
    );
    // No call may trace an unnamed section: a stray `+` would count as `other`
    // and read as a new request shape.
    for (name, c) in &table {
        assert!(
            c.lines.iter().all(|l| l.split('+').all(|k| !k.is_empty())),
            "`tm {name}` traced an empty section name: {:?}",
            c.lines
        );
    }
    for (name, c) in &table {
        assert!(c.replays >= 1, "`tm {name}` traced no replay at all — the scope counter is not live");
        assert!(
            c.scopes.iter().all(|s| s == "hot" || s == "all" || s.starts_with("dates ")),
            "`tm {name}` named a scope this harness does not know: {:?}",
            c.scopes
        );
    }
}

/// **The four verbs gap 275 names**, counted rather than timed.
///
/// `tm plan`, `tm now`, `tm review day` and `tm review week` each compute
/// capacity, and since L9 a capacity request carries a `log` section — so each
/// of them replays the log **twice**: once for `Ctx::replay_with` and once
/// inside the capacity call. That is what moved `tm review week` out of its T11
/// band (README gap 275); this is the same fact as a count, which is a
/// measurement a latency row cannot give because it is noisy.
///
/// It is read-only on purpose: none of the four appends a line, so the table is
/// a function of the fixture and the instant alone, and the four runs do not
/// disturb each other.
const CAPACITY_VERBS: &[(&str, &[&str])] = &[
    ("plan", &["plan"]),
    ("now", &["now"]),
    ("review day", &["review", "day"]),
    ("review week", &["review", "week"]),
];

/// The `log` sections each of the four sends, pinned exactly.
///
/// **One of these is the verb's own replay and one is the capacity call's** —
/// the pairing assertion below is what says which. When gap 275's one-call
/// shape lands, every entry here drops by one.
fn expected_capacity_verb_log_sections(verb: &str) -> u32 {
    match verb {
        "plan" | "now" | "review day" | "review week" => 2,
        other => panic!("`tm {other}` is not in the capacity-verb table"),
    }
}

#[test]
fn every_capacity_verb_replays_the_log_a_second_time_inside_its_capacity_call() {
    let tm = Tm::new();
    let mut table: BTreeMap<&str, Counts> = BTreeMap::new();
    for (name, args) in CAPACITY_VERBS {
        let (code, c) = traced(&tm, cli_common::NOW, args);
        assert_eq!(code, 0, "`tm {}` failed under tracing", args.join(" "));
        table.insert(name, c);
    }

    eprintln!("capacity verbs: sections per verb (gap 275's denominator)");
    eprintln!(
        "{:<12} {:>4} {:>9} {:>6} {:>6}  trace",
        "verb", "log", "capacity", "calls", "multi"
    );
    for (name, c) in &table {
        eprintln!(
            "{:<12} {:>4} {:>9} {:>6} {:>6}  {}",
            name, c.log, c.capacity, c.calls, c.multi, c.lines.join(" ")
        );
    }

    for (name, c) in &table {
        // Each of the four computes capacity exactly once.
        assert_eq!(
            c.capacity, 1,
            "`tm {name}` sent {} capacity section(s), expected 1",
            c.capacity
        );
        // And carries a second replay with it.
        let want = expected_capacity_verb_log_sections(name);
        assert_eq!(
            c.log, want,
            "`tm {name}` sent {} kernel `log` section(s), expected {want} — one for its own \
             replay and one inside its capacity call (gap 275). A lower number means the \
             one-call shape has landed: re-measure this table, close gap 275, and say so in \
             the README block",
            c.log
        );
        // The second replay is *inside* the capacity call, not beside it: the
        // capacity section and a log section travel on the same traced line.
        assert_eq!(
            c.multi, 1,
            "`tm {name}` traced {} call(s) carrying more than one section, expected 1 — the \
             capacity call's log section is what gap 275 costs, and if it is not there the \
             trace has stopped naming it (gap 278)",
            c.multi
        );
        assert!(
            c.lines.iter().any(|l| l == "capacity+log"),
            "`tm {name}` traced no `capacity+log` call: {:?}",
            c.lines
        );
    }
}
