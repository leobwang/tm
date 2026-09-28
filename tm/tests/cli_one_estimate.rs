//! **An estimate has ONE reader, and every writer leaves ONE estimate** —
//! stage 6 W-36 track T: README gap **2929** (the `u32` edge of `tm edit est=`
//! was a kernel fault) and the owner's **D62** (gaps 2926 and 2928, a registered
//! divergence: `tm extend`, `tm stop` and `tm done --partial` write through the
//! kernel's `est` op, the one path `tm edit est=` takes since D56).
//!
//! Every test here reads the bytes on disk and the log, never only an exit
//! code: a refusal that wrote something is the class these exist to catch.

mod cli_common;

use cli_common::Tm;

/// `.tm/log.jsonl`'s bytes, or empty when there is no log yet.
fn log_text(tm: &Tm) -> String {
    std::fs::read_to_string(tm.plan.join(".tm/log.jsonl")).unwrap_or_default()
}

/// **Gap 2929, the refusal half.** Before W-36 the host pre-parsed `est=` in
/// `u32` and the kernel read it again as a `Nat`: `4294967296m` was refused by
/// the HOST (`invalid duration`) and `4294967295m` was written — after which
/// `tm plan` answered `kernel fault: capacity response: need`. The kernel is the
/// one reader now, bounded by `Look.maxPlanMinutes` (fork `u32`), and every
/// spelling past it — minutes, hours, blocks at `plan-basic`'s 60 — is its
/// `badValue est`, rc 1, with not a byte written to the file or the log.
#[test]
fn an_estimate_past_the_hosts_width_is_refused_by_name_and_writes_nothing() {
    let tm = Tm::new();
    let file = tm.read("backlog.md");
    let log = log_text(&tm);
    for v in ["4294967296m", "71582789h", "71582789b"] {
        let out = tm.run(&["edit", "^a1", &format!("est={v}")]);
        assert_eq!(out.code, 1, "est={v}: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("badValue"), "est={v}: refused by the kernel's name: {}", out.stderr);
        assert!(out.stderr.contains(v), "est={v}: the refusal names the value typed: {}", out.stderr);
        assert_eq!(tm.read("backlog.md"), file, "est={v} wrote the file");
        assert_eq!(log_text(&tm), log, "est={v} wrote the log");
    }
    let out = tm.run(&["--json", "edit", "^a1", "est=4294967296m"]);
    let doc: serde_json::Value = serde_json::from_str(out.stderr.trim()).expect("a JSON document");
    assert_eq!(doc["detail"]["refusal"], "badValue");
    assert_eq!(doc["detail"]["key"], "est");
    assert_eq!(doc["detail"]["value"], "4294967296m");
}

/// **Gap 2929, the other half: the bound itself is read, and planning over it
/// is not a fault.** `4294967295m` is an estimate the host's grammar reads, so
/// the edit writes it (one estimate, the leading one), `tm check` finds
/// nothing, and `tm plan` — which decoded the capacity answer's `need`
/// (`⌈4294967295 × 1.3⌉`, past `u32`) as a `u32` and faulted — answers.
#[test]
fn an_estimate_at_the_hosts_width_plans_without_a_fault() {
    let tm = Tm::new();
    tm.ok(&["edit", "^a1", "est=4294967295m"]);
    assert_eq!(
        tm.line("backlog.md", "a1"),
        "- [ ] 2 4294967295m Insurance claim for the bike  ^a1"
    );
    let check = tm.run(&["check"]);
    assert_eq!(check.code, 0, "{}{}", check.stdout, check.stderr);
    let plan = tm.run(&["plan"]);
    assert_eq!(plan.code, 0, "{}{}", plan.stdout, plan.stderr);
    assert!(!plan.stderr.contains("kernel fault"), "{}", plan.stderr);
}

/// **…and with that item RUNNING.** Once the kernel stopped faulting first, the
/// fork planner's plan-honesty sum (`committed`, `u32` with `+`) was the next
/// thing to meet the value: `tm now` and `tm plan` panicked a debug build
/// (exit 101, `attempt to add with overflow` in `Planner::diagnose`). The sum
/// saturates now; both answer, and the header reads the worked minutes.
#[test]
fn a_running_block_at_the_hosts_width_plans_and_reads() {
    let tm = Tm::new();
    tm.ok(&["edit", "^t4", "est=4294967295m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let at = "2026-09-07T09:06:00-05:00";
    for verb in [&["now"][..], &["plan"][..]] {
        let out = tm.run_at(at, verb);
        assert_eq!(out.code, 0, "tm {verb:?}: {}{}", out.stdout, out.stderr);
        assert!(!out.stderr.contains("panicked"), "tm {verb:?}: {}", out.stderr);
    }
    let json = tm.json_at(at, &["now"]);
    assert_eq!(json["active"]["elapsed_min"], 6, "{json}");
}

/// **D62 on a leading-estimate line**: `^t4` is `- [ ] 3 1b Claude Code
/// drafts tests @m2 ^t4`. Each verb that writes the estimate leaves exactly one
/// on the line — the leading one, rewritten in place with the value as the verb
/// spells it — and `tm check` stays clean. Before D62 each of the three
/// appended an `est:` token beside the `1b` (README gap 2926).
#[test]
fn every_estimate_writer_leaves_one_estimate_on_a_leading_estimate_line() {
    // `tm extend 30m`: 60 + 30 = 90 minutes, not whole blocks of 60, so `1h30m`.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm.ok(&["extend", "30m"]);
    assert_eq!(tm.line("week/2026-W37.md", "t4"), "- [>] 3 1h30m Claude Code drafts tests     @m2 ^t4");
    assert_eq!(tm.run(&["check"]).code, 0);

    // `tm stop` 25 minutes in: 60 − 25 = 35 minutes left.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T09:25:00-05:00", &["stop"]);
    assert_eq!(tm.line("week/2026-W37.md", "t4"), "- [ ] 3 35m Claude Code drafts tests     @m2 ^t4");
    assert_eq!(tm.last_ev("stop")["remaining_min"], 35);
    assert_eq!(tm.run_at("2026-09-07T09:26:00-05:00", &["check"]).code, 0);

    // `tm done --partial` an hour in, after an extend: 120 − 60 = 60, `1b`.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm.ok(&["extend", "1b"]);
    tm.ok_at("2026-09-07T10:00:00-05:00", &["done", "--partial"]);
    assert_eq!(tm.line("week/2026-W37.md", "t4"), "- [ ] 3 1b Claude Code drafts tests     @m2 ^t4");
    assert_eq!(tm.last_ev("done")["partial"], true);
    assert_eq!(tm.run_at("2026-09-07T10:01:00-05:00", &["check"]).code, 0);
}

/// **D62 where the slot is an `est:` token** (its second half): `^t3` is
/// `- [>] 4 2b Exercises … est:1b ^t3`, so the token is what `remaining` reads
/// and what the `est` op writes — in canonical minutes, D49's settled
/// rendering, the bytes `tm edit ^t3 est=2b` writes there. Fork `tm extend`
/// wrote the verb's own `est:2b`; the value is the same 120 minutes.
#[test]
fn a_token_slot_is_written_in_canonical_minutes() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t3", "--energy", "4"]);
    tm.ok(&["extend", "1b"]);
    let line = tm.line("week/2026-W37.md", "t3");
    assert_eq!(line, "- [>] 4 2b Exercises 5.3–5.5            @m1 est:120m ^t3");
    let edited = Tm::new();
    edited.ok(&["edit", "^t3", "est=2b"]);
    assert!(
        edited.line("week/2026-W37.md", "t3").ends_with("est:120m ^t3"),
        "`tm extend` and `tm edit est=` write one rendering of one value"
    );
}

/// **An extend past the host's width is refused by name, before anything is
/// written** (D62 with gap 2929): the sum is taken wide and sent in minutes, so
/// the kernel's one reader refuses it — no line, no state, no `extend` event.
/// Before W-36, `remaining + by` was `u32` arithmetic in the host.
#[test]
fn an_extend_past_the_hosts_width_is_refused_by_name() {
    let tm = Tm::new();
    tm.ok(&["edit", "^t4", "est=4294967295m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let file = tm.read("week/2026-W37.md");
    let log = log_text(&tm);
    let state = tm.state();
    let out = tm.run_at("2026-09-07T09:05:00-05:00", &["extend", "1b"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("badValue"), "{}", out.stderr);
    assert_eq!(tm.read("week/2026-W37.md"), file);
    assert_eq!(log_text(&tm), log);
    assert_eq!(tm.state(), state);
}
