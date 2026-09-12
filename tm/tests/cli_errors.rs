//! `--json` on the failure path (tm-spec-v1.md §13).
//!
//! §13 says "every verb accepts `--json`" and gives the failures their own
//! exit codes (`1` error, `3` conflict). §14 then makes the CLI the seam
//! Claude Code drives, "through the CLI (`--json`)" — so a failed verb has to
//! be a document too, not prose a caller has to parse. These tests drive the
//! binary and read *stderr*.

mod cli_common;

use cli_common::{Tm, NOW};
use serde_json::Value;

/// The error document on stderr, with the run's exit code checked.
fn err_doc(stderr: &str) -> Value {
    serde_json::from_str(stderr)
        .unwrap_or_else(|e| panic!("stderr is not one JSON document ({e}): {stderr:?}"))
}

#[test]
fn a_failure_under_json_is_a_document_on_stderr() {
    let tm = Tm::new();
    let out = tm.run(&["drop", "^nope", "--json"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(out.stdout, "", "the document belongs on stderr");

    let doc = err_doc(&out.stderr);
    assert_eq!(doc["ok"], Value::Bool(false));
    assert_eq!(doc["kind"], "not-found");
    assert_eq!(doc["message"], "no such item: ^nope");
    assert_eq!(doc["exit_code"], 1);
    // The id the caller asked for, so a script never parses the sentence.
    assert_eq!(doc["detail"]["id"], "^nope");
}

#[test]
fn the_human_failure_is_unchanged() {
    // §13 gives `--json` its own output; the human line must not move.
    let tm = Tm::new();
    let out = tm.run(&["drop", "^nope"]);
    assert_eq!(out.code, 1);
    assert_eq!(out.stdout, "");
    assert_eq!(out.stderr, "tm: no such item: ^nope\n");
}

#[test]
fn a_rejected_value_names_what_and_the_value() {
    // §4.1's grammar refuses `est=zzz`; the document says which field and
    // which text, the two things a caller wants to fix.
    let tm = Tm::new();
    let out = tm.run(&["--json", "edit", "^t3", "est=zzz"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc = err_doc(&out.stderr);
    assert_eq!(doc["kind"], "invalid");
    assert_eq!(doc["detail"]["what"], "duration");
    assert_eq!(doc["detail"]["value"], "zzz");
}

#[test]
fn a_write_conflict_is_a_document_with_exit_three_and_both_texts() {
    // §1.3's race, provoked the way `cli_undo.rs` provokes it: another writer
    // appends to the file `tm undo` is about to restore. §13's exit code 3,
    // and the two texts the caller needs to reconcile it.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t3", "--energy", "4"]);
    tm.ok_at("2026-09-07T10:00:00-05:00", &["done"]);

    let path = tm.plan.join("week/2026-W37.md");
    let mut text = std::fs::read_to_string(&path).expect("read week");
    text.push_str("- [ ] 3 1b Written by Claude Code   @m2 ^zz1\n");
    std::fs::write(&path, &text).expect("write week");

    let out = tm.run_at("2026-09-07T10:01:00-05:00", &["undo", "--json"]);
    assert_eq!(out.code, 3, "{}{}", out.stdout, out.stderr);
    let doc = err_doc(&out.stderr);
    assert_eq!(doc["kind"], "conflict");
    assert_eq!(doc["exit_code"], 3);
    assert_eq!(doc["detail"]["file"], "week/2026-W37.md");
    assert_eq!(doc["detail"]["theirs"], text);
    assert_ne!(doc["detail"]["ours"], doc["detail"]["theirs"]);
    // Nothing was written: the conflict is reported, not resolved.
    assert_eq!(std::fs::read_to_string(&path).expect("read week"), text);
}

/// A kernel refusal under `--json` is a document whose `kind` is `kernel`
/// and whose `detail.refusal` carries the kernel's own name for it — the
/// name reaches the machine reader verbatim, never only as prose
/// (kernel/README.md, 2026-09-12 "the five lifecycle verbs" block).
#[test]
fn a_kernel_refusal_is_a_named_document() {
    let tm = Tm::new();
    let out = tm.run(&["--json", "move", "^m2", "month"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc = err_doc(&out.stderr);
    assert_eq!(doc["ok"], Value::Bool(false));
    assert_eq!(doc["kind"], "kernel");
    assert_eq!(doc["exit_code"], 1);
    assert_eq!(doc["detail"]["refusal"], "occupied");
    assert!(
        doc["message"]
            .as_str()
            .unwrap_or_default()
            .contains("occupied"),
        "{doc}"
    );
}

#[test]
fn a_usage_error_is_a_document_too() {
    // The verb never ran, but a caller driving `tm` still gets a document
    // rather than clap's prose.
    let tm = Tm::new();
    let out = tm.run(&["drop", "--json"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc = err_doc(&out.stderr);
    assert_eq!(doc["kind"], "usage");
    assert_eq!(doc["exit_code"], 1);
    assert!(
        doc["message"]
            .as_str()
            .unwrap_or_default()
            .contains("Usage: tm drop"),
        "{doc}"
    );

    // Without `--json` it stays clap's own message.
    let human = tm.run(&["drop"]);
    assert_eq!(human.code, 1);
    assert!(human.stderr.starts_with("error: "), "{}", human.stderr);
}

#[test]
fn every_verb_that_can_fail_reports_json() {
    // The point of defining the document once: no verb hand-rolls it, so all
    // of them are machine-readable, not just the ones someone remembered.
    let tm = Tm::new();
    let runs: &[&[&str]] = &[
        &["start", "^nope"],
        &["done", "^nope"],
        &["edit", "^nope", "ci=3"],
        &["move", "^nope", "week"],
        &["rank", "^nope", "1"],
        &["demote", "^nope"],
        &["readopt", "^nope"],
        &["drop", "^nope"],
        &["skip", "nope"],
        &["stop"],
        &["undo"],
        &["extend", "1b"],
        &["energy", "9"],
        &["idle", "z"],
        &["add", "3 1b Dup id ^t1", "--to", "backlog"],
    ];
    for args in runs {
        let mut all = vec!["--json"];
        all.extend_from_slice(args);
        let out = tm.run_at(NOW, &all);
        assert_ne!(out.code, 0, "`tm {}` was expected to fail", args.join(" "));
        let doc = err_doc(&out.stderr);
        assert_eq!(doc["ok"], Value::Bool(false), "tm {}", args.join(" "));
        assert_eq!(doc["exit_code"], out.code, "tm {}", args.join(" "));
        assert!(
            doc["kind"].as_str().is_some_and(|k| !k.is_empty()),
            "tm {}: {doc}",
            args.join(" ")
        );
        assert!(
            doc["message"].as_str().is_some_and(|m| !m.is_empty()),
            "tm {}: {doc}",
            args.join(" ")
        );
    }
}

#[test]
fn validation_problems_stay_on_stdout() {
    // §13's exit code 2 is not a failure: `tm check` *returns* it, and its
    // problems are the verb's own result — so they keep the success path.
    let tm = Tm::new();
    let path = tm.plan.join("week/2026-W37.md");
    let mut text = std::fs::read_to_string(&path).expect("read week");
    text.push_str("- [ ] 3 1b Duplicate ^t5\n");
    std::fs::write(&path, text).expect("write week");

    let out = tm.run(&["--json", "check"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    assert_eq!(out.stderr, "");
    let doc: Value = serde_json::from_str(&out.stdout).expect("check --json is JSON");
    assert_eq!(doc["exit_code"], 2);
    assert!(!doc["problems"].as_array().expect("problems").is_empty());
}
