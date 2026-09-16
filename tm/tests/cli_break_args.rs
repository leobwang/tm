//! **`tm break` reads its arguments in both arms** — the owner's D20, README
//! gap 138 (label W7-a).
//!
//! The verb was two verbs and only one of them validated. `day.rs`'s `break_`
//! took the running-break arm before it ever looked at `args.dur`, so on a
//! fresh tree `tm break zzzz` was refused by name and exited 1, while with a
//! break already running the same spelling exited **0**, ended the break and
//! discarded both arguments. A user could not tell which of the two they had
//! got without knowing whether a break was running — AGENTS §5.13's failure
//! class exactly: a plausible keystroke that neither works nor says so.
//!
//! D20 settles both halves, and this file drives one test per arm:
//! 1. an unreadable duration is **refused by name in both arms**, and the
//!    running break is still running afterwards;
//! 2. a *valid* argument does **not** retime a running break — `tm break 20m`
//!    with a break running still just ends it. Retiming was considered and
//!    declined as a new feature, so this test pins the absence of one.

mod cli_common;

use cli_common::Tm;

/// 25 minutes after `cli_common::NOW`, the instant the running break is ended at.
const LATER: &str = "2026-09-07T09:25:00-05:00";

#[test]
fn an_unreadable_duration_is_refused_whether_or_not_a_break_is_running() {
    // Arm 1, the fresh tree: refused by name. This half always worked.
    let tm = Tm::new();
    let out = tm.run(&["break", "zzzz", "--where", "bed"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains(r#"invalid duration: "zzzz""#),
        "the fresh-tree arm must name the value: {:?}",
        out.stderr
    );
    // Nothing was started.
    assert_eq!(tm.state()["break"], serde_json::Value::Null);

    // Arm 2, with a break running: this is what gap 138 reported as exit 0.
    let tm = Tm::new();
    let start = tm.json(&["break", "20m", "--where", "walk"]);
    assert_eq!(start["action"], "started");
    assert_eq!(tm.state()["break"]["planned_min"], 20);

    let out = tm.run_at(LATER, &["break", "zzzz", "--where", "bed"]);
    assert_eq!(
        out.code, 1,
        "a running break must not swallow an unreadable duration: {}{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains(r#"invalid duration: "zzzz""#),
        "the running-break arm must name the same value: {:?}",
        out.stderr
    );
    // The refusal did not act: the break is still running, unchanged, and no
    // `break` event was appended.
    assert_eq!(tm.state()["break"]["planned_min"], 20);
    assert_eq!(tm.state()["break"]["where"], "walk");
    assert!(
        !tm.events().contains(&"break".to_string()),
        "a refused `tm break` appended a break event: {:?}",
        tm.events()
    );

    // And the break can still be ended normally afterwards.
    let end = tm.json_at(LATER, &["break"]);
    assert_eq!(end["action"], "ended");
    assert_eq!(end["planned_min"], 20);
}

#[test]
fn an_argument_does_not_retime_a_running_break() {
    // D20's second half: the arguments are *read* in both arms but they act in
    // only one. `tm break 20m` with a break running ends it; it does not start
    // a new one, and it does not change the running one's planned minutes or
    // its place. This is unchanged behaviour, pinned so that "validate in both
    // arms" is never mistaken for "retime in both arms".
    let tm = Tm::new();
    tm.ok(&["break", "20m", "--where", "walk"]);

    let end = tm.json_at(LATER, &["break", "45m", "--where", "bed"]);
    assert_eq!(end["action"], "ended");
    // The break that ended is the one that was running: 20m, walk — not 45m, bed.
    assert_eq!(end["planned_min"], 20);
    assert_eq!(end["place"], "walk");
    assert_eq!(end["actual_min"], 25);
    assert_eq!(tm.state()["break"], serde_json::Value::Null);

    // The logged event is the running break's too (§10.1).
    let last = tm.last_ev("break");
    assert_eq!(last["planned_min"], 20);
    assert_eq!(last["where"], "walk");
    assert_eq!(last["actual_min"], 25);
}
