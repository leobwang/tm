//! **`tm start` during an open interruption records the block as PAUSED** —
//! the campaign's D69 call on README gap 3283 (stage 6 W-38 track T, parity
//! P60).
//!
//! `tm start` does not end an interruption, and D42's rebuild of
//! `.tm/state.json` from the log pauses the open block while an interruption
//! is open (`ctx::open_interruption`). Until D69 `tm start` wrote `paused:
//! false` there regardless, so deleting the cache moved `tm --json now`'s
//! `active.paused` from `false` to `true`: two readings of one fact, and the
//! cache must follow the log, never the reverse (D42).
//!
//! Every test reads what a user reads: `.tm/state.json`, `tm --json now` with
//! the cache and after deleting it, and `tm now`'s header.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

/// `tm interrupt` at 09:40 with nothing running, then `tm start ^t4` at 09:45.
fn started_during_an_interruption() -> Tm {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-07T09:40:00-05:00", &["interrupt"]);
    tm.ok_at("2026-09-07T09:45:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm
}

/// `tm --json now` at `at`, then again after `.tm/state.json` is deleted.
fn now_across_the_delete(tm: &Tm, at: &str) -> (Value, Value) {
    let with = tm.json_at(at, &["now"]);
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    let without = tm.json_at(at, &["now"]);
    (with, without)
}

/// **The drive, pinned.** The cache says the block is paused, `tm now`'s
/// header says so, and deleting the cache changes nothing `tm --json now`
/// answers — the interruption comes back identical, and so does the block.
#[test]
fn a_block_started_during_an_interruption_is_paused_as_the_rebuild_says() {
    let tm = started_during_an_interruption();
    let st = tm.state();
    assert_eq!(st["active"]["id"], "t4", "{st}");
    assert_eq!(st["active"]["paused"], true, "the cache writes what the log derives: {st}");
    assert_eq!(st["interrupt"]["started"], "09:40", "{st}");
    let header = tm.ok_at("2026-09-07T09:50:00-05:00", &["now"]).stdout;
    assert!(header.lines().next().is_some_and(|l| l.ends_with("· paused")), "{header}");
    let (with, without) = now_across_the_delete(&tm, "2026-09-07T09:50:00-05:00");
    assert_eq!(with["active"]["paused"], true, "{with}");
    assert_eq!(with, without, "deleting the runtime state changes nothing (D42)");
}

/// **`tm resume` unpauses it**, as it unpauses a block `tm interrupt` paused,
/// and the rebuild agrees after the resume too.
#[test]
fn resume_unpauses_a_block_started_during_the_interruption() {
    let tm = started_during_an_interruption();
    tm.ok_at("2026-09-07T09:55:00-05:00", &["resume"]);
    assert_eq!(tm.state()["active"]["paused"], false, "{}", tm.state());
    let (with, without) = now_across_the_delete(&tm, "2026-09-07T09:56:00-05:00");
    assert_eq!(with["active"]["paused"], false, "{with}");
    assert_eq!(with, without);
}

/// **It does not over-bite** (AGENTS §5.8): with no interruption open, a
/// started block is running — and after an interruption was resumed, too.
#[test]
fn a_block_started_with_no_open_interruption_is_running() {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-07T09:40:00-05:00", &["interrupt"]);
    tm.ok_at("2026-09-07T09:44:00-05:00", &["resume"]);
    tm.ok_at("2026-09-07T09:45:00-05:00", &["start", "^t4", "--energy", "4"]);
    assert_eq!(tm.state()["active"]["paused"], false, "{}", tm.state());
    let (with, without) = now_across_the_delete(&tm, "2026-09-07T09:50:00-05:00");
    assert_eq!(with["active"]["paused"], false, "{with}");
    assert_eq!(with, without);
}
