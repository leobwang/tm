//! **The host reads a break's span as the kernel does** — the owner's **D95** (README gap 4360,
//! parity **P93**, W-44 track H): a `break` line's span is `[t, t + actual_min)`, else
//! `[t, t + planned_min)` when it was logged without `actual_min` — the kernel's `Replay.brkEnd`,
//! the host's `BreakRecord::span` — so `tm now`, `tm stop`, `tm done` and the TUI's timer (the
//! host's worked minutes, `Replay::running_worked_min`) and `tm review day` (the kernel's replay)
//! read a block one way.
//!
//! No verb writes a `break` line without `actual_min` (`tm break`'s end, and every verb that ends
//! a break, logs it), so only a HAND-EDITED log moves. Until D95 the host's pairing of idle marks
//! read such a line as no span, while the replay netted its planned minutes: inside a block, `tm
//! stop` said 60 minutes beside `tm review day`'s 40; run into the block's start, 60 beside 50.

mod cli_common;

use cli_common::Tm;

const WAKE: &str = "2026-09-07T07:00:00-05:00";

fn at(hhmm: &str) -> String {
    format!("2026-09-07T{hhmm}:00-05:00")
}

/// The example tree, woken at 07:00.
fn woken() -> Tm {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm
}

/// Append one line to `.tm/log.jsonl` by hand, as a user's editor would.
fn hand_append(tm: &Tm, line: &str) {
    let path = tm.plan.join(".tm/log.jsonl");
    let mut text = std::fs::read_to_string(&path).expect("the log");
    assert!(text.ends_with('\n'), "the log ends its last line");
    text.push_str(line);
    text.push('\n');
    std::fs::write(&path, text).expect("write the log");
}

/// `(tm now's elapsed at 09:50, tm stop's minutes at 10:00, tm review day's block minutes)`.
fn three_readings(tm: &Tm) -> (u64, u64, u64) {
    let now = tm.json_at(&at("09:50"), &["now"]);
    let elapsed = now["active"]["elapsed_min"].as_u64().unwrap_or_else(|| panic!("{now}"));
    let stop = tm.json_at(&at("10:00"), &["stop"]);
    let worked = stop["worked_min"].as_u64().unwrap_or_else(|| panic!("{stop}"));
    let day = tm.json_at(&at("10:01"), &["review", "day"]);
    let block = day["review"]["block_min"].as_u64().unwrap_or_else(|| panic!("{day}"));
    (elapsed, worked, block)
}

/// **Inside the block**: `^m1` from 09:00, a hand-edited break at 09:20 planned 20 with no
/// `actual_min`, stopped at 10:00 — forty minutes worked, read so by all three.
#[test]
fn a_planned_only_break_inside_a_block_is_read_one_way() {
    let tm = woken();
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    hand_append(&tm, r#"{"t":"2026-09-07T09:20:00-05:00","ev":"break","planned_min":20}"#);
    assert_eq!(three_readings(&tm), (30, 40, 40), "tm now, tm stop and tm review day read the block one way");
    assert_eq!(tm.last_ev("stop")["remaining_min"], 320);
}

/// **Run into the block's start** (D92's shape): a hand-edited break at 08:50 planned 20, `^m1`
/// started at 09:00 inside it — the ten minutes 09:00-09:10 are the break's, not the block's.
#[test]
fn a_planned_only_break_run_into_a_start_is_read_one_way() {
    let tm = woken();
    hand_append(&tm, r#"{"t":"2026-09-07T08:50:00-05:00","ev":"break","planned_min":20}"#);
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    assert_eq!(three_readings(&tm), (40, 50, 50), "tm now, tm stop and tm review day read the block one way");
}

/// **`tm done` logs the same minutes** the review credits, inside the block.
#[test]
fn tm_done_logs_the_minutes_the_review_credits() {
    let tm = woken();
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    hand_append(&tm, r#"{"t":"2026-09-07T09:20:00-05:00","ev":"break","planned_min":20}"#);
    tm.ok_at(&at("10:00"), &["done", "--partial"]);
    assert_eq!(tm.last_ev("done")["actual_min"], 40, "{}", tm.last_ev("done"));
    let day = tm.json_at(&at("10:01"), &["review", "day"]);
    assert_eq!(day["review"]["block_min"], 40, "{day}");
}

/// **The binary's own shape is unchanged** (no over-bite): the same break logged with its
/// `actual_min` reads as it always did, and an `actual_min` SHORTER than the plan is the span.
#[test]
fn a_break_logged_with_its_minutes_reads_as_before() {
    let tm = woken();
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    hand_append(&tm, r#"{"t":"2026-09-07T09:20:00-05:00","ev":"break","planned_min":20,"actual_min":20}"#);
    assert_eq!(three_readings(&tm), (30, 40, 40));

    let tm = woken();
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    hand_append(&tm, r#"{"t":"2026-09-07T09:20:00-05:00","ev":"break","planned_min":30,"actual_min":10}"#);
    assert_eq!(three_readings(&tm), (40, 50, 50), "the actual minutes, not the plan");
}

/// **A planned-only break that ended before the block began takes nothing from it.**
#[test]
fn a_planned_only_break_before_the_block_takes_nothing() {
    let tm = woken();
    hand_append(&tm, r#"{"t":"2026-09-07T08:30:00-05:00","ev":"break","planned_min":20}"#);
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    assert_eq!(three_readings(&tm), (50, 60, 60));
}
