//! **`tm interrupt` ends a running break first** — the owner's **D90** (README gap 4340, parity
//! **P86**, W-43 track H), driven through the binary on every surface that reads a block's minutes.
//!
//! The day: `tm init --example`, woken at 07:00, `^m1` started at 09:00, a twenty-minute break from
//! 09:10, `tm interrupt` at 09:20, `tm resume` at 09:40, `tm stop` at 10:00. The interruption ends
//! the break at 09:20 — its `break` line logged as `tm break` logs its end, ten minutes, BEFORE the
//! `interrupt` line — so the block worked 09:00-09:10 and 09:40-10:00, thirty minutes, and `tm
//! stop`, `tm now`'s header (and the TUI's timer, the same rule) and `tm review day` all say so.
//!
//! Fork 4748911 (and this binary until D90) logged the `interrupt` and left the break running in
//! `.tm/state.json`, so the break's line was written at its END — after the interruption's — and the
//! kernel's replay, which steps the interruption first, credited the break's head as block time
//! while the host's union of idle spans did not: on this day `tm stop` said 10 minutes and `tm
//! review day` 20.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

const WAKE: &str = "2026-09-07T07:00:00-05:00";
const START: &str = "2026-09-07T09:00:00-05:00";
const BREAK_ON: &str = "2026-09-07T09:10:00-05:00";
const INTERRUPT: &str = "2026-09-07T09:20:00-05:00";
const DURING: &str = "2026-09-07T09:30:00-05:00";
const RESUME: &str = "2026-09-07T09:40:00-05:00";
const AFTER_RESUME: &str = "2026-09-07T09:50:00-05:00";
const STOP: &str = "2026-09-07T10:00:00-05:00";
const AFTER: &str = "2026-09-07T10:01:00-05:00";

/// The example tree, woken, `^m1` running from 09:00 and a break of `planned` running from 09:10.
fn a_break_running(planned: &str, place: Option<&str>) -> Tm {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(START, &["start", "^m1", "--energy", "3"]);
    let mut args = vec!["break", planned];
    if let Some(p) = place {
        args.extend(["--where", p]);
    }
    tm.ok_at(BREAK_ON, &args);
    assert!(!tm.state()["break"].is_null(), "the break is running: {}", tm.state());
    tm
}

/// The day file's journal lines (`## Log`), as written.
fn journal(tm: &Tm) -> Vec<String> {
    tm.read("day/2026-09-07.md")
        .lines()
        .skip_while(|l| *l != "## Log")
        .skip(1)
        .take_while(|l| !l.starts_with("## "))
        .filter(|l| !l.trim().is_empty())
        .map(str::to_string)
        .collect()
}

#[test]
fn tm_interrupt_ends_a_running_break_first_and_every_surface_reads_one_count() {
    let tm = a_break_running("20m", None);
    let said = tm.ok_at(INTERRUPT, &["interrupt"]).stdout;
    assert_eq!(said.trim(), "break ended · 10m of 20m · interrupted", "{said}");

    // The log: the break's line BEFORE the interruption's, stamped at the break's start, ten minutes.
    let log = tm.log();
    let tail: Vec<&str> = log[log.len() - 3..].iter().map(|e| e["ev"].as_str().unwrap_or_default()).collect();
    assert_eq!(tail, ["start", "break", "interrupt"], "{log:?}");
    let brk = &log[log.len() - 2];
    assert_eq!((brk["t"].as_str(), brk["planned_min"].as_u64(), brk["actual_min"].as_u64()), (Some(BREAK_ON), Some(20), Some(10)), "{brk}");
    assert_eq!(log[log.len() - 1]["t"], INTERRUPT);

    // The journal: `tm break`'s own ending line, then the interruption's, both at 09:20.
    let j = journal(&tm);
    let at = j.iter().position(|l| l == "09:20 break ended 10m/20m").unwrap_or_else(|| panic!("{j:?}"));
    assert_eq!(j.get(at + 1).map(String::as_str), Some("09:20 interrupt ^m1"), "{j:?}");

    // `.tm/state.json`: no break, the interruption open, the block held by it.
    let st = tm.state();
    assert!(st["break"].is_null(), "{st}");
    assert_eq!((st["interrupt"]["id"].as_str(), st["interrupt"]["started"].as_str()), (Some("m1"), Some("09:20")), "{st}");
    assert_eq!(st["active"]["paused"], true, "{st}");

    // During the interruption the header holds the ten minutes before the break.
    let during = tm.json_at(DURING, &["now"]);
    assert_eq!((during["active"]["elapsed_min"].as_u64(), during["active"]["paused"].as_bool()), (Some(10), Some(true)), "{during}");

    assert!(tm.ok_at(RESUME, &["resume"]).stdout.contains("lost 20m"));
    let mid = tm.json_at(AFTER_RESUME, &["now"]);
    assert_eq!(mid["active"]["elapsed_min"], 20, "`tm now`'s header at 09:50: {mid}");
    let said = tm.ok_at(STOP, &["stop"]).stdout;
    assert!(said.contains("after 30m"), "`tm stop`: {said}");
    assert_eq!(tm.last_ev("stop")["remaining_min"], 330);
    let day = tm.json_at(AFTER, &["review", "day"]);
    assert_eq!(day["review"]["block_min"], 30, "`tm review day` and `tm stop` read the block two ways: {day}");
    assert_eq!(day["review"]["load"], 30.0, "{day}");
}

#[test]
fn the_json_carries_the_ended_break_as_tm_break_reports_its_end() {
    let tm = a_break_running("20m", Some("walk"));
    let out = tm.json_at(INTERRUPT, &["interrupt"]);
    assert_eq!(out["action"], "interrupt");
    assert_eq!(out["id"], "m1");
    assert_eq!(
        out["break_ended"],
        serde_json::json!({"action": "ended", "planned_min": 20, "actual_min": 10, "place": "walk"}),
        "{out}"
    );
    assert_eq!(tm.last_ev("break")["where"], "walk", "the place rides the break's line");
}

/// **With no break running nothing moves**: the human line, the JSON (no `break_ended` key) and the
/// log (the `interrupt` line alone) are what they were before D90.
#[test]
fn with_no_break_running_tm_interrupt_is_unchanged() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(START, &["start", "^m1", "--energy", "3"]);
    let before = tm.events().len();
    assert_eq!(tm.ok_at(INTERRUPT, &["interrupt"]).stdout.trim(), "interrupted");
    let events = tm.events();
    assert_eq!(&events[before..], ["interrupt"], "{events:?}");
    assert!(!journal(&tm).iter().any(|l| l.contains("break ended")), "{:?}", journal(&tm));
    tm.ok_at(DURING, &["resume"]);
    let tm2 = Tm::empty();
    assert_eq!(tm2.run(&["init", "--example"]).code, 0);
    tm2.ok_at(WAKE, &["wake", "07:00"]);
    let out = tm2.json_at(INTERRUPT, &["interrupt"]);
    assert!(out.get("break_ended").is_none(), "{out}");
    assert_eq!(out["id"], Value::Null);
}

/// **A break running with no block** ends too: the interruption interrupts nothing, and the break's
/// line is logged before it.
#[test]
fn a_break_running_with_no_block_ends_before_the_interruption() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(BREAK_ON, &["break", "15m"]);
    let out = tm.json_at(INTERRUPT, &["interrupt"]);
    assert_eq!(out["break_ended"]["actual_min"], 10, "{out}");
    assert_eq!(out["id"], Value::Null);
    let events = tm.events();
    assert_eq!(events[events.len() - 2..], ["break", "interrupt"], "{events:?}");
    assert!(tm.state()["break"].is_null());
}

/// **The owner's D42: deleting the runtime state changes nothing** — after the interruption that
/// ended the break, `.tm/state.json` is rebuilt from the log with the interruption open, no break,
/// and the block held, and `tm now` answers the same document.
#[test]
fn deleting_the_runtime_state_after_the_interruption_changes_nothing() {
    let tm = a_break_running("20m", None);
    tm.ok_at(INTERRUPT, &["interrupt"]);
    let cached = tm.json_at(DURING, &["now"]);
    let cached_state = tm.state();
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("the runtime state");
    let rebuilt = tm.json_at(DURING, &["now"]);
    assert_eq!(rebuilt, cached, "`tm now` across the delete");
    let st = tm.state();
    for key in ["active", "break", "interrupt"] {
        assert_eq!(st[key], cached_state[key], "`{key}` rebuilt from the log: {st}");
    }
}

/// **`tm undo` takes the whole verb back**: both lines it appended are compensated and the break is
/// running again, as it was.
#[test]
fn undo_puts_the_running_break_back() {
    let tm = a_break_running("20m", None);
    tm.ok_at(INTERRUPT, &["interrupt"]);
    tm.ok_at("2026-09-07T09:21:00-05:00", &["undo"]);
    let st = tm.state();
    assert_eq!((st["break"]["started"].as_str(), st["break"]["planned_min"].as_u64()), (Some("09:10"), Some(20)), "{st}");
    assert!(st["interrupt"].is_null(), "{st}");
    let undone: Vec<String> = tm
        .log()
        .iter()
        .filter(|e| e["ev"] == "undo")
        .map(|e| e["of"].as_str().unwrap_or_default().to_string())
        .collect();
    assert_eq!(undone, ["interrupt", "break"], "both lines compensated, the last first");
    let ended = tm.ok_at(DURING, &["break"]).stdout;
    assert!(ended.contains("break ended · 20m of 20m"), "the break ran on: {ended}");
}
