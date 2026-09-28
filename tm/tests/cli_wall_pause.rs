//! **A calendar wall that starts while a block is running STOPS THE TIMER** —
//! the owner's D61 (stage 6 W-36 track T, README gaps 2805 and 2932).
//!
//! `plan-basic`'s calendar holds `^g1 Meeting w/ host at:2026-09-07T12:50/13:50`.
//! A block started at 12:00 runs into it. Before D61 nothing was logged at the
//! wall: `tm now` counted the meeting as worked (`80m of 60m` at 13:20), `tm
//! done` logged it as `actual_min`, and `tm plan` drew the open stretch from
//! 12:00 across the meeting. Now the first verb after the wall BEGAN logs a
//! `pause` stamped at its start, and the first verb after it ENDED an `unpause`
//! stamped at its end — the log's own events, no new kind — so every reading
//! of the block nets the meeting out.
//!
//! Every test reads the log's bytes, not only an exit code: WHEN the entries are
//! written, and that they are written once, is the rule.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

/// The meeting's start and end, as the log stamps them.
const WALL_START: &str = "2026-09-07T12:50:00-05:00";
const WALL_END: &str = "2026-09-07T13:50:00-05:00";

/// `(ev, t)` of every `pause`/`unpause` entry, in file order.
fn timer_marks(tm: &Tm) -> Vec<(String, String)> {
    tm.log()
        .iter()
        .filter(|e| e["ev"] == "pause" || e["ev"] == "unpause")
        .map(|e| (e["ev"].as_str().unwrap_or_default().to_string(), e["t"].as_str().unwrap_or_default().to_string()))
        .collect()
}

/// A day with `^t4` started at 12:00, forty minutes before the meeting.
fn running_before_the_meeting() -> Tm {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T12:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm
}

fn active(tm: &Tm, at: &str) -> Value {
    tm.json_at(at, &["now"])["active"].clone()
}

/// **The drive, pinned**: during the meeting the header reads the fifty minutes
/// before it and says `paused`; after it, fifty plus the twenty since it ended;
/// `tm done` logs those minutes — eighty, where the wall clock says 140.
#[test]
fn a_wall_that_starts_while_a_block_runs_stops_its_timer() {
    let tm = running_before_the_meeting();
    assert!(timer_marks(&tm).is_empty(), "nothing is written before the wall begins");

    let during = active(&tm, "2026-09-07T13:20:00-05:00");
    assert_eq!(during["elapsed_min"], 50, "the meeting is not worked: {during}");
    assert_eq!(during["paused"], true, "the wall paused the timer: {during}");
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), WALL_START.to_string())],
        "the first verb after the wall began logged the pause at its start"
    );

    let after = active(&tm, "2026-09-07T14:10:00-05:00");
    assert_eq!(after["elapsed_min"], 70, "fifty before the meeting and twenty since: {after}");
    assert_eq!(after["paused"], false, "the wall's end restarted it: {after}");
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), WALL_START.to_string()), ("unpause".to_string(), WALL_END.to_string())],
        "the first verb after the wall ended logged the unpause at its end, once"
    );

    tm.ok_at("2026-09-07T14:20:00-05:00", &["done"]);
    assert_eq!(tm.last_ev("done")["actual_min"], 80, "`tm done` logs the minutes the header read");
    assert_eq!(timer_marks(&tm).len(), 2, "nothing was written twice");
}

/// **A verb run only after the wall ended writes both, in order, once** — the
/// automatic close's catching-up shape — and `tm plan` then draws the running
/// stretch from the meeting's END, not from 12:00 across it.
#[test]
fn a_verb_after_the_wall_writes_the_pair_and_the_plan_draws_no_stretch_across_it() {
    let tm = running_before_the_meeting();
    let plan = tm.json_at("2026-09-07T14:10:00-05:00", &["plan"]);
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), WALL_START.to_string()), ("unpause".to_string(), WALL_END.to_string())]
    );
    let segs = plan["segments"].as_array().cloned().unwrap_or_default();
    let t4: Vec<(String, String, String)> = segs
        .iter()
        .filter(|s| s["item"] == "t4")
        .map(|s| {
            (
                s["kind"].as_str().unwrap_or_default().to_string(),
                s["start"].as_str().unwrap_or_default().to_string(),
                s["end"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect();
    assert!(
        t4.iter().any(|(k, a, b)| k == "block" && a == "12:00" && b == "12:50"),
        "the stretch before the meeting ends at its start: {t4:?}"
    );
    assert!(
        !t4.iter().any(|(k, a, b)| k == "block" && a.as_str() < "13:50" && b.as_str() > "12:50"),
        "no block of ^t4 lies across the meeting: {t4:?}"
    );
    // A second verb writes nothing more.
    tm.ok_at("2026-09-07T14:15:00-05:00", &["now"]);
    assert_eq!(timer_marks(&tm).len(), 2);
}

/// **A timer the user stopped is not the wall's to touch**: paused at 12:30, the
/// block was not running when the meeting began, so nothing is logged at it and
/// the timer stays stopped after it.
#[test]
fn a_timer_already_stopped_at_the_wall_is_left_alone() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:30:00-05:00", &["pause"]);
    let after = active(&tm, "2026-09-07T14:10:00-05:00");
    assert_eq!(after["paused"], true, "{after}");
    assert_eq!(after["elapsed_min"], 30, "{after}");
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), "2026-09-07T12:30:00-05:00".to_string())],
        "only the user's own pause"
    );
}

/// **A user who skipped the meeting keeps the timer they set** (the cost D61
/// names: undercounted UNTIL they correct it): the wall paused the block at
/// 12:50, the user unpaused at 13:05 and worked on, and the wall's end writes no
/// unpause of its own over the user's.
#[test]
fn a_user_who_unpaused_during_the_meeting_keeps_their_timer() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T13:00:00-05:00", &["now"]);
    tm.ok_at("2026-09-07T13:05:00-05:00", &["pause"]);
    let after = active(&tm, "2026-09-07T14:10:00-05:00");
    assert_eq!(after["paused"], false, "{after}");
    assert_eq!(after["elapsed_min"], 115, "50 before the wall and 65 since the user unpaused: {after}");
    assert_eq!(
        timer_marks(&tm),
        vec![
            ("pause".to_string(), WALL_START.to_string()),
            ("unpause".to_string(), "2026-09-07T13:05:00-05:00".to_string()),
        ],
        "no second unpause at the wall's end"
    );
}

/// **A timer mark already stamped inside the meeting is the user's word** —
/// the log is the user's file too (hand-edited, or synced from a machine that
/// paused at 13:05 without this housekeeping). The wall's pause is never
/// inserted UNDER a later mark, so its automatic unpause at 13:50 cannot lift
/// the user's own pause: at 14:10 the block has worked 65 minutes, 12:00 to
/// the user's 13:05, and nothing was written.
#[test]
fn a_timer_mark_already_inside_the_meeting_is_left_to_stand() {
    let tm = running_before_the_meeting();
    let log = tm.plan.join(".tm/log.jsonl");
    let mut text = std::fs::read_to_string(&log).expect("read the log");
    text.push_str("{\"t\":\"2026-09-07T13:05:00-05:00\",\"ev\":\"pause\",\"id\":\"t4\"}\n");
    std::fs::write(&log, text).expect("write the log");
    let after = active(&tm, "2026-09-07T14:10:00-05:00");
    assert_eq!(after["elapsed_min"], 65, "{after}");
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), "2026-09-07T13:05:00-05:00".to_string())],
        "no wall pause under the user's mark, and so no wall unpause over it"
    );
}

/// **A block started inside a wall is not paused by it** — the wall did not
/// start while the block ran.
#[test]
fn a_block_started_inside_the_wall_is_not_paused_by_it() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T13:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    let after = active(&tm, "2026-09-07T14:00:00-05:00");
    assert_eq!(after["elapsed_min"], 60, "{after}");
    assert!(timer_marks(&tm).is_empty());
}

/// **A block that ends inside the meeting leaves its wall pause open, and the
/// NEXT block's minutes are still its own** (README gap 2920, the host's one
/// reading).  `tm done` at 13:20 closes `^t4` with the wall's pause unlifted;
/// `^t1` starts after the meeting, and at 14:30 it has run thirty minutes.
/// Before W-36 the host's rule let a pause stamped before a block began swallow
/// it (next test), so D61 would have made this read zero.
#[test]
fn a_block_that_ended_inside_the_meeting_leaves_the_next_block_its_own_minutes() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T13:20:00-05:00", &["done"]);
    assert_eq!(tm.last_ev("done")["actual_min"], 50, "the meeting is not in `^t4`'s minutes");
    tm.ok_at("2026-09-07T14:00:00-05:00", &["start", "^t1", "--energy", "4"]);
    let now = active(&tm, "2026-09-07T14:30:00-05:00");
    assert_eq!(now["id"], "t1", "{now}");
    assert_eq!(now["elapsed_min"], 30, "the old block's open pause is not the new block's: {now}");
    tm.ok_at("2026-09-07T14:35:00-05:00", &["done"]);
    assert_eq!(tm.last_ev("done")["actual_min"], 35);
}

/// **The defect under it, with no wall at all** — driven on `dd8b95b`: `tm
/// pause` then `tm done` logs no `unpause`, and the host's worked-minutes rule
/// (fork `day::worked_min`) kept that pause open into the next block, so `tm
/// now` read `elapsed_min: 0` for `^t1` and `tm done` logged `actual_min: 0`.
#[test]
fn a_pause_left_open_by_a_paused_done_is_not_the_next_blocks() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T09:10:00-05:00", &["pause"]);
    tm.ok_at("2026-09-07T09:20:00-05:00", &["done"]);
    tm.ok_at("2026-09-07T09:30:00-05:00", &["start", "^t1", "--energy", "4"]);
    let now = active(&tm, "2026-09-07T10:00:00-05:00");
    assert_eq!(now["elapsed_min"], 30, "{now}");
    tm.ok_at("2026-09-07T10:05:00-05:00", &["done"]);
    assert_eq!(tm.last_ev("done")["actual_min"], 35);
}
