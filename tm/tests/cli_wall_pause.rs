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

/// The `## Log` section of a day file, one journal line per element.
fn journal(tm: &Tm, rel: &str) -> Vec<String> {
    let text = tm.read(rel);
    text.lines()
        .skip_while(|l| *l != "## Log")
        .skip(1)
        .take_while(|l| !l.starts_with("## "))
        .filter(|l| !l.trim().is_empty())
        .map(str::to_string)
        .collect()
}

/// **A verb run inside a meeting does not take `tm undo` away** (W-37 repair,
/// README gap 3330; D37). D65 gave the wall's pause the day file's journal line,
/// written by housekeeping before any undo recorder runs — so the next `tm
/// undo` of the `tm start` before it found a line it did not write and refused
/// with exit 3 (driven on `faaaac6`; the same drive undid the start on
/// `b3c29a3`). The housekeeping write now goes UNDER the stack: the start is
/// undone, and the pause's journal line stays, as the pause's log entry does.
#[test]
fn a_start_before_a_meeting_can_still_be_undone() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T13:20:00-05:00", &["now"]);
    assert!(journal(&tm, "day/2026-09-07.md").contains(&"12:50 pause ^t4".to_string()));
    let out = tm.run_at("2026-09-07T13:25:00-05:00", &["undo"]);
    assert_eq!(out.code, 0, "the start is undone: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("undid start"), "{}", out.stdout);
    assert!(tm.state()["active"].is_null(), "no block is running: {}", tm.state());
    let j = journal(&tm, "day/2026-09-07.md");
    assert!(!j.iter().any(|l| l.contains("start ^t4")), "the start's journal line is gone: {j:?}");
    assert!(
        j.contains(&"12:50 pause ^t4".to_string()),
        "the pause's journal line stays, as its log entry does: {j:?}"
    );
    assert_eq!(timer_marks(&tm), vec![("pause".to_string(), WALL_START.to_string())]);
}

/// **An undo under the pause keeps the pause** (gap 3330): an unrelated command
/// (an energy report, which writes the day file's journal) is undone after the wall paused
/// the block; the block stays running AND paused — the state the log says —
/// and the pause's journal line stays.
#[test]
fn an_undo_under_a_meeting_pause_keeps_the_pause() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:30:00-05:00", &["energy", "3"]);
    let before = journal(&tm, "day/2026-09-07.md");
    assert!(before.iter().any(|l| l.starts_with("12:30 energy")), "{before:?}");
    tm.ok_at("2026-09-07T13:20:00-05:00", &["now"]);
    let out = tm.run_at("2026-09-07T13:25:00-05:00", &["undo"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let j = journal(&tm, "day/2026-09-07.md");
    assert!(!j.iter().any(|l| l.starts_with("12:30 energy")), "the report is undone: {j:?}");
    assert!(j.contains(&"12:50 pause ^t4".to_string()), "{j:?}");
    let a = &tm.state()["active"];
    assert_eq!(a["id"], "t4", "{a}");
    assert_eq!(a["paused"], true, "the undo put back the state the log says: {a}");
    let now = active(&tm, "2026-09-07T13:30:00-05:00");
    assert_eq!(now["paused"], true, "{now}");
    assert_eq!(now["elapsed_min"], 50, "{now}");
}

/// **The evening before's meeting is paused, and each mark is journaled on its
/// own day** (README gap 3334). `^t4` began at 22:30; a meeting at 22:40–22:50
/// and a late call at 23:30–00:30 follow; the first verb runs at 00:10. The
/// kernel read the walls of the verb's day alone, so the 22:40 meeting wrote
/// nothing, and the host journaled the 23:30 pause into the NEXT day's file.
#[test]
fn a_meeting_the_evening_before_is_paused_and_journaled_on_its_own_day() {
    let tm = Tm::new();
    let cal = tm.plan.join("calendar/2026-W37.md");
    let text = std::fs::read_to_string(&cal).expect("read the calendar");
    let text = text.replace(
        "- [ ] 2 CS 234 lecture       at:2026-09-09T15:00/16:20 loc:JCL ^g2",
        "- [ ] 2 Late call          at:2026-09-07T23:30/2026-09-08T00:30 loc:zoom ^g2\n\
         - [ ] 2 Evening sync       at:2026-09-07T22:40/22:50 loc:zoom ^g5",
    );
    assert!(text.contains("Evening sync"), "the fixture line was found");
    std::fs::write(&cal, text).expect("write the calendar");
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T22:30:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-08T00:10:00-05:00", &["now"]);
    assert_eq!(
        timer_marks(&tm),
        vec![
            ("pause".to_string(), "2026-09-07T22:40:00-05:00".to_string()),
            ("unpause".to_string(), "2026-09-07T22:50:00-05:00".to_string()),
            ("pause".to_string(), "2026-09-07T23:30:00-05:00".to_string()),
        ],
        "both meetings stop the timer"
    );
    let j = journal(&tm, "day/2026-09-07.md");
    for want in ["22:40 pause ^t4", "22:50 unpause ^t4", "23:30 pause ^t4"] {
        assert!(j.contains(&want.to_string()), "{want} is in the evening's own file: {j:?}");
    }
    if tm.exists("day/2026-09-08.md") {
        let next = journal(&tm, "day/2026-09-08.md");
        assert!(!next.iter().any(|l| l.contains("pause ^t4")), "nothing in the next day's file: {next:?}");
    }
}
