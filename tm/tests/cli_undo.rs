//! `tm undo` compensates each state change (§13, §17 M5).
//!
//! Nothing in the log is ever edited: the undo **appends** the compensating
//! `undo{of,id}` event (§10.1) and puts the line and `.tm/state.json` back.

mod cli_common;

use cli_common::Tm;

/// The `of` values of the `undo` events in the log.
fn undone(tm: &Tm) -> Vec<String> {
    tm.log()
        .into_iter()
        .filter(|e| e["ev"] == "undo")
        .map(|e| e["of"].as_str().unwrap_or_default().to_string())
        .collect()
}

#[test]
fn undo_done_puts_the_state_glyph_back() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let before = tm.line("week/2026-W37.md", "t4");
    tm.ok_at("2026-09-07T10:00:00-05:00", &["done"]);
    assert!(tm.line("week/2026-W37.md", "t4").starts_with("- [x]"));

    let json = tm.json_at("2026-09-07T10:01:00-05:00", &["undo"]);
    assert_eq!(json["verb"], "done");
    // `[x]` back to `[>]`, byte for byte.
    assert_eq!(tm.line("week/2026-W37.md", "t4"), before);
    // The block is running again.
    assert_eq!(tm.state()["active"]["id"], "t4");
    assert_eq!(undone(&tm), vec!["done"]);
    let last = tm.last();
    assert_eq!(last["ev"], "undo");
    assert_eq!(last["id"], "t4");
    insta::assert_json_snapshot!("undo_json", json);
}

#[test]
fn undo_start_clears_the_block_and_the_line() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    let before = tm.line("week/2026-W37.md", "t4");
    tm.ok(&["start", "^t4", "--energy", "4"]);

    tm.ok_at("2026-09-07T09:05:00-05:00", &["undo"]);
    assert_eq!(tm.line("week/2026-W37.md", "t4"), before);
    assert_eq!(tm.state()["active"], serde_json::Value::Null);
    assert_eq!(undone(&tm), vec!["start"]);
}

#[test]
fn undo_stop_restores_the_running_block() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let running = tm.line("week/2026-W37.md", "t4");
    tm.ok_at("2026-09-07T09:20:00-05:00", &["stop"]);

    tm.ok_at("2026-09-07T09:21:00-05:00", &["undo"]);
    assert_eq!(tm.line("week/2026-W37.md", "t4"), running);
    assert_eq!(tm.state()["active"]["id"], "t4");
    assert_eq!(undone(&tm), vec!["stop"]);
}

#[test]
fn undo_extend_restores_the_estimate() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let before = tm.line("week/2026-W37.md", "t4");
    let est = tm.state()["active"]["est_min"].clone();
    tm.ok(&["extend", "1b"]);

    tm.ok_at("2026-09-07T09:10:00-05:00", &["undo"]);
    assert_eq!(tm.line("week/2026-W37.md", "t4"), before);
    assert_eq!(tm.state()["active"]["est_min"], est);
    assert_eq!(undone(&tm), vec!["extend"]);
}

#[test]
fn undo_add_removes_the_line() {
    let tm = Tm::new();
    let before = tm.read("backlog.md");
    let json = tm.json(&["add", "2 30m Call the plumber", "--to", "backlog"]);
    let id = json["id"].as_str().expect("an id").to_string();
    assert!(tm.read("backlog.md").contains(&id));

    tm.ok_at("2026-09-07T09:05:00-05:00", &["undo"]);
    assert_eq!(tm.read("backlog.md"), before);
    // The `add` was logged as an `edit` (§10.1 has no `add`).
    assert_eq!(undone(&tm), vec!["edit"]);
}

#[test]
fn undo_edit_restores_every_field_and_cancels_every_event() {
    let tm = Tm::new();
    let before = tm.line("backlog.md", "a1");
    tm.ok(&["edit", "^a1", "ci=3", "est=45m"]);
    assert_ne!(tm.line("backlog.md", "a1"), before);

    tm.ok_at("2026-09-07T09:05:00-05:00", &["undo"]);
    assert_eq!(tm.line("backlog.md", "a1"), before);
    // One `undo` per `edit` the command wrote.
    assert_eq!(undone(&tm), vec!["edit", "edit"]);
}

#[test]
fn undo_move_puts_the_line_back_in_its_file() {
    let tm = Tm::new();
    let backlog = tm.read("backlog.md");
    let week = tm.read("week/2026-W37.md");
    tm.ok(&["move", "^a1", "week"]);
    assert!(!tm.read("backlog.md").contains("^a1"));

    tm.ok_at("2026-09-07T09:05:00-05:00", &["undo"]);
    assert_eq!(tm.read("backlog.md"), backlog);
    assert_eq!(tm.read("week/2026-W37.md"), week);
    assert_eq!(undone(&tm), vec!["move"]);
}

#[test]
fn undo_demote_removes_the_archive_copy() {
    let tm = Tm::new();
    let week = tm.read("week/2026-W37.md");
    let month = tm.read("month/2026-09.md");
    tm.ok(&["demote", "^m4"]);
    assert!(tm.read("month/2026-09.md").contains("^m4"));

    tm.ok_at("2026-09-07T09:05:00-05:00", &["undo"]);
    assert_eq!(tm.read("week/2026-W37.md"), week);
    assert_eq!(tm.read("month/2026-09.md"), month);
    assert_eq!(undone(&tm), vec!["demote"]);
}

#[test]
fn undo_drop_restores_the_open_state() {
    let tm = Tm::new();
    let before = tm.line("week/2026-W37.md", "m4");
    tm.ok(&["drop", "^m4"]);
    assert!(tm.line("week/2026-W37.md", "m4").starts_with("- [~]"));

    tm.ok_at("2026-09-07T09:05:00-05:00", &["undo"]);
    assert_eq!(tm.line("week/2026-W37.md", "m4"), before);
    assert_eq!(undone(&tm), vec!["drop"]);
}

#[test]
fn undo_event_puts_the_item_back_in_waiting() {
    let tm = Tm::new();
    let before = tm.line("backlog.md", "a4");
    tm.ok(&["event", "reply"]);
    assert!(tm.line("backlog.md", "a4").starts_with("- [ ]"));

    tm.ok_at("2026-09-07T09:05:00-05:00", &["undo"]);
    assert_eq!(tm.line("backlog.md", "a4"), before);
    assert_eq!(undone(&tm), vec!["event"]);
}

#[test]
fn undo_skip_cancels_the_instance() {
    let tm = Tm::new();
    tm.ok(&["skip", "lunch"]);
    assert!(tm.events().contains(&"skip".to_string()));

    tm.ok_at("2026-09-07T09:05:00-05:00", &["undo"]);
    assert_eq!(undone(&tm), vec!["skip"]);
    // The log is append-only: the `skip` line is still there, cancelled.
    assert!(tm.events().contains(&"skip".to_string()));
}

#[test]
fn undo_unwinds_the_stack_one_command_at_a_time() {
    let tm = Tm::new();
    let week = tm.read("week/2026-W37.md");
    tm.ok(&["edit", "^t4", "ci=5"]);
    tm.ok(&["drop", "^m4"]);

    tm.ok_at("2026-09-07T09:05:00-05:00", &["undo"]);
    assert!(tm.line("week/2026-W37.md", "t4").contains("[ ] 5"));
    tm.ok_at("2026-09-07T09:06:00-05:00", &["undo"]);
    assert_eq!(tm.read("week/2026-W37.md"), week);
    assert_eq!(undone(&tm), vec!["drop", "edit"]);
}

#[test]
fn undo_of_a_close_reopens_the_period() {
    // §17 M5: "`tm undo` compensates each state change". §6.3's auto-close is
    // keyed on `state.closed`, so leaving the day marked closed while its
    // files are back would strand it — it would never be closed again.
    let tm = Tm::new();
    let week = tm.read("week/2026-W37.md");
    // The first command stamps the periods that ended before the fixture's
    // day; the next morning's `tm close day` closes that day (stage 4 step 6:
    // a close takes only periods that have ended).
    tm.ok_at("2026-09-07T21:00:00-05:00", &["now"]);
    assert_eq!(tm.state()["closed"]["day"], "2026-09-06");
    tm.ok_at("2026-09-08T09:00:00-05:00", &["close", "day"]);
    assert_eq!(tm.state()["closed"]["day"], "2026-09-07");
    assert!(tm.read("week/2026-W37.md").contains("^p1"));

    tm.ok_at("2026-09-08T09:01:00-05:00", &["undo"]);
    assert_eq!(tm.read("week/2026-W37.md"), week);
    // The auto-close of *earlier* periods stands; this day is open again.
    assert_eq!(tm.state()["closed"]["day"], "2026-09-06");
    // One `undo` per event the close wrote: the pinned item's `demote` and
    // the `close` itself (§10.1), most recent first.
    assert_eq!(undone(&tm), vec!["close", "demote"]);
}

#[test]
fn undo_of_a_verb_that_logs_nothing_still_leaves_a_trace() {
    // §13: `tm undo` is "a compensating event for the last state change".
    // `tm rank` rewrites line order (§7.4: rank *is* line order) and logs
    // nothing, so without this the change and its reversal are both invisible.
    let tm = Tm::new();
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    let week = tm.read("week/2026-W37.md");
    tm.ok(&["rank", "^m3", "1"]);
    assert_ne!(tm.read("week/2026-W37.md"), week);

    tm.ok_at("2026-09-07T09:01:00-05:00", &["undo"]);
    assert_eq!(tm.read("week/2026-W37.md"), week);
    assert_eq!(undone(&tm), vec!["rank"]);
}

#[test]
fn undo_refuses_to_discard_another_writers_change() {
    // §1.3: three writers, one file set. Restoring a whole file would throw
    // away everything VS Code or Claude Code wrote since — so a file that no
    // longer holds what the undone command left is §13's exit code 3.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t3", "--energy", "4"]);
    tm.ok_at("2026-09-07T10:00:00-05:00", &["done"]);

    let path = tm.plan.join("week/2026-W37.md");
    let mut text = std::fs::read_to_string(&path).expect("read week");
    text.push_str("- [ ] 3 1b Written by Claude Code   @m2 ^zz1\n");
    std::fs::write(&path, &text).expect("write week");

    let out = tm.run_at("2026-09-07T10:01:00-05:00", &["undo"]);
    assert_eq!(out.code, 3, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("conflict"), "{}", out.stderr);
    assert_eq!(std::fs::read_to_string(&path).expect("read week"), text);
    // The entry is still on the stack: nothing was half-undone.
    assert!(tm.line("week/2026-W37.md", "t3").starts_with("- [x]"));
}

#[test]
fn undo_with_an_empty_stack_is_an_error() {
    let tm = Tm::new();
    let out = tm.run(&["undo"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("nothing to undo"), "{}", out.stderr);
}

/// The log's physical lines (a final `\n` ends the last one), unparsed.
fn physical_lines(tm: &Tm) -> Vec<String> {
    let text = tm.read(".tm/log.jsonl");
    text.strip_suffix('\n').unwrap_or(&text).split('\n').map(str::to_string).collect()
}

/// The top of `.tm/undo.json`.
fn top_of_stack(tm: &Tm) -> serde_json::Value {
    let stack: serde_json::Value = serde_json::from_str(&tm.read(".tm/undo.json")).expect("undo.json");
    stack["entries"].as_array().and_then(|e| e.last()).cloned().expect("an undo entry")
}

#[test]
fn a_malformed_line_does_not_shift_the_recorded_events() {
    // Parity P18 (design §7.2): the recorder counted non-blank lines, malformed
    // ones included, and then skipped that many *parsed* entries, so every
    // malformed line earlier in the log hid one of the command's own events.
    // It now counts physical lines and reads the entries after them.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    let path = tm.plan.join(".tm/log.jsonl");
    let mut text = std::fs::read_to_string(&path).expect("read log");
    text.push_str("this is not json\n\n{\"t\":\"2026-09-07T06:30:00-05:00\",\"ev\":\"wake\"\n");
    std::fs::write(&path, &text).expect("write log");
    let before = physical_lines(&tm).len();

    tm.ok(&["start", "^t4", "--energy", "4"]);
    let lines = physical_lines(&tm);
    let appended: Vec<serde_json::Value> = lines[before..]
        .iter()
        .map(|l| serde_json::from_str(l).expect("an appended line is JSON"))
        .collect();
    assert!(appended.iter().any(|e| e["ev"] == "start" && e["id"] == "t4"), "{appended:?}");
    let top = top_of_stack(&tm);
    assert_eq!(top["verb"], "start");
    let recorded = top["events"].as_array().expect("events").clone();
    let names = |es: &[serde_json::Value]| es.iter().map(|e| e["ev"].as_str().unwrap_or_default().to_string()).collect::<Vec<_>>();
    assert_eq!(names(&recorded), names(&appended), "every appended event is recorded, the first included");
    assert!(recorded.iter().any(|e| e["ev"] == "start" && e["id"] == "t4"), "{recorded:?}");
    assert_eq!(top["log_line"], serde_json::json!(before + 1), "the first appended line, counted physically");

    // And the undo cancels the start by its id, not by name alone.
    tm.ok_at("2026-09-07T09:05:00-05:00", &["undo"]);
    let last: serde_json::Value = serde_json::from_str(physical_lines(&tm).last().expect("a line")).expect("JSON");
    assert_eq!(last["ev"], "undo");
    assert_eq!(last["of"], "start");
    assert_eq!(last["id"], "t4");
    assert_eq!(tm.state()["active"], serde_json::Value::Null);
}

#[test]
fn an_undo_stack_written_before_log_line_still_undoes() {
    // CRIT 27: `.tm/undo.json` files written before `log_line` existed have no
    // such key. They must load (as `None`) and undo exactly as before.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    let before = tm.line("week/2026-W37.md", "t4");
    tm.ok(&["start", "^t4", "--energy", "4"]);
    assert!(top_of_stack(&tm)["log_line"].is_u64(), "a new entry carries its line");

    let path = tm.plan.join(".tm/undo.json");
    let mut stack: serde_json::Value = serde_json::from_str(&tm.read(".tm/undo.json")).expect("undo.json");
    for e in stack["entries"].as_array_mut().expect("entries") {
        e.as_object_mut().expect("an entry").remove("log_line");
    }
    std::fs::write(&path, serde_json::to_string_pretty(&stack).expect("json")).expect("write undo.json");
    assert!(!tm.read(".tm/undo.json").contains("log_line"));

    tm.ok_at("2026-09-07T09:05:00-05:00", &["undo"]);
    assert_eq!(tm.line("week/2026-W37.md", "t4"), before);
    assert_eq!(tm.state()["active"], serde_json::Value::Null);
    assert_eq!(undone(&tm), vec!["start"]);
    assert_eq!(tm.last()["id"], "t4");
    // The older entry (the wake) is still there, without the key, and undoes too.
    tm.ok_at("2026-09-07T09:06:00-05:00", &["undo"]);
    assert_eq!(undone(&tm), vec!["start", "wake"]);
}
