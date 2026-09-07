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
fn undo_with_an_empty_stack_is_an_error() {
    let tm = Tm::new();
    let out = tm.run(&["undo"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("nothing to undo"), "{}", out.stderr);
}
