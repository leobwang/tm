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
    // Two changes ONE writer owns — `ci=` on this line's positional digit is
    // not on the wire, and D49's repair refuses a command that mixes the two
    // rather than letting the host write the kernel's key (W-27).
    tm.ok(&["edit", "^a1", "est=45m", "loc=out"]);
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
    // Q6(d), gap 84: the name is prefixed, so it can never collide with an
    // event tag. `rank` never could; `move` and `close` can.
    assert_eq!(undone(&tm), vec!["verb:rank"]);
    assert_eq!(tm.last()["id"], serde_json::Value::Null);
}

/// Append one raw line to `.tm/log.jsonl`, as a hand edit or an older tm would
/// have left it.
fn append_raw(tm: &Tm, line: &str) {
    use std::io::Write;
    let path = tm.plan.join(".tm/log.jsonl");
    let mut f = std::fs::OpenOptions::new().append(true).open(&path).expect("open the log");
    writeln!(f, "{line}").expect("append");
}

/// The lines `tm log --item <id>` still shows: the mask drops a cancelled one.
fn item_rows(tm: &Tm, now: &str, id: &str) -> Vec<String> {
    tm.json_at(now, &["log", "--item", id])["entries"]
        .as_array()
        .expect("entries")
        .iter()
        .map(|e| e["ev"].as_str().unwrap_or_default().to_string())
        .collect()
}

/// **Q6(d), gap 84 — the fix, in both directions** (design §22.1's step S2).
///
/// The bare spelling an older tm wrote still cancels the latest event of that
/// tag; the `verb:` spelling this tm writes cancels nothing. Both are read by
/// the same mask, so a log that mixes them reads each line as it was meant.
#[test]
fn a_silent_verb_undo_cancels_nothing_while_the_old_spelling_still_cancels() {
    // The old spelling: `undo{of:"move"}` takes the standing `move`.
    let old = Tm::new();
    old.ok_at("2026-09-07T09:00:00-05:00", &["move", "^a1", "week"]);
    assert_eq!(item_rows(&old, "2026-09-07T09:02:00-05:00", "^a1"), vec!["move"]);
    append_raw(&old, r#"{"t":"2026-09-07T09:01:00-05:00","ev":"undo","of":"move"}"#);
    assert!(
        item_rows(&old, "2026-09-07T09:02:00-05:00", "^a1").is_empty(),
        "a log written before this step must still cancel the way it did"
    );

    // The new spelling: `undo{of:"verb:move"}` matches no event tag, so the
    // older, unrelated `move` stands. This is the byte `tm undo` now writes.
    let new = Tm::new();
    new.ok_at("2026-09-07T09:00:00-05:00", &["move", "^a1", "week"]);
    append_raw(&new, r#"{"t":"2026-09-07T09:01:00-05:00","ev":"undo","of":"verb:move"}"#);
    assert_eq!(
        item_rows(&new, "2026-09-07T09:02:00-05:00", "^a1"),
        vec!["move"],
        "a `verb:`-prefixed undo must cancel nothing"
    );
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

/// **Q6(f), gap 86 — a close carries its period as a primary id.**
///
/// `tm close day`, then `tm undo`: the compensating event names the period it
/// closed, so it cancels **that** close. Before this step `close` had no id at
/// all, and the undo cancelled whichever close was latest — which, once a later
/// verb's housekeeping had appended its own automatic close, was the automatic
/// one rather than the one the user undid.
///
/// The other half of the fix — that a log written **before** this step still
/// reads exactly as it did, because an undo carrying no id matches on the tag
/// alone — is proved in the kernel, where both spellings can be put side by
/// side over one replay:
/// `Replay.an_undo_of_a_close_cancels_its_own_period_and_an_older_one_still_cancels_the_latest`.
#[test]
fn an_undo_of_a_close_names_the_period_it_closed() {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-08T09:00:00-05:00", &["close", "day"]);

    // The close itself is unchanged: it always carried its period and key.
    let closes: Vec<(String, String)> = tm
        .log()
        .into_iter()
        .filter(|e| e["ev"] == "close")
        .map(|e| {
            (
                e["period"].as_str().unwrap_or_default().to_string(),
                e["key"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect();
    assert!(!closes.is_empty(), "the close logged nothing: {:?}", tm.log());

    tm.ok_at("2026-09-08T09:01:00-05:00", &["undo"]);

    // What changed is the undo: it names `period:key`, so the mask can tell one
    // close from another.
    let undos: Vec<(String, String)> = tm
        .log()
        .into_iter()
        .filter(|e| e["ev"] == "undo")
        .map(|e| {
            (
                e["of"].as_str().unwrap_or_default().to_string(),
                e["id"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect();
    let close_undo = undos
        .iter()
        .find(|(of, _)| of == "close")
        .unwrap_or_else(|| panic!("no undo of a close: {undos:?}"));
    let (period, key) = closes.last().expect("a close");
    assert_eq!(
        close_undo.1,
        format!("{period}:{key}"),
        "the undo of a close must name the period it closed: {undos:?}"
    );
}

// ---------------------------------------------------------------------------
// W-22 track A — README gap 887: the undo names the writer that got there
// first, and says why that writer is unreachable.
//
// The mechanism is gap 731's: §6.3's automatic close runs inside
// `Ctx::load_with`, before every verb's `Recorder::start`, so it is in no undo
// entry. Until here the refusal said only "the file changed under us", which
// blames an external editor for tm's own write and leaves the stack a dead end
// with nothing to act on. Attribution cannot go on `CliError::message` — that
// sentence is every verb's — so it rides `CliError::UndoBlocked`, which only
// the undo path builds, off `.tm/log.jsonl` read through the one reader (D9):
// `Ctx::log_tail_of` for the tail's headers and `Ctx::entries_at` for the
// close's instant. Neither read happens unless the guard has already tripped.

/// The `--json` failure document of a command that fails: `ErrorOut` goes to
/// **stderr** (§13), so `Tm::json_at` — which asserts exit 0 and reads stdout —
/// cannot be used for one.
fn failure_doc(tm: &Tm, now: &str, args: &[&str]) -> serde_json::Value {
    let out = tm.run_at(now, args);
    assert_ne!(out.code, 0, "expected a failure: {}{}", out.stdout, out.stderr);
    serde_json::from_str(&out.stderr)
        .unwrap_or_else(|e| panic!("stderr is not the JSON document ({e}): {}", out.stderr))
}

/// The physical 1-based line of the first `close` entry in the log.
fn first_close_line(tm: &Tm) -> u64 {
    physical_lines(tm)
        .iter()
        .position(|l| {
            serde_json::from_str::<serde_json::Value>(l)
                .map(|v| v["ev"] == "close")
                .unwrap_or(false)
        })
        .map(|i| i as u64 + 1)
        .expect("the automatic close appended no `close` entry")
}

#[test]
fn an_undo_behind_the_automatic_close_names_the_close() {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t3", "--energy", "4"]);
    tm.ok_at("2026-09-07T10:00:00-05:00", &["done"]);
    // A verb on the next day. §6.3's automatic close runs inside its load and
    // rewrites the day file the `done` above is holding bytes for — and pushes
    // no undo entry of its own, which is the whole of gap 731.
    tm.ok_at("2026-09-08T09:00:00-05:00", &["now"]);

    let at = first_close_line(&tm);
    let out = tm.run_at("2026-09-08T09:05:00-05:00", &["undo"]);
    assert_eq!(out.code, 3, "{}{}", out.stdout, out.stderr);
    // The shared sentence is unchanged — every verb's write race still reads
    // the same — and the new lines sit under it.
    assert!(
        out.stderr.contains("the file changed under us"),
        "{}",
        out.stderr
    );
    assert!(
        out.stderr.contains("the later writer is tm itself"),
        "the refusal still blames an outside editor: {}",
        out.stderr
    );
    assert!(
        out.stderr.contains(&format!(".tm/log.jsonl:{at} records a `close`")),
        "the close is not named at its own line {at}: {}",
        out.stderr
    );
    assert!(
        out.stderr.contains("README gap 731"),
        "the refusal does not say why the close cannot be undone: {}",
        out.stderr
    );

    // The same fact, machine-readable, and pinned to the log's own numbering.
    let doc = failure_doc(&tm, "2026-09-08T09:06:00-05:00", &["--json", "undo"]);
    let blame = &doc["detail"]["laterWriter"];
    assert_eq!(blame["anchored"], true, "{doc}");
    assert_eq!(blame["close_line"], at, "{doc}");
    assert!(
        blame["close_at"].is_string(),
        "the close's instant did not read back: {doc}"
    );
    assert!(
        blame["entries_after"].as_u64().unwrap_or(0) >= 1,
        "{doc}"
    );
    // Nothing was half-undone: the guard still refuses and the entry stays.
    assert_eq!(doc["exit_code"], 3, "{doc}");
    assert_eq!(top_of_stack(&tm)["verb"], "done");
}

#[test]
fn an_undo_behind_an_outside_editor_says_the_log_knows_of_no_writer() {
    // The other direction (AGENTS §5.8): when tm really did not write, the
    // refusal must not invent a close. The log holds nothing after the undone
    // `done`, and that is what it says.
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
    assert!(
        out.stderr.contains("it was changed from outside tm"),
        "{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("`close`"),
        "a close was named where the log holds none: {}",
        out.stderr
    );
    let doc = failure_doc(&tm, "2026-09-07T10:02:00-05:00", &["--json", "undo"]);
    let blame = &doc["detail"]["laterWriter"];
    assert_eq!(blame["anchored"], true, "{doc}");
    assert_eq!(blame["close_line"], serde_json::Value::Null, "{doc}");
    assert_eq!(blame["entries_after"], 0, "{doc}");
}

#[test]
fn an_undo_of_a_verb_that_logged_nothing_says_it_cannot_tell() {
    // `tm rank` is line order and appends no event (§7.4), so its entry has no
    // `log_line` and there is no point in the log to read forward from. The
    // honest answer is to say so — naming the first close in the file instead
    // would name a close that ran BEFORE the command being undone.
    let tm = Tm::new();
    tm.ok(&["rank", "^t4", "1"]);
    let path = tm.plan.join("week/2026-W37.md");
    let mut text = std::fs::read_to_string(&path).expect("read week");
    text.push_str("- [ ] 3 1b Written by an editor   @m2 ^zz2\n");
    std::fs::write(&path, &text).expect("write week");

    let out = tm.run_at("2026-09-07T09:05:00-05:00", &["undo"]);
    assert_eq!(out.code, 3, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("appended no log entry"),
        "{}",
        out.stderr
    );
    let doc = failure_doc(&tm, "2026-09-07T09:06:00-05:00", &["--json", "undo"]);
    assert_eq!(doc["detail"]["laterWriter"]["anchored"], false, "{doc}");

    // **And the unanchored answer is a reading, not a default.** On the same
    // tree and the same file, a verb that DOES log reads `anchored: true` —
    // without this half a `later_writer` that returned `LaterWriter::default()`
    // unconditionally would pass the assertion above (probed: it does).
    std::fs::write(&path, &text).expect("put the editor's line back");
    tm.ok_at("2026-09-07T09:07:00-05:00", &["edit", "^t4", "ci=2"]);
    let mut wider = std::fs::read_to_string(&path).expect("read week");
    wider.push_str("- [ ] 3 1b And another editor line   @m2 ^zz3\n");
    std::fs::write(&path, &wider).expect("write week");
    let doc = failure_doc(&tm, "2026-09-07T09:08:00-05:00", &["--json", "undo"]);
    assert_eq!(doc["detail"]["laterWriter"]["anchored"], true, "{doc}");
}
