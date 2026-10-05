//! **`tm wake` over an open interruption or a running break is refused by
//! name** — the campaign's D81 call on README gap 3824, parity P74, stage 6
//! W-41 track T: D76's rule (README gap 3725) for every running state a wake
//! would clear.
//!
//! The wake cleared `interrupt` from `.tm/state.json` while the log held the
//! interruption open, so every later verb's reconcile (D42) read it back in
//! memory and a `tm resume` logged the whole night as lost; and it cleared the
//! running break, which — host-only — was lost with no line. Fork 4748911
//! clears both and keeps them cleared. Now the wake is refused, naming the
//! state and when it began, and writes nothing; the interruption is the log's,
//! so a deleted cache changes nothing. D76's own refusal names `--at` (the
//! owner's D79, `cli_end_at.rs`).

mod cli_common;

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use cli_common::Tm;

const WAKE: &str = "2026-09-08T06:05:00-05:00";
const MORNING: &str = "2026-09-09T07:00:00-05:00";

/// Every file of the tree but the replay cache, by path, as bytes.
fn files(root: &Path) -> BTreeMap<String, Vec<u8>> {
    fn walk(root: &Path, dir: &Path, out: &mut BTreeMap<String, Vec<u8>>) {
        for entry in fs::read_dir(dir).expect("read dir") {
            let entry = entry.expect("entry");
            let path = entry.path();
            let rel = path.strip_prefix(root).expect("inside").to_string_lossy().into_owned();
            if rel.starts_with(".tm/cache") {
                continue;
            }
            if entry.file_type().expect("type").is_dir() {
                walk(root, &path, out);
            } else {
                out.insert(rel, fs::read(&path).expect("read"));
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(root, root, &mut out);
    out
}

/// A tree with `verb` run at `at` the evening before, nothing else running.
fn left_open(at: &str, verb: &[&str]) -> Tm {
    let tm = Tm::new();
    tm.ok_at(WAKE, &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at(at, verb);
    tm
}

/// **An open interruption**: `tm interrupt` at 22:00 with nothing running; the
/// wake at 07:00 is refused, names the interruption and its start, and writes
/// nothing; `tm resume` ends it and the wake then goes through.
#[test]
fn tm_wake_over_an_open_interruption_is_refused() {
    let tm = left_open("2026-09-08T22:00:00-05:00", &["interrupt"]);
    tm.ok_at(MORNING, &["now"]);
    let before = files(&tm.plan);
    let out = tm.run_at(MORNING, &["wake", "06:30", "--slept", "7h"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("an interruption is still open since 2026-09-08 22:00 — end it (`tm resume`) before `tm wake`"),
        "{}",
        out.stderr
    );
    assert_eq!(files(&tm.plan), before, "the refused wake wrote nothing");
    tm.ok_at("2026-09-09T07:10:00-05:00", &["resume"]);
    let woke = tm.json_at("2026-09-09T07:11:00-05:00", &["wake", "06:30", "--slept", "7h"]);
    assert_eq!(woke["wake"], "06:30", "{woke}");
}

/// **The interruption is the log's**: with `.tm/state.json` deleted the wake
/// is refused the same way, and the log gains nothing.
#[test]
fn deleting_the_cache_changes_nothing() {
    let tm = left_open("2026-09-08T22:00:00-05:00", &["interrupt"]);
    fs::remove_file(tm.plan.join(".tm/state.json")).expect("delete the cache");
    let log = tm.read(".tm/log.jsonl");
    let out = tm.run_at(MORNING, &["wake", "06:30", "--slept", "7h"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("an interruption is still open since 2026-09-08 22:00"), "{}", out.stderr);
    assert_eq!(tm.read(".tm/log.jsonl"), log, "nothing logged");
    assert_eq!(tm.state()["interrupt"]["started"], "22:00", "{}", tm.state());
}

/// **A running break**: begun at 23:50 with nothing running; the wake is
/// refused, names the break's start — the evening's, P73's reading — and
/// writes nothing; `tm break` ends it and the wake then goes through.
#[test]
fn tm_wake_over_a_running_break_is_refused() {
    let tm = left_open("2026-09-08T23:50:00-05:00", &["break", "20m"]);
    tm.ok_at(MORNING, &["now"]);
    let before = files(&tm.plan);
    let out = tm.run_at(MORNING, &["wake", "06:30", "--slept", "7h"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("a break is still running since 2026-09-08 23:50 — end it (`tm break`) before `tm wake`"),
        "{}",
        out.stderr
    );
    assert_eq!(files(&tm.plan), before, "the refused wake wrote nothing");
    assert_eq!(tm.state()["break"]["started"], "23:50", "{}", tm.state());
    tm.ok_at("2026-09-09T07:10:00-05:00", &["break"]);
    let woke = tm.json_at("2026-09-09T07:11:00-05:00", &["wake", "06:30", "--slept", "7h"]);
    assert_eq!(woke["wake"], "06:30", "{woke}");
}

/// **A cached break with no start is still a running break** (the W-41 repair,
/// README gap 4141): `.tm/state.json`'s `break` hand-edited to `started: null`
/// has no instant, and P74's refusal asked for the instant — so the wake went
/// through and cleared the record with no `break` line. The refusal reads the
/// RECORD, writes nothing, and `tm break` still ends it.
///
/// **Since the owner's D105 (parity P100) the start is the log's**: `tm break`
/// logged a `break_start`, so the refusal names that instant whatever the
/// cache's clock says. The record with no instant the W-41 repair was about is
/// a break the log holds no start for — one a binary before D105 began — and
/// that is the second half: the `break_start` line taken out as well.
#[test]
fn tm_wake_over_a_break_with_no_start_is_refused() {
    let tm = left_open("2026-09-08T23:50:00-05:00", &["break", "20m"]);
    tm.ok_at(MORNING, &["now"]);
    let path = tm.plan.join(".tm/state.json");
    let mut state: serde_json::Value = serde_json::from_str(&fs::read_to_string(&path).expect("state")).expect("JSON");
    state["break"]["started"] = serde_json::Value::Null;
    fs::write(&path, serde_json::to_string(&state).expect("JSON")).expect("write the hand edit");
    // D105: the logged start names the break whatever the cache says.
    let out = tm.run_at(MORNING, &["wake", "06:30", "--slept", "7h"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("a break is still running since 2026-09-08 23:50 — end it (`tm break`) before `tm wake`"),
        "the refusal did not name the start `tm break` logged: {}",
        out.stderr
    );
    // A break a binary before D105 began: its log holds no `break_start`.
    let log = tm.read(".tm/log.jsonl");
    let stripped: String =
        log.lines().filter(|l| !l.contains("\"ev\":\"break_start\"")).map(|l| format!("{l}\n")).collect();
    assert_ne!(stripped, log, "`tm break` logged no `break_start`, so this half would prove nothing");
    fs::write(tm.plan.join(".tm/log.jsonl"), &stripped).expect("a log as a binary before D105 wrote it");
    let before = files(&tm.plan);
    let out = tm.run_at(MORNING, &["wake", "06:30", "--slept", "7h"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("a break is still running — end it (`tm break`) before `tm wake`; the wake was not recorded"),
        "{}",
        out.stderr
    );
    assert_eq!(files(&tm.plan), before, "the refused wake wrote nothing");
    tm.ok_at("2026-09-09T07:10:00-05:00", &["break"]);
    assert!(tm.state()["break"].is_null(), "`tm break` ended it: {}", tm.state());
    let woke = tm.json_at("2026-09-09T07:11:00-05:00", &["wake", "06:30", "--slept", "7h"]);
    assert_eq!(woke["wake"], "06:30", "{woke}");
}

/// **D76's refusal names `--at`** (the owner's D79): the way to end a block
/// forgotten overnight when it ended.
#[test]
fn the_running_block_refusal_names_the_end_time() {
    let tm = left_open("2026-09-08T23:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    let out = tm.run_at(MORNING, &["wake", "06:30"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains(
            "^t4 is still running since 2026-09-08 23:00 — stop it (`tm stop`) or finish it (`tm done`) \
             before `tm wake`, with `--at HH:MM` for when it ended if that was earlier"
        ),
        "{}",
        out.stderr
    );
}
