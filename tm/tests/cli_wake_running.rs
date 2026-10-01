//! **`tm wake` while a block is still running is refused by name** — the
//! owner's D76 (README gap 3725), parity P66, stage 6 W-40 track T.
//!
//! `tm wake` cleared `active` in `.tm/state.json` while the log held nothing
//! that ended the block, so the next verb's reconcile (D42) read the block back
//! as running — a verb that did not do what it said. Fork 4748911's wake clears
//! it and, having no reconcile, keeps it cleared. Ending the block at the wake
//! would write a duration nobody stated, so the wake is refused: the message
//! names the block and its start — the log's own instant — and says to stop or
//! finish it first, and the verb writes nothing. The load's housekeeping (the
//! day's roll, the automatic close) is every verb's, so the comparisons below
//! are made against a read verb run at the same instant.

mod cli_common;

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use cli_common::Tm;

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

/// A block left running overnight: `^t4` from Tuesday 23:00.
fn left_running() -> Tm {
    let tm = Tm::new();
    tm.ok_at("2026-09-08T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-08T23:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm
}

/// The morning after, `tm wake` is refused by name and writes nothing: every
/// file is byte-for-byte what `tm now` at the same instant left, the block is
/// still the cache's and the log's, and no `wake` is logged.
#[test]
fn tm_wake_over_a_running_block_is_refused_and_writes_nothing() {
    let tm = left_running();
    let at = "2026-09-09T07:00:00-05:00";
    tm.ok_at(at, &["now"]);
    let before = files(&tm.plan);
    let out = tm.run_at(at, &["wake", "06:30", "--slept", "7h"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("^t4 is still running since 2026-09-08 23:00")
            && out.stderr.contains("`tm stop`")
            && out.stderr.contains("`tm done`"),
        "the refusal names the block, its start and the two verbs that end it: {}",
        out.stderr
    );
    assert_eq!(files(&tm.plan), before, "the refused wake wrote nothing");
    assert_eq!(tm.state()["active"]["id"], "t4", "{}", tm.state());
    assert_eq!(tm.events().iter().filter(|e| *e == "wake").count(), 1, "{:?}", tm.events());
    let now = tm.json_at("2026-09-09T07:01:00-05:00", &["now"]);
    assert_eq!(now["active"]["id"], "t4", "the block still runs, with no reconcile notice needed: {now}");
}

/// A PAUSED block is still running — it ends only when `tm stop` or `tm done`
/// says how — and a block begun today names its start without a date.
#[test]
fn a_paused_block_and_a_block_begun_today_are_running_too() {
    let tm = Tm::new();
    tm.ok_at("2026-09-08T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-08T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-08T09:20:00-05:00", &["pause"]);
    let out = tm.run_at("2026-09-08T09:30:00-05:00", &["wake", "09:25"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("^t4 is still running since 09:00 —"), "{}", out.stderr);

    // An interruption pauses the block too (gap 3725's own world): still refused.
    let tm = Tm::new();
    tm.ok_at("2026-09-08T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-08T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-08T09:40:00-05:00", &["interrupt"]);
    let out = tm.run_at("2026-09-08T09:50:00-05:00", &["wake", "09:50"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("^t4 is still running since 09:00"), "{}", out.stderr);
}

/// With `.tm/state.json` deleted the block is the log's (D42) and the wake is
/// refused all the same: the refused wake and a read verb leave the tree
/// identical, and the log gains nothing.
#[test]
fn deleting_the_cache_changes_nothing() {
    let tm = left_running();
    let twin = left_running();
    for t in [&tm, &twin] {
        fs::remove_file(t.plan.join(".tm/state.json")).expect("delete the cache");
    }
    let at = "2026-09-09T07:00:00-05:00";
    let log_before = tm.read(".tm/log.jsonl");
    let out = tm.run_at(at, &["wake", "06:30", "--slept", "7h"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("^t4 is still running since 2026-09-08 23:00"), "{}", out.stderr);
    twin.ok_at(at, &["now"]);
    assert_eq!(files(&tm.plan), files(&twin.plan), "the refused wake left what a read verb leaves");
    assert_eq!(tm.read(".tm/log.jsonl"), log_before, "nothing logged");
}

/// Once the block is ended, `tm wake` goes through; with nothing running it
/// was never refused.
#[test]
fn tm_wake_with_no_block_running_still_works() {
    let tm = left_running();
    tm.ok_at("2026-09-09T07:00:00-05:00", &["stop"]);
    let woke = tm.json_at("2026-09-09T07:01:00-05:00", &["wake", "06:30", "--slept", "7h"]);
    assert_eq!(woke["wake"], "06:30", "{woke}");
    assert_eq!(tm.last_ev("wake")["slept_min"], 420, "{:?}", tm.last());
    assert!(tm.state()["active"].is_null(), "{}", tm.state());

    let fresh = Tm::new();
    let woke = fresh.json_at("2026-09-08T06:05:00-05:00", &["wake", "06:05"]);
    assert_eq!(woke["wake"], "06:05", "{woke}");
}
