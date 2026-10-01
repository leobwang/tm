//! **`tm stop --at HH:MM` and `tm done --at HH:MM` end the running block when
//! it ended** — the owner's D79 (README gap 3823), stage 6 W-41 track T.
//!
//! D76 refuses `tm wake` over a running block and says to stop or finish it;
//! both verbs ended the block NOW, and since D75 they count from the log's
//! start, so a block forgotten overnight logged the night as worked
//! (`stopped ^t4 after 485m`). The stated end is read by the one time parser
//! (`tm energy --at`'s), placed at the LATEST instant at or before `now` with
//! that clock (`--at 23:40` typed at 07:05 is last night), and the line that
//! ends the block is STAMPED at it: the log holds that instant (D75's clock),
//! appended after anything logged since, and every reader takes it so — the
//! kernel's replay (file order, each entry dated by its own stamp), the day
//! records, the durations §8.5 fits and `tm log`.
//!
//! Refused by name, nothing written: an end before the block's start (which
//! is how a time still to come today reads: the latest such clock is
//! yesterday's), a retro `tm done ^id --at`, an end before a timer mark the
//! log already holds for the block, and an end before a running break began.
//! D61's meeting marks run at the stated end, so a wall inside the block
//! pauses it and one after the end is not the block's.

mod cli_common;

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use cli_common::Tm;
use serde_json::Value;

/// Tuesday's wake, and the instant `^t4` is started and left running.
const WAKE: &str = "2026-09-08T06:05:00-05:00";
const START: &str = "2026-09-08T23:00:00-05:00";
/// Wednesday morning, when the user notices.
const MORNING: &str = "2026-09-09T07:05:00-05:00";
const AFTER: &str = "2026-09-09T07:06:00-05:00";

/// `^t4` from Tuesday 23:00, still running.
fn left_running() -> Tm {
    let tm = Tm::new();
    tm.ok_at(WAKE, &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at(START, &["start", "^t4", "--energy", "4"]);
    tm
}

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

/// A day's review, `--json`, at [`AFTER`].
fn review(tm: &Tm, date: &str) -> Value {
    tm.json_at(AFTER, &["review", "day", "--date", date])["review"].clone()
}

/// Add calendar walls to the tree, as `- [ ] … at:… ^id` lines.
fn walls(tm: &Tm, lines: &[&str]) {
    let path = tm.plan.join("calendar/2026-W37.md");
    let mut text = fs::read_to_string(&path).expect("calendar");
    for l in lines {
        text.push_str(l);
        text.push('\n');
    }
    fs::write(&path, text).expect("write calendar");
}

/// **The owner's drive**: `start` 23:00, `tm stop --at 23:40` at 07:05 — the
/// log, `tm now`, `tm log`, the reviews of both days and the day file all say
/// forty minutes, last night. Without `--at` the same stop counts the night.
#[test]
fn a_block_forgotten_overnight_stops_when_it_stopped() {
    let tm = left_running();
    let out = tm.ok_at(MORNING, &["stop", "--at", "23:40"]);
    assert_eq!(
        out.stdout.trim(),
        "stopped ^t4 after 40m · 20m left · ended 2026-09-08 23:40",
        "{}",
        out.stderr
    );
    let last = tm.last();
    assert_eq!(last["ev"], "stop", "{last}");
    assert_eq!(last["t"], "2026-09-08T23:40:00-05:00", "the log holds the stated instant: {last}");
    assert_eq!(last["remaining_min"], 20, "{last}");
    assert!(tm.state()["active"].is_null(), "{}", tm.state());
    assert_eq!(tm.json_at(AFTER, &["now"])["active"], Value::Null);
    let log = tm.ok_at(AFTER, &["log", "--tail", "1"]);
    assert_eq!(log.stdout.trim(), "2026-09-08 23:40 stop id=\"t4\" remaining_min=20");
    let tue = review(&tm, "2026-09-08");
    assert_eq!((tue["block_min"].as_u64(), tue["mix"]["total_min"].as_u64()), (Some(40), Some(40)), "{tue}");
    let wed = review(&tm, "2026-09-09");
    assert_eq!(wed["block_min"].as_u64(), Some(0), "{wed}");
    assert!(
        tm.read("day/2026-09-08.md").contains("23:40 stop ^t4 40m · 20m left"),
        "the journal line is the evening's, in the evening's file"
    );
    assert_eq!(tm.line("week/2026-W37.md", "t4"), "- [ ] 3 20m Claude Code drafts tests     @m2 ^t4");

    // The same stop without `--at` is the night counted, on Wednesday.
    let plain = left_running();
    let out = plain.ok_at(MORNING, &["stop"]);
    assert_eq!(out.stdout.trim(), "stopped ^t4 after 485m · 5m left");
    assert_eq!(review(&plain, "2026-09-09")["block_min"].as_u64(), Some(485));
}

/// **`tm done --at` logs the stated end and the minutes worked up to it**, so
/// the duration §8.5 fits reads forty minutes of sixty — and `--partial --at`
/// writes back the twenty left.
#[test]
fn done_at_logs_the_end_and_the_minutes_worked_to_it() {
    let tm = left_running();
    let out = tm.json_at(MORNING, &["done", "--at", "23:40"]);
    assert_eq!((out["actual_min"].as_u64(), out["ended"].as_str()), (Some(40), Some("2026-09-08 23:40")), "{out}");
    let done = tm.last_ev("done");
    assert_eq!(done["t"], "2026-09-08T23:40:00-05:00", "{done}");
    assert_eq!((done["actual_min"].as_u64(), done["est_min"].as_u64()), (Some(40), Some(60)), "{done}");
    let tue = review(&tm, "2026-09-08");
    assert_eq!(tue["done"], serde_json::json!(["t4"]), "{tue}");
    assert_eq!(tue["block_min"].as_u64(), Some(40), "{tue}");
    let est = &tue["estimates"][0];
    assert_eq!((est["n"].as_u64(), est["mean_ratio"].as_f64()), (Some(1), Some(0.67)), "40 of 60: {tue}");

    let partial = left_running();
    let out = partial.json_at(MORNING, &["done", "--partial", "--at", "23:40"]);
    assert_eq!((out["actual_min"].as_u64(), out["remaining_min"].as_u64()), (Some(40), Some(20)), "{out}");
    assert_eq!(partial.last_ev("done")["t"], "2026-09-08T23:40:00-05:00");
    assert_eq!(partial.line("week/2026-W37.md", "t4"), "- [ ] 3 20m Claude Code drafts tests     @m2 ^t4");
}

/// **Every reader reads a stated end as the same end logged in time**: a twin
/// that stopped at 23:40 for real, then recorded an event at 06:20, holds the
/// same lines in another order — the stated end is appended AFTER the
/// morning's `event` — and both days' reviews, `tm now` and the tree agree.
#[test]
fn a_stated_end_reads_as_the_same_end_logged_in_time() {
    let late = left_running();
    late.ok_at("2026-09-09T06:20:00-05:00", &["event", "delivered"]);
    late.ok_at(MORNING, &["stop", "--at", "23:40"]);
    let evs = late.events();
    assert_eq!(&evs[evs.len() - 2..], ["event", "stop"], "the stop follows the event in the file");

    let twin = left_running();
    twin.ok_at("2026-09-08T23:40:00-05:00", &["stop"]);
    twin.ok_at("2026-09-09T06:20:00-05:00", &["event", "delivered"]);
    let tevs = twin.events();
    assert_eq!(&tevs[tevs.len() - 2..], ["stop", "event"]);

    let mut a = late.log();
    let mut b = twin.log();
    let key = |v: &Value| v.to_string();
    a.sort_by_key(key);
    b.sort_by_key(key);
    assert_eq!(a, b, "the same lines, in another order");
    for date in ["2026-09-08", "2026-09-09"] {
        assert_eq!(review(&late, date), review(&twin, date), "{date}'s review");
    }
    assert_eq!(late.json_at(AFTER, &["now"])["active"], Value::Null);
    assert_eq!(late.read("week/2026-W37.md"), twin.read("week/2026-W37.md"));
}

/// **An end the block did not run through is refused by name and writes
/// nothing**: before its start (`--at 22:30`), a time still to come today
/// (`--at 07:30` at 07:05 names YESTERDAY's 07:30, before the start), a
/// malformed clock, and `--at` on a retro done.
#[test]
fn an_end_outside_the_block_is_refused_and_writes_nothing() {
    let tm = left_running();
    tm.ok_at(MORNING, &["now"]);
    let before = files(&tm.plan);
    let refuse = |args: &[&str], says: &str| {
        let out = tm.run_at(MORNING, args);
        assert_eq!(out.code, 1, "{args:?}: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains(says), "{args:?}: {}", out.stderr);
        assert_eq!(files(&tm.plan), before, "{args:?} wrote nothing");
    };
    refuse(
        &["stop", "--at", "22:30"],
        "`--at 22:30` names 2026-09-08 22:30, the latest 22:30 at or before now, which is before ^t4 began (2026-09-08 23:00)",
    );
    refuse(&["done", "--at", "07:30"], "names 2026-09-08 07:30");
    refuse(&["done", "--partial", "--at", "07:30"], "before ^t4 began");
    refuse(&["stop", "--at", "7:30"], "invalid time");
    refuse(&["done", "^t1", "--at", "23:30"], "^t1 is not running");
    assert_eq!(tm.state()["active"]["id"], "t4", "still running");
}

/// **D61's marks run at the stated end**: a call inside the block (23:10–23:20)
/// pauses it, a standup after the end (06:30–06:45) is not the block's — and a
/// refused `tm wake` first, D79's own flow, writes no mark.
#[test]
fn a_wall_inside_the_block_pauses_it_and_one_after_its_end_does_not() {
    let world = || {
        let tm = left_running();
        walls(
            &tm,
            &[
                "- [ ] 3 Late call          at:2026-09-08T23:10/23:20 ^g8",
                "- [ ] 3 Standup            at:2026-09-09T06:30/06:45 ^g9",
            ],
        );
        tm
    };
    for wake_first in [false, true] {
        let tm = world();
        if wake_first {
            let out = tm.run_at("2026-09-09T07:00:00-05:00", &["wake", "06:55"]);
            assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
            assert!(out.stderr.contains("with `--at HH:MM` for when it ended"), "{}", out.stderr);
            assert_eq!(tm.last()["ev"], "start", "the refused wake logged no mark");
        }
        let out = tm.ok_at(MORNING, &["stop", "--at", "23:40"]);
        assert_eq!(out.stdout.trim(), "stopped ^t4 after 30m · 30m left · ended 2026-09-08 23:40");
        assert!(out.stderr.contains("paused ^t4 for Late call 23:10–23:20"), "{}", out.stderr);
        assert!(!out.stderr.contains("Standup"), "{}", out.stderr);
        let tail: Vec<(String, String)> = tm.log()[tm.log().len() - 3..]
            .iter()
            .map(|e| (e["ev"].as_str().unwrap_or_default().into(), e["t"].as_str().unwrap_or_default().into()))
            .collect();
        assert_eq!(
            tail,
            [
                ("pause".into(), "2026-09-08T23:10:00-05:00".into()),
                ("unpause".into(), "2026-09-08T23:20:00-05:00".into()),
                ("stop".into(), "2026-09-08T23:40:00-05:00".into()),
            ],
            "wake first: {wake_first}"
        );
        assert_eq!(review(&tm, "2026-09-08")["block_min"].as_u64(), Some(30));
    }
}

/// **An end before a mark the log already holds is refused**: `tm now` at
/// 07:00 logged the standup's pause and unpause into the running block (D61,
/// its housekeeping at `now`), so by the log's account the block ran until
/// 06:30 — `--at 23:40` is refused, naming the mark, and nothing is written;
/// an end after the marks is taken. README gap 4002 is this residue.
#[test]
fn an_end_before_a_logged_mark_is_refused() {
    let tm = left_running();
    walls(&tm, &["- [ ] 3 Standup            at:2026-09-09T06:30/06:45 ^g9"]);
    tm.ok_at("2026-09-09T07:00:00-05:00", &["now"]);
    let before = files(&tm.plan);
    let out = tm.run_at(MORNING, &["stop", "--at", "23:40"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("the log already holds `pause` for ^t4 at 06:30, after the end you gave (2026-09-08 23:40)"),
        "{}",
        out.stderr
    );
    assert_eq!(files(&tm.plan), before, "nothing written");
    let out = tm.ok_at(MORNING, &["stop", "--at", "06:50"]);
    assert_eq!(
        out.stdout.trim(),
        "stopped ^t4 after 455m · 5m left · ended 06:50",
        "23:00–06:50 less the standup's quarter hour; an end today carries no date"
    );
}

/// **A running break and a stated end**: a break begun BEFORE the end is over
/// at the end (logged at its start, with the minutes to the end) and none of
/// it is worked; one begun AFTER the end paused the block after it, by the
/// cache's account, and is refused by name.
#[test]
fn a_running_break_ends_at_the_stated_end_or_refuses_it() {
    let tm = left_running();
    tm.ok_at("2026-09-08T23:20:00-05:00", &["break", "20m"]);
    let out = tm.json_at(MORNING, &["stop", "--at", "23:40"]);
    assert_eq!(out["worked_min"].as_u64(), Some(20), "23:00–23:20, then the break: {out}");
    let evs = tm.log();
    let brk = &evs[evs.len() - 2];
    assert_eq!((brk["ev"].as_str(), brk["t"].as_str()), (Some("break"), Some("2026-09-08T23:20:00-05:00")), "{brk}");
    assert_eq!(brk["actual_min"].as_u64(), Some(20), "the break ended with the block: {brk}");
    assert!(tm.state()["break"].is_null(), "{}", tm.state());

    let late = left_running();
    late.ok_at("2026-09-08T23:50:00-05:00", &["break", "20m"]);
    let out = late.run_at(MORNING, &["stop", "--at", "23:40"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("a break has been running since 2026-09-08 23:50, after the end you gave (2026-09-08 23:40)"),
        "{}",
        out.stderr
    );
    assert_eq!(late.state()["active"]["id"], "t4", "still running");
}

/// **The start is the log's, the cache's deletion changes nothing, and `tm
/// undo` takes the stated end back** — the block runs again from 23:00.
#[test]
fn a_stated_end_reads_the_log_and_is_undone_like_any_stop() {
    let tm = left_running();
    let twin = left_running();
    fs::remove_file(tm.plan.join(".tm/state.json")).expect("delete the cache");
    tm.ok_at(MORNING, &["stop", "--at", "23:40"]);
    twin.ok_at(MORNING, &["stop", "--at", "23:40"]);
    assert_eq!(tm.last(), twin.last());
    assert_eq!(review(&tm, "2026-09-08"), review(&twin, "2026-09-08"));

    twin.ok_at(AFTER, &["undo"]);
    assert_eq!(twin.last()["ev"], "undo", "{}", twin.last());
    let now = twin.json_at("2026-09-09T07:07:00-05:00", &["now"]);
    assert_eq!(now["active"]["id"], "t4", "running again: {now}");
    assert_eq!(review(&twin, "2026-09-08")["block_min"].as_u64(), Some(0), "the stop is cancelled");
}

/// **A routine done at a stated end is the instance of the day it ended** — the
/// `routine` line §10.1 logs for a stateless item carries the instance of the
/// end's own day and moment (Tuesday's `dinner`), stamped at it, never the one
/// a done typed Wednesday morning would name.
#[test]
fn a_routine_done_at_a_stated_end_is_that_days_instance() {
    let tm = Tm::new();
    tm.ok_at(WAKE, &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-08T21:30:00-05:00", &["start", "dinner", "--energy", "3"]);
    tm.ok_at(MORNING, &["done", "--at", "22:00"]);
    let last = tm.last();
    assert_eq!(
        (last["ev"].as_str(), last["item"].as_str(), last["inst"].as_str(), last["t"].as_str()),
        (Some("routine"), Some("dinner"), Some("2026-09-08"), Some("2026-09-08T22:00:00-05:00")),
        "{last}"
    );
    assert_eq!(last["actual_min"].as_u64(), Some(30), "{last}");
}

/// **An on-event item done at a stated end waits from the day it ended** —
/// §5.1's `waiting:<date>` is the end's date, as the `done` line's stamp is.
#[test]
fn an_on_event_item_done_at_a_stated_end_waits_from_that_day() {
    let tm = Tm::new();
    tm.ok_at(WAKE, &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-08T22:50:00-05:00", &["event", "reply", "^a4"]);
    tm.ok_at(START, &["start", "^a4", "--energy", "3"]);
    tm.ok_at(MORNING, &["done", "--at", "23:40"]);
    assert_eq!(
        tm.line("backlog.md", "a4"),
        "- [?] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d waiting:2026-09-08 ^a4"
    );
}
