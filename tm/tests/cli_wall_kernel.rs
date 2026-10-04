//! **D61 decided by the kernel** (stage 6 W-37 track T, README gap 3139) and
//! **`tm pause` inside a meeting names it** (the campaign's D66 call on gap
//! 3048).
//!
//! Until W-37 the host decided which `pause`/`unpause` a calendar wall writes,
//! over its own reader of the calendar (`Ctx::walls_on`) — a second reader of
//! the walls beside the kernel's `Look.wallsOn`. Now one request carries the
//! tree, the zone, the log section and the running break, and the kernel
//! answers the lines to append (`WallTimer.writes`), rendered by its one writer.
//! These tests drive what only the new path can: the running break crossing the
//! wire, a refused tree writing nothing, and the meeting named when a press of
//! `tm pause` resumes the timer it stopped.

mod cli_common;

use cli_common::Tm;

/// `(ev, t)` of every `pause`/`unpause` entry, in file order.
fn timer_marks(tm: &Tm) -> Vec<(String, String)> {
    tm.log()
        .iter()
        .filter(|e| e["ev"] == "pause" || e["ev"] == "unpause")
        .map(|e| (e["ev"].as_str().unwrap_or_default().to_string(), e["t"].as_str().unwrap_or_default().to_string()))
        .collect()
}

/// A day with `^t4` started at 12:00, fifty minutes before `^g1`'s 12:50–13:50.
fn running_before_the_meeting() -> Tm {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T12:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm
}

/// **The running break crosses the wire** (`emit.walls.break`): a break
/// begun at 12:40 and still running when the meeting starts has the timer
/// stopped already, so the wall writes nothing — the one input the log cannot
/// give the kernel (a break is logged when it ends).
#[test]
fn a_break_running_at_the_walls_start_leaves_the_wall_nothing_to_stop() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:40:00-05:00", &["break"]);
    let during = tm.ok_at("2026-09-07T13:20:00-05:00", &["now"]);
    assert!(timer_marks(&tm).is_empty(), "the break had stopped the timer: {:?}", timer_marks(&tm));
    assert!(!during.stderr.contains("paused ^t4 for"), "nothing was paused: {:?}", during.stderr);
}

/// **A break that covered the wall's start and ENDED inside the meeting is not the user's stop**
/// (the W-44 repair, README gap 4550, parity P98): once the break is logged, the wall writes its
/// pause at its start and its unpause at its end, so the clock does not restart inside the meeting
/// at the break's end. DRIVEN on the shipped binary before the repair — `start` 12:00, a break
/// 12:40-13:10 across the 12:50-13:50 meeting, `tm stop` at 14:05 — `after 95m`: the meeting's last
/// forty minutes counted as work, where D61 stops the clock for them. Now 40 before the break and the
/// minutes after the meeting: one number on `tm done` and `tm review day`.
#[test]
fn a_break_ended_inside_the_meeting_leaves_the_meeting_paused() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:40:00-05:00", &["break", "30m"]);
    tm.ok_at("2026-09-07T13:10:00-05:00", &["break"]);
    tm.ok_at("2026-09-07T13:20:00-05:00", &["now"]);
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), "2026-09-07T12:50:00-05:00".to_string())],
        "the meeting's pause, at its start, once the break is logged"
    );
    let during = tm.json_at("2026-09-07T13:30:00-05:00", &["now"]);
    assert_eq!(during["active"]["elapsed_min"], 40, "{during}");
    tm.ok_at("2026-09-07T14:10:00-05:00", &["now"]);
    assert_eq!(
        timer_marks(&tm),
        vec![
            ("pause".to_string(), "2026-09-07T12:50:00-05:00".to_string()),
            ("unpause".to_string(), "2026-09-07T13:50:00-05:00".to_string()),
        ]
    );
    tm.ok_at("2026-09-07T14:20:00-05:00", &["done"]);
    assert_eq!(tm.last_ev("done")["actual_min"], 70, "forty before the break, thirty after the meeting");
}

/// **One answer for both spellings of one break** (README gap 4550): the same break hand-logged
/// with `actual_min` and without it (D95: its planned minutes are its span) writes the same marks
/// and the same minutes. Until the repair the wall rule read the first as a span covering the
/// meeting's start (no pause) and the second as no span at all (a pause): driven, `tm stop` 95
/// beside 55.
#[test]
fn a_planned_only_break_and_its_logged_twin_write_the_same_marks() {
    let mut seen = Vec::new();
    for line in [
        r#"{"t":"2026-09-07T12:40:00-05:00","ev":"break","planned_min":30}"#,
        r#"{"t":"2026-09-07T12:40:00-05:00","ev":"break","planned_min":30,"actual_min":30}"#,
    ] {
        let tm = running_before_the_meeting();
        let log = tm.plan.join(".tm/log.jsonl");
        let mut text = std::fs::read_to_string(&log).expect("log");
        text.push_str(line);
        text.push('\n');
        std::fs::write(&log, text).expect("hand-edited break");
        tm.ok_at("2026-09-07T14:00:00-05:00", &["now"]);
        let out = tm.ok_at("2026-09-07T14:05:00-05:00", &["stop"]);
        let review = tm.json_at("2026-09-07T14:06:00-05:00", &["review", "day"]);
        seen.push((timer_marks(&tm), out.stdout.clone(), review["review"]["block_min"].clone()));
    }
    assert_eq!(seen[0], seen[1], "one break, one reading");
    assert!(seen[0].1.contains("after 55m"), "{}", seen[0].1);
    assert_eq!(seen[0].2, 55);
}

/// **A tree the kernel will not load writes nothing**: the walls cannot be
/// read, so no mark is appended (the automatic close's rule), and the refusal
/// is said by name.
#[test]
fn a_tree_the_kernel_refuses_writes_no_wall_mark() {
    let tm = running_before_the_meeting();
    // Two lines with one id: the kernel refuses the whole tree (`dupId`).
    let path = tm.plan.join("backlog.md");
    let text = std::fs::read_to_string(&path).expect("backlog");
    std::fs::write(&path, format!("{text}- [ ] 2 30m A twin of the drafts ^t4\n")).expect("write");
    let out = tm.run_at("2026-09-07T13:20:00-05:00", &["now"]);
    assert!(timer_marks(&tm).is_empty(), "nothing is written over a refused tree: {:?}", timer_marks(&tm));
    assert!(out.stderr.contains("meeting pause (D61) was not checked"), "the refusal is said: {:?}", out.stderr);
}

/// **`tm pause` inside the meeting resumes the timer and NAMES the meeting**
/// (D66, gap 3048): the housekeeping of the press logs the wall's pause, the
/// press lifts it — the correction for a meeting the user skipped — and says
/// which meeting had stopped it, in text and in `--json`.
#[test]
fn tm_pause_inside_the_meeting_resumes_and_names_it() {
    let tm = running_before_the_meeting();
    let out = tm.ok_at("2026-09-07T13:20:00-05:00", &["pause"]);
    assert!(
        out.stdout.contains("resumed ^t4 (it was paused for Meeting w/ host 12:50–13:50)"),
        "the meeting is named: {:?}",
        out.stdout
    );
    assert_eq!(
        timer_marks(&tm),
        vec![
            ("pause".to_string(), "2026-09-07T12:50:00-05:00".to_string()),
            ("unpause".to_string(), "2026-09-07T13:20:00-05:00".to_string()),
        ],
        "the wall's pause, then the user's unpause"
    );
    // A second press pauses, and names nothing: there is no meeting to name a pause for.
    let again = tm.json_at("2026-09-07T13:25:00-05:00", &["pause"]);
    assert_eq!(again["paused"], true, "{again}");
    assert!(again.get("meeting").is_none(), "{again}");
}

/// **…in `--json` too**: the meeting's walls and span beside `paused: false`.
#[test]
fn tm_pause_json_inside_the_meeting_carries_the_meeting() {
    let tm = running_before_the_meeting();
    let out = tm.json_at("2026-09-07T13:20:00-05:00", &["pause"]);
    assert_eq!(out["paused"], false, "{out}");
    assert_eq!(out["meeting"]["walls"], serde_json::json!(["g1"]), "{out}");
    assert_eq!(out["meeting"]["from"], "12:50", "{out}");
    assert_eq!(out["meeting"]["to"], "13:50", "{out}");
}

/// **A press outside any meeting says what it always said.**
#[test]
fn tm_pause_outside_a_meeting_names_nothing() {
    let tm = running_before_the_meeting();
    let paused = tm.ok_at("2026-09-07T12:10:00-05:00", &["pause"]);
    assert!(paused.stdout.contains("paused ^t4"), "{:?}", paused.stdout);
    let resumed = tm.ok_at("2026-09-07T12:20:00-05:00", &["pause"]);
    assert!(resumed.stdout.contains("resumed ^t4"), "{:?}", resumed.stdout);
    assert!(!resumed.stdout.contains("it was paused for"), "{:?}", resumed.stdout);
}

/// **The host reads no wall to decide it** (README gap 3139): the function the
/// housekeeping calls asks the kernel and never names the host's wall reader —
/// read off the source, because the two paths are equal by design and no drive
/// can tell them apart.
///
/// **The readers are found by their SIGNATURE, not listed** (W-37 repair, README
/// gap 3338): until the repair this named three functions, one of which no
/// longer existed, so a new host wall reader under a fourth name would have
/// passed. Every `fn` of the host (`tm/src`) or `tm-core/src` whose return type
/// names `Wall` is a wall reader, and the body calls none of them — directly or
/// through a helper of `day.rs` it calls.
#[test]
fn the_host_asks_the_kernel_and_reads_no_wall() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut readers: Vec<String> = Vec::new();
    let mut stack = vec![root.join("src"), root.join("../tm-core/src")];
    while let Some(dir) = stack.pop() {
        for e in std::fs::read_dir(&dir).expect("a source directory").flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "rs") {
                let text = std::fs::read_to_string(&p).expect("a source file");
                for line in text.lines() {
                    let Some(at) = line.find("fn ") else { continue };
                    let sig = &line[at + 3..];
                    let Some(ret) = sig.find("->") else { continue };
                    let name: String = sig.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
                    if !name.is_empty() && sig[ret..].contains("Wall") {
                        readers.push(name);
                    }
                }
            }
        }
    }
    readers.sort();
    readers.dedup();
    assert!(readers.iter().any(|r| r == "walls_on"), "the scan finds the host's own reader: {readers:?}");
    let src = std::fs::read_to_string(root.join("src/cli/day.rs")).expect("day.rs");
    let start = src.find("pub(crate) fn stop_the_timer_at_walls").expect("the housekeeping function");
    let end = src[start..].find("\n}\n").map(|e| start + e).expect("its end");
    let body = &src[start..end];
    assert!(body.contains("ask_the_walls"), "it asks the kernel");
    let helper = src.find("fn ask_the_walls").map(|a| &src[a..a + src[a..].find("\n}\n").unwrap_or(0)]).expect("the request builder");
    for reader in &readers {
        for (what, text) in [("the housekeeping", body), ("its request builder", helper)] {
            assert!(
                !text.contains(&format!("{reader}(")),
                "{what} reads the host's walls through `{reader}` (a fn whose return type names Wall)"
            );
        }
    }
}

/// **A block begun the evening before is paused by today's wall** (README gap
/// 3241): the kernel reads the block's start as an instant off the replay, where
/// W-36's host read `state.json`'s `HH:MM` as today's clock time — 23:00 TODAY,
/// later than every wall of the day — and never paused it. And it is paused
/// ONCE: the verbs after it write nothing more.
#[test]
fn a_block_begun_the_evening_before_is_paused_by_todays_wall_once() {
    let tm = Tm::new();
    tm.ok_at("2026-09-06T18:05:00-05:00", &["wake", "18:05", "--slept", "8h"]);
    tm.ok_at("2026-09-06T23:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    let during = tm.ok_at("2026-09-07T13:20:00-05:00", &["now"]);
    assert!(
        during.stderr.contains("paused ^t4 for Meeting w/ host 12:50–13:50"),
        "the overnight block is paused and it is said: {:?}",
        during.stderr
    );
    let after = tm.ok_at("2026-09-07T14:10:00-05:00", &["now"]);
    assert!(!after.stderr.contains("paused ^t4 for"), "said once: {:?}", after.stderr);
    assert_eq!(
        timer_marks(&tm),
        vec![
            ("pause".to_string(), "2026-09-07T12:50:00-05:00".to_string()),
            ("unpause".to_string(), "2026-09-07T13:50:00-05:00".to_string()),
        ],
        "one pause and one unpause"
    );
}

/// **A day with no wake of its own logs the wall's pause once** (README gap
/// 3245). The last wake was 18:05 the day before, within 24 hours, so the
/// replay files the day's entries — the pause included — under that day
/// (`Replay.dayOf`). Reading today's record alone the rule found no pause and
/// wrote it again on every verb (W-36's host wrote it three times over these
/// three verbs); the kernel reads the day before's marks stamped at or after the
/// block's start as well.
#[test]
fn a_day_without_its_own_wake_logs_the_walls_pause_once() {
    let tm = Tm::new();
    tm.ok_at("2026-09-06T18:05:00-05:00", &["wake", "18:05", "--slept", "8h"]);
    tm.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    let mut said = 0;
    for at in ["2026-09-07T13:20:00-05:00", "2026-09-07T13:30:00-05:00", "2026-09-07T14:10:00-05:00"] {
        let out = tm.ok_at(at, &["now"]);
        said += out.stderr.matches("paused ^t4 for").count();
    }
    assert_eq!(said, 1, "the pause is said once");
    assert_eq!(
        timer_marks(&tm),
        vec![
            ("pause".to_string(), "2026-09-07T12:50:00-05:00".to_string()),
            ("unpause".to_string(), "2026-09-07T13:50:00-05:00".to_string()),
        ],
        "one pause and one unpause"
    );
}
