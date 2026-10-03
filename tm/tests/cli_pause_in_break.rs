//! **No clock mark is logged inside a running break** — the W-43 repair's campaign calls on README
//! gap 4501 (parity **P89** and **P90**), D71's and D90's rules reached by the two verbs they did not
//! reach.
//!
//! D90 (README gap 4340, parity P86) made `tm interrupt` end a running break first, on the premise
//! that it was the one verb that stopped the block's clock inside a running break. **It was not.**
//! A running break holds `active.paused`, so `tm pause` pressed inside it logged `unpause`
//! ("resumed") and a second press `pause` — stamped inside the break, whose own `break` line is
//! written at its END. The kernel's replay closes the stretch at that `pause` before it meets the
//! break, and credits the break's head; the host's union of idle spans does not. Driven at
//! `72234b4`: `tm stop` said 10m beside `tm review day`'s 20.
//!
//! * **`tm pause` inside a running break is REFUSED BY NAME (P89)**, D71's sentence with the break
//!   in the interruption's place: the break has already stopped the timer, and `tm break` ends it.
//! * **`tm resume` inside a running break ends the break FIRST (P90)**, as `tm start` and (D90)
//!   `tm interrupt` do: a break begun inside an interruption was still running when the fork's
//!   resume un-paused the block under it, so `tm now` drew `▶ … running` on a break and its header
//!   (12m with the break netted, the host's) read beside a row the kernel's replay credited on.
//!
//! Every test reads what a user reads: the exit code, the words, every file of the tree (the derived
//! replay cache aside, D13), `tm stop`'s minutes and `tm review day`'s, and `tm --json now` — after
//! deleting `.tm/state.json` too (D42) wherever no break is running, a running break being one of its
//! host-only fields.

mod cli_common;

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use cli_common::Tm;
use serde_json::Value;

const WAKE: &str = "2026-09-07T07:00:00-05:00";
const START: &str = "2026-09-07T09:00:00-05:00";
const BREAK_ON: &str = "2026-09-07T09:10:00-05:00";
const PRESS_1: &str = "2026-09-07T09:15:00-05:00";
const PRESS_2: &str = "2026-09-07T09:20:00-05:00";
const BREAK_OFF: &str = "2026-09-07T09:30:00-05:00";
const STOP: &str = "2026-09-07T10:00:00-05:00";
const AFTER: &str = "2026-09-07T10:01:00-05:00";

const REFUSAL: &str = "a break is running since 09:10 — the timer is already stopped; `tm break` ends it";

/// Every file under the plan directory by relative path, **except** `.tm/cache/` — derived and
/// rebuildable (D13). Bytes, not text.
fn snapshot(tm: &Tm) -> BTreeMap<String, Vec<u8>> {
    fn walk(root: &Path, dir: &Path, acc: &mut BTreeMap<String, Vec<u8>>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(root, &path, acc);
            } else if let Ok(bytes) = fs::read(&path) {
                let rel = path.strip_prefix(root).expect("under root").display().to_string();
                if rel.replace('\\', "/").starts_with(".tm/cache/") {
                    continue;
                }
                acc.insert(rel, bytes);
            }
        }
    }
    let mut acc = BTreeMap::new();
    walk(&tm.plan, &tm.plan, &mut acc);
    acc
}

/// The example tree, woken at 07:00, `^m1` running from 09:00 — held by a typed `tm pause` at 09:05
/// when `held` (P84's world) — and a twenty-minute break from 09:10.
fn a_break_running(held: bool) -> Tm {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(START, &["start", "^m1", "--energy", "3"]);
    if held {
        tm.ok_at("2026-09-07T09:05:00-05:00", &["pause"]);
    }
    tm.ok_at(BREAK_ON, &["break", "20m"]);
    assert!(!tm.state()["break"].is_null(), "the break is running: {}", tm.state());
    tm
}

/// `tm review day --json`'s block minutes at `at`.
fn review_block_min(tm: &Tm, at: &str) -> u64 {
    let v = tm.json_at(at, &["review", "day"]);
    let r = if v.get("review").is_some() { &v["review"] } else { &v };
    r["block_min"].as_u64().unwrap_or_else(|| panic!("no block_min: {v}"))
}

/// The minutes `tm stop` said, read off "stopped ^m1 after 40m · …".
fn stopped_after(said: &str) -> u64 {
    let at = said.find("after ").unwrap_or_else(|| panic!("{said}")) + "after ".len();
    said[at..].split('m').next().and_then(|n| n.parse().ok()).unwrap_or_else(|| panic!("{said}"))
}

/// **The drive, pinned, in both worlds** (a running block, and one a typed pause held before the
/// break, P84): `tm pause` inside the break exits 1 with the words, writes nothing — not the log,
/// not `.tm/state.json`, not the day file's journal, not the undo stack — twice in a row, and `tm
/// --json now` still reads the block paused with the minutes before the break.
#[test]
fn pause_inside_a_running_break_is_refused_by_name_and_writes_nothing() {
    for held in [false, true] {
        let tm = a_break_running(held);
        let before = snapshot(&tm);
        for at in [PRESS_1, PRESS_2] {
            let out = tm.run_at(at, &["pause"]);
            assert_eq!(out.code, 1, "held {held}: {}{}", out.stdout, out.stderr);
            assert!(out.stderr.contains(REFUSAL), "held {held}: the refusal is said: {:?}", out.stderr);
            assert_eq!(snapshot(&tm), before, "held {held}: a refusal writes nothing");
        }
        // A running break has no log line until it ends, so it is one of `.tm/state.json`'s
        // host-only fields (D42) and the cache is not deleted here.
        let now = tm.json_at("2026-09-07T09:25:00-05:00", &["now"]);
        assert_eq!((now["active"]["id"].as_str(), now["active"]["paused"].as_bool()), (Some("m1"), Some(true)), "{now}");
        assert_eq!(now["active"]["elapsed_min"], if held { 5 } else { 10 }, "{now}");
    }
}

/// **`--json` carries the same refusal** as §13's failure document — one JSON document on stderr,
/// nothing on stdout — exit code 1, and still writes nothing.
#[test]
fn the_json_refusal_is_the_failure_document() {
    let tm = a_break_running(false);
    let before = snapshot(&tm);
    let out = tm.run_at(PRESS_1, &["--json", "pause"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.is_empty(), "{:?}", out.stdout);
    let doc: Value = serde_json::from_str(&out.stderr)
        .unwrap_or_else(|e| panic!("stderr is not one JSON document ({e}): {:?}", out.stderr));
    assert_eq!((doc["ok"].as_bool(), doc["exit_code"].as_u64()), (Some(false), Some(1)), "{doc}");
    assert_eq!(doc["message"], REFUSAL, "{doc}");
    assert_eq!(snapshot(&tm), before);
}

/// **The auditor's day, one count** (README gap 4501): `^m1` from 09:00, a break from 09:10, two
/// presses of `tm pause` inside it (refused), the break ended at 09:30, `tm stop` at 10:00. The block
/// worked 09:00-09:10 and 09:30-10:00 — forty minutes — and `tm stop` and `tm review day` both say
/// so, with the replay cache and without it. At `72234b4` the presses logged `unpause` 09:15 and
/// `pause` 09:20 inside the break: `tm stop` said 10, `tm review day` 20.
#[test]
fn the_presses_inside_a_break_leave_one_count() {
    let tm = a_break_running(false);
    let _ = tm.run_at(PRESS_1, &["pause"]);
    let _ = tm.run_at(PRESS_2, &["pause"]);
    tm.ok_at(BREAK_OFF, &["break"]);
    let said = tm.ok_at(STOP, &["stop"]).stdout;
    assert_eq!(stopped_after(&said), 40, "{said}");
    assert_eq!(review_block_min(&tm, AFTER), 40, "tm review day reads tm stop's count");
    let _ = fs::remove_dir_all(tm.plan.join(".tm/cache"));
    assert_eq!(review_block_min(&tm, AFTER), 40, "and so does a cache-less replay");
    let evs = tm.events();
    assert!(!evs.iter().any(|e| e == "pause" || e == "unpause"), "nothing logged by the presses: {evs:?}");
}

/// **The auditor's second day** (its `q1f`): an interruption at 09:10, a thirty-minute break begun
/// inside it at 09:20, `tm resume` at 09:30 (which now ends the break first, P90), `tm pause` at 09:35
/// (the clock is the user's again: it pauses), the pause lifted at 09:45, `tm stop` at 10:00. Worked
/// 09:00-09:10, 09:30-09:35 and 09:45-10:00: thirty minutes, one count.
#[test]
fn a_break_inside_an_interruption_leaves_one_count() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(START, &["start", "^m1", "--energy", "3"]);
    tm.ok_at(BREAK_ON, &["interrupt"]);
    tm.ok_at(PRESS_2, &["break", "30m"]);
    tm.ok_at(BREAK_OFF, &["resume"]);
    let p = tm.ok_at("2026-09-07T09:35:00-05:00", &["pause"]).stdout;
    assert_eq!(p.trim(), "paused ^m1", "{p}");
    let u = tm.ok_at("2026-09-07T09:45:00-05:00", &["pause"]).stdout;
    assert_eq!(u.trim(), "resumed ^m1", "{u}");
    let said = tm.ok_at(STOP, &["stop"]).stdout;
    assert_eq!(stopped_after(&said), 30, "{said}");
    assert_eq!(review_block_min(&tm, AFTER), 30, "tm review day reads tm stop's count");
}

/// **`tm resume` ends a running break first (P90)**: the interruption at 09:10, a thirty-minute
/// break from 09:20, `tm resume` at 09:30. It says the break ended and the resume; the log holds the
/// break's line — ten minutes, stamped at its start — BEFORE the `resume` line; the journal has `tm
/// break`'s ending line then the resume's; `.tm/state.json` holds no break and the block running;
/// and at 09:32 `tm now`'s header and its row read one count — twelve minutes worked, 348 left —
/// with the cache and after deleting it.
#[test]
fn tm_resume_ends_a_running_break_first_and_tm_now_reads_one_count() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(START, &["start", "^m1", "--energy", "3"]);
    tm.ok_at(BREAK_ON, &["interrupt"]);
    tm.ok_at(PRESS_2, &["break", "30m"]);
    let said = tm.ok_at(BREAK_OFF, &["resume"]).stdout;
    assert_eq!(said.trim(), "break ended · 10m of 30m · resumed · lost 20m", "{said}");

    let log = tm.log();
    let at = log
        .iter()
        .rposition(|e| e["ev"] == "break")
        .unwrap_or_else(|| panic!("no break line: {log:?}"));
    assert_eq!((log[at]["t"].as_str(), log[at]["actual_min"].as_u64()), (Some(PRESS_2), Some(10)), "{}", log[at]);
    assert_eq!(log.get(at + 1).map(|e| e["ev"].clone()), Some(Value::from("resume")), "the break's line first: {log:?}");

    let j: Vec<String> = tm
        .read("day/2026-09-07.md")
        .lines()
        .skip_while(|l| *l != "## Log")
        .map(str::to_string)
        .collect();
    let b = j.iter().position(|l| l == "09:30 break ended 10m/30m").unwrap_or_else(|| panic!("{j:?}"));
    assert!(j.get(b + 1).is_some_and(|l| l.starts_with("09:30 resume lost=20m")), "{j:?}");

    let st = tm.state();
    assert!(st["break"].is_null() && st["interrupt"].is_null(), "{st}");
    assert_eq!(st["active"]["paused"], false, "{st}");

    let text = tm.ok_at("2026-09-07T09:32:00-05:00", &["now"]).stdout;
    assert!(text.lines().next().is_some_and(|l| l.contains("12m of 360m")), "{text}");
    assert!(text.contains("running · 348m left"), "the row reads the header's count: {text}");
    let with = tm.json_at("2026-09-07T09:32:00-05:00", &["now"]);
    assert_eq!(with["active"]["elapsed_min"], 12, "{with}");
    fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    let without = tm.json_at("2026-09-07T09:32:00-05:00", &["now"]);
    assert_eq!(with["active"], without["active"], "deleting the runtime state changes nothing (D42)");

    let said = tm.ok_at(STOP, &["stop"]).stdout;
    assert_eq!(stopped_after(&said), 40, "{said}");
    assert_eq!(review_block_min(&tm, AFTER), 40, "09:00-09:10 and 09:30-10:00");
}

/// **It does not over-bite** (AGENTS §5.8): after the break ends `tm pause` pauses and resumes the
/// block, logging each; with no break running `tm resume` says what it always said and carries no
/// `break_ended`; and with nothing running the old refusal stands.
#[test]
fn pause_and_resume_are_unchanged_without_a_running_break() {
    let tm = a_break_running(false);
    tm.ok_at(BREAK_OFF, &["break"]);
    let a = tm.ok_at("2026-09-07T09:35:00-05:00", &["pause"]);
    assert_eq!(a.stdout.trim(), "paused ^m1", "{}", a.stdout);
    assert_eq!(tm.last_ev("pause")["id"], "m1");
    let b = tm.ok_at("2026-09-07T09:40:00-05:00", &["pause"]);
    assert_eq!(b.stdout.trim(), "resumed ^m1", "{}", b.stdout);
    tm.ok_at("2026-09-07T09:45:00-05:00", &["interrupt"]);
    let r = tm.json_at("2026-09-07T09:50:00-05:00", &["resume"]);
    assert_eq!(r["action"], "resume", "{r}");
    assert!(r.get("break_ended").is_none(), "{r}");

    let tm = Tm::new();
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(BREAK_ON, &["break", "20m"]);
    let out = tm.run_at(PRESS_1, &["pause"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("nothing is running"), "{}", out.stderr);
}
