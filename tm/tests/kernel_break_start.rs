//! **The owner's D105 — a break's START is a line of the log, and the kernel reads it**
//! (README "Stage 6 — W-46 track K", gaps 1034, 1085 and 4740; parity **P100**).
//!
//! Until D105 a break had one line, the `break` appended when it ENDED, stamped at its start: a
//! break still running lived in `.tm/state.json` alone, so deleting that file mid-break lost it,
//! and the block it had paused came back running. `tm break` now logs a `break_start`
//! (`{"t": <start>, "ev": "break_start", "planned_min": .., "where": ..}`), the kernel's replay
//! holds the running break until a `break` line ends it (`Replay.Machine.brkOpen`), and the `log`
//! answer carries it as `open.break`, which the host decodes into
//! [`tm_core::log::Replay::open_break`] and D42's rebuild reads.
//!
//! What this file pins, each against the kernel through the FFI and the host's own decoder
//! (`kernel_log::decode_facts`, the function `Ctx::replay_with` calls — never a twin of it):
//!
//! * a `break_start` IS the running break: its start, planned minutes, place and day;
//! * the pair is matched in FILE ORDER: a `break` line ends whatever break is running, whatever its
//!   stamp; an undo of the start leaves none, an undo of the end brings it back;
//! * the kernel counts it as a known event (no `unknown`), where fork 4748911 counts one — P100;
//! * a malformed one is a named warning (`badField planned_min`), where the fork reads an entry;
//! * a log with no `break_start` — every corpus log, every log fork 4748911 ever wrote — has no
//!   running break, so the reader changes nothing about them.
//!
//! The D42 half — the binary rebuilding `.tm/state.json`'s `break` from the line — is
//! [`the_rebuild_restores_a_logged_break_and_its_pause`] and `cli_switch_acceptance.rs`'
//! running-break tests. And since the writer's commit — `tm break` logs the line — the start has
//! ONE reading in the host, the logged second over the cache's minute
//! ([`a_running_breaks_start_has_one_reading`], read off the code as a class).

#![allow(clippy::needless_raw_string_hashes)]

mod cli_common;

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

#[allow(dead_code)]
#[path = "../src/cli/kernel_log.rs"]
mod kernel_log;

#[allow(dead_code)]
#[path = "support/loggen.rs"]
mod loggen;

use std::fs;
use std::path::Path;

use chrono::NaiveDate;
use chrono_tz::Tz;
use serde_json::{json, Value};

use cli_common::Tm;

const TZ: Tz = chrono_tz::America::Chicago;

const WAKE: &str = r#"{"t":"2026-09-10T06:05:00-05:00","ev":"wake","slept_min":420}"#;
const START: &str = r#"{"t":"2026-09-10T08:00:00-05:00","ev":"start","id":"p1","pred":3,"loc":"lounge"}"#;
const BRK_START: &str = r#"{"t":"2026-09-10T09:00:00-05:00","ev":"break_start","planned_min":20,"where":"walk"}"#;
const BRK: &str = r#"{"t":"2026-09-10T09:00:00-05:00","ev":"break","planned_min":20,"actual_min":15,"where":"walk"}"#;

/// The kernel's `log` answer for `lines`, one genesis call, facts and every header asked.
fn answer(lines: &[&str]) -> Value {
    let req = json!({
        "docs": [], "now": "2026-09-15", "tz": tz_table::probe(TZ).to_wire(),
        "log": {"ckpt": null, "from": 1, "lines": lines, "terminated": true,
                "reseal": null, "want": {"facts": true, "headersFrom": 1}}
    });
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("the response is JSON");
    assert!(resp["ok"]["log"].is_object(), "no log answer: {}", &raw[..raw.len().min(400)]);
    resp["ok"]["log"].clone()
}

/// The host's decoding of that answer — `kernel_log::decode_facts`, the shipped decoder.
fn replay(lines: &[&str]) -> tm_core::log::Replay {
    kernel_log::decode_facts(&answer(lines), TZ).expect("the kernel's facts decode")
}

fn undo_of(tag: &str) -> String {
    format!(r#"{{"t":"2026-09-10T09:30:00-05:00","ev":"undo","of":"{tag}"}}"#)
}

#[test]
fn a_break_start_is_the_running_break_on_the_wire() {
    let a = answer(&[WAKE, START, BRK_START]);
    // The wire's own shape: `[start, planned, where?, day]` (`Seal.cOptOpenBrk`).
    let wire = &a["facts"]["open"]["break"];
    assert!(wire.is_array(), "no `open.break` on the wire: {}", a["facts"]["open"]);
    assert_eq!(wire.as_array().map(Vec::len), Some(4), "{wire}");

    let r = kernel_log::decode_facts(&a, TZ).expect("decode");
    let b = r.open_break.as_ref().expect("a running break");
    assert_eq!(b.started.to_rfc3339(), "2026-09-10T09:00:00-05:00");
    assert_eq!(b.planned_min, 20);
    assert_eq!(b.r#where.as_deref(), Some("walk"));
    assert_eq!(b.day, NaiveDate::from_ymd_opt(2026, 9, 10).expect("a date"));
    // P100: a known kind — the fork reads it as an unknown event and counts one.
    assert_eq!(r.unknown, 0, "the kernel counted a `break_start` as an unknown event");
    // It moves no clock: the open block is the one the same log without it gives.
    assert_eq!(r.open_block, replay(&[WAKE, START]).open_block, "a running break moved the block's clock");
}

#[test]
fn the_pair_is_matched_in_file_order_and_the_undo_mask_reads_both_lines() {
    assert!(replay(&[WAKE, START, BRK_START, BRK]).open_break.is_none(), "a `break` line did not end it");
    // Whatever the ending line's stamp: an hour before the start still ends it.
    let early = BRK.replace("09:00:00", "08:00:00");
    assert!(replay(&[WAKE, START, BRK_START, &early]).open_break.is_none(), "an earlier-stamped `break` did not end it");
    // `tm undo` of `tm break` cancels the start; of the verb that ended it, the end.
    assert!(replay(&[WAKE, START, BRK_START, &undo_of("break_start")]).open_break.is_none(), "an undone start still runs");
    let back = replay(&[WAKE, START, BRK_START, BRK, &undo_of("break")]);
    assert_eq!(
        back.open_break.as_ref().map(|b| (b.started.to_rfc3339(), b.planned_min)),
        Some(("2026-09-10T09:00:00-05:00".to_string(), 20)),
        "an undone end did not bring the break back"
    );
    // A second start before an end replaces the first.
    let second = BRK_START.replace("09:00:00", "09:10:00").replace("\"planned_min\":20", "\"planned_min\":10");
    assert_eq!(
        replay(&[WAKE, START, BRK_START, &second]).open_break.map(|b| b.planned_min),
        Some(10),
        "the later `break_start` is not the running break"
    );
}

#[test]
fn a_malformed_break_start_is_a_named_warning() {
    let bad = r#"{"t":"2026-09-10T09:00:00-05:00","ev":"break_start","planned_min":"x"}"#;
    let a = answer(&[WAKE, bad]);
    let warned: Vec<(u64, String, String)> = a["warnings"]
        .as_array()
        .expect("warnings")
        .iter()
        .map(|w| {
            (
                w["line"].as_u64().unwrap_or(0),
                w["w"].as_str().unwrap_or_default().to_string(),
                w["key"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect();
    assert_eq!(warned, vec![(2, "badField".to_string(), "planned_min".to_string())], "{}", a["warnings"]);
    assert!(kernel_log::decode_facts(&a, TZ).expect("decode").open_break.is_none());
}

#[test]
fn a_log_with_no_break_start_has_no_running_break() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/corpus/logs");
    let mut n = 0;
    for entry in fs::read_dir(&dir).expect("the corpus logs") {
        let path = entry.expect("an entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("jsonl") {
            continue;
        }
        let text = fs::read_to_string(&path).expect("a log");
        assert!(!text.contains("\"break_start\""), "{} holds a `break_start`", path.display());
        let lines: Vec<&str> = text.lines().collect();
        if lines.len() > 8_192 {
            continue;
        }
        let r = replay(&lines);
        assert!(r.open_break.is_none(), "{}: a running break out of a log with no `break_start`", path.display());
        n += 1;
    }
    assert_eq!(n, 4, "the corpus holds four logs, and each is read");
    // And a generated month, at both of the generator's rates: it writes `break` lines, in the
    // fork's shape, and never a `break_start`.
    for rate in [loggen::Rate::Forty, loggen::Rate::SixtyOne] {
        let lines = loggen::log(rate, 30);
        assert!(lines.iter().any(|l| l.contains("\"break\"")), "the generated month holds no `break`");
        assert!(!lines.iter().any(|l| l.contains("\"break_start\"")));
        let lines: Vec<&str> = lines.iter().map(String::as_str).collect();
        assert!(replay(&lines).open_break.is_none(), "a running break out of a generated month");
    }
}

/// One plan root holding `text`, and its bytes (`kernel_log_door.rs`' shape).
fn tree(text: &str) -> (tempfile::TempDir, Vec<u8>) {
    let dir = tempfile::tempdir().expect("a temp dir");
    fs::create_dir_all(dir.path().join(".tm")).expect("mkdir .tm");
    fs::write(dir.path().join(".tm/log.jsonl"), text).expect("write the log");
    let bytes = fs::read(dir.path().join(".tm/log.jsonl")).expect("read the log");
    (dir, bytes)
}

/// **A running break crosses a seal cut and survives the resume** (D105, step 3): a 200-day
/// generated log with a `break_start` three quarters of the way in and every `break` line after it
/// taken out, so nothing ends it — read through the door (`kernel_log::replay_scoped`, the one
/// `Ctx::replay_with` calls) at `Hot` and `All`, from genesis and then from the checkpoint the
/// first read wrote. The checkpoint FOLDS the `break_start`'s line (its cut is past it), so the
/// running break reaches the second read through the machine the checkpoint carries
/// (`Seal.cMachine`) and nothing else; and the ledger day never passes the break's day
/// (`Seal.machineDays`: the `break` line that ends it will be stamped at its start).
#[test]
fn a_running_break_crosses_a_seal_cut() {
    let lines = loggen::log(loggen::Rate::Forty, 200);
    let at = lines.len() * 3 / 4;
    let t = serde_json::from_str::<Value>(&lines[at]).expect("a generated line")["t"]
        .as_str()
        .expect("a stamp")
        .to_string();
    let brk = format!(r#"{{"t":"{t}","ev":"break_start","planned_min":20,"where":"walk"}}"#);
    let mut log: Vec<String> = lines[..at].to_vec();
    log.push(brk);
    log.extend(lines[at..].iter().filter(|l| !l.contains("\"ev\":\"break\"")).cloned());
    let text = loggen::text(&log);
    let (dir, bytes) = tree(&text);
    let last = log.iter().rev().find_map(|l| serde_json::from_str::<Value>(l).ok()?["t"].as_str().map(str::to_string)).expect("a dated line");
    let today = chrono::DateTime::parse_from_rfc3339(&last).expect("a stamp").with_timezone(&TZ).date_naive() + chrono::Duration::days(1);
    let started = chrono::DateTime::parse_from_rfc3339(&t).expect("the break's stamp");
    let wire = tz_table::wire_for(Some(&dir.path().join(kernel_log::CACHE_DIR)), TZ);

    let mut reads = 0;
    for pass in ["genesis", "from the checkpoint"] {
        for scope in [kernel_log::Scope::Hot, kernel_log::Scope::All] {
            let read = kernel_log::replay_scoped(dir.path(), &bytes, TZ, &wire, today, scope, None)
                .unwrap_or_else(|e| panic!("{pass}: the door answers: {e:?}"));
            let b = read.replay.open_break.as_ref().unwrap_or_else(|| panic!("{pass}, {scope:?}: no running break"));
            assert_eq!(b.started, started, "{pass}, {scope:?}");
            assert_eq!((b.planned_min, b.r#where.as_deref()), (20, Some("walk")), "{pass}, {scope:?}");
            let day = kernel_log::day_of(b.day);
            let ledger = read.ledger_day.unwrap_or_else(|| panic!("{pass}, {scope:?}: nothing was sealed, so no cut was crossed"));
            assert!(ledger <= day, "{pass}, {scope:?}: the ledger day {ledger} passed the running break's day {day}");
            reads += 1;
        }
    }
    // Not vacuous: the checkpoint FOLDED the `break_start` — its cut is past the line — so the
    // second pass met the running break in the checkpoint's machine, not in the tail it replayed.
    let ckpt = fs::read_to_string(dir.path().join(kernel_log::CACHE_DIR).join(kernel_log::CKPT_FILE)).expect("a checkpoint");
    let snap = kernel_log::Snapshot::from_text(&ckpt).expect("the checkpoint reads");
    assert!(
        snap.meta.cut > at as u64,
        "the checkpoint's cut {} did not pass the `break_start` at line {}",
        snap.meta.cut,
        at + 1
    );
    assert_eq!(reads, 4);
    eprintln!(
        "a running break across a seal cut: `break_start` at line {} of {}, the checkpoint's cut {}, its ledger day {} \
         (the break's day {}), 4 reads agreeing",
        at + 1,
        log.len(),
        snap.meta.cut,
        kernel_log::date_of(snap.meta.ledger_day),
        started.with_timezone(&TZ).date_naive()
    );
}

/// **D42's rebuild reads the line** — the reader's half of `cli_switch_acceptance.rs`'
/// running-break tests. The `break_start` is appended by hand here, exactly as D105's `tm break`
/// writes it, so this pins the rebuild whoever wrote the line: deleting `.tm/state.json` gives
/// back the break `tm break` started (its start, planned minutes and place) and the pause it set,
/// and the notice says the break was RESTORED.
#[test]
fn the_rebuild_restores_a_logged_break_and_its_pause() {
    const AT: &str = "2026-09-07T10:00:00-05:00";
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at("2026-09-07T07:00:00-05:00", &["wake", "07:00"]);
    tm.ok_at("2026-09-07T09:00:00-05:00", &["start", "^m1", "--energy", "3"]);
    tm.ok_at(AT, &["break", "20m", "--where", "walk"]);
    let log = tm.plan.join(".tm/log.jsonl");
    let text = fs::read_to_string(&log).expect("the log");
    if !text.contains("\"break_start\"") {
        fs::write(&log, format!("{text}{{\"t\":\"{AT}\",\"ev\":\"break_start\",\"planned_min\":20,\"where\":\"walk\"}}\n"))
            .expect("append the line D105's `tm break` writes");
    }
    let before = tm.state();
    assert_eq!(before["active"]["paused"], true, "{before}");
    assert_eq!(before["break"]["started"], "10:00", "{before}");

    fs::remove_file(tm.plan.join(".tm/state.json")).expect("delete the runtime state");
    let out = tm.run_at("2026-09-07T10:05:00-05:00", &["--json", "now"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("RESTORED from the log: `break`"), "the rebuild did not say the break came back: {}", out.stderr);
    assert!(!out.stderr.contains("GONE"), "the rebuild said something was gone: {}", out.stderr);
    let after = tm.state();
    assert_eq!(after["break"], before["break"], "the break did not come back as `tm break` cached it");
    assert_eq!(after["active"]["paused"], true, "the pause the break set did not come back: {after}");
    assert_eq!(after["active"]["id"], before["active"]["id"]);
}

/// **The lines of a Rust file that are not a `#[cfg(test)]` item** — a column-zero
/// `#[cfg(test)]` gates the item after it (and any attributes between), which runs to the next
/// column-zero `}` (rustfmt's shape for a top-level item's close), or is that one line when it
/// ends in `;` or opens and closes its braces on it. Test code calls `BreakState::started_at`
/// on purpose, to pin it; the class below is the binary's readers.
fn non_test_lines(text: &str) -> Vec<&str> {
    let (mut out, mut pending, mut skip) = (Vec::new(), false, false);
    for line in text.lines() {
        if skip {
            skip = line != "}";
            continue;
        }
        if line == "#[cfg(test)]" {
            pending = true;
            continue;
        }
        if pending {
            if line.starts_with("#[") {
                continue;
            }
            pending = false;
            let opens = line.matches('{').count();
            let one_line = line.ends_with(';') || (opens > 0 && opens == line.matches('}').count());
            skip = !one_line;
            continue;
        }
        out.push(line);
    }
    out
}

/// Every `.rs` file under `dir`, recursively, in path order.
fn rust_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    let mut entries: Vec<_> = fs::read_dir(dir).expect("a source directory").map(|e| e.expect("an entry").path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            rust_files(&p, out);
        } else if p.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(p);
        }
    }
}

/// **A running break's start has ONE reading** (the owner's D105, parity P100; AGENTS §5.3) —
/// read off the code as a CLASS, never as a list of the readers somebody remembered. The cache
/// stores the start as `HH:MM` and a `break_start` line to the second, so a reader left on the
/// cache's clock would disagree with one on the log's by the start's seconds: before D105 every
/// reader read the cache, and the writer's commit moved the CLI to the log. So: the only call to
/// the cache's reading (`BreakState::started_at`) in `tm/src` and `tm-core/src` is the logged
/// reading's own fallback (`BreakState::started_at_logged`), and the logged reading is called by
/// the three readers there are — `Ctx::running_break` (every CLI verb), `App::running_break` (the
/// TUI's timer and break-overrun prompt) and `planwire::state_json` (the planner request).
#[test]
fn a_running_breaks_start_has_one_reading() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut files = Vec::new();
    for dir in ["tm/src", "tm-core/src"] {
        rust_files(&root.join(dir), &mut files);
    }
    let (mut cache, mut logged) = (Vec::new(), Vec::new());
    for f in &files {
        let text = fs::read_to_string(f).expect("a source file");
        let rel = f.strip_prefix(&root).expect("under the root").display().to_string();
        for line in non_test_lines(&text).into_iter().map(str::trim).filter(|l| !l.starts_with("//")) {
            if line.contains(".started_at(") {
                cache.push(format!("{rel}: {line}"));
            }
            if line.contains(".started_at_logged(") {
                logged.push(rel.clone());
            }
        }
    }
    assert_eq!(
        cache,
        vec!["tm-core/src/store.rs: None => self.started_at(tz, now),".to_string()],
        "a reader of a running break's start reads the cache's clock and not the ONE reading"
    );
    logged.sort();
    assert_eq!(
        logged,
        vec!["tm-core/src/planwire.rs", "tm/src/cli/ctx.rs", "tm/src/tui/app.rs"],
        "the readers of a running break's start are not the three there are"
    );
}
