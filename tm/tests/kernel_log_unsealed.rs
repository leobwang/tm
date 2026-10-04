//! **`kernel_log::replay_unsealed`, by name** — the replay of a log that WRITES NOTHING (the owner's
//! D96, W-44 track H, README gaps 4392, 4393 and 4557): how a TUI past midnight reads its log while
//! it holds `tm plan`'s housekeeping in memory — the file's bytes with the held lines after them.
//!
//! It is the test `every_door_function_the_switch_calls_is_exercised_here` would ask of a door
//! function, in a file of its own: that guard reads `tests/kernel_log_door.rs`, a file track K
//! holds in W-44, so the function sits above the door banner and its test is here (gap 4557).
//!
//! What it holds the function to, by value: over a log whose cache is warm, with lines appended
//! after the file's bytes that the file does not hold, the answer at every scope is the replay a
//! fresh tree holding those lines WRITTEN reads through the door (`kernel_log::replay_scoped`) —
//! the replay `tm plan` reads after its housekeeping writes them — and not one byte under the
//! cache directory moves; and a sealed month file that is missing is answered `None`, never
//! rebuilt, since a rebuild is a write.

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

#[allow(dead_code)]
#[path = "../src/cli/kernel_log.rs"]
mod kernel_log;

#[allow(dead_code)]
#[path = "support/loggen.rs"]
mod loggen;

use std::collections::BTreeMap;
use std::path::Path;

use chrono::NaiveDate;
use chrono_tz::Tz;
use serde_json::Value;

const TZ: Tz = chrono_tz::America::Chicago;

/// The zone table the host sends, cached under the plan root as the binary caches it (D13).
fn wire(root: &Path) -> Value {
    tz_table::wire_for(Some(&root.join(kernel_log::CACHE_DIR)), TZ)
}

/// A plan root whose `.tm/log.jsonl` holds `text`.
fn tree(text: &str) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("a temp dir");
    std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir .tm");
    std::fs::write(dir.path().join(".tm/log.jsonl"), text).expect("write the log");
    dir
}

/// Every file under `dir`, by path, as bytes.
fn bytes_under(dir: &Path) -> BTreeMap<String, Vec<u8>> {
    let mut out = BTreeMap::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).expect("a directory").flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else {
                out.insert(p.strip_prefix(dir).expect("inside").display().to_string(), std::fs::read(&p).expect("bytes"));
            }
        }
    }
    out
}

/// Copy a directory tree.
fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).expect("create dir");
    for e in std::fs::read_dir(from).expect("read dir").flatten() {
        let target = to.join(e.file_name());
        if e.file_type().expect("file type").is_dir() {
            copy_dir(&e.path(), &target);
        } else {
            std::fs::copy(e.path(), &target).expect("copy file");
        }
    }
}

/// The day of `line`'s stamp, in `TZ`.
fn day_of_line(line: &str) -> NaiveDate {
    let v: Value = serde_json::from_str(line).expect("a log line");
    let t = chrono::DateTime::parse_from_rfc3339(v["t"].as_str().expect("a stamp")).expect("an instant");
    t.with_timezone(&TZ).date_naive()
}

/// A generated log of 60 days, split: the lines the file holds, and its last day's last eight
/// lines, which the hold holds; and the day after its last line.
fn the_log() -> (String, String, NaiveDate) {
    let lines = loggen::log(loggen::Rate::Forty, 60);
    let cut = lines.len() - 8;
    let today = day_of_line(&lines[lines.len() - 1]) + chrono::Duration::days(1);
    (loggen::text(&lines[..cut]), loggen::text(&lines[cut..]), today)
}

/// The scopes a TUI reads at: its default screen's week so far and its Review screen's every day.
fn scopes(today: NaiveDate) -> Vec<kernel_log::Scope> {
    vec![
        kernel_log::Scope::Hot,
        kernel_log::Scope::Dates { from: today - chrono::Duration::days(6), to: today },
        kernel_log::Scope::All,
    ]
}

#[test]
fn the_unsealed_replay_writes_nothing_and_reads_the_held_lines_as_the_written_log_is_read() {
    let (written, held, today) = the_log();
    let dir = tree(&written);
    let root = dir.path();
    let file = std::fs::read(root.join(".tm/log.jsonl")).expect("the log");
    // Warm the process cache, as the TUI's own read does before anything is held.
    kernel_log::replay_scoped(root, &file, TZ, &wire(root), today, kernel_log::Scope::All, None).expect("the door");
    let cache = root.join(kernel_log::CACHE_DIR);
    let before = bytes_under(&cache);
    assert!(before.keys().any(|k| k.starts_with("sealed/")), "the log seals a month: {:?}", before.keys());

    let mut as_held = file.clone();
    as_held.extend_from_slice(held.as_bytes());
    // The comparand: the same plan root — its checkpoint and month files too, so `Hot` narrows to the
    // same open days (a narrowing, never a disagreement: `kernel_log_door.rs`) — with the held lines
    // WRITTEN, read through the door, as `tm plan` reads its directory after its housekeeping writes them.
    let full = tempfile::tempdir().expect("a temp dir");
    copy_dir(root, full.path());
    std::fs::write(full.path().join(".tm/log.jsonl"), &as_held).expect("the held lines, written");
    for scope in scopes(today) {
        let unsealed = kernel_log::replay_unsealed(root, &as_held, TZ, &wire(root), today, scope)
            .expect("the unsealed replay answers")
            .expect("no month file is missing");
        let fbytes = std::fs::read(full.path().join(".tm/log.jsonl")).expect("the full log");
        let door = kernel_log::replay_scoped(full.path(), &fbytes, TZ, &wire(full.path()), today, scope, None).expect("the door");
        assert!(unsealed.replay == door.replay, "{scope:?}: the held lines read as the written ones");
        assert_eq!(unsealed.replay.entry_count(), door.replay.entry_count(), "{scope:?}");
        assert_eq!(bytes_under(&cache), before, "{scope:?}: the unsealed replay wrote under the cache");
    }
    // And the held lines are read: without them the answer is another one.
    let without = kernel_log::replay_unsealed(root, &file, TZ, &wire(root), today, kernel_log::Scope::Hot)
        .expect("answers")
        .expect("no month missing");
    let with = kernel_log::replay_unsealed(root, &as_held, TZ, &wire(root), today, kernel_log::Scope::Hot)
        .expect("answers")
        .expect("no month missing");
    assert!(without.replay != with.replay, "the held lines move the answer");
    assert_eq!(bytes_under(&cache), before);
}

#[test]
fn a_missing_sealed_month_is_answered_none_and_rebuilt_never() {
    let (written, held, today) = the_log();
    let dir = tree(&written);
    let root = dir.path();
    let file = std::fs::read(root.join(".tm/log.jsonl")).expect("the log");
    kernel_log::replay_scoped(root, &file, TZ, &wire(root), today, kernel_log::Scope::All, None).expect("the door");
    let cache = root.join(kernel_log::CACHE_DIR);
    let sealed: Vec<String> = bytes_under(&cache).into_keys().filter(|k| k.starts_with("sealed/")).collect();
    assert!(!sealed.is_empty(), "the log seals a month");
    std::fs::remove_file(cache.join(&sealed[0])).expect("delete a month file");
    let before = bytes_under(&cache);
    let mut as_held = file;
    as_held.extend_from_slice(held.as_bytes());
    let answer = kernel_log::replay_unsealed(root, &as_held, TZ, &wire(root), today, kernel_log::Scope::All).expect("no fault");
    assert!(answer.is_none(), "a missing month file is not answered");
    assert_eq!(bytes_under(&cache), before, "nothing was rebuilt");
    // The hot scope reads no month file, so it still answers.
    assert!(kernel_log::replay_unsealed(root, &as_held, TZ, &wire(root), today, kernel_log::Scope::Hot)
        .expect("no fault")
        .is_some());
    assert_eq!(bytes_under(&cache), before);
}
