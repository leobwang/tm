//! **A sealed month file the replay cache names and the disk lacks is REBUILT
//! from the log** — README gap 3711, stage 6 W-39 repair (owner D13: the cache
//! `.tm/cache/replay/` is derived and rebuildable).
//!
//! Two readers of one condition gave two wrong answers until the repair, both
//! DRIVEN on the W-39 binary with one month file deleted: `tm review week`
//! raised a KERNEL FAULT ("names no month file for the sealed days … this is a
//! bug in tm"), so the TUI exited on its Review screen; and `tm review day`
//! reported `0/6 blocks · done -` for a day the log holds `1/6 · done t4`,
//! under a notice that said "rebuilt in memory" while nothing was rebuilt.
//! These tests delete the month file and read what a user reads: the same
//! review as before the deletion, one notice naming the rebuild, and a cache
//! whose manifest names a file on disk again.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

/// The instant every review is asked at: the Thursday of the week after, when
/// the week of 2026-09-07 is SEALED.
const AT: &str = "2026-09-17T09:00:00-05:00";

/// `cli_week_cut`'s sealed-week recipe: two worked days in the week of
/// 2026-09-07, the undo stack removed (the state of a history longer than the
/// stack), a day of the next week, so a review on its Thursday reseals.
fn sealed_tree() -> Tm {
    let tm = Tm::new();
    let steps: &[(&str, &[&str])] = &[
        ("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]),
        ("2026-09-07T12:00:00-05:00", &["start", "^t4", "--energy", "4"]),
        ("2026-09-07T14:10:00-05:00", &["pause"]),
        ("2026-09-07T14:25:00-05:00", &["pause"]),
        ("2026-09-07T15:00:00-05:00", &["done"]),
        ("2026-09-08T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]),
        ("2026-09-08T09:00:00-05:00", &["start", "^t4", "--energy", "4"]),
        ("2026-09-08T11:00:00-05:00", &["done"]),
    ];
    for (at, args) in steps {
        tm.ok_at(at, args);
    }
    let _ = std::fs::remove_file(tm.plan.join(".tm/undo.json"));
    tm.ok_at("2026-09-16T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-16T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-16T09:30:00-05:00", &["done"]);
    let _ = std::fs::remove_file(tm.plan.join(".tm/undo.json"));
    tm
}

/// The checkpoint's manifest: month key to the file it names.
fn manifest(tm: &Tm) -> Vec<String> {
    let ckpt: Value = serde_json::from_str(&tm.read(".tm/cache/replay/ckpt.json")).expect("a checkpoint");
    ckpt["manifest"]
        .as_object()
        .map(|m| m.values().filter_map(|v| v.as_str().map(str::to_string)).collect())
        .unwrap_or_default()
}

/// Delete every month file the manifest names, asserting there was one.
fn delete_the_months(tm: &Tm) {
    let named = manifest(tm);
    assert!(!named.is_empty(), "the week is sealed: the manifest names a month");
    for rel in named {
        std::fs::remove_file(tm.plan.join(".tm/cache/replay").join(&rel)).expect("a month file");
    }
}

/// **The week review.** Asked before the deletion and after it, `tm --json
/// review week` answers the same document; the run after the deletion exits 0,
/// says once that the cache was rebuilt, and leaves a manifest whose files
/// exist — so the next review says nothing.
#[test]
fn a_missing_month_file_rebuilds_and_the_week_review_is_unchanged() {
    let tm = sealed_tree();
    let before = tm.json_at(AT, &["review", "week", "--date", "2026-09-07"]);
    delete_the_months(&tm);
    let out = tm.run_at(AT, &["--json", "review", "week", "--date", "2026-09-07"]);
    assert_eq!(out.code, 0, "no kernel fault: {}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("kernel fault"), "{}", out.stderr);
    assert!(out.stderr.contains("rebuilt from the log"), "the rebuild is named: {}", out.stderr);
    assert_eq!(out.json(), before, "the week review is the one before the deletion");
    for rel in manifest(&tm) {
        assert!(tm.exists(&format!(".tm/cache/replay/{rel}")), "the rebuilt cache names {rel}, and it is there");
    }
    let again = tm.run_at(AT, &["--json", "review", "week", "--date", "2026-09-07"]);
    assert_eq!((again.code, again.stderr.as_str()), (0, ""), "the healed cache says nothing");
    assert_eq!(again.json(), before);
}

/// **The day review — the silent wrong answer.** Before the repair the day
/// review of a sealed day read ZERO blocks after the deletion, twice, under a
/// notice claiming a rebuild; it now reads the day the log holds.
#[test]
fn a_missing_month_file_rebuilds_and_the_day_review_is_unchanged() {
    let tm = sealed_tree();
    let before = tm.json_at(AT, &["review", "day", "--date", "2026-09-08"]);
    assert_eq!(before["review"]["done"], serde_json::json!(["t4"]), "the day the log holds: {before}");
    delete_the_months(&tm);
    for run in 0..2 {
        let out = tm.run_at(AT, &["--json", "review", "day", "--date", "2026-09-08"]);
        assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
        assert_eq!(out.stderr.contains("rebuilt from the log"), run == 0, "run {run}: {}", out.stderr);
        assert_eq!(out.json(), before, "run {run}: the day review is the one before the deletion");
    }
}
