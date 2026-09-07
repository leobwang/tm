//! `horizon.rs` closes (§6.3, §17 M2 "`tm close week` snapshot tests on
//! fixtures") on temp copies of `tests/fixtures/plan-basic`.
//!
//! `close_day` resets the active block's line and moves the pinned item into
//! the week; `close_week` demotes, folds children away and sends the overdue
//! pset to `backlog.md#Overdue` (snapshotted); `close_month` carries
//! outcomes and demoted lines into the next month, honouring `--drop`; and
//! `auto_close` runs each of them exactly once. Every test also asserts that
//! the lines it did not name are byte-identical before and after.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use chrono::{DateTime, FixedOffset, NaiveDate};
use chrono_tz::Tz;
use tempfile::TempDir;
use tm_core::horizon::{
    auto_close, churn, close_day, close_month, close_week, pending_closes, Ctx, MIN_REMAINING_MIN,
    REVIEW_PLACEHOLDER,
};
use tm_core::log::{replay, Event, Log, LogEntry, Replay};
use tm_core::model::{Id, IsoWeek, Period, Stamp, State, YearMonth};
use tm_core::store::{FsStore, Store};

const WEEK: &str = "week/2026-W37.md";
const MONTH: &str = "month/2026-09.md";
const NEXT_MONTH: &str = "month/2026-10.md";
const DAY: &str = "day/2026-09-07.md";
const BACKLOG: &str = "backlog.md";

// ---------------------------------------------------------------------------
// Fixture plumbing
// ---------------------------------------------------------------------------

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/plan-basic")
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        let dest = to.join(entry.file_name());
        if path.is_dir() {
            copy_dir(&path, &dest);
        } else {
            fs::copy(&path, &dest).unwrap();
        }
    }
}

/// A temp copy of `plan-basic` (never the fixture itself) and a store on it.
fn plan() -> (TempDir, FsStore) {
    let dir = TempDir::new().unwrap();
    let root = dir.path().join("plan");
    copy_dir(&fixture_dir(), &root);
    (dir, FsStore::new(root))
}

/// Every `.md` file under the plan root, `path -> text`.
fn tree_text(store: &FsStore) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for rel in store.list_files().unwrap() {
        out.insert(rel.clone(), store.read_text(&rel).unwrap());
    }
    out
}

fn text(store: &FsStore, rel: &str) -> String {
    store.read_text(rel).unwrap()
}

fn at(s: &str) -> DateTime<FixedOffset> {
    DateTime::parse_from_rfc3339(s).unwrap()
}

fn d(s: &str) -> NaiveDate {
    s.parse().unwrap()
}

fn id(s: &str) -> Id {
    Id::new(s)
}

/// The line carrying `^id`, or `None` when the file has none.
fn line_of(store: &FsStore, rel: &str, id: &str) -> Option<String> {
    let needle = format!("^{id}");
    text(store, rel)
        .lines()
        .find(|l| l.split_whitespace().any(|w| w == needle))
        .map(str::to_string)
}

/// `(lines only in `before`, lines only in `after`)` — the byte-level diff
/// every test uses to prove that untouched lines stayed untouched.
fn diff(before: &str, after: &str) -> (Vec<String>, Vec<String>) {
    let b: Vec<&str> = before.lines().collect();
    let a: Vec<&str> = after.lines().collect();
    let gone = b
        .iter()
        .filter(|l| !a.contains(*l))
        .map(|l| l.to_string())
        .collect();
    let new = a
        .iter()
        .filter(|l| !b.contains(*l))
        .map(|l| l.to_string())
        .collect();
    (gone, new)
}

/// Assert that every file except `changed` is byte-identical.
fn only_changed(before: &BTreeMap<String, String>, after: &BTreeMap<String, String>, changed: &[&str]) {
    for (path, text) in after {
        if changed.contains(&path.as_str()) {
            continue;
        }
        assert_eq!(
            before.get(path),
            Some(text),
            "{path} changed but should not have"
        );
    }
    for path in before.keys() {
        assert!(after.contains_key(path), "{path} disappeared");
    }
}

/// The log lines the store wrote, as `(ev, id)` pairs.
fn log_events(store: &FsStore) -> Vec<(String, String)> {
    let path = store.abs_path(".tm/log.jsonl").unwrap();
    Log::read(path)
        .unwrap()
        .entries
        .iter()
        .map(|e| {
            (
                e.ev.name().to_string(),
                e.ev.primary_id().unwrap_or_default().to_string(),
            )
        })
        .collect()
}

/// A replay in which `id` got `minutes` of block time on `date`.
fn replay_of(id: &str, minutes: u32, at_time: &str) -> Replay {
    let entries = vec![LogEntry::new(
        at(at_time),
        Event::Done {
            id: id.to_string(),
            est_min: 60,
            actual_min: minutes,
            went: Some(2),
            tags: vec![],
            ci: 4,
            partial: true,
        },
    )];
    replay(&entries, None, Tz::America__Chicago)
}

// ---------------------------------------------------------------------------
// close day (§6.3)
// ---------------------------------------------------------------------------

#[test]
fn close_day_resets_the_active_line_and_moves_the_pinned_item() {
    let (_dir, store) = plan();
    let before = tree_text(&store);
    let date = d("2026-09-07");
    let r = replay_of("t3", 60, "2026-09-07T10:32:00-05:00");
    assert_eq!(r.block_minutes_on("t3", date), 60);

    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-07T22:30:00-05:00")).with_replay(&r);
    let report = close_day(&cx, date).unwrap();

    // `[>]` -> `[ ]`, `est:` = 1b remaining − 60m done, floored.
    let t3 = line_of(&store, WEEK, "t3").unwrap();
    assert_eq!(
        t3,
        format!("- [ ] 4 2b Exercises 5.3–5.5            @m1 est:{MIN_REMAINING_MIN}m ^t3")
    );
    assert_eq!(report.reopened.len(), 1);
    assert_eq!(report.reopened[0].id, id("t3"));
    assert_eq!(report.reopened[0].est_min, MIN_REMAINING_MIN);

    // The pinned item left the day file for the week, stamped `D07`.
    assert!(line_of(&store, DAY, "p1").is_none());
    let p1 = line_of(&store, WEEK, "p1").unwrap();
    assert!(p1.contains("demoted:D07"), "{p1}");
    assert!(p1.starts_with("- [ ] 2 20m Call the bank about the card"), "{p1}");
    assert_eq!(report.moved.len(), 1);
    assert_eq!(report.moved[0].from, DAY);
    assert_eq!(report.moved[0].to, WEEK);
    assert_eq!(report.demoted[0].stamps, vec![Stamp::Day(7)]);

    // The day file keeps everything else and gains the review placeholder.
    let day = text(&store, DAY);
    assert!(day.contains("<!-- tm:review start -->"));
    assert!(day.contains(REVIEW_PLACEHOLDER));
    assert!(day.contains("<!-- tm:review end -->"));
    assert!(day.contains("<!-- tm:plan start 10:42 -->"), "the plan block survives");
    let (gone, new) = diff(before.get(DAY).unwrap(), &day);
    assert_eq!(gone, vec!["- [ ] 2 20m Call the bank about the card  ^p1"]);
    assert_eq!(
        new,
        vec![
            "<!-- tm:review start -->",
            REVIEW_PLACEHOLDER,
            "<!-- tm:review end -->",
        ]
    );

    // Nothing else in the week file moved.
    let after = tree_text(&store);
    only_changed(&before, &after, &[WEEK, DAY]);
    let (gone, new) = diff(before.get(WEEK).unwrap(), after.get(WEEK).unwrap());
    assert_eq!(gone, vec!["- [>] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3"]);
    assert_eq!(new, vec![t3, p1]);

    assert_eq!(
        log_events(&store),
        vec![
            ("demote".to_string(), "p1".to_string()),
            ("close".to_string(), String::new()),
        ]
    );
}

#[test]
fn close_day_without_a_replay_keeps_the_whole_remaining_estimate() {
    let (_dir, store) = plan();
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-07T22:30:00-05:00"));
    close_day(&cx, d("2026-09-07")).unwrap();
    assert_eq!(
        line_of(&store, WEEK, "t3").unwrap(),
        "- [ ] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3"
    );
}

// ---------------------------------------------------------------------------
// close week (§6.3) — the M2 snapshot
// ---------------------------------------------------------------------------

fn run_close_week(store: &FsStore) -> tm_core::horizon::CloseReport {
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(store, &files, &tree, at("2026-09-14T09:00:00-05:00"));
    close_week(&cx, IsoWeek::new(2026, 37)).unwrap()
}

#[test]
fn close_week_demotes_folds_children_and_files_the_overdue_item() {
    let (_dir, store) = plan();
    let before = tree_text(&store);
    let report = run_close_week(&store);

    insta::assert_snapshot!("week_after_close", text(&store, WEEK));
    insta::assert_snapshot!("month_after_close", text(&store, MONTH));
    insta::assert_snapshot!("backlog_after_close", text(&store, BACKLOG));

    // The §4.3 example line's shape: `[-] ci est title @parent est: demoted: ^id`.
    assert_eq!(
        line_of(&store, MONTH, "m2").unwrap(),
        "- [-] 4 6b Rollback path passes tests   @O2 est:6b demoted:W37 ^m2"
    );
    // The week line stays as an archive, marked `[-]`.
    assert_eq!(
        line_of(&store, WEEK, "m2").unwrap(),
        "- [-] 4 6b Rollback path passes tests   @O2 ^m2"
    );
    assert!(text(&store, WEEK).contains("closed: 2026-09-14"));

    // Children whose parent is in the same week file are gone from it.
    let mut dropped: Vec<String> = report
        .dropped_children
        .iter()
        .map(|i| i.to_string())
        .collect();
    dropped.sort();
    assert_eq!(dropped, vec!["t1", "t3", "t4", "t5", "x2"]);
    for child in ["t1", "t3", "t4", "t5", "x2"] {
        assert!(line_of(&store, WEEK, child).is_none(), "^{child} still in the week");
        assert!(line_of(&store, MONTH, child).is_none(), "^{child} reached the month");
    }

    // The dated milestone past its due date went to the backlog instead.
    assert_eq!(report.overdue_to_backlog, vec![id("d1")]);
    assert!(line_of(&store, WEEK, "d1").is_none());
    assert_eq!(
        line_of(&store, BACKLOG, "d1").unwrap(),
        "- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1"
    );

    let demoted: Vec<(String, u32)> = report
        .demoted
        .iter()
        .map(|d| (d.id.to_string(), d.est_min))
        .collect();
    assert_eq!(
        demoted,
        vec![
            ("m1".to_string(), 360),
            ("m2".to_string(), 360),
            ("m3".to_string(), 180),
            ("m4".to_string(), 120),
            ("x1".to_string(), 120),
        ]
    );
    assert!(report
        .demoted
        .iter()
        .all(|d| d.stamps == vec![Stamp::Week(37)]));

    let after = tree_text(&store);
    only_changed(&before, &after, &[WEEK, MONTH, BACKLOG]);
    // The month file only gained lines (and rewrote its one demoted copy).
    let (gone, _) = diff(before.get(MONTH).unwrap(), after.get(MONTH).unwrap());
    assert_eq!(
        gone,
        vec!["- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2"]
    );
    // The backlog only gained the overdue section.
    let (gone, new) = diff(before.get(BACKLOG).unwrap(), after.get(BACKLOG).unwrap());
    assert!(gone.is_empty(), "{gone:?}");
    assert_eq!(
        new,
        vec![
            "# Overdue".to_string(),
            "- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1"
                .to_string(),
        ]
    );

    let events = log_events(&store);
    assert_eq!(
        events,
        vec![
            ("demote".to_string(), "m1".to_string()),
            ("demote".to_string(), "m2".to_string()),
            ("demote".to_string(), "m3".to_string()),
            ("demote".to_string(), "m4".to_string()),
            ("demote".to_string(), "x1".to_string()),
            ("move".to_string(), "d1".to_string()),
            ("close".to_string(), String::new()),
        ]
    );
}

#[test]
fn a_closed_week_reparses_into_one_item_per_id() {
    let (_dir, store) = plan();
    run_close_week(&store);
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    // The `[-]` week line and the stamped month copy are the §6.3 pair, not a
    // duplicate id: the copy with the stamps wins.
    assert!(tree.duplicate_ids().is_empty(), "{:?}", tree.duplicate_ids());
    let m2 = tree.get(&id("m2")).unwrap();
    assert_eq!(m2.state, State::Demoted);
    assert_eq!(m2.stamps.demoted, vec![Stamp::Week(37)]);
    assert_eq!(m2.est.unwrap().as_minutes(), 360);
    assert_eq!(m2.src.file, MONTH);
    // Nothing is left to plan in the archived week.
    assert!(tree
        .week_items(IsoWeek::new(2026, 37))
        .iter()
        .all(|i| !i.state.is_open()));
}

#[test]
fn close_week_creates_the_month_file_it_demotes_into() {
    let (_dir, store) = plan();
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    // Closing W37 in October: `month/<current>` is 2026-10, which does not
    // exist yet (§6.3 "copied to month/<current>#Demoted").
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-02T09:00:00-05:00"));
    close_week(&cx, IsoWeek::new(2026, 37)).unwrap();
    let text = text(&store, NEXT_MONTH);
    assert!(text.starts_with("---\nmonth: 2026-10\n---\n"), "{text}");
    assert!(text.contains("# Demoted"), "{text}");
    assert!(
        text.contains("- [-] 5 3b Read ch.6                    @O1 est:3b demoted:W37 ^m3"),
        "{text}"
    );
    // The September file is untouched: the demoted copies went to October.
    assert_eq!(
        line_of(&store, MONTH, "m2").unwrap(),
        "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2"
    );
}

#[test]
fn a_close_report_is_json() {
    let (_dir, store) = plan();
    let report = run_close_week(&store);
    insta::assert_snapshot!("close_week_report_json", serde_json::to_string_pretty(&report).unwrap());
}

// ---------------------------------------------------------------------------
// close month (§6.3)
// ---------------------------------------------------------------------------

#[test]
fn close_month_carries_outcomes_and_demoted_lines_and_honours_drop() {
    let (_dir, store) = plan();
    let before = tree_text(&store);
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:00:00-05:00"));
    let report = close_month(&cx, YearMonth::new(2026, 9), &[id("O3")]).unwrap();

    insta::assert_snapshot!("month_after_month_close", text(&store, MONTH));
    insta::assert_snapshot!("next_month_after_month_close", text(&store, NEXT_MONTH));

    // Dropped outcomes stay behind as `[~]`.
    assert_eq!(report.dropped, vec![id("O3")]);
    assert_eq!(
        line_of(&store, MONTH, "O3").unwrap(),
        "- [~] 2 !3 Winter course selection + admin done        ^O3"
    );
    assert!(line_of(&store, NEXT_MONTH, "O3").is_none());

    // Outcomes keep their `!k`; the demoted copy keeps its stamps.
    assert_eq!(
        line_of(&store, NEXT_MONTH, "O1").unwrap(),
        "- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1"
    );
    assert_eq!(
        line_of(&store, NEXT_MONTH, "m2").unwrap(),
        "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2"
    );
    assert!(text(&store, NEXT_MONTH).contains("month: 2026-10"));
    assert!(text(&store, NEXT_MONTH).contains("# Outcomes"));
    assert!(text(&store, NEXT_MONTH).contains("# Demoted"));

    let moved: Vec<String> = report.moved.iter().map(|m| m.id.to_string()).collect();
    assert_eq!(moved, vec!["O1", "O2", "m2"]);
    assert_eq!(report.demoted.len(), 1);
    assert_eq!(report.demoted[0].stamps, vec![Stamp::Week(37)]);
    assert_eq!(report.demoted[0].est_min, 180);

    let after = tree_text(&store);
    only_changed(&before, &after, &[MONTH, NEXT_MONTH]);
    assert_eq!(
        log_events(&store),
        vec![
            ("drop".to_string(), "O3".to_string()),
            ("move".to_string(), "O1".to_string()),
            ("move".to_string(), "O2".to_string()),
            ("move".to_string(), "m2".to_string()),
            ("close".to_string(), String::new()),
        ]
    );
}

#[test]
fn a_second_stamp_becomes_a_cut_proposal() {
    let (_dir, store) = plan();
    // Two stamps on the demoted copy: `/plan-month` proposes a cut (§6.3).
    let old = line_of(&store, MONTH, "m2").unwrap();
    store
        .write_line_in(
            Some(MONTH),
            &id("m2"),
            &old.replace("demoted:W37", "demoted:W36,W37"),
        )
        .unwrap();

    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:00:00-05:00"));
    let report = close_month(&cx, YearMonth::new(2026, 9), &[]).unwrap();
    assert_eq!(report.demoted[0].stamps, vec![Stamp::Week(36), Stamp::Week(37)]);
    assert_eq!(report.notes.len(), 1);
    assert!(report.notes[0].contains("^m2"), "{:?}", report.notes);
    assert!(report.notes[0].contains("2 demotion stamps"), "{:?}", report.notes);
}

// ---------------------------------------------------------------------------
// auto_close (§13 "auto-run when overdue", §10.2)
// ---------------------------------------------------------------------------

#[test]
fn auto_close_runs_each_period_once() {
    let (_dir, store) = plan();
    let mut state = store.load_state().unwrap();
    assert_eq!(state.closed.week, None);

    let ran = auto_close(
        &store,
        &mut state,
        d("2026-09-14"),
        at("2026-09-14T09:00:00-05:00"),
        None,
    )
    .unwrap();

    // The last unclosed day and week ran; August has no file, so it is only
    // recorded.
    let periods: Vec<(Period, String)> = ran.iter().map(|c| (c.period, c.key.clone())).collect();
    assert_eq!(
        periods,
        vec![
            (Period::Day, "2026-09-13".to_string()),
            (Period::Week, "2026-W37".to_string()),
        ]
    );
    assert_eq!(state.closed.day, Some(d("2026-09-13")));
    assert_eq!(state.closed.week, Some(IsoWeek::new(2026, 37)));
    assert_eq!(state.closed.month, Some(YearMonth::new(2026, 8)));
    assert!(!store.exists("day/2026-09-13.md"), "no file is invented for an unplanned day");
    assert!(text(&store, WEEK).contains("closed: 2026-09-14"));

    // The state was persisted, so the next command starts from it …
    let reloaded = store.load_state().unwrap();
    assert_eq!(reloaded.closed.week, Some(IsoWeek::new(2026, 37)));

    // … and running it again is a no-op: no writes, no events.
    let snapshot = tree_text(&store);
    let events = log_events(&store);
    let mut state = reloaded;
    let again = auto_close(
        &store,
        &mut state,
        d("2026-09-14"),
        at("2026-09-14T17:00:00-05:00"),
        None,
    )
    .unwrap();
    assert!(again.is_empty(), "{again:?}");
    assert_eq!(tree_text(&store), snapshot);
    assert_eq!(log_events(&store), events);
}

#[test]
fn pending_closes_names_what_auto_close_would_run() {
    let (_dir, store) = plan();
    let mut state = store.load_state().unwrap();
    let today = d("2026-09-14");
    let pending = pending_closes(&store, &state, today);
    assert_eq!(
        pending,
        vec![
            (Period::Day, "2026-09-13".to_string()),
            (Period::Week, "2026-W37".to_string()),
        ]
    );
    auto_close(&store, &mut state, today, at("2026-09-14T09:00:00-05:00"), None).unwrap();
    assert!(pending_closes(&store, &state, today).is_empty());
}

#[test]
fn churn_lists_the_repeatedly_demoted_items() {
    let (_dir, store) = plan();
    // One close stamps everything with W37; the month copy of ^m2 already
    // carried that stamp, so it stays at one.
    run_close_week(&store);
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let once: Vec<Id> = churn(&tree, 1).into_iter().map(|(i, _)| i).collect();
    assert_eq!(
        once,
        vec![id("m1"), id("m2"), id("m3"), id("m4"), id("x1")]
    );
    assert!(churn(&tree, 2).is_empty());
}

#[test]
fn auto_close_only_closes_the_last_unclosed_period() {
    let (_dir, store) = plan();
    let mut state = store.load_state().unwrap();
    // Three weeks later: W37 is not the last unclosed week any more, so the
    // week close does not touch it (its file is an archive of a planned week
    // nobody closed; `tm close week --week 2026-W37` is the way back).
    let ran = auto_close(
        &store,
        &mut state,
        d("2026-10-05"),
        at("2026-10-05T09:00:00-05:00"),
        None,
    )
    .unwrap();
    assert!(
        ran.iter().all(|c| c.period != Period::Week),
        "{:?}",
        ran.iter().map(|c| &c.key).collect::<Vec<_>>()
    );
    assert_eq!(state.closed.week, Some(IsoWeek::new(2026, 40)));
    assert!(!text(&store, WEEK).contains("closed:"));
    // The month that ended is closed, though.
    assert_eq!(state.closed.month, Some(YearMonth::new(2026, 9)));
    assert!(store.exists(NEXT_MONTH));
}
