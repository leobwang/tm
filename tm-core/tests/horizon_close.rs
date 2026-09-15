//! `horizon.rs` closes (§6.3, §17 M2 "`tm close week` snapshot tests on
//! fixtures") on temp copies of `tests/fixtures/plan-basic`.
//!
//! `close_day` resets the active block's line and moves the pinned item into
//! the week; `close_week` demotes, folds children away and sends the overdue
//! pset to `backlog.md#Overdue` (snapshotted); `close_month` carries
//! outcomes and demoted lines into the next month, honouring `--drop`. Every
//! test also asserts that the lines it did not name are byte-identical
//! before and after. (These are the fork-point library closes; since stage 4
//! step 6 the shipped `tm close` and automatic close go through the kernel
//! instead — see `tm-core/src/horizon.rs`'s module docs.)

#[path = "../../tm/tests/support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use chrono::{DateTime, FixedOffset, NaiveDate};
use chrono_tz::Tz;
use tempfile::TempDir;
use tm_core::horizon::{
    churn, close_day, close_month, close_week, CloseReport, Ctx,
    HorizonError, Moved, MIN_REMAINING_MIN, REVIEW_PLACEHOLDER,
};
use tm_core::log::{Event, LogEntry, Replay};
use tm_core::model::{Id, IsoWeek, Period, Stamp, State, YearMonth};
use tm_core::review::write_day_review;
use tm_core::store::{FsStore, MemStore, Store};

const WEEK: &str = "week/2026-W37.md";
const MONTH: &str = "month/2026-09.md";
const NEXT_WEEK: &str = "week/2026-W38.md";
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
    let text = match fs::read_to_string(&path) {
        Ok(text) => text,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(e) => panic!("{}: {e}", path.display()),
    };
    chokepoint::headers_of_text(&text)
        .into_iter()
        .map(|(tag, id)| (tag, id.unwrap_or_default()))
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
    chokepoint::replay_of_entries(&entries, Tz::America__Chicago)
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

    // `[>]` -> `[ ]`, `est:` = remaining. The §17 M2 definition of done: the
    // 60 logged minutes are the ones the partial `done` already took off the
    // line (`est:1b`), so the close must not take them off a second time.
    let t3 = line_of(&store, WEEK, "t3").unwrap();
    assert_eq!(
        t3,
        "- [ ] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3"
    );
    assert_eq!(report.reopened.len(), 1);
    assert_eq!(report.reopened[0].id, id("t3"));
    assert_eq!(report.reopened[0].est_min, 60);

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

/// The subtraction the M2 definition of done leaves implicit: today's logged
/// minutes come off an estimate **no tool has written** (`est:` absent). A
/// line that already carries `est:` keeps it — §9.1 wrote that number after
/// the block, so taking the minutes off again would count them twice (the
/// case `close_day_resets_the_active_line_and_moves_the_pinned_item` pins).
#[test]
fn close_day_subtracts_todays_minutes_from_an_untouched_estimate() {
    let floor = format!("{MIN_REMAINING_MIN}m");
    let cases = [
        (0, "1b".to_string()),
        (10, "50m".to_string()),
        (30, "30m".to_string()),
        (45, "15m".to_string()),
        (60, floor.clone()),
        (90, floor),
    ];
    for (done, expected) in cases {
        let (_dir, store) = plan();
        // `^t4` is `1b` with no `est:`: nothing has rewritten it yet.
        store
            .write_line_in(
                Some(WEEK),
                &id("t4"),
                "- [>] 3 1b Claude Code drafts tests     @m2 ^t4",
            )
            .unwrap();
        let r = replay_of("t4", done, "2026-09-07T10:32:00-05:00");
        assert_eq!(r.block_minutes_on("t4", d("2026-09-07")), done);

        let files = store.read_tree().unwrap();
        let tree = files.tree();
        let cx = Ctx::new(&store, &files, &tree, at("2026-09-07T22:30:00-05:00")).with_replay(&r);
        let report = close_day(&cx, d("2026-09-07")).unwrap();

        assert_eq!(
            line_of(&store, WEEK, "t4").unwrap(),
            format!("- [ ] 3 1b Claude Code drafts tests     @m2 est:{expected} ^t4"),
            "{done}m done"
        );
        let t4 = report
            .reopened
            .iter()
            .find(|r| r.id == id("t4"))
            .unwrap_or_else(|| panic!("^t4 was not reopened ({done}m done)"));
        assert_eq!(t4.est_min, 60u32.saturating_sub(done).max(MIN_REMAINING_MIN));
    }
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

/// §6.3 gives the day file its review *section*; §13's `tm review day
/// --write` gives it the review *text*. The close runs automatically on the
/// first command after the day ends, so it routinely arrives after a review
/// was written — and must not put `review pending` over it, because that copy
/// of the text is the only one there is.
#[test]
fn close_day_never_overwrites_a_written_review() {
    let (_dir, store) = plan();
    let date = d("2026-09-07");
    let review = " Day 2026-09-07 · lounge · 5/6 blocks\n done      t1 t2 t3\n sleep     8h10m";
    write_day_review(&store, date, review).unwrap();
    let before = text(&store, DAY);

    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-07T22:30:00-05:00"));
    close_day(&cx, date).unwrap();

    let after = text(&store, DAY);
    assert!(after.contains(review), "the review was destroyed:\n{after}");
    assert!(!after.contains(REVIEW_PLACEHOLDER), "{after}");
    // The close still moved the pinned item; only that line changed.
    let (gone, new) = diff(&before, &after);
    assert_eq!(gone, vec!["- [ ] 2 20m Call the bank about the card  ^p1"]);
    assert!(new.is_empty(), "{new:?}");
}

/// Closing twice is idempotent (§6.3): the second close finds the placeholder
/// its own first run left, recognises it as "no review yet" and leaves the
/// file byte-identical — one block, one placeholder.
#[test]
fn closing_the_day_twice_leaves_one_review_placeholder() {
    let (_dir, store) = plan();
    let date = d("2026-09-07");
    for _ in 0..2 {
        let files = store.read_tree().unwrap();
        let tree = files.tree();
        let cx = Ctx::new(&store, &files, &tree, at("2026-09-07T22:30:00-05:00"));
        close_day(&cx, date).unwrap();
    }
    let after = text(&store, DAY);
    assert_eq!(after.matches("<!-- tm:review start -->").count(), 1, "{after}");
    assert_eq!(after.matches(REVIEW_PLACEHOLDER).count(), 1, "{after}");
    assert!(after.trim_end().ends_with("<!-- tm:review end -->"), "{after}");
}

/// An empty review block — the block without a body a stray edit can leave —
/// is not user-visible content, so the close still fills it with the
/// placeholder rather than adding a second block.
#[test]
fn close_day_fills_an_empty_review_block() {
    let (_dir, store) = plan();
    let date = d("2026-09-07");
    let day = format!(
        "{}\n<!-- tm:review start -->\n\n<!-- tm:review end -->\n",
        text(&store, DAY).trim_end()
    );
    store.write_file(DAY, &day).unwrap();

    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-07T22:30:00-05:00"));
    close_day(&cx, date).unwrap();

    let after = text(&store, DAY);
    assert_eq!(after.matches("<!-- tm:review start -->").count(), 1, "{after}");
    assert!(
        after.trim_end().ends_with(&format!(
            "<!-- tm:review start -->\n{REVIEW_PLACEHOLDER}\n<!-- tm:review end -->"
        )),
        "{after}"
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
    insta::assert_snapshot!("next_week_after_close", text(&store, NEXT_WEEK));

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

    // Children whose parent is demoted in the same week file are gone from
    // it; their remaining is folded into that parent's `est:` (here every
    // parent's own estimate already covers its subtasks, §6.4).
    let mut dropped: Vec<String> = report
        .dropped_children
        .iter()
        .map(|i| i.to_string())
        .collect();
    dropped.sort();
    assert_eq!(dropped, vec!["t1", "t3", "t4", "t5"]);
    for child in ["t1", "t3", "t4", "t5"] {
        assert!(line_of(&store, WEEK, child).is_none(), "^{child} still in the week");
        assert!(line_of(&store, MONTH, child).is_none(), "^{child} reached the month");
    }

    // The wall and its prep are never demoted (§6.3): they stay `[ ]` and
    // move, byte for byte, into the current week.
    assert_eq!(report.carried, vec![id("x1"), id("x2")]);
    assert!(line_of(&store, WEEK, "x1").is_none());
    assert!(line_of(&store, MONTH, "x1").is_none());
    assert_eq!(
        line_of(&store, NEXT_WEEK, "x1").as_deref(),
        before
            .get(WEEK)
            .unwrap()
            .lines()
            .find(|l| l.ends_with("^x1"))
    );
    assert_eq!(
        line_of(&store, NEXT_WEEK, "x2").as_deref(),
        before
            .get(WEEK)
            .unwrap()
            .lines()
            .find(|l| l.ends_with("^x2"))
    );

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
        ]
    );
    assert!(report
        .demoted
        .iter()
        .all(|d| d.stamps == vec![Stamp::Week(37)]));

    let after = tree_text(&store);
    only_changed(&before, &after, &[WEEK, MONTH, BACKLOG, NEXT_WEEK]);
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
            ("move".to_string(), "x1".to_string()),
            ("move".to_string(), "x2".to_string()),
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
    // September keeps its outcomes, but not its `# Demoted` copy of `^m2`:
    // the record moved into the copy October now holds, stamps and all
    // (§6.3 gives an id one archive copy; two of them in two month files
    // become one file's `dup-id` the moment a month close carries the older
    // one forward, §4.1, §17.2).
    let september = store.read_text(MONTH).unwrap();
    assert!(line_of(&store, MONTH, "m2").is_none(), "{september}");
    assert!(september.contains("# Demoted"), "the heading stays");
    assert_eq!(
        line_of(&store, NEXT_MONTH, "m2").unwrap(),
        "- [-] 4 6b Rollback path passes tests   @O2 est:6b demoted:W37 ^m2"
    );
    assert_eq!(text.matches("^m2").count(), 1, "one archive copy: {text}");
}

#[test]
fn a_close_report_is_json() {
    let (_dir, store) = plan();
    let report = run_close_week(&store);
    let json = serde_json::to_string_pretty(&report).unwrap();
    insta::assert_snapshot!("close_week_report_json", json);
    // A stamp is `W37` everywhere it is written or read (§4.1 `demoted:`),
    // the `--json` payload `/plan-month` consumes included.
    assert!(json.contains("\"W37\""), "{json}");
    assert!(!json.contains("\"Week\""), "{json}");
}

/// §6.3: a *wall* — a dated interval, §7.2's "calendar, exams, meetings" —
/// is never demoted. The exam five weeks out stays `[ ]` with its prep, and
/// moves into the live week rather than being archived with the file.
#[test]
fn a_future_wall_and_its_prep_are_carried_not_demoted() {
    let (_dir, store) = plan();
    let before = text(&store, WEEK);
    let report = run_close_week(&store);

    assert_eq!(report.carried, vec![id("x1"), id("x2")]);
    assert!(report.demoted.iter().all(|d| d.id != id("x1")));
    assert!(report.dropped_children.iter().all(|c| *c != id("x2")));
    for wall in ["x1", "x2"] {
        let line = line_of(&store, NEXT_WEEK, wall).unwrap();
        assert!(line.starts_with("- [ ] "), "{line}");
        assert_eq!(
            Some(line.as_str()),
            before.lines().find(|l| l.ends_with(&format!("^{wall}"))),
            "^{wall} did not cross byte for byte"
        );
    }
    // 8b of prep is still 8b of prep, in a file the planner reads (§6.2).
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    assert_eq!(tree.remaining(&id("x2")), Some(480));
    assert_eq!(tree.prep_need(&id("x1")), 480);
    assert!(tree
        .day_candidate_ids(d("2026-09-14"), IsoWeek::new(2026, 38))
        .contains(&id("x1")));
}

/// Closing the week you are still in — `tm close week` on the Sunday, the
/// verb's documented default — archives that file, so its walls have to go
/// to the *following* week rather than staying in an archive the planner no
/// longer reads (§6.2, §6.3, §0 principle 6).
#[test]
fn closing_the_week_from_inside_it_carries_the_wall_to_the_next_week() {
    let (_dir, store) = plan();
    let before = text(&store, WEEK);
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-13T20:00:00-05:00"));
    let report = close_week(&cx, IsoWeek::new(2026, 37)).unwrap();

    assert_eq!(report.carried, vec![id("x1"), id("x2")]);
    assert!(line_of(&store, WEEK, "x1").is_none(), "^x1 left the archive");
    assert!(line_of(&store, WEEK, "x2").is_none(), "^x2 left the archive");
    for wall in ["x1", "x2"] {
        let line = line_of(&store, NEXT_WEEK, wall).unwrap();
        assert!(line.starts_with("- [ ] "), "{line}");
        assert_eq!(
            Some(line.as_str()),
            before.lines().find(|l| l.ends_with(&format!("^{wall}"))),
            "^{wall} did not cross byte for byte"
        );
    }
    // The exam is still a candidate on its own day (§6.2).
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    assert!(tree
        .day_candidate_ids(d("2026-10-20"), IsoWeek::new(2026, 38))
        .contains(&id("x1")));
}

/// A wall that is already over carries nothing forward — its instance
/// expired (§5.3) — and is still never demoted: the line stays as written in
/// the week it was planned in.
#[test]
fn a_wall_that_is_over_stays_in_the_archived_week() {
    let line = "- [ ] 3 Guest lecture at:2026-09-09T15:00/16:20 on-miss:expire ^gv2";
    let store = MemStore::new()
        .with_file(
            WEEK,
            &format!("---\nweek: 2026-W37\n---\n# Milestones\n{line}\n"),
        )
        .with_file(MONTH, "---\nmonth: 2026-09\n---\n# Demoted\n");
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-14T09:00:00-05:00"));
    let report = close_week(&cx, IsoWeek::new(2026, 37)).unwrap();

    assert_eq!(report.carried, vec![id("gv2")]);
    assert!(report.demoted.is_empty(), "{report:?}");
    assert!(report.moved.is_empty(), "{report:?}");
    assert!(!store.paths().contains(&NEXT_WEEK.to_string()));
    assert!(store.text(WEEK).unwrap().contains(line), "{}", store.text(WEEK).unwrap());
}

/// §6.3's parenthetical: the remaining of the children dropped with a
/// demoted parent is folded into its `est:`. A parent whose own estimate no
/// longer covers what is under it carries their sum instead, so a week close
/// never removes work from the tree (§0 principle 6).
#[test]
fn the_remaining_of_dropped_children_is_folded_into_the_parent() {
    let store = MemStore::new()
        .with_file(
            WEEK,
            "---\nweek: 2026-W37\n---\n# Milestones\n\
             - [ ] 4 2b Parent ^par\n\
             - [ ] 4 3b Kid one @par ^kid1\n\
             - [ ] 4 3b Kid two @par ^kid2\n\
             - [ ] 4 1b Grandkid @kid1 ^kid3\n",
        )
        .with_file(MONTH, "---\nmonth: 2026-09\n---\n# Demoted\n");
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let before: u32 = ["par", "kid1", "kid2", "kid3"]
        .iter()
        .map(|k| tree.get(&id(k)).unwrap().own_remaining().unwrap().as_minutes())
        .sum();
    assert_eq!(before, 120 + 180 + 180 + 60);

    let cx = Ctx::new(&store, &files, &tree, at("2026-09-14T09:00:00-05:00"));
    let report = close_week(&cx, IsoWeek::new(2026, 37)).unwrap();

    let mut dropped: Vec<String> = report.dropped_children.iter().map(|c| c.to_string()).collect();
    dropped.sort();
    assert_eq!(dropped, vec!["kid1", "kid2", "kid3"]);
    assert_eq!(report.demoted.len(), 1);
    assert_eq!(report.demoted[0].id, id("par"));
    // 2b of parent no longer covers 3b + 3b + 1b of dropped lines: it carries
    // the 7b that is actually left.
    assert_eq!(report.demoted[0].est_min, 420);
    assert!(
        store
            .text(MONTH)
            .unwrap()
            .contains("- [-] 4 2b Parent est:7b demoted:W37 ^par"),
        "{}",
        store.text(MONTH).unwrap()
    );
    // Nothing left the tree: the one line that survives carries it all.
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    assert_eq!(tree.remaining(&id("par")), Some(420));
}

/// §5.5 makes a parent cycle a `tm check` error — not a licence to delete
/// the lines in it. Every member is demoted as a root of its own.
#[test]
fn a_parent_cycle_is_demoted_not_deleted() {
    let store = MemStore::new()
        .with_file(
            WEEK,
            "---\nweek: 2026-W37\n---\n# Milestones\n\
             - [ ] 4 6b Self parent @mm2 ^mm2\n\
             - [ ] 4 6b Aye @bbbb ^aaaa\n\
             - [ ] 4 6b Bee @aaaa ^bbbb\n",
        )
        .with_file(MONTH, "---\nmonth: 2026-09\n---\n# Demoted\n");
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    assert_eq!(tree.parent(&id("mm2")), Some(&id("mm2")));
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-14T09:00:00-05:00"));
    let report = close_week(&cx, IsoWeek::new(2026, 37)).unwrap();

    assert!(report.dropped_children.is_empty(), "{report:?}");
    let demoted: Vec<String> = report.demoted.iter().map(|d| d.id.to_string()).collect();
    assert_eq!(demoted, vec!["mm2", "aaaa", "bbbb"]);
    let month = store.text(MONTH).unwrap();
    for key in ["mm2", "aaaa", "bbbb"] {
        assert!(month.contains(&format!("^{key}")), "^{key} was deleted: {month}");
    }
    assert_eq!(report.notes.len(), 3, "{:?}", report.notes);
    assert!(report.notes.iter().all(|n| n.contains("parent cycle")));
}

/// §6.3 "stamps accumulate: `W36,W37`" — the history lives on the archive
/// copy under `# Demoted`, which the live week line knows nothing about.
#[test]
fn a_week_close_keeps_the_stamps_already_on_the_archive_copy() {
    let (_dir, store) = plan();
    let old = line_of(&store, MONTH, "m2").unwrap();
    store
        .write_line_in(
            Some(MONTH),
            &id("m2"),
            &old.replace("demoted:W37", "demoted:W35,W36"),
        )
        .unwrap();

    let report = run_close_week(&store);
    let m2 = report.demoted.iter().find(|d| d.id == id("m2")).unwrap();
    assert_eq!(
        m2.stamps,
        vec![Stamp::Week(35), Stamp::Week(36), Stamp::Week(37)]
    );
    assert_eq!(
        line_of(&store, MONTH, "m2").unwrap(),
        "- [-] 4 6b Rollback path passes tests   @O2 est:6b demoted:W35,W36,W37 ^m2"
    );
    // Three stamps is a cut proposal for `/plan-month` (§6.3, §11) …
    assert!(
        report
            .notes
            .iter()
            .any(|n| n.contains("^m2") && n.contains("3 demotion stamps")),
        "{:?}",
        report.notes
    );
    // … and the churn monitor sees it.
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let churned: Vec<Id> = churn(&tree, 2).into_iter().map(|(i, _)| i).collect();
    assert_eq!(churned, vec![id("m2")]);
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

/// The item lines of a file, headings and blank lines dropped.
fn item_lines(text: &str) -> Vec<&str> {
    text.lines().filter(|l| l.trim_start().starts_with("- [")).collect()
}

/// The whole tree after one `close_month(month, drops)` on a fresh fixture.
fn month_closed_once(drops: &[Id]) -> BTreeMap<String, String> {
    let (_dir, store) = plan();
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:00:00-05:00"));
    close_month(&cx, YearMonth::new(2026, 9), drops).unwrap();
    tree_text(&store)
}

#[test]
fn a_drop_still_lands_after_the_close_already_carried_the_line() {
    // §6.3's month close auto-runs on the first command after the month ends
    // (`Ctx::load` → `auto_close`) with no drop list, so by the time anyone
    // types `tm close month --drop ^id` the carry has usually happened and
    // the line is in the *next* month's file. An explicit `--drop` is never
    // discarded: the line comes back and is dropped, leaving exactly the tree
    // the one-shot close would have left.
    let want = month_closed_once(&[id("O3")]);

    let (_dir, store) = plan();
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:00:00-05:00"));
    close_month(&cx, YearMonth::new(2026, 9), &[]).unwrap();
    assert!(line_of(&store, NEXT_MONTH, "O3").is_some(), "carried first");

    // The snapshot is stale after a close; re-read, as `auto_close` does.
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:01:00-05:00"));
    let report = close_month(&cx, YearMonth::new(2026, 9), &[id("O3")]).unwrap();

    assert_eq!(report.dropped, vec![id("O3")]);
    assert!(report.moved.is_empty(), "{:?}", report.moved);
    assert!(line_of(&store, NEXT_MONTH, "O3").is_none(), "pulled back");
    assert_eq!(
        line_of(&store, MONTH, "O3").unwrap(),
        "- [~] 2 !3 Winter course selection + admin done        ^O3"
    );
    assert_eq!(tree_text(&store), want, "the two orders converge");

    // The report of the two runs together says what the tree says.
    let mut merged = report;
    merged.absorb(CloseReport {
        period: Some(Period::Month),
        key: "2026-09".to_string(),
        moved: vec![
            Moved { id: id("O1"), from: MONTH.into(), to: NEXT_MONTH.into() },
            Moved { id: id("O3"), from: MONTH.into(), to: NEXT_MONTH.into() },
        ],
        ..CloseReport::default()
    });
    let moved: Vec<String> = merged.moved.iter().map(|m| m.id.to_string()).collect();
    assert_eq!(moved, vec!["O1"], "the carry the drop undid is not reported");
    assert_eq!(merged.dropped, vec![id("O3")]);
}

#[test]
fn a_demoted_line_can_be_dropped_after_it_carried() {
    // The same, for a `# Demoted` line: it goes back into `# Demoted`.
    let want = month_closed_once(&[id("m2")]);

    let (_dir, store) = plan();
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:00:00-05:00"));
    close_month(&cx, YearMonth::new(2026, 9), &[]).unwrap();

    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:01:00-05:00"));
    let report = close_month(&cx, YearMonth::new(2026, 9), &[id("m2")]).unwrap();

    assert_eq!(report.dropped, vec![id("m2")]);
    assert!(report.demoted.is_empty(), "a dropped line is not carried");
    assert!(line_of(&store, NEXT_MONTH, "m2").is_none());

    // The two orders converge on the same lines. (The carry-then-pull-back
    // leaves the `# Demoted` heading it created behind in the next month —
    // an empty section, like the ones a close leaves in the month it just
    // emptied.)
    let after = tree_text(&store);
    for (path, want_text) in &want {
        assert_eq!(
            item_lines(after.get(path).unwrap_or(&String::new())),
            item_lines(want_text),
            "{path}"
        );
    }
    assert_eq!(
        text(&store, MONTH),
        want[MONTH],
        "the closed month is byte-identical either way"
    );
}

/// A `--drop` names an item, and the line the close finds for it is not
/// always the item: §4.3's example tree ships `^m2` twice — live in
/// `week/2026-W37` and as the `[-]` archive copy under
/// `month/2026-09#Demoted`, §6.3's one sanctioned pair — so the close meets
/// the copy. Marking *that* line `[~]` left the item live and turned the
/// record into a second **live** line (`tree::is_archive_copy` is a state
/// test, so a `[~]` copy is no longer one), which is a `dup-id`: two
/// commands from `tm init --example` and `tm check` exits 2. §4.1's ids are
/// global and `tree::record_rank` makes the live line the item, so the `[~]`
/// belongs there and the record stays `[-]`.
#[test]
fn dropping_an_id_that_resolves_to_an_archive_copy_marks_the_live_line() {
    const LIVE: &str = "- [~] 4 6b Rollback path passes tests   @O2 ^m2";
    const RECORD: &str = "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2";

    let (_dir, store) = plan();
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:00:00-05:00"));
    let report = close_month(&cx, YearMonth::new(2026, 9), &[id("m2")]).unwrap();

    assert_eq!(report.dropped, vec![id("m2")]);
    assert_eq!(line_of(&store, WEEK, "m2").unwrap(), LIVE, "the item was dropped");
    assert_eq!(line_of(&store, MONTH, "m2").unwrap(), RECORD, "the record is left as it is");
    assert!(line_of(&store, NEXT_MONTH, "m2").is_none(), "a dropped line is not carried");
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    assert!(tree.duplicate_ids().is_empty(), "{:?}", tree.duplicate_ids());
    assert_eq!(tree.get(&id("m2")).unwrap().state, State::Dropped);

    // The same when the auto-close carried the record first and the `--drop`
    // pulls it back (§6.3 "idempotent"): the record returns to `# Demoted`
    // and the `[~]` is still on the item.
    let (_dir, store) = plan();
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:00:00-05:00"));
    close_month(&cx, YearMonth::new(2026, 9), &[]).unwrap();
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:01:00-05:00"));
    close_month(&cx, YearMonth::new(2026, 9), &[id("m2")]).unwrap();

    assert_eq!(line_of(&store, WEEK, "m2").unwrap(), LIVE);
    assert_eq!(line_of(&store, MONTH, "m2").unwrap(), RECORD);
    let files = store.read_tree().unwrap();
    assert!(
        files.tree().duplicate_ids().is_empty(),
        "{:?}",
        files.tree().duplicate_ids()
    );
}

#[test]
fn a_drop_that_cannot_be_honoured_fails_without_writing() {
    // A `--drop` that names nothing this close can act on is an error, not a
    // silent no-op — and it fails before the first write (§6.3 closes decide
    // from the snapshot, then apply).
    let (_dir, store) = plan();
    let before = tree_text(&store);
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:00:00-05:00"));

    let err = close_month(&cx, YearMonth::new(2026, 9), &[id("nope")]).unwrap_err();
    assert!(matches!(err, HorizonError::NotFound(ref i) if *i == id("nope")), "{err}");

    // An item that exists, but not in this month or where this close put it.
    let err = close_month(&cx, YearMonth::new(2026, 9), &[id("m1")]).unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("^m1"), "{msg}");
    assert!(msg.contains("tm drop"), "{msg}");

    assert_eq!(tree_text(&store), before, "nothing was written");
    assert_eq!(log_events(&store), Vec::new(), "nothing was logged");
}

#[test]
fn re_running_a_drop_that_already_landed_is_not_an_error() {
    // §6.3: "idempotent". `tm close month --drop ^O3` leaves `^O3` `[~]` in
    // the month it closed; typing the same command again closes the month
    // after that one (the auto-close has moved on), and `^O3` is in neither
    // that month's file nor the next. It is already in the state the drop
    // asked for, so the second run reports it and does nothing — it does not
    // fail the whole close.
    let (_dir, store) = plan();
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:00:00-05:00"));
    close_month(&cx, YearMonth::new(2026, 9), &[id("O3")]).unwrap();
    let dropped = line_of(&store, MONTH, "O3").unwrap();
    assert!(dropped.starts_with("- [~] "), "{dropped}");

    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-11-01T08:00:00-05:00"));
    let before = tree_text(&store);
    let events = log_events(&store);
    let report = close_month(&cx, YearMonth::new(2026, 10), &[id("O3")]).unwrap();

    assert_eq!(report.dropped, vec![id("O3")], "the drop is reported as done");
    assert_eq!(line_of(&store, MONTH, "O3").unwrap(), dropped, "left as it was");
    assert!(line_of(&store, NEXT_MONTH, "O3").is_none());
    assert_eq!(
        tree_text(&store).get(MONTH),
        before.get(MONTH),
        "an already-dropped id writes nothing"
    );
    let new_events = log_events(&store)[events.len()..].to_vec();
    assert!(
        !new_events.iter().any(|(ev, _)| ev == "drop"),
        "nothing happened to ^O3: {new_events:?}"
    );

    // The error is still there for an id this close cannot honour: `^m1` is
    // a live week line, not something the month close dropped.
    let err = close_month(&cx, YearMonth::new(2026, 10), &[id("m1")]).unwrap_err();
    assert!(err.to_string().contains("tm drop"), "{err}");
    let err = close_month(&cx, YearMonth::new(2026, 10), &[id("nope")]).unwrap_err();
    assert!(matches!(err, HorizonError::NotFound(ref i) if *i == id("nope")), "{err}");
}

/// §6.3's week close writes `est:` = remaining onto the archive copy and
/// never onto the line it archives, dropped children folded in ("their
/// remaining is folded into the parent's `est:`", and their lines leave the
/// week file) — so the copy is the only line in the tree that still knows
/// what that demotion measured. A close catching up in a *newer* month took
/// the copy's `demoted:` stamps and deleted its line, and the remaining went
/// with it: `^s1`, demoted in September carrying the 4b of children the
/// close dropped, was demoted again in October with no `est:` at all. §0
/// principle 6 is "demotion, not deletion".
#[test]
fn a_second_demotion_a_month_later_keeps_what_the_first_one_measured() {
    let (_dir, store) = plan();
    // A milestone with no estimate of its own and two 2b children: §6.4's
    // rollup makes it worth 4b, and every one of those minutes is on a line
    // the demotion is about to delete.
    for line in [
        "- [ ] 4 Ship the thing @O2 ^s1",
        "- [ ] 3 2b Draft it @s1 ^s2",
        "- [ ] 3 2b Review it @s1 ^s3",
    ] {
        store.insert_line(WEEK, Some("Milestones"), line).unwrap();
    }

    // September's close: `^s2`/`^s3` go, their 4b folded into the copy.
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-14T09:00:00-05:00"));
    close_week(&cx, IsoWeek::new(2026, 37)).unwrap();
    assert_eq!(
        line_of(&store, MONTH, "s1").unwrap(),
        "- [-] 4 Ship the thing @O2 est:4b demoted:W37 ^s1"
    );
    for key in ["s2", "s3"] {
        assert!(line_of(&store, WEEK, key).is_none(), "^{key} is still in {WEEK}");
    }

    // The item comes back live the way §4.3's own example tree has it — a
    // `[ ]` week line beside its `[-]` archive copy. (`tm readopt` takes the
    // copy *with* it, which is `absorb_into_live`'s case, not this one.)
    store
        .insert_line(
            "week/2026-W41.md",
            Some("Milestones"),
            "- [ ] 4 Ship the thing @O2 ^s1",
        )
        .unwrap();

    // October's close writes into `month/2026-10` and deletes September's
    // record — the only line that knew about the 4b.
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-12T09:00:00-05:00"));
    close_week(&cx, IsoWeek::new(2026, 41)).unwrap();

    assert_eq!(
        line_of(&store, NEXT_MONTH, "s1").unwrap(),
        "- [-] 4 Ship the thing @O2 est:4b demoted:W37,W41 ^s1",
        "the remaining and both stamps are on the surviving line (§6.3, §0.6)"
    );
    assert!(
        line_of(&store, MONTH, "s1").is_none(),
        "September still has a copy: {}",
        text(&store, MONTH)
    );
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    assert!(tree.duplicate_ids().is_empty(), "{:?}", tree.duplicate_ids());
    // …and the tree reads that one record back: §11 counts two stamps for
    // the cut proposal, and §6.4's remaining is the 4b, not nothing.
    let s1 = tree.get(&id("s1")).unwrap();
    assert_eq!(s1.stamps.demoted, vec![Stamp::Week(37), Stamp::Week(41)]);
    assert_eq!(tree.remaining(&id("s1")), Some(240));
}

/// …but that floor is under a line that says nothing about its own size, not
/// over one that does. §4.1 makes the leading estimate the item's estimate —
/// what §13's `tm edit ^id est=…` writes — and `est:` the remaining that `tm
/// stop` and a partial `tm done` keep; all of them land on the live line,
/// never on the archive copy (`tree::record_rank`). So a user who re-scopes
/// an item downwards and lets it fall again got the earlier close's larger
/// number written straight back over the re-estimate.
#[test]
fn a_re_estimate_on_the_line_beats_what_an_earlier_close_measured() {
    /// A `plan-basic` whose `^s1` was demoted in W37 with 4b of children
    /// folded into the archive copy, then came back live in W41 as `line`.
    fn demoted_then_live_again(line: &str) -> (TempDir, FsStore) {
        let (dir, store) = plan();
        for l in [
            "- [ ] 4 Ship the thing @O2 ^s1",
            "- [ ] 3 2b Draft it @s1 ^s2",
            "- [ ] 3 2b Review it @s1 ^s3",
        ] {
            store.insert_line(WEEK, Some("Milestones"), l).unwrap();
        }
        let files = store.read_tree().unwrap();
        let tree = files.tree();
        let cx = Ctx::new(&store, &files, &tree, at("2026-09-14T09:00:00-05:00"));
        close_week(&cx, IsoWeek::new(2026, 37)).unwrap();
        assert_eq!(
            line_of(&store, MONTH, "s1").unwrap(),
            "- [-] 4 Ship the thing @O2 est:4b demoted:W37 ^s1",
            "the 4b of children the September close dropped"
        );
        store
            .insert_line("week/2026-W41.md", Some("Milestones"), line)
            .unwrap();
        (dir, store)
    }

    /// The `est:` the October close writes onto the new archive copy.
    fn demote_again(store: &FsStore) -> String {
        let files = store.read_tree().unwrap();
        let tree = files.tree();
        let cx = Ctx::new(store, &files, &tree, at("2026-10-12T09:00:00-05:00"));
        close_week(&cx, IsoWeek::new(2026, 41)).unwrap();
        line_of(store, NEXT_MONTH, "s1").unwrap()
    }

    // `tm edit ^s1 est=1b` cut it to one block: that is the item's estimate
    // now, and the demotion records it rather than September's measurement.
    let (_dir, store) = demoted_then_live_again("- [ ] 4 1b Ship the thing @O2 ^s1");
    assert_eq!(
        demote_again(&store),
        "- [-] 4 1b Ship the thing @O2 est:1b demoted:W37,W41 ^s1",
        "the user's re-estimate, not the 4b"
    );

    // Raising it works the same way — the line's own number is the answer,
    // in either direction.
    let (_dir, store) = demoted_then_live_again("- [ ] 4 8b Ship the thing @O2 ^s1");
    assert_eq!(
        demote_again(&store),
        "- [-] 4 8b Ship the thing @O2 est:8b demoted:W37,W41 ^s1"
    );

    // And a line that states no estimate of its own still gets the floor:
    // there is nothing of the user's to undo, and §0 principle 6 says the
    // work September folded in does not leave the tree.
    let (_dir, store) = demoted_then_live_again("- [ ] 4 Ship the thing @O2 ^s1");
    assert_eq!(
        demote_again(&store),
        "- [-] 4 Ship the thing @O2 est:4b demoted:W37,W41 ^s1",
        "what the first close measured survives an untouched line"
    );
}

/// A tree that arrived with two `# Demoted` copies of one id — from another
/// writer (§1.3), or from a `tm` that used to write them — is not carried
/// forward twice for ever: the month close folds the second into the first,
/// stamps and all (§6.3 "`demoted: [W36,W37]`" on one line).
#[test]
fn a_month_close_never_carries_an_id_a_file_already_has() {
    let (_dir, store) = plan();
    let extra = "- [-] 4 6b Rollback path passes tests   @O2 est:6b demoted:W36 ^m2";
    let month = format!("{}{extra}\n", text(&store, MONTH));
    store.write_file(MONTH, &month).unwrap();

    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-10-01T08:00:00-05:00"));
    let report = close_month(&cx, YearMonth::new(2026, 9), &[]).unwrap();

    assert_eq!(
        text(&store, NEXT_MONTH).matches("^m2").count(),
        1,
        "{}",
        text(&store, NEXT_MONTH)
    );
    // The stamps of both copies, each once, on the line that survived — the
    // record §6.3 keeps, not two of them. The order is the order the two
    // lines were read in (the carried copy's first): a `Stamp` is `W36` with
    // no year, so there is no age to sort them by.
    assert_eq!(
        line_of(&store, NEXT_MONTH, "m2").unwrap(),
        "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W36,W37 ^m2"
    );
    assert!(line_of(&store, MONTH, "m2").is_none(), "{}", text(&store, MONTH));
    assert!(
        report.notes.iter().any(|n| n.contains("^m2") && n.contains("merged")),
        "{:?}",
        report.notes
    );
    // §10.1 records every state change, and this close moved *two* records
    // out of the month that closed: the first `^m2` line by the ordinary
    // carry, the second by the fold. Both log the carry's own event, so `tm
    // log --item ^m2` and `tm undo` see the fold like any other carried
    // line. It has to be counted rather than looked for: the ordinary carry
    // logs one `move` for this id whatever the fold does, so `contains` is
    // an assertion the fold cannot fail.
    let events = log_events(&store);
    let moves = events.iter().filter(|(ev, i)| ev == "move" && i == "m2").count();
    assert_eq!(moves, 2, "the fold logged nothing: {events:?}");
    let files = store.read_tree().unwrap();
    assert!(
        files.tree().duplicate_ids().is_empty(),
        "{:?}",
        files.tree().duplicate_ids()
    );
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
    assert_eq!(once, vec![id("m1"), id("m2"), id("m3"), id("m4")]);
    assert!(churn(&tree, 2).is_empty());
}

// The fork-point `auto_close` tests (`auto_close_runs_each_period_once`,
// `pending_closes_names_what_auto_close_would_run`,
// `auto_close_without_history_catches_up_over_the_window`,
// `auto_close_catches_up_on_every_skipped_period`,
// `auto_close_catch_up_is_capped`, `a_catch_up_sweep_leaves_one_archive_copy_per_id`)
// were deleted with the function at stage 4
// step 6: the shipped automatic close is one kernel `autoClose` call per
// command, tested through the binary in `tm/tests/cli_close_kernel.rs`.
