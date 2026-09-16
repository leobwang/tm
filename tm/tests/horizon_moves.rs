//! `horizon.rs` single-item verbs (§6.3, §13): `tm move`, `tm demote`,
//! `tm readopt`, `tm drop`, `tm rank` on temp copies of
//! `tm-core/tests/fixtures/plan-basic`.
//!
//! The invariant these tests are really about: a line that crosses a horizon
//! crosses it **byte for byte**, apart from the tokens the verb is defined to
//! change (the state, `est:`, `demoted:`).

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use chrono::{DateTime, FixedOffset};
use tempfile::TempDir;
use tm_core::horizon::{demote, drop_item, move_item, rank, readopt, Ctx, HorizonError};
use tm_core::model::{Horizon, Id, IsoWeek, Stamp, State, YearMonth};
use tm_core::store::{FsStore, MemStore, PlanFiles, Store};
use tm_core::tree::Tree;

const WEEK: &str = "week/2026-W37.md";
const NEXT_WEEK: &str = "week/2026-W38.md";
const MONTH: &str = "month/2026-09.md";
const BACKLOG: &str = "backlog.md";

// ---------------------------------------------------------------------------
// Fixture plumbing
// ---------------------------------------------------------------------------

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-core/tests/fixtures/plan-basic")
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

fn plan() -> (TempDir, FsStore) {
    let dir = TempDir::new().unwrap();
    let root = dir.path().join("plan");
    copy_dir(&fixture_dir(), &root);
    (dir, FsStore::new(root))
}

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

fn id(s: &str) -> Id {
    Id::new(s)
}

fn day(s: &str) -> chrono::NaiveDate {
    s.parse().unwrap()
}

fn line_of(store: &FsStore, rel: &str, id: &str) -> Option<String> {
    let needle = format!("^{id}");
    text(store, rel)
        .lines()
        .find(|l| l.split_whitespace().any(|w| w == needle))
        .map(str::to_string)
}

fn snapshot(store: &FsStore) -> (PlanFiles, Tree) {
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    (files, tree)
}

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

/// Every file except `changed` is byte-identical — and none of them is gone:
/// a verb that deleted a whole file would otherwise slip through the loop
/// over `after`.
fn only_changed(before: &BTreeMap<String, String>, after: &BTreeMap<String, String>, changed: &[&str]) {
    for (path, text) in after {
        if changed.contains(&path.as_str()) {
            continue;
        }
        assert_eq!(before.get(path), Some(text), "{path} changed unexpectedly");
    }
    for path in before.keys() {
        assert!(after.contains_key(path), "{path} disappeared");
    }
}

// ---------------------------------------------------------------------------
// move (§13 `tm move ^id <backlog|month|week|day>`)
// ---------------------------------------------------------------------------

#[test]
fn move_between_backlog_and_week_preserves_the_line_bytes() {
    let (_dir, store) = plan();
    let before = tree_text(&store);
    let original = line_of(&store, BACKLOG, "a1").unwrap();

    // backlog -> week
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-08T09:00:00-05:00"));
    let moved = move_item(&cx, &id("a1"), &Horizon::Week(IsoWeek::new(2026, 37)), None).unwrap();
    assert_eq!(moved.from, BACKLOG);
    assert_eq!(moved.to, WEEK);
    assert_eq!(line_of(&store, WEEK, "a1").as_deref(), Some(original.as_str()));
    assert!(line_of(&store, BACKLOG, "a1").is_none());

    // … and back again, into a named section.
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-08T09:05:00-05:00"));
    move_item(&cx, &id("a1"), &Horizon::Backlog, Some("Untied")).unwrap();
    assert_eq!(
        line_of(&store, BACKLOG, "a1").as_deref(),
        Some(original.as_str())
    );

    // The round trip is byte-exact everywhere; in the backlog the line comes
    // back at the end of `# Untied` (a move appends), so the file holds the
    // same lines in a different order and nothing else changed.
    let after = tree_text(&store);
    only_changed(&before, &after, &[BACKLOG]);
    let mut was: Vec<&str> = before.get(BACKLOG).unwrap().lines().collect();
    let mut is: Vec<&str> = after.get(BACKLOG).unwrap().lines().collect();
    assert_ne!(was, is, "a1 moved to the end of its section");
    was.sort_unstable();
    is.sort_unstable();
    assert_eq!(was, is, "no line changed a byte");
    assert_eq!(
        log_events(&store),
        vec![
            ("move".to_string(), "a1".to_string()),
            ("move".to_string(), "a1".to_string()),
        ]
    );
}

#[test]
fn move_creates_the_target_file_with_its_front_matter() {
    let (_dir, store) = plan();
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-08T09:00:00-05:00"));
    move_item(&cx, &id("a3"), &Horizon::Week(IsoWeek::new(2026, 38)), None).unwrap();
    assert_eq!(
        text(&store, NEXT_WEEK),
        "---\nweek: 2026-W38\nwindow: 2026-09-14..2026-09-20\n---\n- [ ] 1 Pick up package  win:2026-09-07T09:00/21:00 dur:20m ^a3\n"
    );
}

/// §13's `tm move ^id <horizon>` takes no section, and three section names
/// change what a line *means* (§4.2). A move with no section keeps clear of
/// them: into a day it goes to `# Pinned` (§6.2 — the only day section the
/// planner reads), into a month to the outcomes rather than `# Demoted`
/// (§6.3), into the backlog outside `## series:` (§5.4 — only the head of a
/// series is active).
#[test]
fn a_move_with_no_section_stays_out_of_the_loaded_ones() {
    let (_dir, store) = plan();

    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-07T09:00:00-05:00"));
    move_item(&cx, &id("t4"), &Horizon::Day(day("2026-09-07")), None).unwrap();
    let (files, tree) = snapshot(&store);
    assert_eq!(
        files.find(&id("t4")).unwrap().src.section.as_deref(),
        Some("Pinned")
    );
    assert!(tree
        .day_candidate_ids(day("2026-09-07"), IsoWeek::new(2026, 37))
        .contains(&id("t4")));

    let cx = Ctx::new(&store, &files, &tree, at("2026-09-07T09:05:00-05:00"));
    move_item(&cx, &id("t5"), &Horizon::Month(YearMonth::new(2026, 9)), None).unwrap();
    let (files, tree) = snapshot(&store);
    assert_eq!(
        files.find(&id("t5")).unwrap().src.section.as_deref(),
        Some("Outcomes")
    );

    let cx = Ctx::new(&store, &files, &tree, at("2026-09-07T09:10:00-05:00"));
    move_item(&cx, &id("t1"), &Horizon::Backlog, None).unwrap();
    let (files, _tree) = snapshot(&store);
    let t1 = files.find(&id("t1")).unwrap();
    assert_eq!(t1.series, None, "^t1 joined the series it was appended after");
    assert_ne!(t1.src.section.as_deref(), Some("series:cell-bio"));
}

/// A target whose every section is loaded gets the horizon's canonical one
/// instead — created at the end of the file by the store.
#[test]
fn a_move_creates_the_canonical_section_when_every_section_is_loaded() {
    let store = MemStore::new()
        .with_file(
            BACKLOG,
            "## series:cell-bio\n- [ ] 4 4b Cell Biology vol. 2 ^c2\n",
        )
        .with_file(
            WEEK,
            "---\nweek: 2026-W37\n---\n# Tasks\n- [ ] 3 1b Something ^ss1\n",
        );
    let files = store.read_tree().unwrap();
    let tree = files.tree();
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-08T09:00:00-05:00"));
    move_item(&cx, &id("ss1"), &Horizon::Backlog, None).unwrap();

    let backlog = store.text(BACKLOG).unwrap();
    assert!(backlog.contains("# Untied\n- [ ] 3 1b Something ^ss1"), "{backlog}");
    let files = store.read_tree().unwrap();
    assert_eq!(files.find(&id("ss1")).unwrap().series, None);
}

#[test]
fn moving_a_missing_id_is_an_error_and_writes_nothing() {
    let (_dir, store) = plan();
    let before = tree_text(&store);
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-08T09:00:00-05:00"));
    let err = move_item(&cx, &id("zzzz"), &Horizon::Backlog, None).unwrap_err();
    assert!(matches!(err, HorizonError::NotFound(_)), "{err}");
    assert_eq!(before, tree_text(&store));
    assert!(!store.exists(".tm/log.jsonl"));
}

// ---------------------------------------------------------------------------
// demote / readopt (§6.3)
// ---------------------------------------------------------------------------

#[test]
fn demote_marks_the_week_line_and_copies_it_into_the_month() {
    let (_dir, store) = plan();
    let before = tree_text(&store);
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-10T18:00:00-05:00"));
    let out = demote(&cx, &id("m3")).unwrap();

    assert_eq!(out.est_min, 180);
    assert_eq!(out.stamps, vec![Stamp::Week(37)]);
    assert_eq!(
        line_of(&store, WEEK, "m3").unwrap(),
        "- [-] 5 3b Read ch.6                    @O1 ^m3"
    );
    assert_eq!(
        line_of(&store, MONTH, "m3").unwrap(),
        "- [-] 5 3b Read ch.6                    @O1 est:3b demoted:W37 ^m3"
    );
    only_changed(&before, &tree_text(&store), &[WEEK, MONTH]);
    assert_eq!(log_events(&store), vec![("demote".to_string(), "m3".to_string())]);

    // The demoted item now *is* the month copy, so demoting it again is
    // refused rather than making a copy of a copy.
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-10T18:05:00-05:00"));
    let err = demote(&cx, &id("m3")).unwrap_err();
    assert!(matches!(err, HorizonError::Horizon { .. }), "{err}");

    // Readopting it into the next week and demoting it again accumulates the
    // stamps on one line (§6.3 `W36,W37`).
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-14T09:00:00-05:00"));
    readopt(&cx, &id("m3"), None).unwrap();
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-20T18:00:00-05:00"));
    let out = demote(&cx, &id("m3")).unwrap();
    assert_eq!(out.stamps, vec![Stamp::Week(37), Stamp::Week(38)]);
    assert_eq!(
        text(&store, MONTH).matches("^m3").count(),
        1,
        "one archive copy only"
    );
    assert_eq!(
        line_of(&store, MONTH, "m3").unwrap(),
        "- [-] 5 3b Read ch.6                    @O1 est:3b demoted:W37,W38 ^m3"
    );
}

#[test]
fn demote_refuses_an_item_that_is_not_in_a_week_file() {
    let (_dir, store) = plan();
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-10T18:00:00-05:00"));
    let err = demote(&cx, &id("a1")).unwrap_err();
    assert!(matches!(err, HorizonError::Horizon { .. }), "{err}");
    assert!(!store.exists(".tm/log.jsonl"));
}

/// §4.1: ids are global, so the live line is the item and the `# Demoted`
/// copy is only the record — readopting into a week the live line is *not*
/// in moves that line and absorbs the copy, rather than carrying the copy
/// across and leaving `^m2` live in two week files.
#[test]
fn readopt_takes_the_demoted_copy_into_a_week_and_keeps_the_stamps() {
    let (_dir, store) = plan();
    let before = tree_text(&store);
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-14T09:00:00-05:00"));
    let moved = readopt(
        &cx,
        &id("m2"),
        Some(&Horizon::Week(IsoWeek::new(2026, 38))),
    )
    .unwrap();

    assert_eq!(moved.from, MONTH);
    assert_eq!(moved.to, NEXT_WEEK);
    // The live line itself, byte for byte, plus the copy's stamp and the
    // remaining §6.3's close recorded on the copy (`est:` = remaining, the
    // number the demotion existed to keep — §0 principle 6).
    assert_eq!(
        text(&store, NEXT_WEEK),
        "---\nweek: 2026-W38\nwindow: 2026-09-14..2026-09-20\n---\n- [ ] 4 6b Rollback path passes tests   @O2 est:3b demoted:W37 ^m2\n"
    );
    // The month keeps its `# Demoted` heading, without the line.
    assert!(line_of(&store, MONTH, "m2").is_none());
    assert!(text(&store, MONTH).contains("# Demoted"));
    // … and W37 no longer carries it, so the id is on exactly one line.
    assert!(line_of(&store, WEEK, "m2").is_none());
    only_changed(&before, &tree_text(&store), &[MONTH, WEEK, NEXT_WEEK]);
    assert_eq!(log_events(&store), vec![("readopt".to_string(), "m2".to_string())]);

    // The tree resolves the readopted line, not the archive copy.
    let (files, tree) = snapshot(&store);
    assert!(tree.duplicate_ids().is_empty(), "{:?}", tree.duplicate_ids());
    assert_eq!(
        files.items().filter(|i| Tree::key_of(i) == id("m2")).count(),
        1
    );
    let m2 = tree.get(&id("m2")).unwrap();
    assert_eq!(m2.state, State::Todo);
    assert_eq!(m2.stamps.demoted, vec![Stamp::Week(37)]);
    assert_eq!(m2.horizon, Horizon::Week(IsoWeek::new(2026, 38)));
}

/// §6.3: readopt is the verb for a *demoted* line. An id with no demoted
/// line anywhere has nothing to readopt, so the verb refuses instead of
/// quietly acting as `tm move` and writing a `readopt` event §11 counts as
/// demotion churn.
#[test]
fn readopt_refuses_an_item_that_was_never_demoted() {
    let (_dir, store) = plan();
    let before = tree_text(&store);
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-14T09:00:00-05:00"));
    let err = readopt(&cx, &id("t1"), None).unwrap_err();
    assert!(matches!(err, HorizonError::Horizon { .. }), "{err}");
    assert!(err.to_string().contains("not demoted"), "{err}");
    assert_eq!(before, tree_text(&store));
    assert!(!store.exists(".tm/log.jsonl"));
}

#[test]
fn readopt_defaults_to_the_current_week() {
    let (_dir, store) = plan();
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-16T09:00:00-05:00"));
    let moved = readopt(&cx, &id("m2"), None).unwrap();
    assert_eq!(moved.to, NEXT_WEEK); // 2026-09-16 is in W38
    assert!(line_of(&store, NEXT_WEEK, "m2").unwrap().starts_with("- [ ] "));
}

/// §4.1: ids are global. `tm readopt ^m2` into the week that already holds a
/// live `^m2` — the shape §4.3's own example tree ships, a `[ ]` milestone
/// beside its `[-]` archive copy under `month/…# Demoted` — used to move the
/// copy in anyway, leaving the id twice in one file and `tm check` at exit 2.
#[test]
fn readopt_into_a_week_that_already_has_the_item_absorbs_the_archive_copy() {
    let (_dir, store) = plan();
    let before_week = text(&store, WEEK);
    let (files, tree) = snapshot(&store);
    // 2026-09-07 is in W37, the week the live `^m2` is in.
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-07T09:00:00-05:00"));
    let moved = readopt(&cx, &id("m2"), None).unwrap();

    assert_eq!(moved.from, MONTH);
    assert_eq!(moved.to, WEEK);
    // One `^m2` in the week …
    assert_eq!(text(&store, WEEK).matches("^m2").count(), 1);
    // … carrying the stamp the archive copy held (§11's demotion churn).
    let line = line_of(&store, WEEK, "m2").unwrap();
    assert!(line.starts_with("- [ ] "), "{line}");
    assert!(line.contains("demoted:W37"), "{line}");
    // … and the archive copy is gone, its heading kept.
    assert!(line_of(&store, MONTH, "m2").is_none());
    assert!(text(&store, MONTH).contains("# Demoted"));
    assert_eq!(log_events(&store), vec![("readopt".to_string(), "m2".to_string())]);

    // The rest of the week file is untouched.
    let after = text(&store, WEEK);
    for line in before_week.lines().filter(|l| !l.contains("^m2")) {
        assert!(after.contains(line), "lost `{line}`");
    }

    // And the tree has one node for the id: `tm check` is clean.
    let (files, tree) = snapshot(&store);
    assert_eq!(
        files.items().filter(|i| Tree::key_of(i) == id("m2")).count(),
        1
    );
    assert_eq!(tree.get(&id("m2")).unwrap().state, State::Todo);
    assert!(tree.problems().is_empty(), "{:?}", tree.problems());
}

// ---------------------------------------------------------------------------
// drop / rank (§13)
// ---------------------------------------------------------------------------

#[test]
fn drop_sets_the_state_where_the_line_lives() {
    let (_dir, store) = plan();
    let before = tree_text(&store);
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-08T09:00:00-05:00"));
    let line = drop_item(&cx, &id("t5")).unwrap();
    assert_eq!(line, "- [~] 3 1b Review the drafts            @m2 after:^t4 ^t5");
    assert_eq!(line_of(&store, WEEK, "t5").as_deref(), Some(line.as_str()));
    only_changed(&before, &tree_text(&store), &[WEEK]);
    assert_eq!(log_events(&store), vec![("drop".to_string(), "t5".to_string())]);
}

/// §1.3: writers address items by id, and the line a reader resolves an id to
/// must be the line a writer rewrites.
///
/// After a demotion the id names two `[-]` lines — the archive in the week
/// file and the stamped copy under `month/…# Demoted`. `Tree::get` ranked the
/// most-stamped copy as the record while `Store::write_line` took the first
/// match outside a `# Demoted` section, so `tm edit ^id` read the month copy
/// and wrote its text into the week line, which then gained the month copy's
/// `est:` and `demoted:` tokens while the record itself stayed unchanged.
#[test]
fn a_demoted_id_reads_and_writes_the_same_copy() {
    let (_dir, store) = plan();
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-08T09:00:00-05:00"));
    demote(&cx, &id("m1")).unwrap();

    let week_before = line_of(&store, WEEK, "m1").unwrap();
    let month_before = line_of(&store, MONTH, "m1").unwrap();
    assert!(week_before.starts_with("- [-] "), "{week_before}");
    assert!(month_before.contains("demoted:W37"), "{month_before}");

    // The record — what a reader resolves `^m1` to.
    let (files, tree) = snapshot(&store);
    let record = tree.get(&id("m1")).unwrap().line_text();
    assert_eq!(record, month_before, "the month copy is the record");

    // An id-addressed write — `Store::write_line`, with no file named, which
    // is what every `tm edit ^id` goes through — rewrites *that* line.
    let edited = record.replace("- [-] 5 ", "- [-] 2 ");
    assert_ne!(edited, record);
    store.write_line(&id("m1"), &edited).unwrap();
    assert_eq!(
        line_of(&store, WEEK, "m1").as_deref(),
        Some(week_before.as_str()),
        "the week archive was rewritten from the other copy"
    );
    assert_eq!(line_of(&store, MONTH, "m1").as_deref(), Some(edited.as_str()));
    let _ = &files;
}

#[test]
fn rank_moves_a_line_inside_its_own_section() {
    let (_dir, store) = plan();
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-08T09:00:00-05:00"));

    // `# Tasks` is t1 t3 t4 t5; rank t5 first.
    assert!(rank(&cx, &id("t5"), 1).unwrap());
    let tasks: Vec<String> = text(&store, WEEK)
        .lines()
        .skip_while(|l| !l.starts_with("# Tasks"))
        .skip(1)
        .filter(|l| l.starts_with("- "))
        .map(str::to_string)
        .collect();
    assert!(tasks[0].ends_with("^t5"), "{tasks:?}");
    assert!(tasks[1].ends_with("^t1"), "{tasks:?}");
    assert_eq!(tasks.len(), 4);

    // Milestones are untouched: rank never leaves the section.
    assert!(line_of(&store, WEEK, "m1").unwrap().ends_with("^m1"));

    // Ranking it where it already is writes nothing; a rank past the end
    // clamps to the last position.
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-08T09:01:00-05:00"));
    assert!(!rank(&cx, &id("t5"), 1).unwrap());
    assert!(rank(&cx, &id("t5"), 99).unwrap());
    let last = text(&store, WEEK)
        .lines()
        .filter(|l| l.starts_with("- "))
        .last()
        .unwrap()
        .to_string();
    assert!(last.ends_with("^t5"), "{last}");
}

// ---------------------------------------------------------------------------
// The §6.3 sequence end to end
// ---------------------------------------------------------------------------

#[test]
fn demote_then_readopt_leaves_one_live_line_and_one_archive() {
    let (_dir, store) = plan();
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-13T18:00:00-05:00"));
    demote(&cx, &id("m1")).unwrap();

    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-14T09:00:00-05:00"));
    readopt(&cx, &id("m1"), None).unwrap();

    let (_files, tree) = snapshot(&store);
    assert!(tree.duplicate_ids().is_empty(), "{:?}", tree.duplicate_ids());
    let m1 = tree.get(&id("m1")).unwrap();
    assert_eq!(m1.state, State::Todo);
    assert_eq!(m1.horizon, Horizon::Week(IsoWeek::new(2026, 38)));
    assert_eq!(m1.stamps.demoted, vec![Stamp::Week(37)]);
    assert_eq!(m1.est.unwrap().as_minutes(), 360);
    // The archived `[-]` line stays in the closed week; the month copy left.
    assert_eq!(
        line_of(&store, WEEK, "m1").unwrap(),
        "- [-] 5 6b Finish ch.5 exercises        @O1 ^m1"
    );
    assert!(line_of(&store, MONTH, "m1").is_none());
    assert_eq!(
        tree.demoted_copies()
            .iter()
            .filter(|i| i.id == id("m1"))
            .count(),
        1
    );
    assert_eq!(
        tree.month_items(YearMonth::new(2026, 9))
            .iter()
            .filter(|i| i.id == id("m1"))
            .count(),
        0
    );
}

/// §6.3 records the remaining on the archive copy (`est:` = remaining) — the
/// number the whole demotion exists to keep (§0 principle 6, "demotion, not
/// deletion"). A readopt that *absorbs* the copy into a live line (§4.1: the
/// id can only be on one live line) must therefore carry that estimate onto
/// the line that survives, together with the `demoted:` stamps; throwing the
/// copy away with its `est:` silently restores the stale pre-demotion
/// estimate.
#[test]
fn a_demote_readopt_round_trip_keeps_the_remaining_and_the_stamps() {
    let (_dir, store) = plan();
    // The tree §4.3 ships: a live `[ ] 4 6b … ^m2` in W37 and the archive
    // copy `[-] … est:3b demoted:W37 ^m2` under `month/2026-09#Demoted`,
    // which says 3b of the 6b are left.
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-14T09:00:00-05:00"));
    readopt(&cx, &id("m2"), Some(&Horizon::Week(IsoWeek::new(2026, 38)))).unwrap();

    assert_eq!(
        line_of(&store, NEXT_WEEK, "m2").unwrap(),
        "- [ ] 4 6b Rollback path passes tests   @O2 est:3b demoted:W37 ^m2"
    );
    assert!(line_of(&store, MONTH, "m2").is_none(), "the copy was absorbed");
    let (_files, tree) = snapshot(&store);
    assert!(tree.duplicate_ids().is_empty(), "{:?}", tree.duplicate_ids());
    assert_eq!(
        tree.remaining(&id("m2")),
        Some(180),
        "the readopted line is worth what the demotion said was left"
    );

    // Demoting it again writes one copy carrying that same remaining and
    // both stamps (§6.3 `demoted: [W36,W37]` accumulate on one line).
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-20T18:00:00-05:00"));
    let out = demote(&cx, &id("m2")).unwrap();
    assert_eq!(out.est_min, 180);
    assert_eq!(out.stamps, vec![Stamp::Week(37), Stamp::Week(38)]);
    assert_eq!(
        line_of(&store, MONTH, "m2").unwrap(),
        "- [-] 4 6b Rollback path passes tests   @O2 est:3b demoted:W37,W38 ^m2"
    );

    // And readopting that copy — no live line left to absorb it into — keeps
    // both across the move.
    let (files, tree) = snapshot(&store);
    let cx = Ctx::new(&store, &files, &tree, at("2026-09-21T09:00:00-05:00"));
    readopt(&cx, &id("m2"), None).unwrap();
    assert_eq!(
        line_of(&store, "week/2026-W39.md", "m2").unwrap(),
        "- [ ] 4 6b Rollback path passes tests   @O2 est:3b demoted:W37,W38 ^m2"
    );
    let (_files, tree) = snapshot(&store);
    assert!(tree.duplicate_ids().is_empty(), "{:?}", tree.duplicate_ids());
    assert_eq!(tree.remaining(&id("m2")), Some(180));
}
