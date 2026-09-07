//! `store.rs` against the filesystem: the §1.3 `write_line` guard (happy
//! path, the race that retries, the race that conflicts), generated sections
//! (§1.3), section appends and the id-addressed line moves — all on temp
//! copies of `tests/fixtures/plan-basic`, asserting that every byte outside
//! the edited line is untouched.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use tempfile::TempDir;
use tm_core::model::{Horizon, Id, IsoWeek};
use tm_core::store::{FsStore, MemStore, Store, StoreError};

const WEEK: &str = "week/2026-W37.md";
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
    let store = FsStore::new(&root);
    (dir, store)
}

/// Every file under `root`, `relative path -> text`.
fn tree_text(root: &Path) -> BTreeMap<String, String> {
    fn walk(root: &Path, dir: &Path, out: &mut BTreeMap<String, String>) {
        for entry in fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_dir() {
                walk(root, &path, out);
            } else {
                let rel = path
                    .strip_prefix(root)
                    .unwrap()
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect::<Vec<_>>()
                    .join("/");
                out.insert(rel, fs::read_to_string(&path).unwrap());
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(root, root, &mut out);
    out
}

/// Assert every file but `changed` is byte-identical, and that no temp file
/// was left behind by the atomic writes.
fn only_changed(before: &BTreeMap<String, String>, after: &BTreeMap<String, String>, changed: &[&str]) {
    for (rel, text) in before {
        if !changed.contains(&rel.as_str()) {
            assert_eq!(after.get(rel), Some(text), "{rel} should not have changed");
        }
    }
    for rel in after.keys() {
        assert!(
            before.contains_key(rel) || changed.contains(&rel.as_str()),
            "unexpected new file {rel}"
        );
        assert!(!rel.contains("tm-tmp"), "temp file left behind: {rel}");
    }
}

/// The one line of `text` ending in `^id`.
fn line_with(text: &str, id: &str) -> String {
    let token = format!("^{id}");
    text.lines()
        .find(|l| l.trim_end().ends_with(&token))
        .unwrap_or_else(|| panic!("no line carries {token}"))
        .to_string()
}

// ---------------------------------------------------------------------------
// Reading
// ---------------------------------------------------------------------------

#[test]
fn read_tree_is_ordered_and_skips_dot_directories() {
    let (dir, store) = plan();
    let root = dir.path().join("plan");
    fs::create_dir_all(root.join(".claude/skills/plan-week")).unwrap();
    fs::write(root.join(".claude/skills/plan-week/SKILL.md"), "# skill\n").unwrap();
    fs::create_dir_all(root.join(".tm")).unwrap();
    fs::write(root.join(".tm/state.json"), "{}\n").unwrap();
    fs::write(root.join("CLAUDE.md"), "# rules\n").unwrap();

    assert_eq!(
        store.list_files().unwrap(),
        [
            "month/2026-09.md",
            "week/2026-W37.md",
            BACKLOG,
            "routines.md",
            "optional.md",
            "calendar/2026-W37.md",
            DAY,
            "inbox.md",
        ]
    );

    let files = store.read_tree().unwrap();
    assert_eq!(files.config.tz.name(), "America/Chicago");
    assert_eq!(files.files.len(), 8);
    // Every file re-serializes byte-identically (grammar round trip through
    // the store).
    for f in &files.files {
        assert_eq!(f.to_text(), store.read_text(&f.path).unwrap(), "{}", f.path);
    }

    let loc = files.locate(&Id::new("t3")).unwrap();
    assert_eq!(files.files[loc.file].path, WEEK);
    assert_eq!(files.files[loc.file].lines[loc.line].item().unwrap().id, Id::new("t3"));
    assert_eq!(files.file_of(&Id::new("O1")), Some("month/2026-09.md"));
    assert_eq!(files.find(&Id::new("g1")).unwrap().title, "Meeting w/ host");
    // An id-less routine line is addressed by its title key.
    assert_eq!(files.file_of(&Id::new("lunch")), Some("routines.md"));
    assert!(files.ids().contains("t3"));
    assert!(files.tree().get(&Id::new("t3")).is_some());

    // The same tree read out of memory.
    let mem = MemStore::from_dir(&root).unwrap();
    assert_eq!(mem.list_files().unwrap(), store.list_files().unwrap());
    let mem_files = mem.read_tree().unwrap();
    assert_eq!(mem_files.files, files.files);
    assert!(mem.exists(".tm/state.json"), "MemStore::from_dir keeps .tm/ files");
}

// ---------------------------------------------------------------------------
// write_line (§1.3, M1 "write_line survives a concurrent edit")
// ---------------------------------------------------------------------------

#[test]
fn write_line_touches_one_line_and_no_other_byte() {
    let (dir, store) = plan();
    let root = dir.path().join("plan");
    let before = tree_text(&root);

    let old = line_with(&before[WEEK], "t3");
    let new = old.replacen("[>]", "[x]", 1);
    store.write_line(&Id::new("t3"), &new).unwrap();

    let after = tree_text(&root);
    assert_eq!(after[WEEK], before[WEEK].replacen(&old, &new, 1));
    only_changed(&before, &after, &[WEEK]);

    // Writing the same text again is a no-op.
    store.write_line(&Id::new("t3"), &new).unwrap();
    assert_eq!(tree_text(&root)[WEEK], after[WEEK]);

    // The replacement must stay one item line with the same id.
    for bad in [
        old.replacen("^t3", "^zz", 1),
        old.replacen(" ^t3", "", 1),
        format!("{new}\n{new}"),
        "just prose".to_string(),
    ] {
        let err = store.write_line(&Id::new("t3"), &bad).unwrap_err();
        assert!(matches!(err, StoreError::Parse { .. }), "{bad:?} -> {err}");
    }
    assert!(store.write_line(&Id::new("nope"), "- [ ] 3 x ^nope").unwrap_err().is_not_found());
    assert_eq!(tree_text(&root), after, "a refused write changes nothing");
}

/// A store whose before-write hook saves `texts[attempt]` over `root/rel`,
/// like an editor writing between our read and our write; `None` leaves the
/// file alone. `hits` counts the guarded attempts.
fn racing_store(root: &Path, rel: &str, texts: Vec<Option<String>>, hits: Arc<AtomicUsize>) -> FsStore {
    let path = root.join(rel);
    FsStore::new(root).with_before_write_hook(Box::new(move |touched, attempt| {
        hits.fetch_add(1, Ordering::SeqCst);
        if touched == path {
            if let Some(Some(text)) = texts.get(attempt) {
                fs::write(&path, text).unwrap();
            }
        }
    }))
}

#[test]
fn write_line_retries_once_after_a_concurrent_edit() {
    let (dir, _) = plan();
    let root = dir.path().join("plan");
    let before = tree_text(&root);

    // Someone else saves an edit to a *different* line of the same file.
    let their_old = line_with(&before[WEEK], "m1");
    let their_new = their_old.replacen("6b", "8b", 1);
    let their_file = before[WEEK].replacen(&their_old, &their_new, 1);

    let hits = Arc::new(AtomicUsize::new(0));
    let store = racing_store(&root, WEEK, vec![Some(their_file.clone()), None], Arc::clone(&hits));

    let our_old = line_with(&before[WEEK], "t3");
    let our_new = our_old.replacen("[>]", "[x]", 1);
    store.write_line(&Id::new("t3"), &our_new).unwrap();

    // The retry re-read their version and applied our line to it.
    let after = tree_text(&root);
    assert_eq!(after[WEEK], their_file.replacen(&our_old, &our_new, 1));
    assert_eq!(hits.load(Ordering::SeqCst), 2, "one guarded attempt, then the retry");
    only_changed(&before, &after, &[WEEK]);
}

#[test]
fn write_line_conflicts_when_the_race_repeats() {
    let (dir, _) = plan();
    let root = dir.path().join("plan");
    let before = tree_text(&root);

    // Both attempts are raced, each time on the very line we are writing.
    let their_old = line_with(&before[WEEK], "t3");
    let first = their_old.replacen("[>]", "[~]", 1);
    let second = their_old.replacen("[>]", "[?]", 1);
    let hits = Arc::new(AtomicUsize::new(0));
    let store = racing_store(
        &root,
        WEEK,
        vec![
            Some(before[WEEK].replacen(&their_old, &first, 1)),
            Some(before[WEEK].replacen(&their_old, &second, 1)),
        ],
        Arc::clone(&hits),
    );

    let our_new = their_old.replacen("[>]", "[x]", 1);
    let err = store.write_line(&Id::new("t3"), &our_new).unwrap_err();
    assert!(err.is_conflict());
    match err {
        StoreError::Conflict { id, file, ours, theirs } => {
            assert_eq!(id, Id::new("t3"));
            assert_eq!(file, WEEK);
            assert_eq!(ours, our_new);
            assert_eq!(theirs, second, "the conflict carries the line as it is now");
        }
        other => panic!("expected a conflict, got {other}"),
    }
    assert_eq!(hits.load(Ordering::SeqCst), 2);

    // Nothing of ours reached the disk; their last save stands.
    let after = tree_text(&root);
    assert_eq!(after[WEEK], before[WEEK].replacen(&their_old, &second, 1));
    only_changed(&before, &after, &[WEEK]);
}

#[test]
fn write_line_conflicts_when_the_other_writer_removes_the_line() {
    let (dir, _) = plan();
    let root = dir.path().join("plan");
    let before = tree_text(&root);

    let their_old = line_with(&before[WEEK], "t3");
    let without = before[WEEK].replacen(&format!("{their_old}\n"), "", 1);
    let hits = Arc::new(AtomicUsize::new(0));
    let store = racing_store(&root, WEEK, vec![Some(without.clone())], Arc::clone(&hits));

    let err = store
        .write_line(&Id::new("t3"), &their_old.replacen("[>]", "[x]", 1))
        .unwrap_err();
    match err {
        StoreError::Conflict { file, theirs, .. } => {
            assert_eq!(file, WEEK);
            assert!(theirs.is_empty(), "the line is gone, so `theirs` is empty");
        }
        other => panic!("expected a conflict, got {other}"),
    }
    assert_eq!(tree_text(&root)[WEEK], without);
    assert_eq!(hits.load(Ordering::SeqCst), 1);
}

// ---------------------------------------------------------------------------
// Generated sections (§1.3, §4.3)
// ---------------------------------------------------------------------------

/// `(before the start marker, the body, after the end marker)`.
fn split_generated<'a>(text: &'a str, start: &str, end: &str) -> (&'a str, &'a str, &'a str) {
    let (head, rest) = text.split_once(start).expect("start marker");
    let (body, tail) = rest.split_once(end).expect("end marker");
    (head, body, tail)
}

#[test]
fn replace_generated_keeps_every_byte_outside_the_markers() {
    let (dir, store) = plan();
    let root = dir.path().join("plan");
    let before = tree_text(&root);
    let start = "<!-- tm:plan start 10:42 -->";
    let end = "<!-- tm:plan end -->";
    let (head, old_body, tail) = split_generated(&before[DAY], start, end);
    assert!(old_body.contains("Exercises 5.3"));

    store
        .replace_generated(DAY, "plan", "07:00  5 p1 Read ch.6 §1–2\n08:00  ·   break 20m\n")
        .unwrap();

    let after = tree_text(&root);
    let (head2, body2, tail2) = split_generated(&after[DAY], start, end);
    assert_eq!(head2, head, "text before the block is untouched");
    assert_eq!(tail2, tail, "text after the block is untouched");
    assert_eq!(body2, "\n07:00  5 p1 Read ch.6 §1–2\n08:00  ·   break 20m\n");
    only_changed(&before, &after, &[DAY]);

    // The start marker can be re-stamped; a body without a trailing newline
    // and an empty body both work.
    store.replace_generated_stamped(DAY, "plan", Some("11:07"), "one row").unwrap();
    let text = fs::read_to_string(root.join(DAY)).unwrap();
    let stamped = "<!-- tm:plan start 11:07 -->";
    assert_eq!(split_generated(&text, stamped, end), (head, "\none row\n", tail));
    store.replace_generated_stamped(DAY, "plan", Some("11:20"), "").unwrap();
    let text = fs::read_to_string(root.join(DAY)).unwrap();
    assert_eq!(
        split_generated(&text, "<!-- tm:plan start 11:20 -->", end),
        (head, "\n", tail)
    );

    // The `## Log` and `# Pinned` sections survived all of that.
    assert!(text.contains("- [ ] 2 20m Call the bank about the card  ^p1"));
    assert!(text.contains("06:05 wake slept=8h10m"));
}

#[test]
fn replace_generated_inserts_missing_markers() {
    let (dir, store) = plan();
    let root = dir.path().join("plan");
    let before = tree_text(&root);

    // No markers: the block goes right after the front matter.
    store.replace_generated(WEEK, "review", "planned 20 / budget 25\n").unwrap();
    let week = fs::read_to_string(root.join(WEEK)).unwrap();
    let (front, body) = before[WEEK].split_once("# Milestones").unwrap();
    assert_eq!(
        week,
        format!("{front}<!-- tm:review start -->\nplanned 20 / budget 25\n<!-- tm:review end -->\n# Milestones{body}")
    );

    // A fresh day file: after the `![day](…)` image line of §4.3.
    let day = Horizon::Day(chrono::NaiveDate::from_ymd_opt(2026, 9, 8).unwrap());
    assert!(store.ensure_horizon_file(&day).unwrap());
    store
        .replace_generated_stamped("day/2026-09-08.md", "plan", Some("07:00"), "07:00 row")
        .unwrap();
    assert_eq!(
        fs::read_to_string(root.join("day/2026-09-08.md")).unwrap(),
        "---\ndate: 2026-09-08\n---\n![day](2026-09-08.svg)\n\
         <!-- tm:plan start 07:00 -->\n07:00 row\n<!-- tm:plan end -->\n"
    );
    assert!(!store.ensure_horizon_file(&day).unwrap(), "already there");

    only_changed(&before, &tree_text(&root), &[WEEK, "day/2026-09-08.md"]);

    // A name or stamp that would break the marker is refused.
    assert!(store.replace_generated(WEEK, "two words", "x").is_err());
    assert!(store
        .replace_generated_stamped(WEEK, "review", Some("a -->"), "x")
        .is_err());
}

// ---------------------------------------------------------------------------
// Sections and lines
// ---------------------------------------------------------------------------

#[test]
fn append_to_section_extends_the_day_log() {
    let (dir, store) = plan();
    let root = dir.path().join("plan");
    let before = tree_text(&root);
    let entry = "16:10 done ^t3 62m/60m went=1";

    store.append_to_section(DAY, "## Log", entry).unwrap();

    let after = tree_text(&root);
    let mut expected: Vec<&str> = before[DAY].lines().collect();
    let last = expected.iter().position(|l| l.starts_with("12:10 interrupt")).unwrap();
    expected.insert(last + 1, entry);
    assert_eq!(after[DAY], format!("{}\n", expected.join("\n")));
    only_changed(&before, &after, &[DAY]);

    // `## Notes` is empty: the line lands right under the heading. A missing
    // section is created at the end of the file.
    store.append_to_section(DAY, "Notes", "went well").unwrap();
    store.append_to_section(BACKLOG, "# Overdue", "- [ ] 3 2b Late thing ^ov1").unwrap();
    let text = fs::read_to_string(root.join(DAY)).unwrap();
    assert!(text.ends_with("## Notes\nwent well\n"), "{text}");
    assert!(fs::read_to_string(root.join(BACKLOG))
        .unwrap()
        .ends_with("- [ ] 4 4b Cell Biology vol. 3 ^c3\n\n# Overdue\n- [ ] 3 2b Late thing ^ov1\n"));
    assert!(store.append_to_section(DAY, "## Log", "two\nlines").is_err());
}

#[test]
fn insert_move_remove_and_reorder_lines() {
    let (dir, store) = plan();
    let root = dir.path().join("plan");
    let before = tree_text(&root);

    // insert: at the end of a section, and at the end of the file.
    store.insert_line(WEEK, Some("Tasks"), "- [ ] 3 1b New task ^n1").unwrap();
    store.insert_line(BACKLOG, None, "- [ ] 3 1b Tail ^n2").unwrap();
    let week = fs::read_to_string(root.join(WEEK)).unwrap();
    assert_eq!(week, format!("{}- [ ] 3 1b New task ^n1\n", before[WEEK]));
    assert!(fs::read_to_string(root.join(BACKLOG))
        .unwrap()
        .ends_with("- [ ] 4 4b Cell Biology vol. 3 ^c3\n- [ ] 3 1b Tail ^n2\n"));

    // move: the exact line text is preserved, the source loses it.
    let moved = line_with(&before[BACKLOG], "a1");
    store.move_line(&Id::new("a1"), WEEK, Some("Tasks")).unwrap();
    let backlog = fs::read_to_string(root.join(BACKLOG)).unwrap();
    assert!(!backlog.contains(&moved));
    assert!(fs::read_to_string(root.join(WEEK))
        .unwrap()
        .ends_with(&format!("- [ ] 3 1b New task ^n1\n{moved}\n")));

    // move into a missing horizon file: created with its front matter.
    let far = line_with(&before[BACKLOG], "d2");
    store.move_line(&Id::new("d2"), "week/2026-W38.md", Some("Milestones")).unwrap();
    assert_eq!(
        fs::read_to_string(root.join("week/2026-W38.md")).unwrap(),
        format!("---\nweek: 2026-W38\nwindow: 2026-09-14..2026-09-20\n---\n# Milestones\n{far}\n")
    );
    assert!(!store
        .ensure_horizon_file(&Horizon::Week(IsoWeek::new(2026, 38)))
        .unwrap());

    // remove: returns the exact text.
    let dropped = line_with(&before[BACKLOG], "a3");
    assert_eq!(store.remove_line(&Id::new("a3")).unwrap(), dropped);
    assert!(!fs::read_to_string(root.join(BACKLOG)).unwrap().contains(&dropped));

    // reorder inside the section only (TUI J/K), clamped at both ends.
    assert!(store.reorder_line(&Id::new("m3"), -1).unwrap());
    let ids = |text: &str| -> Vec<String> {
        text.lines()
            .filter(|l| l.starts_with("- "))
            .map(|l| l.rsplit('^').next().unwrap().to_string())
            .collect()
    };
    let week = fs::read_to_string(root.join(WEEK)).unwrap();
    assert_eq!(
        ids(&week),
        ["m1", "m3", "m2", "m4", "d1", "x1", "x2", "t1", "t3", "t4", "t5", "n1", "a1"]
    );
    assert!(!store.reorder_line(&Id::new("m1"), -3).unwrap(), "first item cannot rise");
    assert!(store.reorder_line(&Id::new("x1"), 9).unwrap(), "clamped to the last milestone");
    let week = fs::read_to_string(root.join(WEEK)).unwrap();
    assert_eq!(
        ids(&week),
        ["m1", "m3", "m2", "m4", "d1", "x2", "x1", "t1", "t3", "t4", "t5", "n1", "a1"],
        "the Tasks section is untouched"
    );

    // Everything else is byte-identical.
    only_changed(
        &before,
        &tree_text(&root),
        &[WEEK, BACKLOG, "week/2026-W38.md"],
    );
    assert_eq!(tree_text(&root)[DAY], before[DAY]);
}

#[test]
fn ensure_file_and_horizon_paths() {
    let (dir, store) = plan();
    let root = dir.path().join("plan");
    assert!(store.ensure_file("notes/scratch.md", "# Scratch\n").unwrap());
    assert!(!store.ensure_file("notes/scratch.md", "overwritten?").unwrap());
    assert_eq!(
        fs::read_to_string(root.join("notes/scratch.md")).unwrap(),
        "# Scratch\n"
    );
    assert!(!store.ensure_horizon_file(&Horizon::Backlog).unwrap());
    assert!(store
        .ensure_horizon_file(&Horizon::Month(tm_core::model::YearMonth::new(2026, 10)))
        .unwrap());
    assert_eq!(
        fs::read_to_string(root.join("month/2026-10.md")).unwrap(),
        "---\nmonth: 2026-10\n---\n"
    );
    assert_eq!(store.abs_path(BACKLOG), Some(root.join(BACKLOG)));
    assert_eq!(store.root(), root.as_path());
}

// ---------------------------------------------------------------------------
// Whole-file edits under the same guard
// ---------------------------------------------------------------------------

#[test]
fn a_whole_file_edit_merges_a_concurrent_save() {
    let (dir, _) = plan();
    let root = dir.path().join("plan");
    let before = tree_text(&root);

    // Someone types a note into `## Notes` while we append to `## Log`.
    let theirs = before[DAY].replace("## Notes\n", "## Notes\nfelt slow after lunch\n");
    let hits = Arc::new(AtomicUsize::new(0));
    let store = racing_store(&root, DAY, vec![Some(theirs.clone()), None], Arc::clone(&hits));

    store.append_to_section(DAY, "## Log", "16:10 done ^t3 62m/60m went=1").unwrap();

    let after = tree_text(&root);
    assert_eq!(
        after[DAY],
        theirs.replace("dropped=^t5\n", "dropped=^t5\n16:10 done ^t3 62m/60m went=1\n"),
        "the append was re-applied to their version, not written over it"
    );
    assert_eq!(hits.load(Ordering::SeqCst), 2);
    only_changed(&before, &after, &[DAY]);
}

#[test]
fn a_whole_file_edit_conflicts_when_every_attempt_is_raced() {
    let (dir, _) = plan();
    let root = dir.path().join("plan");
    let before = tree_text(&root);

    let versions: Vec<Option<String>> = (0..3)
        .map(|i| Some(before[DAY].replace("## Notes\n", &format!("## Notes\nnote {i}\n"))))
        .collect();
    let last = versions[2].clone().unwrap();
    let hits = Arc::new(AtomicUsize::new(0));
    let store = racing_store(&root, DAY, versions, Arc::clone(&hits));

    let err = store.replace_generated(DAY, "plan", "07:00 one row\n").unwrap_err();
    assert!(err.is_conflict());
    match err {
        StoreError::Conflict { id, file, ours, theirs } => {
            assert!(id.is_empty(), "a whole-file edit carries no id");
            assert_eq!(file, DAY);
            assert!(ours.contains("07:00 one row"), "ours is the file we wanted to write");
            assert_eq!(theirs, last, "theirs is the file as it is now");
        }
        other => panic!("expected a conflict, got {other}"),
    }
    assert_eq!(hits.load(Ordering::SeqCst), 3);
    assert_eq!(tree_text(&root)[DAY], last, "nothing of ours reached the disk");
}
