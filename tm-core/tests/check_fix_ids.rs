//! `tm check --fix-ids` (§13, §17.2) against a temp copy of the
//! `plan-conflicts/` fixture: ids are appended only where they are missing,
//! every other byte survives, and a re-check has no `missing-id` problem.

use std::collections::HashSet;
use std::fs;
use std::path::Path;

use tempfile::TempDir;

use tm_core::check;
use tm_core::grammar::IdGen;
use tm_core::model::Id;
use tm_core::store::{FsStore, MemStore, Store};
use tm_core::tree::Tree;

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/{name}", env!("CARGO_MANIFEST_DIR"))
}

/// Copy a fixture tree into a fresh temp directory.
fn temp_copy(name: &str) -> TempDir {
    let dir = TempDir::new().expect("temp dir");
    copy_dir(Path::new(&fixture(name)), dir.path());
    dir
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("mkdir");
    for entry in fs::read_dir(from).expect("readdir") {
        let entry = entry.expect("entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).expect("copy");
        }
    }
}

/// Every file of the tree as `(relative path, text)`, in sorted order.
fn texts(store: &FsStore) -> Vec<(String, String)> {
    let mut files = store.list_files().expect("list");
    files.sort();
    files
        .into_iter()
        .map(|rel| {
            let text = store.read_text(&rel).expect("read");
            (rel, text)
        })
        .collect()
}

#[test]
fn fix_ids_appends_only_missing_ids() {
    let dir = temp_copy("plan-conflicts");
    let store = FsStore::new(dir.path());
    let before = texts(&store);

    let mut plan = store.read_tree().expect("tree");
    let mut gen = IdGen::new(20260907);
    let assigned = check::fix_ids(&store, &mut plan.files, &mut gen).expect("fix-ids");

    // Exactly the one line without an `^id` in the fixture.
    assert_eq!(assigned.len(), 1, "{assigned:?}");
    assert_eq!(assigned[0].0, "week/2026-W37.md");
    assert_eq!(assigned[0].1, 24);
    insta::assert_snapshot!(
        "fix_ids_assigned",
        assigned
            .iter()
            .map(|(f, l, id)| format!("{f}:{l} {}", id.token()))
            .collect::<Vec<_>>()
            .join("\n")
    );

    // Every other byte of every file is unchanged; the fixed lines differ
    // only by the appended token. Compared whole, so a changed terminator or
    // a gained trailing newline in the rewritten file fails too.
    let after = texts(&store);
    assert_eq!(before.len(), after.len());
    for ((rel_a, text_a), (rel_b, text_b)) in before.iter().zip(&after) {
        assert_eq!(rel_a, rel_b);
        let fixed: Vec<(usize, &Id)> = assigned
            .iter()
            .filter(|(f, _, _)| f == rel_a)
            .map(|(_, line, id)| (*line, id))
            .collect();
        assert_eq!(*text_b, with_ids_appended(text_a, &fixed), "{rel_a} changed");
    }
}

/// `text` with ` ^id` appended to the given 1-based lines and nothing else
/// touched — not the line terminators, not a missing final newline.
fn with_ids_appended(text: &str, ids: &[(usize, &Id)]) -> String {
    let mut out = String::new();
    for (i, chunk) in text.split_inclusive('\n').enumerate() {
        match ids.iter().find(|(line, _)| *line == i + 1) {
            Some((_, id)) => {
                let body = chunk.trim_end_matches('\n').trim_end_matches('\r');
                out.push_str(body);
                out.push(' ');
                out.push_str(&id.token());
                out.push_str(&chunk[body.len()..]);
            }
            None => out.push_str(chunk),
        }
    }
    out
}

/// §4.1 "serialization is byte-faithful": the rewritten file keeps its CRLF
/// terminators and gains no final newline of its own. `plan-conflicts` is
/// all LF and ends every file with a newline, so this is the path the
/// fixture cannot reach.
#[test]
fn fix_ids_keeps_terminators_and_an_unterminated_last_line() {
    const WEEK: &str = "week/2026-W37.md";
    let text = "- [ ] 3 1b One\r\n- [ ] 3 1b Two ^aa11\r\n- [ ] 3 1b Three";
    let store = MemStore::new().with_file(WEEK, text);
    let mut plan = store.read_tree().expect("tree");
    let mut gen = IdGen::new(77);
    let assigned = check::fix_ids(&store, &mut plan.files, &mut gen).expect("fix-ids");

    let fixed: Vec<(usize, &Id)> = assigned.iter().map(|(_, l, id)| (*l, id)).collect();
    assert_eq!(fixed.iter().map(|(l, _)| *l).collect::<Vec<_>>(), vec![1, 3]);
    let out = store.read_text(WEEK).unwrap();
    assert_eq!(out, with_ids_appended(text, &fixed));
    assert!(out.contains("One ^") && out.contains("Three ^"), "{out:?}");
    assert!(out.matches("\r\n").count() == 2, "CRLF lost: {out:?}");
    assert!(!out.ends_with('\n'), "a final newline was added: {out:?}");
}

#[test]
fn after_fix_ids_no_line_is_missing_an_id() {
    let dir = temp_copy("plan-conflicts");
    let store = FsStore::new(dir.path());
    let mut plan = store.read_tree().expect("tree");
    let mut gen = IdGen::new(1);
    let assigned = check::fix_ids(&store, &mut plan.files, &mut gen).expect("fix-ids");
    assert!(!assigned.is_empty());

    // The in-memory files handed to `fix_ids` were refreshed in place, and a
    // fresh read agrees with them.
    let reread = store.read_tree().expect("re-read");
    assert_eq!(
        plan.files.iter().map(|f| f.to_text()).collect::<Vec<_>>(),
        reread.files.iter().map(|f| f.to_text()).collect::<Vec<_>>()
    );

    for files in [&plan.files, &reread.files] {
        let tree = Tree::build(files, &plan.config);
        let problems = check::check(files, &tree, &plan.config);
        assert!(
            problems.iter().all(|p| p.code != check::MISSING_ID),
            "still missing ids: {problems:#?}"
        );
        // The only duplicate left is the one the fixture ships on purpose.
        let dups: Vec<String> = problems
            .iter()
            .filter(|p| p.code == check::DUP_ID)
            .map(|p| p.to_string())
            .collect();
        assert_eq!(dups.len(), 2, "{dups:#?}");
        assert!(dups.iter().all(|d| d.contains("^a1")));
    }

    // Ids stay unique: each new one is on exactly one line of the tree
    // (`^a1` is the fixture's deliberate duplicate and `^m2` the §6.3
    // archive copy, neither of which `fix_ids` touches).
    let new: HashSet<String> = assigned.iter().map(|(_, _, id)| id.as_str().to_string()).collect();
    for id in &new {
        let uses = reread
            .files
            .iter()
            .flat_map(|f| f.items())
            .filter(|i| i.id.as_str() == id)
            .count();
        assert_eq!(uses, 1, "^{id} was assigned to {uses} lines");
    }
}

#[test]
fn fix_ids_is_idempotent() {
    let dir = temp_copy("plan-conflicts");
    let store = FsStore::new(dir.path());
    let mut plan = store.read_tree().expect("tree");
    let mut gen = IdGen::new(42);
    check::fix_ids(&store, &mut plan.files, &mut gen).expect("first pass");
    let after_first = texts(&store);

    let mut plan = store.read_tree().expect("tree");
    let again = check::fix_ids(&store, &mut plan.files, &mut gen).expect("second pass");
    assert!(again.is_empty(), "{again:?}");
    assert_eq!(after_first, texts(&store));
}

/// §1.3: a save that lands between our read and our write is merged, not
/// clobbered — `fix_ids` goes through `Store::modify_file`, so the racing
/// writer's new line is there afterwards and gets an id of its own.
#[test]
fn fix_ids_merges_a_concurrent_save() {
    let dir = temp_copy("plan-conflicts");
    let store = FsStore::new(dir.path());
    const WEEK: &str = "week/2026-W37.md";
    let theirs = format!("{}- [ ] 2 15m Their new task\n", store.read_text(WEEK).unwrap());

    let path = dir.path().join(WEEK);
    let saved = std::sync::atomic::AtomicBool::new(false);
    let racing = FsStore::new(dir.path()).with_before_write_hook(Box::new(move |touched, attempt| {
        if touched == path && attempt == 0 && !saved.swap(true, std::sync::atomic::Ordering::SeqCst) {
            fs::write(&path, &theirs).unwrap();
        }
    }));

    let mut plan = racing.read_tree().expect("tree");
    let mut gen = IdGen::new(5);
    let assigned = check::fix_ids(&racing, &mut plan.files, &mut gen).expect("fix-ids");

    assert_eq!(assigned.len(), 2, "both id-less lines get ids: {assigned:?}");
    let text = store.read_text(WEEK).unwrap();
    assert!(text.contains("Their new task ^"), "{text}");
    assert!(text.contains("Book the flight home ^"), "{text}");

    let plan = store.read_tree().expect("re-read");
    let tree = Tree::build(&plan.files, &plan.config);
    let problems = check::check(&plan.files, &tree, &plan.config);
    assert!(problems.iter().all(|p| p.code != check::MISSING_ID), "{problems:#?}");
}

#[test]
fn fix_ids_leaves_a_clean_tree_alone() {
    let dir = temp_copy("plan-basic");
    let store = FsStore::new(dir.path());
    let before = texts(&store);
    let mut plan = store.read_tree().expect("tree");
    let mut gen = IdGen::new(3);
    let assigned = check::fix_ids(&store, &mut plan.files, &mut gen).expect("fix-ids");
    assert!(assigned.is_empty(), "{assigned:?}");
    assert_eq!(before, texts(&store));
}
