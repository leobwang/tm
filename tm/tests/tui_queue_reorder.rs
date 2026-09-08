//! §17 M7: "`J`/`K` reorder rewrites files byte-faithfully."
//!
//! The Queue's `J`/`K` go through [`queue::reorder`] →
//! [`tm_core::store::Store::reorder_line`], on a temp copy of the `plan-basic`
//! fixture. Every assertion here is about bytes: the file after a reorder is
//! the file before with exactly two lines exchanged, and nothing else — not a
//! space, not a line ending, not a heading.

mod tui_queue_common;

use std::fs;
use std::path::{Path, PathBuf};

use crossterm::event::KeyCode;
use tempfile::TempDir;
use tm_core::model::Id;
use tm_core::store::FsStore;

use tui_queue_common::{fixture, key, queue, world_from};

const WEEK: &str = "week/2026-W37.md";

/// A temp copy of `plan-basic` (the fixture itself is never touched).
struct Plan {
    _tmp: TempDir,
    root: PathBuf,
}

impl Plan {
    fn new() -> Plan {
        let tmp = TempDir::new().expect("temp dir");
        let root = tmp.path().join("plan");
        copy_dir(Path::new(&fixture("plan-basic")), &root);
        Plan { _tmp: tmp, root }
    }

    fn store(&self) -> FsStore {
        FsStore::new(self.root.clone())
    }

    fn text(&self, rel: &str) -> String {
        fs::read_to_string(self.root.join(rel)).expect("read")
    }
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("create dir");
    for entry in fs::read_dir(from).expect("read fixture") {
        let entry = entry.expect("dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).expect("copy file");
        }
    }
}

/// Assert `after` is `before` with the lines at `i` and `j` exchanged and
/// every other byte untouched.
#[track_caller]
fn assert_only_swapped(before: &str, after: &str, i: usize, j: usize) {
    let b: Vec<&str> = before.split_inclusive('\n').collect();
    let a: Vec<&str> = after.split_inclusive('\n').collect();
    assert_eq!(b.len(), a.len(), "line count changed");
    for k in 0..b.len() {
        let expect = if k == i {
            b[j]
        } else if k == j {
            b[i]
        } else {
            b[k]
        };
        assert_eq!(
            a[k], expect,
            "line {} differs (only {i} and {j} may move)",
            k + 1
        );
    }
    assert_eq!(
        before.len(),
        after.len(),
        "the file changed size: reorder must move lines, not rewrite them"
    );
}

#[test]
fn j_moves_a_line_down_byte_faithfully() {
    let plan = Plan::new();
    let before = plan.text(WEEK);
    // `- [ ] 5 6b Finish ch.5 exercises … ^m1` is line 8 (index 7) and `^m2`
    // is line 9 (index 8).
    assert!(before.split_inclusive('\n').nth(7).unwrap().contains("^m1"));
    assert!(before.split_inclusive('\n').nth(8).unwrap().contains("^m2"));

    let moved = queue::reorder(&plan.store(), &Id::new("m1"), None, 1).expect("reorder");
    assert!(moved, "m1 has a line below it in # Milestones");

    let after = plan.text(WEEK);
    assert_only_swapped(&before, &after, 7, 8);
    assert!(after.split_inclusive('\n').nth(7).unwrap().contains("^m2"));
    assert!(after.split_inclusive('\n').nth(8).unwrap().contains("^m1"));

    // Every other file is untouched.
    for rel in ["month/2026-09.md", "backlog.md", "routines.md"] {
        assert_eq!(
            plan.text(rel),
            fs::read_to_string(Path::new(&fixture("plan-basic")).join(rel)).expect("fixture"),
            "{rel} must not change"
        );
    }
}

#[test]
fn k_moves_a_line_up_and_round_trips_to_the_original_bytes() {
    let plan = Plan::new();
    let original = plan.text(WEEK);
    let store = plan.store();

    assert!(queue::reorder(&store, &Id::new("t5"), None, -1).expect("up"));
    let moved = plan.text(WEEK);
    assert_ne!(moved, original);

    assert!(queue::reorder(&store, &Id::new("t5"), None, 1).expect("down"));
    assert_eq!(
        plan.text(WEEK),
        original,
        "up then down must restore the file byte for byte"
    );
}

#[test]
fn reorder_stays_inside_its_section() {
    let plan = Plan::new();
    let before = plan.text(WEEK);
    let store = plan.store();

    // ^x2 is the last line of `# Milestones`; `J` must not push it into
    // `# Tasks` (§4.2: a section is the rank unit).
    assert!(
        !queue::reorder(&store, &Id::new("x2"), None, 1).expect("clamped"),
        "the last line of a section cannot move down"
    );
    assert_eq!(plan.text(WEEK), before, "a clamped reorder writes nothing");

    // ^t1 is the first line of `# Tasks`.
    assert!(
        !queue::reorder(&store, &Id::new("t1"), None, -1).expect("clamped"),
        "the first line of a section cannot move up"
    );
    assert_eq!(plan.text(WEEK), before);
}

#[test]
fn reordering_changes_rank_and_therefore_the_queue_order() {
    let plan = Plan::new();
    let root = plan.root.to_string_lossy().to_string();

    let before: Vec<String> = {
        let w = world_from(&root);
        queue::week_rows(&w.view())
            .iter()
            .map(|r| r.id.to_string())
            .collect()
    };
    assert_eq!(before[0], "m1");
    assert_eq!(before[1], "m2");

    queue::reorder(&plan.store(), &Id::new("m1"), None, 1).expect("reorder");

    let after: Vec<String> = {
        let w = world_from(&root);
        queue::week_rows(&w.view())
            .iter()
            .map(|r| r.id.to_string())
            .collect()
    };
    assert_eq!(after[0], "m2");
    assert_eq!(after[1], "m1");
    assert_eq!(after.len(), before.len());
}

#[test]
fn shift_j_and_shift_k_ask_the_shell_for_the_reorder() {
    let w = world_from(&fixture("plan-basic"));
    let view = w.view();
    let mut state = queue::QueueState::new();
    assert_eq!(
        queue::on_key(&mut state, &view, key('J')),
        queue::Action::Mutate(queue::Mutation::Reorder {
            id: Id::new("m1"),
            file: Some(WEEK.to_string()),
            delta: 1
        })
    );
    assert_eq!(
        queue::on_key(&mut state, &view, key('K')),
        queue::Action::Mutate(queue::Mutation::Reorder {
            id: Id::new("m1"),
            file: Some(WEEK.to_string()),
            delta: -1
        })
    );
    // The selection itself does not move — the line does.
    assert_eq!(state.week_sel, 0);

    // And on the Month pane the same keys address the outcome under the cursor.
    queue::on_key(&mut state, &view, key('h'));
    assert_eq!(state.pane, queue::Pane::Month);
    assert_eq!(
        queue::on_key(&mut state, &view, key('J')),
        queue::Action::Mutate(queue::Mutation::Reorder {
            id: Id::new("O1"),
            file: Some("month/2026-09.md".to_string()),
            delta: 1
        })
    );
    assert_eq!(
        queue::on_key(&mut state, &view, tui_queue_common::special(KeyCode::Esc)),
        queue::Action::Ignored
    );
}

/// The two halves of M7's "`J`/`K` reorder rewrites files byte-faithfully"
/// joined: the key press produces a mutation, `queue::apply_reorder` — the
/// whole of the shell's wiring for it — carries that mutation out, and the
/// file it wrote differs from the original in exactly two swapped lines.
#[test]
fn pressing_j_rewrites_the_file_byte_faithfully() {
    let plan = Plan::new();
    let root = plan.root.to_string_lossy().to_string();
    let before = plan.text(WEEK);

    let w = world_from(&root);
    let view = w.view();
    let mut state = queue::QueueState::new();
    let action = queue::on_key(&mut state, &view, key('J'));
    let queue::Action::Mutate(m) = action else {
        panic!("J must ask the shell to reorder, got {action:?}");
    };

    let moved = queue::apply_reorder(&plan.store(), &m)
        .expect("apply_reorder handles Mutation::Reorder")
        .expect("reorder");
    assert!(moved);
    assert_only_swapped(&before, &plan.text(WEEK), 7, 8);

    // Anything else is a §13 verb and not this module's to perform.
    assert!(
        queue::apply_reorder(&plan.store(), &queue::Mutation::Drop(Id::new("m1"))).is_none(),
        "apply_reorder must not silently swallow another mutation"
    );
}

/// §6.3: `tm close week` leaves the same `^id` on the demoted week line and on
/// its `month/…#Demoted` archive copy. `J` on the Month pane's archive row must
/// move *that* line — the store's bare-id lookup prefers the copy outside
/// `# Demoted`, i.e. the week file the user is not looking at.
#[test]
fn shift_j_on_a_demoted_row_moves_the_month_copy_only() {
    const MONTH: &str = "month/2026-09.md";
    let plan = Plan::new();

    // The post-close shape: the week line is `[-]`, and `# Demoted` holds two
    // archive copies so there is somewhere to move to.
    let week = plan
        .text(WEEK)
        .replace(
            "- [ ] 4 6b Rollback path passes tests   @O2 ^m2",
            "- [-] 4 3b Rollback path passes tests   @O2 est:3b demoted:W37 ^m2",
        )
        .replace(
            "- [ ] 2 2b Pick winter courses          @O3 ^m4",
            "- [-] 2 2b Pick winter courses          @O3 demoted:W37 ^m4",
        );
    fs::write(plan.root.join(WEEK), &week).expect("write week");
    let month = format!(
        "{}- [-] 2 2b Pick winter courses @O3 demoted:W37 ^m4\n",
        plan.text(MONTH)
    );
    fs::write(plan.root.join(MONTH), &month).expect("write month");

    let root = plan.root.to_string_lossy().to_string();
    let w = world_from(&root);
    let view = w.view();
    let rows = queue::month_rows(&view);
    let at = rows
        .iter()
        .position(|r| r.demoted && r.id.as_str() == "m2")
        .expect("the # Demoted archive row");
    assert_eq!(rows[at].file, MONTH);

    let mut state = queue::QueueState::new();
    state.pane = queue::Pane::Month;
    state.month_sel = at;
    let action = queue::on_key(&mut state, &view, key('J'));
    assert_eq!(
        action,
        queue::Action::Mutate(queue::Mutation::Reorder {
            id: Id::new("m2"),
            file: Some(MONTH.to_string()),
            delta: 1
        }),
        "the mutation must name the file the row was read from"
    );
    let queue::Action::Mutate(m) = action else {
        unreachable!()
    };
    assert!(queue::apply_reorder(&plan.store(), &m)
        .expect("a reorder")
        .expect("reorder"));

    // The month's `# Demoted` moved; the week file did not change at all.
    assert_eq!(plan.text(WEEK), week, "the week file must not be touched");
    let after = plan.text(MONTH);
    let n = month.split_inclusive('\n').count();
    assert_only_swapped(&month, &after, n - 2, n - 1);

    // `e` opens the archive line the cursor is on, not the week line.
    let queue::Action::Edit { id, file } = queue::on_key(&mut state, &view, key('e')) else {
        panic!("e must produce an Edit");
    };
    assert_eq!(
        queue::edit_command(view.cfg, view.tree, &id, file.as_deref()).as_deref(),
        Some("code -g month/2026-09.md:10")
    );

    // And `D` refuses: the row *is* the record of the demotion.
    match queue::on_key(&mut state, &view, key('D')) {
        queue::Action::Note(msg) => assert!(msg.contains("already demoted"), "{msg}"),
        other => panic!("D on a # Demoted row must refuse, got {other:?}"),
    }
}
