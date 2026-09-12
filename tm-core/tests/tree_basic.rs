//! `tree.rs` against the `plan-basic` fixture: resolution, rollups, derived
//! due, series, dependencies, candidate sources.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use chrono::NaiveDate;
use tm_core::config::Config;
use tm_core::grammar::{parse_file, ParsedFile};
use tm_core::model::{parse_datetime, Dep, Horizon, Id, IsoWeek, Moment, Shape, State, YearMonth};
use tm_core::tree::Tree;

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/plan-basic")
}

/// Build order: month, week, backlog, routines, optional, calendar, day, inbox.
const FILES: &[&str] = &[
    "month/2026-09.md",
    "week/2026-W37.md",
    "backlog.md",
    "routines.md",
    "optional.md",
    "calendar/2026-W37.md",
    "day/2026-09-07.md",
    "inbox.md",
];

fn load() -> (Tree, Config) {
    let cfg = Config::load(fixture_dir().join("config.toml")).unwrap();
    let parsed: Vec<ParsedFile> = FILES
        .iter()
        .map(|rel| {
            let text = std::fs::read_to_string(fixture_dir().join(rel)).unwrap();
            parse_file(rel, &text, &cfg)
        })
        .collect();
    (Tree::build(&parsed, &cfg), cfg)
}

fn id(s: &str) -> Id {
    Id::new(s)
}

fn ids(v: &[&str]) -> Vec<Id> {
    v.iter().map(|s| id(s)).collect()
}

fn dt(s: &str) -> chrono::NaiveDateTime {
    parse_datetime(s).unwrap()
}

#[test]
fn builds_cleanly_from_the_fixture() {
    let (t, _) = load();
    assert_eq!(t.files().len(), 8);
    // 4 month + 11 week + 7 backlog + 8 routines + 2 optional + 4 calendar + 1 day + 4 inbox
    assert_eq!(t.nodes().len(), 41);
    // ^m2 is the sanctioned duplicate (§6.3 copy), so one fewer primary.
    assert_eq!(t.len(), 40);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    assert!(t.duplicate_ids().is_empty());
    assert!(t.dangling_parents().is_empty());
    assert!(t.dangling_deps().is_empty());
    assert!(t.parent_cycles().is_empty());
    assert!(t.dep_cycles().is_empty());
    assert!(t.missing_ids().is_empty());
}

#[test]
fn demoted_copy_is_shadowed_by_the_week_line() {
    let (t, _) = load();
    let m2 = t.get(&id("m2")).unwrap();
    assert_eq!(m2.horizon, Horizon::Week(IsoWeek::new(2026, 37)));
    assert_eq!(m2.state, State::Todo);
    let copies = t.demoted_copies();
    assert_eq!(copies.len(), 1);
    assert_eq!(copies[0].state, State::Demoted);
    assert_eq!(copies[0].src.file, "month/2026-09.md");
    assert_eq!(t.all(&id("m2")).len(), 2);
    // The copy still resolves its own parent and shows up in the month listing.
    assert_eq!(t.month_items(YearMonth::new(2026, 9)).len(), 4);
    assert_eq!(t.items_in("month/2026-09.md").len(), 4);
    assert_eq!(t.items_in("plan/month/2026-09.md").len(), 4, "falls back to the horizon");
    assert!(t.items_in("month/2027-01.md").is_empty());
}

#[test]
fn hierarchy_and_roots() {
    let (t, _) = load();
    assert_eq!(t.parent(&id("t3")), Some(&id("m1")));
    assert_eq!(t.parent(&id("m1")), Some(&id("O1")));
    assert_eq!(t.parent(&id("O1")), None);
    assert_eq!(t.ancestors(&id("t3")), ids(&["m1", "O1"]));
    assert_eq!(t.depth(&id("t3")), 2);
    assert_eq!(t.depth(&id("O1")), 0);
    assert_eq!(t.root(&id("t3")), id("O1"));
    assert_eq!(t.root(&id("a1")), id("a1"));
    assert_eq!(t.root(&id("nope")), id("nope"));
    assert!(t.is_root(&id("O1")));
    assert!(!t.is_root(&id("m1")));
    assert_eq!(t.children(&id("O1")), &ids(&["m1", "m3"])[..]);
    assert_eq!(t.children(&id("O3")), &ids(&["m4", "d1", "x1"])[..]);
    assert_eq!(t.children(&id("m2")), &ids(&["t4", "t5"])[..]);
    assert_eq!(t.descendants(&id("O1")), ids(&["m1", "t3", "m3", "t1"]));
    assert!(t.has_children(&id("x1")));
    assert!(!t.has_children(&id("x2")));
    // Roots in (file, line) order: month outcomes, then the untied lines.
    let roots: Vec<&str> = t.roots().iter().map(|i| i.as_str()).collect();
    assert_eq!(&roots[..3], &["O1", "O2", "O3"]);
    assert!(roots.contains(&"a1"));
    assert!(roots.contains(&"sleep"), "routines are keyed by title");
    assert!(roots.contains(&"Severance S3E4"));
    assert!(!roots.contains(&"m1"));
    assert_eq!(t.order(&id("O1")), Some((0, 5)));
    assert_eq!(t.order(&id("m1")), Some((1, 8)));
    assert_eq!(t.file_of(&id("c2")).unwrap().path, "backlog.md");
}

#[test]
fn root_priority_walks_to_the_month_outcome() {
    let (t, cfg) = load();
    // t3 → m1 → O1 (!1)
    assert_eq!(t.root_priority(&id("t3")), 1);
    assert_eq!(t.own_priority(&id("t3")), None);
    assert_eq!(t.own_priority(&id("O1")), Some(1));
    assert_eq!(t.root_priority(&id("m1")), 1);
    assert_eq!(t.root_priority(&id("t5")), 1, "t5 → m2 → O2 (!1)");
    assert_eq!(t.root_priority(&id("d1")), 3, "d1 → O3 (!3)");
    assert_eq!(t.root_priority(&id("x2")), 3, "x2 → x1 → O3");
    assert_eq!(t.root_priority(&id("d2")), 1, "backlog line under O2");
    // Untied → the config default.
    assert_eq!(t.root_priority(&id("a1")), cfg.priority.default_priority);
    assert_eq!(t.root_priority(&id("a1")), 3);
    assert_eq!(t.root_priority(&id("nope")), 3);
}

#[test]
fn ci_is_resolved_from_the_hierarchy() {
    let (t, _) = load();
    // Every fixture line has an explicit ci or a file default; check both
    // are left alone.
    assert_eq!(t.get(&id("t5")).unwrap().ci, 3);
    assert!(t.get(&id("t5")).unwrap().ci_explicit);
    assert_eq!(t.get(&id("sleep")).unwrap().ci, 0);
    assert_eq!(t.get(&id("breakfast")).unwrap().ci, 1, "routine default");
    assert!(!t.get(&id("breakfast")).unwrap().ci_explicit);
    assert_eq!(t.get(&id("Factorio")).unwrap().ci, 0, "optional default");
}

#[test]
fn tags_of_the_fixture_lines() {
    // The fixture has exactly one tagged line and no tagged ancestor, so this
    // only pins its own-tag behaviour; inheritance through the chain is
    // `tags_are_inherited_through_the_chain` in tree_synthetic.rs.
    let (t, _) = load();
    assert_eq!(t.tags_effective(&id("d2")), vec!["soundcode".to_string()]);
    assert!(t.tags_effective(&id("t3")).is_empty());
    // d2 is a child of the untagged O2: nothing is invented.
    assert_eq!(t.parent(&id("d2")), Some(&id("O2")));
    assert!(t.tags_effective(&id("O2")).is_empty());
}

#[test]
fn effective_shape_and_due() {
    let (t, _) = load();
    // x2 is a shape-less child of the Midterm interval → prep, due at the start.
    assert_eq!(t.get(&id("x2")).unwrap().shape, Shape::None);
    assert_eq!(
        t.effective_shape(&id("x2")),
        Shape::Point {
            due: Moment::DateTime(dt("2026-10-20T10:00"))
        }
    );
    assert_eq!(t.effective_due(&id("x2")), Some(dt("2026-10-20T10:00")));
    assert!(t.is_prep(&id("x2")));
    assert!(!t.is_prep(&id("x1")));
    // The interval itself: due = start.
    assert_eq!(t.effective_due(&id("x1")), Some(dt("2026-10-20T10:00")));
    assert!(matches!(t.effective_shape(&id("x1")), Shape::Interval { .. }));
    // Explicit points, date-time and bare date (→ 23:59).
    assert_eq!(t.effective_due(&id("d1")), Some(dt("2026-09-11T23:59")));
    assert_eq!(t.effective_due(&id("d2")), Some(dt("2026-11-20T23:59")));
    // Undated, windows, and unknown ids.
    assert_eq!(t.effective_due(&id("m1")), None);
    assert_eq!(t.effective_shape(&id("m1")), Shape::None);
    assert_eq!(t.effective_due(&id("a3")), None, "a window has no due");
    assert_eq!(t.effective_due(&id("lunch")), None);
    assert_eq!(t.effective_shape(&id("nope")), Shape::None);
    // Prep children / need of the interval.
    assert_eq!(t.prep_children(&id("x1")), ids(&["x2"]));
    assert_eq!(t.prep_need(&id("x1")), 8 * 60);
    assert!(t.prep_children(&id("d1")).is_empty(), "a point is not an interval");
    assert_eq!(t.prep_need(&id("m1")), 0);
}

#[test]
fn remaining_rolls_up() {
    let (t, _) = load();
    // Own estimate wins over the children (m1 has t3 below it).
    assert_eq!(t.remaining(&id("m1")), Some(6 * 60));
    // est: overrides the leading estimate.
    assert_eq!(t.remaining(&id("t3")), Some(60));
    assert_eq!(t.remaining(&id("t1")), Some(60));
    // Month outcomes have no estimate: Σ children.
    // O1 → m1 (6b) + m3 (3b) = 9b
    assert_eq!(t.remaining(&id("O1")), Some(9 * 60));
    // O3 → m4 (2b) + d1 (6b) + x1 (2h) = 10h
    assert_eq!(t.remaining(&id("O3")), Some(10 * 60));
    // O2 → m2 (week copy, 6b) + d2 (10b)
    assert_eq!(t.remaining(&id("O2")), Some(16 * 60));
    // Done items have nothing left; windows and optionals use dur.
    assert_eq!(t.remaining(&id("c1")), Some(0));
    assert_eq!(t.remaining(&id("a3")), Some(20));
    assert_eq!(t.remaining(&id("Factorio")), Some(120));
    assert_eq!(t.remaining(&id("nope")), None);
    // Planned (progress denominator) ignores state and est:.
    assert_eq!(t.planned_minutes(&id("t3")), Some(120));
    assert_eq!(t.planned_minutes(&id("c1")), Some(240));
    assert_eq!(t.planned_minutes(&id("O1")), Some(9 * 60));
}

#[test]
fn done_minutes_and_progress_sum_descendants() {
    let (t, _) = load();
    let done: HashMap<Id, u32> = [(id("t1"), 67), (id("t3"), 80), (id("m3"), 10)].into_iter().collect();
    assert_eq!(t.done_minutes(&id("t1"), &done), 67);
    assert_eq!(t.done_minutes(&id("m3"), &done), 77);
    assert_eq!(t.done_minutes(&id("m1"), &done), 80);
    assert_eq!(t.done_minutes(&id("O1"), &done), 157);
    assert_eq!(t.done_minutes(&id("O2"), &done), 0);
    let p = t.progress(&id("m1"), &done).unwrap();
    assert!((p - 80.0 / 360.0).abs() < 1e-9);
    let p = t.progress(&id("O1"), &done).unwrap();
    assert!((p - 157.0 / 540.0).abs() < 1e-9);
    assert_eq!(t.progress(&id("a3"), &done), Some(0.0));
    assert_eq!(t.progress(&id("O1_missing"), &done), None);
}

#[test]
fn series_head_is_the_first_open_line() {
    let (t, _) = load();
    assert_eq!(t.series_names().collect::<Vec<_>>(), vec!["cell-bio"]);
    assert_eq!(t.series_members("cell-bio"), &ids(&["c1", "c2", "c3"])[..]);
    assert_eq!(t.series_head("cell-bio"), Some(id("c2")), "c1 is done");
    assert_eq!(t.series_heads(), ids(&["c2"]));
    assert_eq!(t.series_of(&id("c3")), Some(("cell-bio", 2)));
    assert_eq!(t.series_of(&id("a1")), None);
    assert!(!t.is_series_active(&id("c1")));
    assert!(t.is_series_active(&id("c2")));
    assert!(!t.is_series_active(&id("c3")));
    assert!(!t.is_series_active(&id("a1")), "not in a series");
    assert!(t.series_suppressed(&id("c3")));
    assert!(t.series_suppressed(&id("c1")));
    assert!(!t.series_suppressed(&id("c2")));
    assert!(!t.series_suppressed(&id("a1")));
    // The implied after: is the previous line.
    assert_eq!(t.implied_dep(&id("c1")), None);
    assert_eq!(t.implied_dep(&id("c2")), Some(id("c1")));
    assert_eq!(t.implied_dep(&id("c3")), Some(id("c2")));
    assert!(t.deps(&id("c2")).is_empty(), "nothing written");
    assert_eq!(t.all_deps(&id("c2")), vec![Dep::Item(id("c1"))]);
    let none = HashSet::new();
    let no_events = HashSet::new();
    assert!(t.deps_satisfied(&id("c2"), &none, &no_events), "c1 is [x] in the file");
    assert!(!t.deps_satisfied(&id("c3"), &none, &no_events));
    assert_eq!(t.blocked_by(&id("c3"), &none, &no_events), vec![Dep::Item(id("c2"))]);
    let done: HashSet<Id> = [id("c2")].into_iter().collect();
    assert!(t.deps_satisfied(&id("c3"), &done, &no_events));
}

#[test]
fn t5_is_blocked_by_t4_until_done() {
    let (t, _) = load();
    let none = HashSet::new();
    let no_events = HashSet::new();
    assert_eq!(t.deps(&id("t5")), &[Dep::Item(id("t4"))]);
    assert_eq!(t.all_deps(&id("t5")), vec![Dep::Item(id("t4"))]);
    assert!(!t.deps_satisfied(&id("t5"), &none, &no_events));
    assert_eq!(t.blocked_by(&id("t5"), &none, &no_events), vec![Dep::Item(id("t4"))]);
    let done: HashSet<Id> = [id("t4")].into_iter().collect();
    assert!(t.deps_satisfied(&id("t5"), &done, &no_events));
    assert!(t.blocked_by(&id("t5"), &done, &no_events).is_empty());
    // No deps at all.
    assert!(t.deps_satisfied(&id("t4"), &none, &no_events));
    assert!(t.deps_satisfied(&id("nope"), &none, &no_events));
}

#[test]
fn day_candidates_for_monday_w37() {
    let (t, _) = load();
    let today = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
    let week = IsoWeek::new(2026, 37);
    let cands = t.day_candidate_ids(today, week);
    let names: Vec<&str> = cands.iter().map(|i| i.as_str()).collect();
    // week items (all open, incl. the blocked t5 and the far interval x1),
    // then backlog (a4 waiting and the non-head series lines excluded),
    // then the pinned day line.
    assert_eq!(
        names,
        vec!["m1", "m2", "m3", "m4", "d1", "x1", "x2", "t1", "t3", "t4", "t5", "a1", "a3", "d2", "c2", "p1"]
    );
    insta::assert_yaml_snapshot!("day_candidates_2026-09-07", names);
    // Another week or day: only the backlog and the series head remain.
    let other = t.day_candidate_ids(
        NaiveDate::from_ymd_opt(2026, 9, 14).unwrap(),
        IsoWeek::new(2026, 38),
    );
    let other: Vec<&str> = other.iter().map(|i| i.as_str()).collect();
    assert_eq!(other, vec!["a1", "a3", "d2", "c2"]);
}

#[test]
fn other_candidate_sources() {
    let (t, _) = load();
    let names = |v: Vec<Id>| v.iter().map(|i| i.to_string()).collect::<Vec<_>>();
    assert_eq!(
        names(t.routine_ids()),
        vec!["sleep", "breakfast", "lunch", "dinner", "workout", "shower", "laundry", "groceries"]
    );
    assert_eq!(names(t.optional_ids()), vec!["Severance S3E4", "Factorio"]);
    assert_eq!(names(t.calendar_ids(IsoWeek::new(2026, 37))), vec!["g1", "g2", "g3", "g4"]);
    assert!(t.calendar_ids(IsoWeek::new(2026, 38)).is_empty());
    assert_eq!(t.week_items(IsoWeek::new(2026, 37)).len(), 11);
    assert!(t.week_items(IsoWeek::new(2026, 36)).is_empty());
    assert_eq!(names(t.waiting_ids()), vec!["a4"]);
    assert!(t.month_items_with_est_and_no_children().is_empty());
}

#[test]
fn overdue_uses_effective_due_and_persist() {
    let (t, _) = load();
    let names = |v: Vec<Id>| v.iter().map(|i| i.to_string()).collect::<Vec<_>>();
    assert!(t.overdue(dt("2026-09-07T10:00")).is_empty());
    // Friday's pset deadline has passed; calendar walls never count.
    assert_eq!(names(t.overdue(dt("2026-09-12T00:00"))), vec!["d1"]);
    // At the exam start the prep child is overdue (derived due); the exam
    // itself only once it has ended.
    assert_eq!(names(t.overdue(dt("2026-10-20T10:30"))), vec!["d1", "x2"]);
    assert_eq!(names(t.overdue(dt("2026-10-20T12:01"))), vec!["d1", "x1", "x2"]);
    // d2 (bare date) becomes overdue after 23:59 that day.
    assert!(!t.overdue(dt("2026-11-20T23:00")).contains(&id("d2")));
    assert!(t.overdue(dt("2026-11-21T00:00")).contains(&id("d2")));
}
