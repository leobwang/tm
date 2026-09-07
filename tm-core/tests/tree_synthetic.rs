//! `tree.rs` on small in-test trees: ci inheritance, rollup sums through
//! estimate-less children, event dependencies, cycles, dangling refs, and
//! the derived prep due through a shape-less chain.

use std::collections::HashSet;

use chrono::NaiveDate;
use tm_core::config::Config;
use tm_core::model::{parse_datetime, Dep, Id, IsoWeek, Moment, Ref, Shape};
use tm_core::tree::{Tree, TreeProblem};

fn tree(files: &[(&str, &str)]) -> Tree {
    Tree::from_texts(files, &Config::default())
}

fn id(s: &str) -> Id {
    Id::new(s)
}

fn ids(v: &[&str]) -> Vec<Id> {
    v.iter().map(|s| id(s)).collect()
}

#[test]
fn ci_defaults_to_the_nearest_explicit_ancestor() {
    let t = tree(&[
        ("month/2026-09.md", "- [ ] 4 !2 Outcome ^O\n- [ ] Untied outcome ^U\n"),
        (
            "week/2026-W37.md",
            "- [ ] 2b Milestone @O ^m\n\
             - [ ] 1b Task @m ^t\n\
             - [ ] 2 1b Explicit @m ^e\n\
             - [ ] 1b Under explicit @e ^f\n\
             - [ ] 1b Under untied @U ^u\n\
             - [ ] 1b Lonely ^l\n",
        ),
        ("routines.md", "- lunch win:11:30-13:30 dur:30m every:day\n"),
    ]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    // m has no ci → its parent's 4; t inherits through m.
    assert_eq!(t.get(&id("m")).unwrap().ci, 4);
    assert!(!t.get(&id("m")).unwrap().ci_explicit);
    assert_eq!(t.get(&id("t")).unwrap().ci, 4);
    // An explicit ci in between wins.
    assert_eq!(t.get(&id("e")).unwrap().ci, 2);
    assert_eq!(t.get(&id("f")).unwrap().ci, 2);
    // No explicit ancestor → the file default (3), routines → 1.
    assert_eq!(t.get(&id("u")).unwrap().ci, 3);
    assert_eq!(t.get(&id("l")).unwrap().ci, 3);
    assert_eq!(t.get(&id("lunch")).unwrap().ci, 1);
    // Priorities: only the root's !k counts.
    assert_eq!(t.root_priority(&id("f")), 2);
    assert_eq!(t.root_priority(&id("u")), 3);
}

#[test]
fn non_root_priority_is_ignored_for_root_priority() {
    let t = tree(&[
        ("month/2026-09.md", "- [ ] 4 !1 Outcome ^O\n"),
        ("week/2026-W37.md", "- [ ] 4 2b !4 Milestone @O ^m\n- [ ] 1b Task @m ^t\n"),
    ]);
    assert_eq!(t.own_priority(&id("m")), Some(4));
    assert_eq!(t.root_priority(&id("m")), 1);
    assert_eq!(t.root_priority(&id("t")), 1);
}

#[test]
fn remaining_sums_children_that_lack_estimates() {
    let t = tree(&[(
        "week/2026-W37.md",
        "- [ ] 3 Parent ^p\n\
         - [ ] 3 Middle @p ^m\n\
         - [ ] 3 1b Leaf one @m ^a\n\
         - [ ] 3 30m Leaf two @m ^b\n\
         - [x] 3 2b Leaf done @m ^c\n\
         - [ ] 3 No estimate anywhere @p ^n\n\
         - [ ] 3 Sibling 45m @p est:45m ^s\n",
    )]);
    assert_eq!(t.remaining(&id("a")), Some(60));
    assert_eq!(t.remaining(&id("c")), Some(0), "done");
    assert_eq!(t.remaining(&id("n")), None, "nothing to sum");
    // Middle: 60 + 30 + 0 (done) = 90
    assert_eq!(t.remaining(&id("m")), Some(90));
    // Parent: middle 90 + n (none) + s 45 = 135
    assert_eq!(t.remaining(&id("p")), Some(135));
    // Planned keeps the done leaf: 60 + 30 + 120 = 210; parent 210 + 0 (s has no leading est)
    assert_eq!(t.planned_minutes(&id("m")), Some(210));
    assert_eq!(t.planned_minutes(&id("p")), Some(210));
    assert_eq!(t.planned_minutes(&id("s")), None);
}

#[test]
fn event_dependencies_resolve_from_the_events_set() {
    let t = tree(&[(
        "week/2026-W37.md",
        "- [ ] 3 1b Apply for the visa after:event:visa ^v\n\
         - [ ] 3 1b Book flights after:event:visa,^v ^f\n\
         - [x] 3 1b Fill the form ^d\n\
         - [~] 3 1b Abandoned ^x\n\
         - [ ] 3 1b Needs the form @v after:^d ^n\n\
         - [ ] 3 1b Needs abandoned after:^x ^y\n",
    )]);
    let none: HashSet<Id> = HashSet::new();
    let no_events: HashSet<String> = HashSet::new();
    assert_eq!(t.deps(&id("v")), &[Dep::Event("visa".into())]);
    assert!(!t.deps_satisfied(&id("v"), &none, &no_events));
    assert_eq!(t.blocked_by(&id("v"), &none, &no_events), vec![Dep::Event("visa".into())]);
    let events: HashSet<String> = ["visa".to_string()].into_iter().collect();
    assert!(t.deps_satisfied(&id("v"), &none, &events));
    // Both kinds on one line.
    assert_eq!(t.blocked_by(&id("f"), &none, &events), vec![Dep::Item(id("v"))]);
    let done: HashSet<Id> = [id("v")].into_iter().collect();
    assert!(t.deps_satisfied(&id("f"), &done, &events));
    assert_eq!(
        t.blocked_by(&id("f"), &none, &no_events),
        vec![Dep::Event("visa".into()), Dep::Item(id("v"))]
    );
    // A Done item in the file satisfies; a Dropped one does not.
    assert!(t.deps_satisfied(&id("n"), &none, &no_events));
    assert!(!t.deps_satisfied(&id("y"), &none, &no_events));
    assert!(t.problems().is_empty(), "{:?}", t.problems());
}

#[test]
fn series_head_skips_dropped_lines_and_the_implied_dep_follows() {
    let t = tree(&[(
        "backlog.md",
        "## series:vols\n- [x] 3 1b One ^s1\n- [~] 3 1b Two ^s2\n- [ ] 3 1b Three ^s3\n- [ ] 3 1b Four ^s4\n\n# Other\n- [ ] 3 1b Untied ^u\n",
    )]);
    assert_eq!(t.series_head("vols"), Some(id("s3")));
    assert_eq!(t.series_head("missing"), None);
    let none: HashSet<Id> = HashSet::new();
    let no_events: HashSet<String> = HashSet::new();
    // The implied dep on the dropped s2 does not block the head.
    assert_eq!(t.implied_dep(&id("s3")), Some(id("s2")));
    assert!(t.deps_satisfied(&id("s3"), &none, &no_events));
    assert!(!t.deps_satisfied(&id("s4"), &none, &no_events));
    let today = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
    assert_eq!(t.day_candidate_ids(today, IsoWeek::new(2026, 37)), ids(&["s3", "u"]));
}

#[test]
fn series_head_in_a_week_file_is_a_candidate_anywhere() {
    let t = tree(&[
        ("week/2026-W36.md", "## series:old\n- [ ] 3 1b Head ^h\n- [ ] 3 1b Next ^n\n"),
        ("week/2026-W37.md", "- [ ] 3 1b This week ^w\n"),
    ]);
    let today = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
    assert_eq!(t.day_candidate_ids(today, IsoWeek::new(2026, 37)), ids(&["h", "w"]));
}

#[test]
fn pinned_requires_the_section_and_today() {
    let t = tree(&[
        ("day/2026-09-07.md", "# Pinned\n- [ ] 2 20m Call ^p\n\n## Notes\n- [ ] 2 20m Note line ^q\n"),
        ("day/2026-09-06.md", "# Pinned\n- [ ] 2 20m Yesterday ^y\n"),
        ("month/2026-09.md", "- [ ] 4 !1 Outcome ^O\n"),
        ("inbox.md", "- capture me\n"),
    ]);
    let today = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
    assert_eq!(t.day_candidate_ids(today, IsoWeek::new(2026, 37)), ids(&["p"]));
    // Waiting / done / demoted lines never qualify.
    let t = tree(&[(
        "week/2026-W37.md",
        "- [ ] 3 1b Todo ^a\n- [>] 3 1b Active ^b\n- [x] 3 1b Done ^c\n- [-] 3 1b Demoted ^d\n- [~] 3 1b Dropped ^e\n- [?] 3 1b Waiting ^f\n",
    )]);
    assert_eq!(t.day_candidate_ids(today, IsoWeek::new(2026, 37)), ids(&["a", "b"]));
    assert_eq!(t.waiting_ids(), ids(&["f"]));
}

#[test]
fn prep_due_derives_through_shapeless_ancestors_only() {
    let t = tree(&[(
        "week/2026-W37.md",
        "- [ ] 5 2h Exam at:2026-10-20T10:00/12:00 ^x\n\
         - [ ] 5 Review @x ^r\n\
         - [ ] 5 1b Review ch.3 @r ^r3\n\
         - [ ] 4 6b Pset @x due:2026-09-11T23:59 ^d\n\
         - [ ] 4 1b Pset part @d ^dp\n\
         - [ ] 1 Errand @x win:09:00-21:00 dur:20m ^w\n\
         - [ ] 1 Errand step @w ^ws\n",
    )]);
    let start = parse_datetime("2026-10-20T10:00").unwrap();
    assert_eq!(t.effective_due(&id("r")), Some(start));
    assert_eq!(t.effective_due(&id("r3")), Some(start), "through the shape-less r");
    assert!(t.is_prep(&id("r3")));
    // An explicit point below the interval keeps its own due and derives
    // nothing for its children; likewise a window.
    assert_eq!(t.effective_due(&id("d")), Some(parse_datetime("2026-09-11T23:59").unwrap()));
    assert_eq!(t.effective_shape(&id("dp")), Shape::None);
    assert_eq!(t.effective_due(&id("dp")), None);
    assert_eq!(t.effective_shape(&id("ws")), Shape::None);
    assert_eq!(
        t.effective_shape(&id("r")),
        Shape::Point {
            due: Moment::DateTime(start)
        }
    );
    // Only direct shape-less children are prep children; need = Σ remaining.
    assert_eq!(t.prep_children(&id("x")), ids(&["r"]));
    assert_eq!(t.prep_need(&id("x")), 60, "r has no est → its child's 1b");
}

#[test]
fn parent_cycles_are_detected() {
    let t = tree(&[(
        "week/2026-W37.md",
        "- [ ] 3 1b A @c ^a\n- [ ] 3 1b B @a ^b\n- [ ] 3 1b C @b ^c\n- [ ] 3 1b D @c ^d\n- [ ] 3 1b Fine ^f\n",
    )]);
    // Edges point at the parent: a → c → b → a, rotated to the smallest id.
    assert_eq!(t.parent_cycles(), vec![ids(&["a", "c", "b"])]);
    assert_eq!(t.roots(), &ids(&["f"])[..]);
    assert!(t.dep_cycles().is_empty());
    // Everything still answers.
    assert_eq!(t.ancestors(&id("d")), ids(&["c", "b", "a"]));
    // Depth-first pre-order: a's subtree (b) before the sibling d.
    assert_eq!(t.descendants(&id("c")), ids(&["a", "b", "d"]));
    assert_eq!(t.remaining(&id("a")), Some(60));
    assert_eq!(t.remaining(&id("c")), Some(60));
    let problems = t.problems();
    assert_eq!(problems.len(), 1);
    assert_eq!(problems[0], TreeProblem::ParentCycle { ids: ids(&["a", "c", "b"]) });
    assert_eq!(problems[0].to_string(), "parent cycle: ^a -> ^c -> ^b -> ^a");
}

#[test]
fn dep_cycles_are_detected_including_implied_series_deps() {
    let t = tree(&[(
        "week/2026-W37.md",
        "- [ ] 3 1b A after:^b ^a\n\
         - [ ] 3 1b B after:^c ^b\n\
         - [ ] 3 1b C after:^a,^d ^c\n\
         - [ ] 3 1b D ^d\n\
         - [ ] 3 1b Self after:^e ^e\n\
         ## series:s\n\
         - [ ] 3 1b First after:^second ^first\n\
         - [ ] 3 1b Second ^second\n",
    )]);
    let cycles = t.dep_cycles();
    assert_eq!(
        cycles,
        vec![ids(&["a", "b", "c"]), ids(&["e"]), ids(&["first", "second"])]
    );
    assert!(t.parent_cycles().is_empty());
    let dep_problems: Vec<TreeProblem> = t
        .problems()
        .into_iter()
        .filter(|p| matches!(p, TreeProblem::DepCycle { .. }))
        .collect();
    assert_eq!(dep_problems.len(), 3);
    assert_eq!(dep_problems[1].to_string(), "dependency cycle: ^e -> ^e");
}

#[test]
fn dangling_parents_and_deps_are_reported() {
    let t = tree(&[(
        "week/2026-W37.md",
        "- [ ] 3 1b Orphan @zzz ^o\n- [ ] 3 1b Child of orphan @o ^c\n- [ ] 3 1b Waits after:^gone,event:x ^w\n- [ ] 3 1b Fine ^f\n",
    )]);
    assert_eq!(t.dangling_parents(), &[(id("o"), Ref::new("zzz"))][..]);
    assert_eq!(t.dangling_deps(), vec![(id("w"), id("gone"))]);
    // An item with a dangling parent is its own root.
    assert_eq!(t.parent(&id("o")), None);
    assert!(t.is_root(&id("o")));
    assert_eq!(t.roots(), &ids(&["o", "w", "f"])[..]);
    assert_eq!(t.root(&id("c")), id("o"));
    assert_eq!(t.root_priority(&id("c")), 3);
    // The missing dep never satisfies.
    assert!(!t.deps_satisfied(&id("w"), &HashSet::new(), &["x".to_string()].into_iter().collect()));
    let problems = t.problems();
    assert_eq!(problems.len(), 2);
    assert_eq!(
        problems[0],
        TreeProblem::DanglingParent {
            id: id("o"),
            parent: Ref::new("zzz"),
            file: "week/2026-W37.md".into(),
            line: 1,
        }
    );
    assert_eq!(
        problems[0].to_string(),
        "week/2026-W37.md:1: ^o has parent @zzz which does not exist"
    );
    assert_eq!(
        problems[1],
        TreeProblem::DanglingDep {
            id: id("w"),
            dep: id("gone"),
            file: "week/2026-W37.md".into(),
            line: 3,
        }
    );
}

#[test]
fn missing_ids_and_month_estimate_warning_inputs() {
    let t = tree(&[
        (
            "month/2026-09.md",
            "# Outcomes\n- [ ] 5 !1 Has children ^O1\n- [ ] 4 3b !2 Estimate, no children ^O2\n- [ ] 2 !3 No estimate ^O3\n\
             # Demoted\n- [-] 4 3b Parked @O1 est:3b demoted:W37 ^m9\n",
        ),
        ("week/2026-W37.md", "- [ ] 5 6b Milestone @O1 ^m1\n- [ ] 5 1b No id yet\n"),
        ("inbox.md", "- no id is fine here\n"),
    ]);
    assert_eq!(t.month_items_with_est_and_no_children(), ids(&["O2"]));
    let missing = t.missing_ids();
    assert_eq!(missing.len(), 1);
    assert_eq!(missing[0].title, "No id yet");
    assert!(t.contains(&id("No id yet")), "keyed by title until --fix-ids");
    let problems = t.problems();
    assert_eq!(problems.len(), 1);
    assert_eq!(
        problems[0].to_string(),
        "week/2026-W37.md:2: missing ^id on `No id yet`"
    );
}

#[test]
fn empty_tree_answers_everything() {
    let t = tree(&[]);
    assert!(t.is_empty());
    assert_eq!(t.len(), 0);
    assert!(t.roots().is_empty());
    assert!(t.series_heads().is_empty());
    assert!(t.problems().is_empty());
    let today = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
    assert!(t.day_candidate_ids(today, IsoWeek::new(2026, 37)).is_empty());
    assert!(t.overdue(parse_datetime("2026-09-07T10:00").unwrap()).is_empty());
    assert_eq!(t.root_priority(&id("x")), 3);
}
