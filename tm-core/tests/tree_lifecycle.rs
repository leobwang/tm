//! `tree.rs` against the file states the §6.3 lifecycle produces: the `[-]`
//! archive line a closed week keeps, the `month/…# Demoted` copy, and the
//! readopted line in a later week all carry one `^id` and must resolve to
//! one item — the newest record — without a `DuplicateId`.

use chrono::NaiveDate;
use tm_core::config::Config;
use tm_core::model::{Horizon, Id, IsoWeek, Stamp, State, YearMonth};
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

fn est_minutes(t: &Tree, i: &str) -> Option<u32> {
    t.get(&id(i)).unwrap().est.map(|d| d.as_minutes())
}

#[test]
fn readopted_line_wins_over_the_archived_week_line() {
    // After `tm readopt`: the closed week keeps `[-]`, the current week holds
    // the live line with its stamp.
    let t = tree(&[
        ("week/2026-W37.md", "- [-] 4 6b Rollback ^m2\n"),
        ("week/2026-W38.md", "- [ ] 4 3b Rollback est:3b demoted:W37 ^m2\n"),
    ]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    assert!(t.duplicate_ids().is_empty());
    let m2 = t.get(&id("m2")).unwrap();
    assert_eq!(m2.state, State::Todo);
    assert_eq!(m2.horizon, Horizon::Week(IsoWeek::new(2026, 38)));
    assert_eq!(m2.stamps.demoted, vec![Stamp::Week(37)]);
    assert_eq!(est_minutes(&t, "m2"), Some(180));
    assert_eq!(t.len(), 1);
    assert_eq!(t.all(&id("m2")).len(), 2);
    // The archive line is a shadowed copy, still listed under its week.
    let copies = t.demoted_copies();
    assert_eq!(copies.len(), 1);
    assert_eq!(copies[0].src.file, "week/2026-W37.md");
    assert_eq!(t.week_items(IsoWeek::new(2026, 37)).len(), 1);
    assert_eq!(t.week_items(IsoWeek::new(2026, 38)).len(), 1);
    // The planner sees the readopted line in its week.
    let monday_w38 = NaiveDate::from_ymd_opt(2026, 9, 14).unwrap();
    assert_eq!(t.day_candidate_ids(monday_w38, IsoWeek::new(2026, 38)), ids(&["m2"]));
    let monday_w37 = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
    assert!(t.day_candidate_ids(monday_w37, IsoWeek::new(2026, 37)).is_empty());
}

#[test]
fn month_demoted_copy_is_the_record_between_close_and_readopt() {
    let t = tree(&[
        (
            "month/2026-09.md",
            "# Outcomes\n- [ ] 4 !1 Out ^O2\n# Demoted\n- [-] 4 6b Rollback @O2 est:3b demoted:W37 ^m2\n",
        ),
        ("week/2026-W37.md", "- [-] 4 6b Rollback @O2 ^m2\n"),
    ]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    let m2 = t.get(&id("m2")).unwrap();
    assert_eq!(m2.src.file, "month/2026-09.md");
    assert_eq!(m2.state, State::Demoted);
    assert_eq!(m2.stamps.demoted, vec![Stamp::Week(37)]);
    assert_eq!(est_minutes(&t, "m2"), Some(180));
    // The outcome's remaining uses the folded `est:`, not the stale 6b.
    assert_eq!(t.remaining(&id("O2")), Some(180));
    assert_eq!(t.children(&id("O2")), &ids(&["m2"])[..]);
    assert_eq!(t.demoted_copies()[0].src.file, "week/2026-W37.md");
    assert_eq!(t.month_items(YearMonth::new(2026, 9)).len(), 2);
    assert_eq!(t.week_items(IsoWeek::new(2026, 37)).len(), 1);
    // A demoted line is never a day candidate.
    let monday = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
    assert!(t.day_candidate_ids(monday, IsoWeek::new(2026, 37)).is_empty());
}

#[test]
fn open_week_line_still_wins_over_its_month_copy() {
    // The plan-basic shape: the week line is open, the month copy is `[-]`.
    let t = tree(&[
        ("month/2026-09.md", "# Demoted\n- [-] 4 3b Copy est:3b demoted:W37 ^m\n"),
        ("week/2026-W37.md", "- [>] 4 6b Copy ^m\n"),
    ]);
    assert!(t.problems().is_empty());
    assert_eq!(t.get(&id("m")).unwrap().state, State::Active);
    assert_eq!(t.get(&id("m")).unwrap().src.file, "week/2026-W37.md");
    assert_eq!(t.demoted_copies().len(), 1);
}

#[test]
fn repeated_demotions_follow_the_newest_stamps() {
    // Demoted at W36 close, readopted in W37, demoted again at W37 close.
    let w36 = ("week/2026-W36.md", "- [-] 4 6b Twice ^m\n");
    let w37 = ("week/2026-W37.md", "- [-] 4 6b Twice est:3b demoted:W36 ^m\n");
    let month = ("month/2026-09.md", "# Demoted\n- [-] 4 6b Twice est:2b demoted:W36,W37 ^m\n");
    let t = tree(&[w36, w37, month]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    assert_eq!(t.get(&id("m")).unwrap().src.file, "month/2026-09.md");
    assert_eq!(est_minutes(&t, "m"), Some(120));
    assert_eq!(t.demoted_copies().len(), 2);
    assert_eq!(t.len(), 1);

    // Readopted once more into W38: the month line moves there.
    let w38 = ("week/2026-W38.md", "- [ ] 4 6b Twice est:2b demoted:W36,W37 ^m\n");
    let t = tree(&[w36, w37, w38]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    assert_eq!(t.get(&id("m")).unwrap().src.file, "week/2026-W38.md");
    assert_eq!(t.get(&id("m")).unwrap().state, State::Todo);
    let monday_w38 = NaiveDate::from_ymd_opt(2026, 9, 14).unwrap();
    assert_eq!(t.day_candidate_ids(monday_w38, IsoWeek::new(2026, 38)), ids(&["m"]));

    // Dropped at month close (`--drop`): only the two archive lines remain;
    // the newer one is the record and nothing is reported.
    let t = tree(&[w36, w37]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    assert_eq!(t.get(&id("m")).unwrap().src.file, "week/2026-W37.md");
    assert_eq!(t.demoted_copies().len(), 1);

    // Readopted and finished: the `[x]` line is the record.
    let t = tree(&[w36, ("week/2026-W37.md", "- [x] 4 6b Twice demoted:W36 ^m\n")]);
    assert!(t.problems().is_empty());
    assert_eq!(t.get(&id("m")).unwrap().state, State::Done);
    assert_eq!(t.remaining(&id("m")), Some(0));
}

#[test]
fn real_duplicates_are_still_reported() {
    // Two open copies in different files.
    let t = tree(&[
        ("week/2026-W37.md", "- [ ] 4 6b First ^x\n"),
        ("week/2026-W38.md", "- [ ] 4 6b Second ^x\n"),
    ]);
    let problems = t.problems();
    assert_eq!(
        problems,
        vec![TreeProblem::DuplicateId {
            id: id("x"),
            locations: vec![("week/2026-W37.md".into(), 1), ("week/2026-W38.md".into(), 1)],
        }]
    );
    assert_eq!(t.get(&id("x")).unwrap().title, "First");
    assert!(t.demoted_copies().is_empty());
    // An open copy plus an archive copy plus a second open copy: still a
    // duplicate, every location listed, the first open copy primary.
    let t = tree(&[
        ("week/2026-W36.md", "- [-] 4 6b Old ^x\n"),
        ("week/2026-W37.md", "- [ ] 4 6b First ^x\n"),
        ("week/2026-W38.md", "- [ ] 4 6b Second ^x\n"),
    ]);
    assert_eq!(t.duplicate_ids().len(), 1);
    assert_eq!(t.duplicate_ids()[0].1.len(), 3);
    assert_eq!(t.get(&id("x")).unwrap().title, "First");
    // Two `[-]` copies in the same file are never what the lifecycle produces.
    let t = tree(&[("week/2026-W37.md", "- [-] 4 6b A ^x\n- [-] 4 6b B ^x\n")]);
    assert_eq!(t.duplicate_ids().len(), 1);
    assert_eq!(t.get(&id("x")).unwrap().title, "A");
    assert!(t.demoted_copies().is_empty());
    let t = tree(&[(
        "month/2026-09.md",
        "# Demoted\n- [-] 4 6b A demoted:W37 ^x\n- [-] 4 6b B demoted:W37 ^x\n",
    )]);
    assert_eq!(t.duplicate_ids().len(), 1);
}

#[test]
fn an_archive_copy_is_a_state_and_a_horizon() {
    // `[-]` alone is not the exception: a close writes `[-]` into the week
    // file it archives and into `month/…# Demoted`, nowhere else. The same
    // id on a `[-]` line in backlog.md, in a day file, or in a month section
    // that is not `# Demoted` is a real collision.
    let live = ("week/2026-W38.md", "- [ ] 4 6b Rollback demoted:W37 ^m2\n");
    for elsewhere in [
        ("backlog.md", "- [-] 4 6b Rollback ^m2\n"),
        ("day/2026-09-14.md", "# Pinned\n- [-] 4 6b Rollback ^m2\n"),
        ("month/2026-09.md", "# Outcomes\n- [-] 4 6b Rollback ^m2\n"),
    ] {
        let t = tree(&[elsewhere, live]);
        assert_eq!(
            t.duplicate_ids().len(),
            1,
            "`[-]` in {} is not an archive copy",
            elsewhere.0
        );
        assert!(t.demoted_copies().is_empty());
    }
    // The two sanctioned horizons, same states, are not reported.
    for archive in [
        ("week/2026-W37.md", "- [-] 4 6b Rollback ^m2\n"),
        ("month/2026-09.md", "# Demoted\n- [-] 4 6b Rollback ^m2\n"),
    ] {
        let t = tree(&[archive, live]);
        assert!(t.problems().is_empty(), "{:?}", t.problems());
        assert_eq!(t.get(&id("m2")).unwrap().src.file, "week/2026-W38.md");
        assert_eq!(t.demoted_copies().len(), 1);
    }
}

#[test]
fn the_plan_basic_state_resolves_to_the_open_week_line() {
    // The shipped fixture: `^m2` is `[ ]` in week/W37 and `[-]` in
    // month/2026-09 `# Demoted` with the folded `est:3b`.
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/plan-basic");
    let files: Vec<(String, String)> = ["month/2026-09.md", "week/2026-W37.md"]
        .iter()
        .map(|p| (p.to_string(), std::fs::read_to_string(format!("{root}/{p}")).unwrap()))
        .collect();
    let t = tree(&files.iter().map(|(p, s)| (p.as_str(), s.as_str())).collect::<Vec<_>>());
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    let m2 = t.get(&id("m2")).unwrap();
    assert_eq!(m2.state, State::Todo);
    assert_eq!(m2.horizon, Horizon::Week(IsoWeek::new(2026, 37)));
    assert_eq!(est_minutes(&t, "m2"), None, "the week line has no est:");
    assert_eq!(t.demoted_copies().len(), 1);
    assert_eq!(t.demoted_copies()[0].src.file, "month/2026-09.md");
    let monday = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
    assert!(t.day_candidate_ids(monday, IsoWeek::new(2026, 37)).contains(&id("m2")));
}
