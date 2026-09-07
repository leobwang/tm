//! `tm check` against the fixture trees (§17.1): `plan-basic/` is clean,
//! `plan-conflicts/` produces exactly one problem of every kind.

use std::collections::BTreeSet;

use tm_core::check::{self, CheckProblem, Severity};
use tm_core::store::{MemStore, Store};
use tm_core::tree::Tree;

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/{name}", env!("CARGO_MANIFEST_DIR"))
}

/// Read a fixture tree and run `check` over it.
fn check_fixture(name: &str) -> Vec<CheckProblem> {
    let store = MemStore::from_dir(fixture(name)).expect("fixture readable");
    let plan = store.read_tree().expect("tree parses");
    let tree = Tree::build(&plan.files, &plan.config);
    check::check(&plan.files, &tree, &plan.config)
}

fn lines(problems: &[CheckProblem]) -> String {
    problems
        .iter()
        .map(|p| p.to_string())
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn plan_basic_has_no_errors() {
    let problems = check_fixture("plan-basic");
    let errors: Vec<&CheckProblem> = problems.iter().filter(|p| p.is_error()).collect();
    assert!(errors.is_empty(), "plan-basic must be clean, got: {errors:#?}");
    assert!(!check::has_errors(&problems));
    assert_eq!(check::exit_code(&problems), 0);
    // Any warnings are recorded here so a regression is visible.
    insta::assert_snapshot!("plan_basic_warnings", lines(&problems));
}

#[test]
fn plan_conflicts_reports_every_kind() {
    let problems = check_fixture("plan-conflicts");
    assert!(check::has_errors(&problems));
    assert_eq!(check::exit_code(&problems), 2);

    // Every code the module knows shows up in this fixture, and no other.
    let seen: BTreeSet<&str> = problems.iter().map(|p| p.code).collect();
    let known: BTreeSet<&str> = check::CODES.iter().copied().collect();
    assert_eq!(seen, known, "plan-conflicts must exercise every code");

    insta::assert_snapshot!("plan_conflicts_problems", lines(&problems));
    insta::assert_snapshot!("plan_conflicts_summary", check::summary(&problems));
}

#[test]
fn plan_conflicts_problems_are_sorted_and_located() {
    let problems = check_fixture("plan-conflicts");
    let keys: Vec<(&str, usize)> = problems.iter().map(|p| (p.file.as_str(), p.line)).collect();
    let mut sorted = keys.clone();
    sorted.sort();
    assert_eq!(keys, sorted, "problems must come out in (file, line) order");
    for p in &problems {
        assert!(!p.file.is_empty(), "{p} has no file");
        assert!(p.line > 0, "{p} has no line");
        assert!(check::CODES.contains(&p.code), "unknown code in {p}");
    }
}

#[test]
fn severities_match_the_documented_split() {
    let problems = check_fixture("plan-conflicts");
    // Every occurrence is checked, not just the first: a code with one
    // documented severity must never come out with the other.
    let all = |code: &str, want: Severity| {
        let seen: Vec<&CheckProblem> = problems.iter().filter(|p| p.code == code).collect();
        assert!(!seen.is_empty(), "no {code} problem");
        for p in seen {
            assert_eq!(p.severity, want, "{p} must be a {want}");
        }
    };
    for code in [
        check::DUP_ID,
        check::DANGLING_PARENT,
        check::PARENT_CYCLE,
        check::DEP_CYCLE,
        check::DANGLING_DEP,
        check::BAD_CI,
        check::ROUTINE_SHAPE,
        check::CALENDAR_SHAPE,
    ] {
        all(code, Severity::Error);
    }
    for code in [
        check::UNKNOWN_KEY,
        check::MISSING_ID,
        check::OUTCOME_WITH_EST,
        check::OPTIONAL_SHAPE,
        check::PRIORITY_ON_CHILD,
        check::SERIES_ORDER,
        check::WALL_CONFLICT,
        check::UNCLASSIFIED_TOKEN,
        check::DAY_SECTION,
        check::WAITING_STATE,
    ] {
        all(code, Severity::Warning);
    }

    // `bad-value` is the one code with two documented severities, and the
    // fixture exercises both: a value that did not parse is an error, a
    // token the parser resolved by rule is a warning.
    let bad: Vec<&CheckProblem> = problems.iter().filter(|p| p.code == check::BAD_VALUE).collect();
    let errors: Vec<&&CheckProblem> = bad.iter().filter(|p| p.is_error()).collect();
    let warnings: Vec<&&CheckProblem> = bad.iter().filter(|p| !p.is_error()).collect();
    assert!(
        errors.iter().any(|p| p.message.contains("due:tomorrow")),
        "{bad:#?}"
    );
    assert!(
        warnings.iter().any(|p| p.message.contains("duplicate key")),
        "{bad:#?}"
    );
}

/// Text the module does not own is never judged (§4.3 free text, §1.3 the
/// commit hook) and neither is day-level calendar context (`#all-day`).
#[test]
fn prose_and_context_lines_are_not_judged() {
    let problems = check_fixture("plan-conflicts");
    for p in &problems {
        assert!(
            !(p.file == "day/2026-09-07.md" && p.line >= 21),
            "`## Log` / `## Notes` are free text: {p}"
        );
        assert!(
            !p.to_string().contains("^b1"),
            "an all-day entry is not a wall: {p}"
        );
    }
    // The buffered flight, on the other hand, does conflict with the
    // appointment inside its buffer (§8.2 step 1).
    let walls: Vec<&CheckProblem> = problems
        .iter()
        .filter(|p| p.code == check::WALL_CONFLICT)
        .collect();
    assert!(
        walls
            .iter()
            .any(|p| p.message.contains("^g8") && p.message.contains("^g3") && p.message.contains("2h buffer")),
        "{walls:#?}"
    );
}

#[test]
fn check_is_deterministic() {
    let a = lines(&check_fixture("plan-conflicts"));
    let b = lines(&check_fixture("plan-conflicts"));
    assert_eq!(a, b);
}
