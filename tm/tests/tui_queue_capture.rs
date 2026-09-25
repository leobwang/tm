//! §17 M7: "capture preview matches `tm add`."
//!
//! For each capture line the screen's preview ([`inbox::capture`]) is compared
//! with what the real CLI writes: the test runs the built binary
//! (`tm add "<line>" --to <file> --section <s> --json`) against a temp copy of
//! `plan-basic` and asserts the line it put in the file is the preview's line
//! plus the `^id` §4.1 makes the CLI assign — and that the file and section it
//! chose are the ones the preview named.
//!
//! The two agree by construction: [`inbox::capture`] hands its assembled text
//! through [`tm_core::grammar::parse_line`] + `format_item_line`, which is the
//! same canonical form `tm add` re-parses and writes back — which is also why
//! the `tm add` half of this test cannot see a *wrong* line: it re-parses and
//! writes back whatever canonical §4.1 line it is given. So every case states
//! the line the natural-language layer is supposed to produce, and that
//! expectation is what pins [`inbox::normalize`]; the `tm add` run then pins
//! that the line survives the real CLI unchanged.

mod cli_common;
mod tui_queue_common;

use cli_common::Tm;
use tui_queue_common::{inbox, world_from};

/// `(input, forced target, the §4.1 line the preview must show)`.
///
/// §12.5's own example, plus five more shapes of capture line.
const CASES: &[(&str, Option<usize>, &str)] = &[
    // The spec's line: a weekday, an estimate, a `ci`, and a two-word cap.
    (
        "pset2 fri 6b ci4 max 2b/d",
        None,
        "- [ ] 4 6b pset2 due:2026-09-11T23:59 max:2b/d",
    ),
    // A child of an existing milestone: `@parent` sends it to `# Tasks`.
    (
        "read ch.7 @m3 1b ci5 #lean",
        None,
        "- [ ] 5 1b read ch.7 @m3 #lean",
    ),
    // Nothing the parser claims: untriaged capture, verbatim into `inbox.md`.
    (
        "ask Kun about the dinner place",
        None,
        "- ask Kun about the dinner place",
    ),
    // `tomorrow`, a minute estimate and an explicit priority.
    (
        "call the dentist tomorrow 20m ci2 p2",
        None,
        "- [ ] 2 20m call the dentist !2 due:2026-09-08T23:59",
    ),
    // An explicit target (index 2 = `backlog.md`) with a floor and a flag.
    (
        "lean practice min 6b/w open ci4",
        Some(2),
        "- [ ] 4 lean practice min:6b/w open",
    ),
    // A written-out `due:` beats the weekday guess: "Sat" stays in the title.
    (
        "Sat prep 2b due:2026-09-12 @m1",
        None,
        "- [ ] 2b Sat prep @m1 due:2026-09-12",
    ),
];

#[test]
fn preview_matches_tm_add() {
    for (input, target, expected_line) in CASES {
        let tm = Tm::new();
        let root = tm.plan.to_string_lossy().to_string();
        let world = world_from(&root);
        let cap = inbox::capture(input, &world.view(), *target);
        assert!(
            cap.problem.is_none(),
            "{input:?} did not parse: {:?}",
            cap.problem
        );
        // The natural-language layer, pinned here and not by a snapshot it
        // wrote itself: without this the `tm add` round trip below would pass
        // for any canonical line, right or wrong.
        assert_eq!(
            cap.line, *expected_line,
            "the preview line for {input:?} changed"
        );
        assert_eq!(cap.warning, None, "{input:?} should name nothing dangling");

        // `--` because a §4.1 line starts with `- `, which clap would read as
        // a flag.
        let mut args = vec!["add", "--to", cap.target.file.as_str()];
        if let Some(section) = &cap.target.section {
            args.push("--section");
            args.push(section);
        }
        args.push("--");
        args.push(cap.line.as_str());

        // **AND ONE OF THESE CAPTURES BRICKED THE TREE, AND THIS TEST SAID SO
        // AND ASSERTED SUCCESS ANYWAY** (W-31 repair, kernel/README.md gap
        // 2263).  `plan-basic/inbox.md:2` already holds `- ask Kun about the
        // dinner place`, and a bare line is keyed by its TITLE (§4.1), so
        // writing the capture verbatim puts two lines with one store key in one
        // file.  DRIVEN on the binary built from the commit before the repair:
        // `tm add --to inbox.md -- "- ask Kun about the dinner place"` printed
        // the line and exited **0**, and `tm check` then exited 2, `tm review
        // day` 1 and `tm plan` 1 — the whole tree refused for every reading
        // verb.  `tm add` now asks the kernel about the TREE after it writes
        // and puts the file back, so the same capture is refused by name and
        // the file is byte-identical.  The case stays in CASES: it is the one
        // that shows a preview can be a correct §4.1 line and still not be a
        // legal write, which is a thing the queue has to know.
        let before = std::fs::read_to_string(tm.plan.join(&cap.target.file)).expect("read target");
        let raw = tm.run(&args);
        if raw.code != 0 {
            assert!(
                raw.stderr.contains("dupId"),
                "{input:?} was refused for something other than the duplicate key: {}",
                raw.stderr
            );
            let after = std::fs::read_to_string(tm.plan.join(&cap.target.file)).expect("read target");
            assert_eq!(before, after, "a refused `tm add` must leave {} alone", cap.target.file);
            continue;
        }
        let out = tm.json(&args);

        let written = out["line"].as_str().expect("line");
        let id = out["id"].as_str().expect("id");
        // §4.1: a stateful file gets an `^id` appended; `inbox.md` and the
        // other bare files keep the line as written (their key is the title).
        let expected = if cap.target.is_bare() {
            cap.line.clone()
        } else {
            assert_eq!(id.len(), 4, "a generated id for {input:?}");
            format!("{} ^{id}", cap.line)
        };
        assert_eq!(
            written, expected,
            "preview and `tm add` disagree for {input:?}"
        );
        assert_eq!(out["file"].as_str(), Some(cap.target.file.as_str()));
        // A target that names a section must land in it; a target that names
        // none lets `tm add` append at the end of the file and report where
        // that was (`backlog.md`'s last ordinary heading, §4.3).
        if let Some(section) = &cap.target.section {
            assert_eq!(
                out["section"].as_str(),
                Some(section.as_str()),
                "section for {input:?}"
            );
        }

        // And the line really is in the file, byte for byte.
        let text = std::fs::read_to_string(tm.plan.join(&cap.target.file)).expect("read target");
        assert!(
            text.lines().any(|l| l == expected),
            "{expected:?} is not a line of {}:\n{text}",
            cap.target.file
        );
    }
}

#[test]
fn spec_example_preview() {
    let w = world_from(&tui_queue_common::fixture("plan-basic"));
    let view = w.view();
    let cap = inbox::capture("pset2 fri 6b ci4 max 2b/d", &view, None);
    // §12.5, modulo the mock's column padding.
    assert_eq!(cap.line, "- [ ] 4 6b pset2 due:2026-09-11T23:59 max:2b/d");
    assert_eq!(cap.target.to_string(), "week/2026-W37.md #Milestones");
    insta::assert_snapshot!("capture_spec_example", inbox::preview_text(&cap));
}

#[test]
fn previews_for_every_case() {
    let w = world_from(&tui_queue_common::fixture("plan-basic"));
    let view = w.view();
    let table: Vec<String> = CASES
        .iter()
        .map(|(input, target, _)| {
            let cap = inbox::capture(input, &view, *target);
            format!("{input}\n  {}", inbox::preview_text(&cap))
        })
        .collect();
    insta::assert_snapshot!("capture_previews", table.join("\n"));
}

/// §12.5's shorthands only fire on words that are unambiguously grammar. Prose
/// that happens to contain `after` or `loc` stays prose: guessing there writes
/// a §5.5 dependency on nothing, which `tm check` calls `dangling-dep` and
/// which makes the captured item permanently ineligible.
#[test]
fn prose_keywords_are_not_guessed_into_tokens() {
    let w = world_from(&tui_queue_common::fixture("plan-basic"));
    let view = w.view();
    for (input, expected) in [
        ("call mom after lunch", "- [ ] call mom after lunch"),
        ("call mom after zzzqq", "- [ ] call mom after zzzqq"),
        ("loc test something", "- [ ] loc test something"),
        ("wash up loc home", "- [ ] wash up loc:home"),
        ("finish it after ^t4", "- [ ] finish it after:^t4"),
        (
            "ship it after event:review",
            "- [ ] ship it after:event:review",
        ),
    ] {
        let cap = inbox::capture(input, &view, Some(0));
        assert_eq!(cap.line, expected, "{input:?}");
        assert_eq!(cap.problem, None, "{input:?}");
        assert_eq!(cap.warning, None, "{input:?}");
    }
}

/// §4.1: ids are global. `tm add` refuses a taken `^id` (exit 1) instead of
/// writing a `tm check` duplicate, so the preview must refuse it too — a green
/// preview would promise a save that cannot happen.
#[test]
fn a_taken_id_is_refused_exactly_as_tm_add_refuses_it() {
    let tm = Tm::new();
    let root = tm.plan.to_string_lossy().to_string();
    let w = world_from(&root);
    let view = w.view();

    let cap = inbox::capture("^t4 duplicate id line", &view, Some(0));
    assert!(cap.line.is_empty());
    let problem = cap.problem.as_deref().expect("a refusal");
    assert!(problem.contains("^t4 is already used"), "{problem}");
    assert!(problem.contains("week/2026-W37.md"), "{problem}");

    // The real CLI refuses the same line, with exit code 1.
    let out = tm.run(&[
        "add",
        "--to",
        "week/2026-W37.md",
        "--section",
        "Milestones",
        "--",
        "- [ ] duplicate id line ^t4",
    ]);
    assert_eq!(out.code, 1, "stdout: {} stderr: {}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("^t4 is already used"),
        "stderr: {}",
        out.stderr
    );

    // And Enter does not hand the shell a capture it cannot perform.
    let mut state = inbox::CaptureState::new();
    state.editing = true;
    state.target = Some(0);
    state.buffer = "^t4 duplicate id line".to_string();
    let action = inbox::on_key(
        &mut state,
        &view,
        tui_queue_common::special(crossterm::event::KeyCode::Enter),
    );
    assert!(
        matches!(action, tui_queue_common::queue::Action::Note(_)),
        "{action:?}"
    );
    assert!(state.editing, "a refused save keeps the line open");
}

/// An `after:^id` that names nothing is what `tm check` calls dangling.
/// `tm add` writes such a line, so the capture does too — but the preview says
/// so instead of showing a clean parse. A `@parent` that names nothing is
/// refused instead, since the owner's D6: `tm add` refuses it (a tree with one
/// refuses every kernel-backed verb, kernel/README.md gap 22), so the preview
/// blocks `Enter` exactly as it does for a taken `^id`. (Until D6 this test
/// asserted the parent half was a warning too, as `a_dangling_reference_is_a_
/// warning_not_a_refusal`.)
#[test]
fn a_dangling_dependency_is_a_warning_and_a_dangling_parent_a_refusal() {
    let w = world_from(&tui_queue_common::fixture("plan-basic"));
    let view = w.view();

    let cap = inbox::capture("read ch.9 @nosuch 1b", &view, Some(0));
    assert_eq!(cap.line, "", "a refused capture has no line to save");
    assert_eq!(
        cap.problem.as_deref(),
        Some("parent @nosuch does not exist — `tm add` refuses a dangling parent")
    );
    assert_eq!(cap.warning, None);

    let cap = inbox::capture("ship it after:^zzzq", &view, Some(0));
    assert_eq!(cap.problem, None);
    assert_eq!(
        cap.warning.as_deref(),
        Some("dependency after:^zzzq does not exist")
    );

    // A real parent and a real dependency are clean.
    let cap = inbox::capture("read ch.9 @m3 1b", &view, Some(0));
    assert_eq!(cap.warning, None);
}

#[test]
fn tab_cycles_the_target_ring() {
    let w = world_from(&tui_queue_common::fixture("plan-basic"));
    let view = w.view();
    let ring: Vec<String> = inbox::targets(&view)
        .iter()
        .map(|t| t.to_string())
        .collect();
    insta::assert_snapshot!("capture_target_ring", ring.join("\n"));

    let mut state = inbox::CaptureState::new();
    state.editing = true;
    state.buffer = "pset2 fri 6b".to_string();
    assert_eq!(state.capture(&view).target_index, 0);
    let mut seen = Vec::new();
    for _ in 0..ring.len() + 1 {
        inbox::on_key(
            &mut state,
            &view,
            tui_queue_common::special(crossterm::event::KeyCode::Tab),
        );
        seen.push(state.capture(&view).target.to_string());
    }
    assert_eq!(seen[0], ring[1]);
    assert_eq!(seen[ring.len() - 1], ring[0], "Tab wraps");
}

#[test]
fn a_bad_line_is_reported_not_saved() {
    let w = world_from(&tui_queue_common::fixture("plan-basic"));
    let view = w.view();
    // Only a due date: nothing left to be a title.
    let cap = inbox::capture("fri", &view, Some(0));
    assert!(cap.line.is_empty());
    assert_eq!(cap.problem.as_deref(), Some("no title"));

    let mut state = inbox::CaptureState::new();
    state.editing = true;
    state.buffer = "fri".to_string();
    state.target = Some(0);
    let action = inbox::on_key(
        &mut state,
        &view,
        tui_queue_common::special(crossterm::event::KeyCode::Enter),
    );
    assert_eq!(action, tui_queue_common::queue::Action::Note("no title".into()));
    assert!(state.editing, "a refused save keeps the line open");
}

#[test]
fn enter_saves_to_the_previewed_target() {
    let w = world_from(&tui_queue_common::fixture("plan-basic"));
    let view = w.view();
    let mut state = inbox::CaptureState::new();
    state.editing = true;
    state.triaging = Some(1);
    state.buffer = "pset2 fri 6b ci4 max 2b/d".to_string();
    let action = inbox::on_key(
        &mut state,
        &view,
        tui_queue_common::special(crossterm::event::KeyCode::Enter),
    );
    assert_eq!(
        action,
        tui_queue_common::queue::Action::Mutate(tui_queue_common::queue::Mutation::Capture {
            text: "- [ ] 4 6b pset2 due:2026-09-11T23:59 max:2b/d".to_string(),
            file: "week/2026-W37.md".to_string(),
            section: Some("Milestones".to_string()),
            from_inbox: Some(1),
        })
    );
    assert!(!state.editing);
    assert!(state.buffer.is_empty());
    assert_eq!(state.triaging, None);
}
