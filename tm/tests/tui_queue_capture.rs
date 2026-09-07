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
//! same canonical form `tm add` re-parses and writes back.

mod cli_common;
mod tui_queue_common;

use cli_common::Tm;
use tui_queue_common::{inbox, world_from};

/// §12.5's own example, plus four more shapes of capture line.
const CASES: &[(&str, Option<usize>)] = &[
    // The spec's line: a weekday, an estimate, a `ci`, and a two-word cap.
    ("pset2 fri 6b ci4 max 2b/d", None),
    // A child of an existing milestone: `@parent` sends it to `# Tasks`.
    ("read ch.7 @m3 1b ci5 #lean", None),
    // Nothing the parser claims: untriaged capture, verbatim into `inbox.md`.
    ("ask Kun about the dinner place", None),
    // `tomorrow`, a minute estimate and an explicit priority.
    ("call the dentist tomorrow 20m ci2 p2", None),
    // An explicit target (index 2 = `backlog.md`) with a floor and a flag.
    ("lean practice min 6b/w open ci4", Some(2)),
    // A written-out `due:` beats the weekday guess: "Sat" stays in the title.
    ("Sat prep 2b due:2026-09-12 @m1", None),
];

#[test]
fn preview_matches_tm_add() {
    for (input, target) in CASES {
        let tm = Tm::new();
        let root = tm.plan.to_string_lossy().to_string();
        let world = world_from(&root);
        let cap = inbox::capture(input, &world.view(), *target);
        assert!(
            cap.problem.is_none(),
            "{input:?} did not parse: {:?}",
            cap.problem
        );

        // `--` because a §4.1 line starts with `- `, which clap would read as
        // a flag.
        let mut args = vec!["add", "--to", cap.target.file.as_str()];
        if let Some(section) = &cap.target.section {
            args.push("--section");
            args.push(section);
        }
        args.push("--");
        args.push(cap.line.as_str());
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
        .map(|(input, target)| {
            let cap = inbox::capture(input, &view, *target);
            format!("{input}\n  {}", inbox::preview_text(&cap))
        })
        .collect();
    insta::assert_snapshot!("capture_previews", table.join("\n"));
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
