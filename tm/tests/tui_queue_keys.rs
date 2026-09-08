//! §12.6's keymap, key by key.
//!
//! One snapshot per screen: every key the `queue` and `necessities` rows of
//! §12.6 list (and the §12.5 capture keys), pressed on a fresh state over the
//! `plan-basic` fixture, with the [`queue::Action`] it produced. Nothing here
//! writes a file — the mutating keys hand the shell a [`queue::Mutation`].

mod tui_queue_common;

use crossterm::event::KeyCode;
use tm_core::model::Id;

use tui_queue_common::{fixture, inbox, key, necessities, queue, special, world_from};

/// `Debug`, on one line.
fn label(a: &queue::Action) -> String {
    format!("{a:?}")
}

#[test]
fn queue_keymap() {
    let w = world_from(&fixture("plan-basic"));
    let view = w.view();
    let mut out = Vec::new();
    for (name, code) in queue_keys() {
        // A fresh cursor per key, so the table reads as a dispatch table.
        let mut state = queue::QueueState::new();
        let action = queue::on_key(&mut state, &view, code);
        out.push(format!(
            "{name:<9} → {:<72} pane={:?} sel={} focus={}",
            label(&action),
            state.pane,
            state.week_sel,
            state
                .focus
                .as_ref()
                .map(|f| f.to_string())
                .unwrap_or_else(|| "-".into())
        ));
    }
    insta::assert_snapshot!("queue_keymap", out.join("\n"));
}

/// Every key of §12.6's two `queue` rows, plus the arrows and `Esc`.
fn queue_keys() -> Vec<(String, crossterm::event::KeyEvent)> {
    let mut v: Vec<(String, crossterm::event::KeyEvent)> = "hljkJKacEPDAxe"
        .chars()
        .map(|c| (c.to_string(), key(c)))
        .collect();
    v.push(("Enter".into(), special(KeyCode::Enter)));
    v.push(("Esc".into(), special(KeyCode::Esc)));
    v.push(("Left".into(), special(KeyCode::Left)));
    v.push(("Right".into(), special(KeyCode::Right)));
    v.push(("Down".into(), special(KeyCode::Down)));
    v.push(("Up".into(), special(KeyCode::Up)));
    v.push(("q".into(), key('q')));
    v
}

#[test]
fn queue_p_only_on_roots() {
    let w = world_from(&fixture("plan-basic"));
    let view = w.view();

    // ^m1's root is the month outcome ^O1, so `P` on the week line refuses.
    let mut state = queue::QueueState::new();
    match queue::on_key(&mut state, &view, key('P')) {
        queue::Action::Note(msg) => assert!(msg.contains("O1"), "{msg}"),
        other => panic!("expected a refusal, got {other:?}"),
    }

    // On the Month pane it is a root, so `P` prompts.
    state.pane = queue::Pane::Month;
    assert_eq!(
        queue::on_key(&mut state, &view, key('P')),
        queue::Action::Prompt(queue::Prompt::Priority(Id::new("O1")))
    );
}

#[test]
fn queue_a_adds_into_the_focused_pane() {
    let w = world_from(&fixture("plan-basic"));
    let view = w.view();
    let mut state = queue::QueueState::new();
    assert_eq!(
        queue::on_key(&mut state, &view, key('a')),
        queue::Action::Prompt(queue::Prompt::Add {
            file: "week/2026-W37.md".into(),
            section: Some("Milestones".into()),
        })
    );
    state.pane = queue::Pane::Month;
    assert_eq!(
        queue::on_key(&mut state, &view, key('a')),
        queue::Action::Prompt(queue::Prompt::Add {
            file: "month/2026-09.md".into(),
            section: Some("Outcomes".into()),
        })
    );
}

#[test]
fn queue_e_resolves_the_editor_command() {
    let w = world_from(&fixture("plan-basic"));
    let view = w.view();
    let mut state = queue::QueueState::new();
    let action = queue::on_key(&mut state, &view, key('e'));
    let queue::Action::Edit { id, file } = action else {
        panic!("expected Edit");
    };
    assert_eq!(file.as_deref(), Some("week/2026-W37.md"));
    assert_eq!(
        queue::edit_command(view.cfg, view.tree, &id, file.as_deref()).as_deref(),
        Some("code -g week/2026-W37.md:8")
    );
    // A file that holds no copy of the id falls back to the primary line.
    assert_eq!(
        queue::edit_command(view.cfg, view.tree, &id, Some("backlog.md")).as_deref(),
        Some("code -g week/2026-W37.md:8")
    );
}

#[test]
fn necessities_keymap() {
    let w = world_from(&fixture("plan-basic"));
    let view = w.view();
    let mut out = Vec::new();
    for (name, code) in necessities_keys() {
        let mut state = necessities::NecessitiesState::new();
        // Row 0 is a dated item; the waiting and instance rows are exercised
        // below.
        let action = necessities::on_key(&mut state, &view, code);
        out.push(format!("{name:<6} → {:<62} sel={}", label(&action), state.sel));
    }
    // The same keys on the `[?]` row and on a mandatory instance row.
    let rows = necessities::rows(&view);
    let waiting = rows
        .iter()
        .position(|r| r.section == necessities::Section::Waiting)
        .expect("a waiting row");
    let necessary = rows
        .iter()
        .position(|r| r.section == necessities::Section::Necessary)
        .expect("a necessary row");
    for (name, sel) in [("waiting", waiting), ("necessary", necessary)] {
        for k in ['t', 'k', 'E', 'e'] {
            let mut state = necessities::NecessitiesState { sel };
            let action = necessities::on_key(&mut state, &view, key(k));
            out.push(format!("{name}/{k}  → {}", label(&action)));
        }
    }
    insta::assert_snapshot!("necessities_keymap", out.join("\n"));
}

/// §12.6's `necessities` row, plus movement.
fn necessities_keys() -> Vec<(String, crossterm::event::KeyEvent)> {
    let mut v: Vec<(String, crossterm::event::KeyEvent)> = "Etke"
        .chars()
        .map(|c| (c.to_string(), key(c)))
        .collect();
    v.push(("Down".into(), special(KeyCode::Down)));
    v.push(("Up".into(), special(KeyCode::Up)));
    v.push(("j".into(), key('j')));
    v.push(("q".into(), key('q')));
    v
}

#[test]
fn inbox_keymap() {
    let w = world_from(&fixture("plan-basic"));
    let view = w.view();
    let mut out = Vec::new();
    for (name, code) in [
        ("i".to_string(), key('i')),
        ("t".to_string(), key('t')),
        ("C".to_string(), key('C')),
        ("x".to_string(), key('x')),
        ("j".to_string(), key('j')),
        ("k".to_string(), key('k')),
        ("q".to_string(), key('q')),
    ] {
        let mut state = inbox::CaptureState::new();
        let action = inbox::on_key(&mut state, &view, code);
        out.push(format!(
            "list/{name}   → {:<72} editing={} buffer={:?}",
            label(&action),
            state.editing,
            state.buffer
        ));
    }
    for (name, code) in [
        ("char".to_string(), key('z')),
        ("Backspace".to_string(), special(KeyCode::Backspace)),
        ("Tab".to_string(), special(KeyCode::Tab)),
        ("Esc".to_string(), special(KeyCode::Esc)),
        ("Enter".to_string(), special(KeyCode::Enter)),
    ] {
        let mut state = inbox::CaptureState::new();
        state.editing = true;
        state.buffer = "pset2 fri 6b".to_string();
        let action = inbox::on_key(&mut state, &view, code);
        out.push(format!(
            "edit/{name:<9} → {:<72} editing={} buffer={:?}",
            label(&action),
            state.editing,
            state.buffer
        ));
    }
    insta::assert_snapshot!("inbox_keymap", out.join("\n"));
}

#[test]
fn c_prints_the_claude_command_and_shells_out_to_nothing() {
    let w = world_from(&fixture("plan-basic"));
    let view = w.view();
    let mut state = inbox::CaptureState::new();
    let action = inbox::on_key(&mut state, &view, key('C'));
    assert_eq!(
        action,
        queue::Action::Note(inbox::CLAUDE_TRIAGE.to_string())
    );
    assert_eq!(state.note.as_deref(), Some(inbox::CLAUDE_TRIAGE));
    insta::assert_snapshot!("inbox_claude_command", inbox::CLAUDE_TRIAGE);
}

#[test]
fn t_loads_the_inbox_line_into_the_capture_box() {
    let w = world_from(&fixture("plan-basic"));
    let view = w.view();
    let mut state = inbox::CaptureState::new();
    inbox::on_key(&mut state, &view, key('t'));
    assert!(state.editing);
    assert_eq!(state.buffer, "pset2 fri 6b ci4 max 2b/d");
    assert_eq!(state.triaging, Some(1));
    assert_eq!(
        state.capture(&view).line,
        "- [ ] 4 6b pset2 due:2026-09-11T23:59 max:2b/d"
    );
}
