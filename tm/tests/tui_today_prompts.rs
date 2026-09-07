//! §9's two prompts and the `?` help overlay (tm-spec-v1.md §9.1, §9.2,
//! §12.6).

mod tui_common;

use ratatui::backend::TestBackend;
use ratatui::layout::Rect;
use ratatui::Terminal;

use tui_common::app::{Action, Answer, Effect, Mode, Prompt};
use tui_common::{app, app_at, idle_app, prompts, today};

use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

/// A plain character keystroke.
fn key(c: char) -> KeyEvent {
    KeyEvent::new(KeyCode::Char(c), KeyModifiers::NONE)
}

/// Draw an overlay over an 80×12 frame.
fn overlay(draw: impl Fn(&mut ratatui::Frame)) -> String {
    overlay_sized(80, 12, draw)
}

/// Draw an overlay over a frame of the given size.
fn overlay_sized(w: u16, h: u16, draw: impl Fn(&mut ratatui::Frame)) -> String {
    let mut term = Terminal::new(TestBackend::new(w, h)).expect("terminal");
    term.draw(|f| draw(f)).expect("draw");
    term.backend().to_string()
}

#[test]
fn the_overtime_prompt_fires_past_est_times_the_multiplier() {
    // ^t3 started 09:32 with est_min 192 (2b × 1.6), so it is due at 12:44.
    assert!(app_at(12, 0).overtime_due().is_none());
    let over = app_at(12, 51).overtime_due().expect("overtime is due");
    assert_eq!(over.id.to_string(), "t3");
    assert_eq!(over.planned_min, 192);
    assert_eq!(over.elapsed_min, 199);
}

#[test]
fn the_overtime_box() {
    let over = app_at(12, 51).overtime_due().expect("overtime is due");
    insta::assert_snapshot!(overlay(|f| {
        prompts::draw(f, Rect::new(0, 0, 80, 12), &Prompt::Overtime(over.clone()));
    }));
}

#[test]
fn the_overtime_prompt_asks_again_after_the_reprompt_interval() {
    let cfg = tui_common::config();
    let mut app = app_at(12, 51);
    assert!(app.raise_prompt());
    // Answering with anything else clears it and starts the 15m clock (§9.1).
    let action = app.action_for(key('z'));
    assert_eq!(action, Action::Answer(Answer::Later));
    assert!(app.apply(action).is_empty());
    assert!(app.prompt.is_none());
    // Ten minutes later it stays quiet; seventeen minutes later it is back.
    app.tick(tui_common::at(&cfg, 13, 1));
    assert!(app.prompt.is_none());
    app.tick(tui_common::at(&cfg, 13, 8));
    assert!(app.prompt.is_some(), "back after overtime_reprompt_min");
}

#[test]
fn the_overtime_box_names_what_extending_would_drop() {
    // §9.1: the consequence is computed by re-planning with the extension.
    // On a day whose budget is nearly spent the extra block costs the tail.
    let over = tui_common::tight_overtime_app()
        .overtime_due()
        .expect("overtime is due");
    assert_eq!(over.drops, vec!["Claude Code drafts tests (p3)"]);
    insta::assert_snapshot!(overlay(|f| {
        prompts::draw(f, Rect::new(0, 0, 80, 12), &Prompt::Overtime(over.clone()));
    }));
}

#[test]
fn the_overtime_keys_run_the_matching_verbs() {
    for (k, verb) in [('x', "extend"), ('s', "stop"), ('d', "done")] {
        let mut app = app_at(12, 51);
        assert!(app.raise_prompt());
        let action = app.action_for(key(k));
        let effects = app.apply(action);
        assert_eq!(effects, vec![Effect::Verb(vec![verb.to_string()])]);
        assert!(app.prompt.is_none());
    }
}

#[test]
fn the_idle_prompt_fires_after_idle_min_with_nothing_running() {
    // The last log entry is the 09:32 start; with no active block, 09:50 is
    // 18 minutes of nothing (cfg.day.idle_min = 12).
    assert!(idle_app(9, 40).idle_due().is_none());
    let idle = idle_app(9, 50).idle_due().expect("idle is due");
    assert_eq!(idle.minutes, 18);
}

#[test]
fn the_idle_box() {
    let idle = idle_app(9, 50).idle_due().expect("idle is due");
    insta::assert_snapshot!(overlay(|f| {
        prompts::draw(f, Rect::new(0, 0, 80, 12), &Prompt::Idle(idle.clone()));
    }));
}

#[test]
fn the_idle_keys_attribute_the_gap() {
    for (k, arg) in [
        ('w', "w"),
        ('b', "b"),
        ('t', "t"),
        ('i', "i"),
        ('l', "l"),
    ] {
        let mut app = idle_app(9, 50);
        assert!(app.raise_prompt());
        let action = app.action_for(key(k));
        let effects = app.apply(action);
        assert_eq!(
            effects,
            vec![Effect::Verb(vec!["idle".to_string(), arg.to_string()])]
        );
    }
}

#[test]
fn the_help_overlay() {
    insta::assert_snapshot!(overlay_sized(84, 18, |f| prompts::draw_help(f, f.area())));
}

#[test]
fn the_help_overlay_is_clipped_rather_than_lost_on_a_small_terminal() {
    // `centred` never draws outside the frame it is given.
    let small = overlay_sized(30, 5, |f| prompts::draw_help(f, f.area()));
    assert_eq!(small.lines().count(), 5);
    insta::assert_snapshot!(small);
}

#[test]
fn the_help_overlay_is_drawn_over_the_screen() {
    let mut app = app();
    let action = app.action_for(key('?'));
    app.apply(action);
    assert_eq!(app.mode, Mode::Help);
    let mut term = Terminal::new(TestBackend::new(120, 30)).expect("terminal");
    term.draw(|f| today::draw(f, &app)).expect("draw");
    insta::assert_snapshot!(term.backend().to_string());
    // Any key closes it.
    let action = app.action_for(key('j'));
    assert_eq!(action, Action::Cancel);
    app.apply(action);
    assert_eq!(app.mode, Mode::Normal);
}

#[test]
fn a_prompt_is_drawn_over_the_screen() {
    let mut app = app_at(12, 51);
    assert!(app.raise_prompt());
    let mut term = Terminal::new(TestBackend::new(120, 30)).expect("terminal");
    term.draw(|f| today::draw(f, &app)).expect("draw");
    insta::assert_snapshot!(term.backend().to_string());
}
