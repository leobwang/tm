//! §9's two prompts and the `?` help overlay (tm-spec-v1.md §9.1, §9.2,
//! §12.6).

mod tui_common;

use ratatui::backend::TestBackend;
use ratatui::layout::Rect;
use ratatui::Terminal;

use chrono::{NaiveTime, TimeZone};

use tm_core::log::Event;
use tm_core::model::Id;
use tm_core::store::{ActiveBlock, BreakState};

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
fn the_idle_keys_attribute_the_gap_and_make_the_transition() {
    // §9.2 / §9's table: `w` starts the next block, `b` a break, `i` an
    // interruption — each *after* the gap has been attributed (`tm idle …`,
    // which is what keeps the leak ledger honest). `t` and `l` only attribute:
    // §13 has no verb that starts a routine, and a leak starts nothing.
    let verb = |args: &[&str]| {
        Effect::Verb(args.iter().map(|s| (*s).to_string()).collect::<Vec<_>>())
    };
    let cases: Vec<(char, Vec<Effect>)> = vec![
        ('w', vec![verb(&["idle", "w"]), verb(&["start", "^t3"])]),
        ('b', vec![verb(&["idle", "b"]), verb(&["break"])]),
        ('t', vec![verb(&["idle", "t"])]),
        ('i', vec![verb(&["idle", "i"]), verb(&["interrupt"])]),
        ('l', vec![verb(&["idle", "l"])]),
    ];
    for (k, want) in cases {
        let mut app = idle_app(9, 50);
        assert!(app.raise_prompt());
        let action = app.action_for(key(k));
        assert_eq!(app.apply(action), want, "key {k}");
    }
}

#[test]
fn the_overtime_box_names_the_remainder_that_stays_in_the_week_queue() {
    // §9.1's `s stop, demote rest → 0.5b stays in week queue`: the line is the
    // item's remaining estimate minus what has been worked, which is only
    // interesting when it does not hit the `MIN_REMAINING_MIN` floor.
    // `^m1` is 6b; 5h30m of it are gone by 15:02, so half a block is left.
    let over = tui_common::overtime_app_for("m1", 300, 15, 2)
        .overtime_due()
        .expect("overtime is due");
    assert_eq!(over.elapsed_min, 330);
    assert_eq!(over.stays, "0.5b");
    insta::assert_snapshot!(overlay(|f| {
        prompts::draw(f, Rect::new(0, 0, 80, 12), &Prompt::Overtime(over.clone()));
    }));
}

#[test]
fn the_elapsed_minutes_are_worked_minutes_not_wall_clock() {
    // §9.1 fires at `est × r` of *worked* time: a pause (§12.6's `Space`) does
    // not bring the prompt closer, and the number in the box is the one
    // `planner::active_run` sizes the rest of the block from.
    let cfg = tui_common::config();
    let paused = tui_common::log_plus(
        &cfg,
        vec![
            tui_common::entry(&cfg, 11, 0, Event::Pause { id: "t3".into() }),
            tui_common::entry(&cfg, 11, 20, Event::Unpause { id: "t3".into() }),
        ],
    );
    let at = |h, m| tui_common::at(&cfg, h, m);
    let app = tui_common::app_with_log_text(at(12, 51), tui_common::state(), &paused);
    assert_eq!(app.active_elapsed_min(), Some(179), "199 wall, 20 paused");
    assert!(app.overtime_due().is_none(), "not yet 192 worked minutes");
    // 09:32 → 11:00 is 88 worked; 192 is reached 104 minutes after the
    // unpause, at 13:04 — twenty minutes later than the wall clock would say.
    let app = tui_common::app_with_log_text(at(13, 4), tui_common::state(), &paused);
    let over = app.overtime_due().expect("192 worked minutes by 13:04");
    assert_eq!(over.elapsed_min, 192);
}

#[test]
fn a_block_started_before_midnight_still_goes_overtime() {
    // §10.2: `active.started` is a bare `HH:MM` and `state.date` says which
    // day it belongs to. Anchoring it to *today* makes a block that started at
    // 23:30 report zero elapsed for ever.
    let cfg = tui_common::config();
    let mut state = tui_common::state();
    if let Some(active) = state.active.as_mut() {
        active.started = NaiveTime::from_hms_opt(23, 30, 0).expect("time");
        active.est_min = 60;
    }
    let midnight = cfg
        .tz
        .from_local_datetime(
            &tui_common::date()
                .succ_opt()
                .expect("tomorrow")
                .and_hms_opt(0, 30, 0)
                .expect("time"),
        )
        .single()
        .expect("unambiguous");
    // An empty log: the state is all there is to go on.
    let app = tui_common::app_with_log_text(midnight, state, "");
    assert_eq!(app.active_elapsed_min(), Some(60));
    assert!(app.overtime_due().is_some(), "an hour into a one-hour block");
}

#[test]
fn a_break_that_overran_still_raises_the_idle_prompt() {
    // §9's "Break overran" row. `tm break` pauses the block, so the overtime
    // prompt is silent by design; nothing else may be, or an unended break
    // hides the whole afternoon from the leak ledger (§11).
    let cfg = tui_common::config();
    let mut state = tui_common::state();
    // A 20-minute break from 12:00, inside the 11:50 block of the hand-built
    // day and before the 12:50 wall (a meeting *is* something running).
    state.break_ = Some(BreakState {
        started: Some(NaiveTime::from_hms_opt(12, 0, 0).expect("time")),
        planned_min: 20,
        place: Some("walk".to_string()),
    });
    if let Some(active) = state.active.as_mut() {
        active.paused = true;
    }
    let app = tui_common::app_with_log_text(tui_common::at(&cfg, 12, 25), state.clone(), &log_of(&cfg));
    assert!(app.idle_due().is_none(), "five minutes over is not idle yet");
    let app = tui_common::app_with_log_text(tui_common::at(&cfg, 12, 45), state, &log_of(&cfg));
    assert!(app.overtime_due().is_none(), "the timer is paused");
    let idle = app.idle_due().expect("25 minutes past a 20m break");
    assert_eq!(idle.minutes, 25);
}

/// The fixture log (a second copy, for tests that build two apps).
fn log_of(cfg: &tm_core::config::Config) -> String {
    tui_common::log(cfg)
}

#[test]
fn the_two_prompts_keep_their_own_clocks() {
    // §9.1 fires "at est × r, then every overtime_reprompt_min" — answering
    // §9.2's idle prompt must not start that clock.
    let mut app = idle_app(9, 50);
    assert!(app.raise_prompt(), "the idle prompt");
    let action = app.action_for(key('l'));
    app.apply(action);
    assert!(app.idle_at.is_some());
    assert!(app.overtime_at.is_none(), "the overtime clock is untouched");
    // A block that is already past its estimate prompts straight away.
    app.state.active = Some(ActiveBlock {
        id: Id::new("t3"),
        started: NaiveTime::from_hms_opt(9, 32, 0).expect("time"),
        est_min: 10,
        paused: false,
    });
    assert!(app.overtime_due().is_some(), "§9.1 is not on §9.2's clock");
}

#[test]
fn a_prompt_never_steals_a_character_from_the_command_line() {
    // §12.6's `:` line takes any §13 verb. A prompt raised under it used to
    // swallow the next key: the `s` of `start …` ran `tm stop`.
    let mut app = tui_common::tight_overtime_app();
    let action = app.action_for(key(':'));
    app.apply(action);
    assert_eq!(app.mode, Mode::Command);
    assert!(!app.raise_prompt(), "no prompt while a line is being typed");
    app.tick(tui_common::at(&tui_common::config(), 12, 51));
    assert!(app.prompt.is_none(), "not on a tick either");
    // Even with one open, the character belongs to the line.
    app.prompt = Some(Prompt::Overtime(
        tui_common::tight_overtime_app()
            .overtime_due()
            .expect("overtime is due"),
    ));
    for c in "start ^t4".chars() {
        let action = app.action_for(key(c));
        assert!(
            matches!(action, Action::Input(_)),
            "{c:?} became {action:?}"
        );
        assert!(app.apply(action).is_empty());
    }
    assert_eq!(app.input, "start ^t4");
}

#[test]
fn the_help_overlay() {
    insta::assert_snapshot!(overlay_sized(84, 18, |f| prompts::draw_help(f, f.area())));
}

#[test]
fn the_help_overlay_is_clipped_rather_than_lost_on_a_small_terminal() {
    // `centred` clamps the box to the frame it is given instead of drawing
    // nothing (a `TestBackend` always prints `height` rows, so counting them
    // would prove nothing — what matters is that the box is *there*).
    let small = overlay_sized(30, 5, |f| prompts::draw_help(f, f.area()));
    assert!(small.contains('┌') && small.contains('└'), "a box: {small}");
    assert!(small.contains("Keys"), "with its title: {small}");
    assert!(
        small.contains("screens"),
        "and the first row of §12.6: {small}"
    );
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
