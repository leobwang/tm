//! §12.6's keymap, row by row (tm-spec-v1.md §12.6, §9).
//!
//! Every key of the `global` and `today` rows is mapped to its action, and
//! every action that changes a fact is checked to produce the §13 verb the
//! CLI would run — §12's "every action goes through the same code path the
//! CLI verbs use".

mod tui_common;

use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

use tui_common::app::{
    resolve, Action, Answer, BreakPlace, Effect, InputKind, Mode, PromptKind, Screen,
};
use tui_common::{app, app_at, review};

/// A plain keystroke.
fn k(code: KeyCode) -> KeyEvent {
    KeyEvent::new(code, KeyModifiers::NONE)
}

/// A character keystroke.
fn c(ch: char) -> KeyEvent {
    k(KeyCode::Char(ch))
}

/// How a key prints in the table snapshot.
fn name(key: KeyEvent) -> String {
    match key.code {
        KeyCode::Char(' ') => "Space".to_string(),
        KeyCode::Char(ch) => ch.to_string(),
        other => format!("{other:?}"),
    }
}

/// §12.6's `global` and `today` rows, in the order the table lists them.
fn today_rows() -> Vec<(KeyEvent, Action)> {
    vec![
        (c('1'), Action::Screen(Screen::Today)),
        (c('2'), Action::Screen(Screen::Queue)),
        (c('3'), Action::Screen(Screen::Necessities)),
        (c('4'), Action::Screen(Screen::Review)),
        (c('5'), Action::Screen(Screen::Inbox)),
        (c('?'), Action::Help),
        (c(':'), Action::CommandLine),
        (c('q'), Action::Quit),
        (c('e'), Action::Edit),
        (c('r'), Action::ReplanOrResume),
        (c('R'), Action::Sync),
        (c('d'), Action::Done),
        (c('x'), Action::Extend),
        (c('s'), Action::Stop),
        (c('b'), Action::Break),
        (c('i'), Action::Interrupt),
        (c('0'), Action::EnergyPrompt),
        (c('l'), Action::Location),
        (c('K'), Action::SkipRoutine),
        (c('n'), Action::Note),
        (c(' '), Action::Pause),
        (c('j'), Action::SelectNext),
        (c('k'), Action::SelectPrev),
        (k(KeyCode::Down), Action::SelectNext),
        (k(KeyCode::Up), Action::SelectPrev),
        (k(KeyCode::Enter), Action::Open),
        (k(KeyCode::Esc), Action::Cancel),
    ]
}

#[test]
fn every_key_of_the_today_rows_maps_to_its_action() {
    let mut table = String::new();
    for (key, want) in today_rows() {
        let got = resolve(Screen::Today, Mode::Normal, None, key);
        assert_eq!(got, want, "key {}", name(key));
        table.push_str(&format!("{:<6} {got:?}\n", name(key)));
    }
    insta::assert_snapshot!(table);
}

#[test]
fn the_break_chord_covers_all_four_places() {
    let places = [
        ('w', BreakPlace::Walk),
        ('s', BreakPlace::Seat),
        ('b', BreakPlace::Bed),
        ('p', BreakPlace::Phone),
    ];
    for (key, place) in places {
        assert_eq!(
            resolve(Screen::Today, Mode::BreakWhere, None, c(key)),
            Action::BreakWhere(place)
        );
    }
}

#[test]
fn the_energy_report_takes_zero_to_five() {
    for level in 0..=5u8 {
        let key = c(char::from_digit(u32::from(level), 10).expect("digit"));
        assert_eq!(
            resolve(Screen::Today, Mode::Energy, None, key),
            Action::Energy(level)
        );
    }
}

#[test]
fn the_command_line_collects_text() {
    assert_eq!(
        resolve(Screen::Today, Mode::Command, None, c('p')),
        Action::Input('p')
    );
    assert_eq!(
        resolve(Screen::Today, Mode::Command, None, k(KeyCode::Enter)),
        Action::Submit
    );
    assert_eq!(
        resolve(Screen::Today, Mode::Command, None, k(KeyCode::Backspace)),
        Action::Backspace
    );
    assert_eq!(
        resolve(
            Screen::Today,
            Mode::Input(InputKind::Note),
            None,
            k(KeyCode::Esc)
        ),
        Action::Cancel
    );
}

#[test]
fn a_prompt_takes_precedence_over_every_row() {
    assert_eq!(
        resolve(
            Screen::Today,
            Mode::Normal,
            Some(PromptKind::Overtime),
            c('x')
        ),
        Action::Answer(Answer::Extend)
    );
    assert_eq!(
        resolve(Screen::Today, Mode::Normal, Some(PromptKind::Idle), c('w')),
        Action::Answer(Answer::Work)
    );
    // §12.6's `q` does not quit while a prompt is up (§9.1: "any other key").
    assert_eq!(
        resolve(
            Screen::Today,
            Mode::Normal,
            Some(PromptKind::Overtime),
            c('q')
        ),
        Action::Answer(Answer::Later)
    );
}

#[test]
fn a_character_being_typed_is_never_a_prompt_answer() {
    // …but not over a line being typed: the `s` of `start …` is text, not
    // §9.1's "stop" (§12.6's `:` command line, `n` note, `l` location).
    for mode in [
        Mode::Command,
        Mode::Input(InputKind::Note),
        Mode::Input(InputKind::Location),
    ] {
        for kind in [PromptKind::Overtime, PromptKind::Idle] {
            assert_eq!(
                resolve(Screen::Today, mode.clone(), Some(kind), c('s')),
                Action::Input('s'),
                "{mode:?} + {kind:?}"
            );
            assert_eq!(
                resolve(Screen::Today, mode.clone(), Some(kind), k(KeyCode::Enter)),
                Action::Submit
            );
        }
    }
}

#[test]
fn ctrl_c_always_quits() {
    let key = KeyEvent::new(KeyCode::Char('c'), KeyModifiers::CONTROL);
    assert_eq!(
        resolve(Screen::Today, Mode::Command, None, key),
        Action::Quit
    );
}

#[test]
fn the_help_overlay_swallows_the_next_key() {
    assert_eq!(
        resolve(Screen::Today, Mode::Help, None, c('d')),
        Action::Cancel
    );
}

#[test]
fn the_clock_verbs_reach_the_cli() {
    let cases: Vec<(char, Vec<&str>)> = vec![
        ('d', vec!["done"]),
        ('x', vec!["extend"]),
        ('s', vec!["stop"]),
        ('i', vec!["interrupt"]),
        (' ', vec!["pause"]),
        ('r', vec!["plan"]),
    ];
    for (key, verb) in cases {
        let mut app = app();
        let action = app.action_for(c(key));
        let effects = app.apply(action);
        assert_eq!(
            effects,
            vec![Effect::Verb(verb.iter().map(|s| (*s).to_string()).collect())],
            "key {key}"
        );
    }
}

#[test]
fn r_resumes_while_an_interruption_is_open() {
    let mut app = app();
    app.state.interrupt = Some(tm_core::store::InterruptState {
        started: None,
        id: None,
    });
    let action = app.action_for(c('r'));
    assert_eq!(action, Action::ReplanOrResume);
    assert_eq!(
        app.apply(action),
        vec![Effect::Verb(vec!["resume".to_string()])]
    );
}

#[test]
fn the_break_chord_runs_tm_break_with_where() {
    let mut app = app();
    let action = app.action_for(c('b'));
    assert_eq!(app.apply(action), Vec::new());
    assert_eq!(app.mode, Mode::BreakWhere);
    let action = app.action_for(c('w'));
    assert_eq!(
        app.apply(action),
        vec![Effect::Verb(vec![
            "break".to_string(),
            "--where".to_string(),
            "walk".to_string()
        ])]
    );
    assert_eq!(app.mode, Mode::Normal);
}

#[test]
fn the_energy_chord_runs_tm_energy() {
    let mut app = app();
    let action = app.action_for(c('0'));
    app.apply(action);
    assert_eq!(app.mode, Mode::Energy);
    let action = app.action_for(c('4'));
    assert_eq!(
        app.apply(action),
        vec![Effect::Verb(vec!["energy".to_string(), "4".to_string()])]
    );
}

#[test]
fn r_capital_syncs_then_replans() {
    let mut app = app();
    let action = app.action_for(c('R'));
    assert_eq!(
        app.apply(action),
        vec![
            Effect::Verb(vec!["sync-cal".to_string()]),
            Effect::Verb(vec!["plan".to_string()]),
        ]
    );
}

#[test]
fn the_command_line_runs_any_cli_verb() {
    let mut app = app();
    let action = app.action_for(c(':'));
    app.apply(action);
    for ch in "edit ^t3 est=1b".chars() {
        let action = app.action_for(c(ch));
        app.apply(action);
    }
    let action = app.action_for(k(KeyCode::Enter));
    assert_eq!(
        app.apply(action),
        vec![Effect::Verb(vec![
            "edit".to_string(),
            "^t3".to_string(),
            "est=1b".to_string()
        ])]
    );
    assert_eq!(app.mode, Mode::Normal);
}

#[test]
fn the_note_and_location_keys_have_their_own_effects() {
    let mut app = app();
    let action = app.action_for(c('n'));
    app.apply(action);
    assert_eq!(app.mode, Mode::Input(InputKind::Note));
    for ch in "phone call".chars() {
        let action = app.action_for(c(ch));
        app.apply(action);
    }
    let action = app.action_for(k(KeyCode::Enter));
    assert_eq!(
        app.apply(action),
        vec![Effect::Note("phone call".to_string())]
    );

    let action = app.action_for(c('l'));
    app.apply(action);
    for ch in "home".chars() {
        let action = app.action_for(c(ch));
        app.apply(action);
    }
    let action = app.action_for(k(KeyCode::Enter));
    assert_eq!(
        app.apply(action),
        vec![Effect::SetLocation("home".to_string())]
    );
}

#[test]
fn e_opens_the_selected_line_in_the_editor() {
    let mut app = app();
    // The first row is the 07:00 block on ^t1.
    app.select(0);
    let action = app.action_for(c('e'));
    assert_eq!(
        app.apply(action),
        vec![Effect::Editor {
            file: "week/2026-W37.md".to_string(),
            line: 17,
        }]
    );
}

#[test]
fn j_and_k_move_the_selection_and_enter_drills() {
    let mut app = app();
    assert_eq!(app.selection, 0);
    for _ in 0..3 {
        let action = app.action_for(c('j'));
        app.apply(action);
    }
    assert_eq!(app.selection, 3);
    assert_eq!(
        app.selected_item.as_ref().map(|i| i.to_string()),
        Some("t3".to_string())
    );
    let action = app.action_for(c('k'));
    app.apply(action);
    assert_eq!(app.selection, 2);
    // Row 2 is the break: it names no item, so `Enter` has nothing to drill.
    let action = app.action_for(k(KeyCode::Enter));
    app.apply(action);
    assert_eq!(app.screen, Screen::Today);
    let action = app.action_for(c('j'));
    app.apply(action);
    let action = app.action_for(k(KeyCode::Enter));
    app.apply(action);
    assert_eq!(app.screen, Screen::Queue);
}

#[test]
fn skipping_needs_a_routine_row() {
    let mut app = app();
    // Row 4 is the lunch routine of the hand-built day.
    app.select(4);
    let action = app.action_for(c('K'));
    assert_eq!(
        app.apply(action),
        vec![Effect::Verb(vec!["skip".to_string(), "lunch".to_string()])]
    );
    // On a block row it says so instead of guessing.
    app.select(-4);
    let action = app.action_for(c('K'));
    assert!(app.apply(action).is_empty());
    assert!(app.message.is_some());
}

#[test]
fn q_quits() {
    let mut app = app_at(10, 42);
    let action = app.action_for(c('q'));
    assert_eq!(app.apply(action), vec![Effect::Quit]);
    assert!(app.quit);
}

#[test]
fn screens_two_to_five_own_their_keys_and_keep_the_global_row() {
    // §12.6: screens 2–5 have their own rows (`h l j k J K Enter a c E P D A
    // x`, `E t k e`), which the global `j`/`k`/`Enter`/`e` would otherwise
    // swallow — so every key but the five that can never be taken is offered
    // to the screen first.
    for screen in [Screen::Queue, Screen::Necessities, Screen::Review, Screen::Inbox] {
        for key in ['r', 'j', 'k', 'J', 'K', 'h', 'l', 'a', 'c', 'E', 'P', 'D', 'A', 'x', 't'] {
            assert_eq!(
                resolve(screen, Mode::Normal, None, c(key)),
                Action::ScreenKey(c(key)),
                "{screen:?} {key}"
            );
        }
        // The five the screens may not take.
        assert_eq!(resolve(screen, Mode::Normal, None, c('1')), Action::Screen(Screen::Today));
        assert_eq!(resolve(screen, Mode::Normal, None, c('?')), Action::Help);
        assert_eq!(resolve(screen, Mode::Normal, None, c(':')), Action::CommandLine);
        assert_eq!(resolve(screen, Mode::Normal, None, c('q')), Action::Quit);
        assert_eq!(resolve(screen, Mode::Normal, None, c('R')), Action::Sync);
    }

    // A key the screen ignores falls through to the global row: `r` replans.
    let mut app = app_at(10, 42);
    app.screen = Screen::Review;
    let action = app.action_for(c('r'));
    assert_eq!(
        app.apply(action),
        vec![Effect::Verb(vec!["plan".to_string()])]
    );
}

/// §12.6's `queue` row reaches `queue::on_key` from the shipped binary: `J`
/// asks for the byte-faithful reorder, `D`/`A`/`x` for their §13 verbs and
/// `a c E P` for the value prompt. They used to resolve to `Action::None`,
/// because the module was not in the binary's `mod` list at all.
#[test]
fn the_queue_row_reaches_the_queue_screen() {
    let mut app = app_at(10, 42);
    app.screen = Screen::Queue;
    // `l` moves to the Tasks pane, `j` down a row — the screen's own keys.
    for key in ['l', 'j'] {
        let action = app.action_for(c(key));
        assert!(app.apply(action).is_empty(), "{key} produced an effect");
    }
    assert!(app.selected_item.is_some(), "the queue cursor selects an item");

    // `D` is `tm demote ^id`.
    let action = app.action_for(c('D'));
    let effects = app.apply(action);
    assert!(
        effects.iter().any(|e| matches!(e, Effect::Verb(a) if a[0] == "demote"))
            || app.message.is_some(),
        "D did nothing: {effects:?}"
    );

    // `c` opens the ci prompt (§12.6's `c ci`).
    app.screen = Screen::Queue;
    let action = app.action_for(c('c'));
    assert!(app.apply(action).is_empty());
    assert!(
        matches!(app.mode, Mode::Input(InputKind::Screen(_))),
        "{:?}",
        app.mode
    );
}

/// Screen 4 exists and answers §12.4's own keys.
#[test]
fn the_review_screen_shows_the_monitors() {
    let mut app = app_at(10, 42);
    app.screen = Screen::Review;
    let reviews = app.reviews();
    assert!(
        reviews.text(review::Period::Day).contains("adherence"),
        "{}",
        reviews.text(review::Period::Day)
    );
    // `l` moves Day → Week.
    let action = app.action_for(c('l'));
    assert!(app.apply(action).is_empty());
    assert_eq!(app.review.period, review::Period::Week);
    // `w` offers §12.4's "write to day file".
    let action = app.action_for(c('w'));
    assert!(app.apply(action).is_empty());
    assert_eq!(app.message.as_deref(), Some("review week --write"));
}
