//! The exhaustive screen router (AGENTS.md §8.1 scope item 7; the second row
//! of PLAN-lean-kernel.md §4's integration-bug table: "a finished screen
//! never routed into the binary").
//!
//! The compile-time half already lives in the source and this test leans on
//! it: [`Screen`] is an enum, and every dispatch on it — `App::screen_key`'s
//! key router, `today::draw`'s body match, `Screen::title` — is a `match`
//! with no `_` arm, so adding a screen without routing it is a compile
//! error. [`digit_of`] below extends that guarantee to *this* test: it too
//! matches every variant by name, so a new screen refuses to compile here
//! until it gets a key and a smoke case.
//!
//! The runtime half: open every screen by its §12.6 digit through the same
//! `action_for` → `apply` path the binary's event loop drives (`tui/mod.rs`
//! line ~280), draw the whole frame into a ratatui `TestBackend`, and assert
//! the first frame has a non-empty body that differs from every other
//! screen's — a screen that routed but drew nothing, or drew some other
//! screen's body, fails here.

mod cli_common;
mod tui_common;

use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};
use tui_common::app::{Action, Screen};

/// A plain character keystroke, as the terminal driver would deliver it.
fn key(c: char) -> KeyEvent {
    KeyEvent::new(KeyCode::Char(c), KeyModifiers::NONE)
}

/// The §12.6 digit that opens each screen. **No `_` arm on purpose**: a new
/// `Screen` variant is a compile error on this match until it is given a key
/// here — which is what makes the smoke loop below exhaustive by
/// construction, not by convention.
fn digit_of(s: Screen) -> char {
    match s {
        Screen::Today => '1',
        Screen::Queue => '2',
        Screen::Necessities => '3',
        Screen::Review => '4',
        Screen::Inbox => '5',
    }
}

/// The frame's body: everything between the status/day-bar head and the
/// hint line, joined back together.
fn body_of(frame: &str) -> String {
    let lines: Vec<&str> = frame.lines().collect();
    // Head is status row + day bar (2 rows); the last row is the hint line.
    lines[3..lines.len().saturating_sub(1)].join("\n")
}

#[test]
fn every_screen_opens_by_its_key_and_draws_a_distinct_first_frame() {
    // `Screen::ALL` and `digit_of` must agree on the full variant list:
    // `digit_of` is exhaustive by `match`, and this loop walks `ALL`, so a
    // variant missing from `ALL` still fails `from_digit` round-trip below
    // the moment `digit_of` is extended for it.
    assert_eq!(Screen::ALL.len(), 5, "extend digit_of, ALL and this test together");

    let mut frames: Vec<(Screen, String)> = Vec::new();
    for s in Screen::ALL {
        let d = digit_of(s);
        assert_eq!(
            Screen::from_digit(d),
            Some(s),
            "the digit {d} must route to {s:?} (Screen::from_digit)"
        );

        // Through the binary's own path: resolve the keystroke, apply it.
        let mut a = tui_common::app();
        let action = a.action_for(key(d));
        assert_eq!(
            action,
            Action::Screen(s),
            "pressing {d} in Normal mode must resolve to Action::Screen({s:?})"
        );
        a.apply(action);
        assert_eq!(a.screen, s, "apply must land on {s:?}");

        let frame = tui_common::render(&a, 120, 30);
        let body = body_of(&frame);
        assert!(
            body.chars().any(|c| !c.is_whitespace()),
            "{s:?}'s first frame has an empty body:\n{frame}"
        );
        frames.push((s, body));
    }

    // Distinct bodies: a screen that routed but rendered another screen's
    // pane (the G-class bug this test exists for) collides here.
    for i in 0..frames.len() {
        for j in (i + 1)..frames.len() {
            assert_ne!(
                frames[i].1, frames[j].1,
                "{:?} and {:?} drew the same body — one of them is not routed",
                frames[i].0, frames[j].0
            );
        }
    }
}

#[test]
fn a_digit_outside_the_screen_list_routes_nowhere() {
    // `from_digit` must not invent a sixth screen.
    for c in ['0', '6', '7', '8', '9'] {
        assert_eq!(Screen::from_digit(c), None, "digit {c}");
    }
    let mut a = tui_common::app();
    let action = a.action_for(key('6'));
    assert_eq!(action, Action::None);
    a.apply(action);
    assert_eq!(a.screen, Screen::Today);
}
