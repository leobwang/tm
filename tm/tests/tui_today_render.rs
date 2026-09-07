//! Screen 1 — Today, rendered (tm-spec-v1.md §12.1, §17 M6: "`ratatui`
//! `TestBackend` snapshots of each pane at 120 and 90 columns").
//!
//! Every snapshot comes from a hand-built `App`: the `plan-basic` fixture,
//! a fixed `now` of 2026-09-07 10:42 and the hand-written `DayPlan` of
//! `tui_common::day_plan`, so nothing here moves when the planner changes.

mod tui_common;

use tui_common::today;
use tui_common::{app, app_at, lines, render, render_lines};

#[test]
fn the_whole_screen_at_120_columns() {
    insta::assert_snapshot!(render(&app(), 120, 30));
}

#[test]
fn the_whole_screen_at_90_columns_stacks_the_panes() {
    // §12: "below that, panes stack (Now on top, Timeline below, Week folded
    // into the status line)".
    insta::assert_snapshot!(render(&app(), 90, 34));
}

#[test]
fn the_status_line() {
    insta::assert_snapshot!(lines(&[today::status_line(&app(), 120)]));
}

#[test]
fn the_week_fold_used_below_min_width() {
    insta::assert_snapshot!(lines(&[today::week_fold(&app(), 90)]));
}

#[test]
fn the_timeline_pane() {
    insta::assert_snapshot!(render_lines(&today::timeline_lines(&app(), 38, 14), 38));
}

#[test]
fn the_timeline_pane_scrolls_to_keep_the_selection_visible() {
    let mut app = app();
    app.select(20);
    let rendered = render_lines(&today::timeline_lines(&app, 38, 5), 38);
    assert!(
        rendered.contains("wind-down"),
        "the last row must be on screen: {rendered}"
    );
    insta::assert_snapshot!(rendered);
}

#[test]
fn the_now_pane() {
    insta::assert_snapshot!(render_lines(&today::now_lines(&app(), 46), 46));
}

#[test]
fn the_now_pane_with_nothing_running() {
    // 16:30: past the last block of the hand-built day.
    insta::assert_snapshot!(render_lines(&today::now_lines(&app_at(16, 30), 46), 46));
}

#[test]
fn the_energy_pane() {
    insta::assert_snapshot!(render_lines(&today::energy_lines(&app(), 46), 46));
}

#[test]
fn the_week_pane() {
    let app = app();
    let title = today::week_title(&app);
    let body = render_lines(&today::week_lines(&app, 38), 38);
    insta::assert_snapshot!(format!("{title}\n{body}"));
}

#[test]
fn the_hint_line() {
    insta::assert_snapshot!(lines(&[today::hint_line(&app(), 120)]));
}

#[test]
fn the_command_line_replaces_the_hint() {
    let mut app = app();
    let action = app.action_for(key(':'));
    app.apply(action);
    for c in "plan --diff".chars() {
        let action = app.action_for(key(c));
        app.apply(action);
    }
    insta::assert_snapshot!(lines(&[today::hint_line(&app, 120)]));
}

use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

/// A plain character keystroke.
fn key(c: char) -> KeyEvent {
    KeyEvent::new(KeyCode::Char(c), KeyModifiers::NONE)
}
