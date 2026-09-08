//! Screen 1 — Today, rendered (tm-spec-v1.md §12.1, §17 M6: "`ratatui`
//! `TestBackend` snapshots of each pane at 120 and 90 columns").
//!
//! Every snapshot comes from a hand-built `App`: the `plan-basic` fixture,
//! a fixed `now` of 2026-09-07 10:42 and the hand-written `DayPlan` of
//! `tui_common::day_plan`, so nothing here moves when the planner changes.

mod tui_common;

use tui_common::today;
use tui_common::{app, idle_app, lines, render, render_lines};

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
fn the_status_line_folds_the_week_in_below_min_width() {
    // §12: "Week folded into the status line" — one row, not a row of its own.
    let row = lines(&[today::status_row(&app(), 90)]);
    assert_eq!(row.lines().count(), 1);
    assert!(row.contains("W37"), "the week is in the status line: {row}");
    insta::assert_snapshot!(row);
}

#[test]
fn the_narrow_frame_spends_no_row_on_the_week() {
    // The frame is status · bar · bar · body … at either width, so the bar
    // sits on the same rows and `bar_area` can hit-test it (§17.2).
    let wide = render(&app(), 120, 30);
    let narrow = render(&app(), 90, 34);
    for screen in [&wide, &narrow] {
        let head = screen.lines().next().expect("a status row");
        assert!(head.contains("tm · Mon 2026-09-07"), "{head}");
        let bar = screen.lines().nth(1).expect("the plan bar");
        assert!(bar.contains("▲ 10:42"), "the bar follows the status row: {bar}");
    }
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
    // 16:30 with no `active` and no segment flagged current: past the last
    // block of the hand-built day, in the gap before dinner.
    let app = idle_app(16, 30);
    let pane = render_lines(&today::now_lines(&app, 46), 46);
    assert!(
        pane.contains("nothing running (16:30)"),
        "the idle row, not a block: {pane}"
    );
    insta::assert_snapshot!(pane);
}

#[test]
fn a_row_that_contains_the_divider_glyph_is_still_its_own_segment() {
    // The `───     window ends` divider is the one row that belongs to no
    // segment. Detecting it by searching the whole row for `───` would also
    // match an item's own text and shift every later row onto the wrong
    // segment — `e` would then open the wrong file and line (§12).
    let mut app = app();
    app.plan.segments[0].flags.note = Some("a ─── b".to_string());
    app.refresh();
    assert!(app.rows[0].text.contains("───"), "{}", app.rows[0].text);
    assert_eq!(app.rows[0].segment, Some(0));
    let mapped: Vec<usize> = app.rows.iter().filter_map(|r| r.segment).collect();
    assert_eq!(mapped, (0..app.plan.segments.len()).collect::<Vec<_>>());
    let dividers: Vec<&String> = app
        .rows
        .iter()
        .filter(|r| r.segment.is_none())
        .map(|r| &r.text)
        .collect();
    assert_eq!(dividers.len(), 1);
    assert!(dividers[0].contains("window ends"), "{}", dividers[0]);
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
