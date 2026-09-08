//! The day-bar widget: cells, cursor, ghost row, hover tooltip and click
//! (tm-spec-v1.md §12.1, §17.2's "Mouse").

mod tui_common;

use ratatui::backend::TestBackend;
use ratatui::layout::Rect;
use ratatui::Terminal;

use tui_common::{app, daybar, today};

/// Draw only the two day-bar rows.
fn render_bar(app: &tui_common::app::App, width: u16) -> String {
    let mut term = Terminal::new(TestBackend::new(width, 2)).expect("terminal");
    term.draw(|f| daybar::draw(f, Rect::new(0, 0, width, 2), app))
        .expect("draw");
    term.backend().to_string()
}

#[test]
fn the_two_rows_of_cells() {
    insta::assert_snapshot!(render_bar(&app(), 120));
}

#[test]
fn the_cells_at_the_configured_minimum_width() {
    insta::assert_snapshot!(render_bar(&app(), 110));
}

#[test]
fn the_cursor_column_is_where_now_is() {
    let app = app();
    let bar = daybar::bar(&app, 96);
    // The bar runs wake → wake (06:05 → 06:05); 10:42 is 4h37m in, so the
    // cursor sits at 4.62/24 of the way across.
    assert_eq!(bar.cursor_col, 18);
    assert_eq!(bar.cols, 96);
}

#[test]
fn hovering_a_column_gives_the_spec_tooltip() {
    let app = app();
    let bar = daybar::bar(&app, 96);
    // Column 18 is the running block, ^t3 (§12.1: title · dur · ci · p · @root).
    insta::assert_snapshot!(daybar::tooltip(&bar, bar.cursor_col).expect("tooltip"));
}

#[test]
fn every_kind_of_cell_has_a_tooltip_of_its_own() {
    let app = app();
    let bar = daybar::bar(&app, 96);
    let mut seen: Vec<String> = Vec::new();
    for col in 0..bar.cols {
        if let Some(text) = daybar::tooltip(&bar, col) {
            if !seen.contains(&text) {
                seen.push(text);
            }
        }
    }
    insta::assert_snapshot!(seen.join("\n"));
}

#[test]
fn the_tooltip_is_drawn_over_the_ghost_row() {
    let mut app = app();
    let bar = daybar::bar(&app, daybar::bar_width(Rect::new(0, 0, 120, 2)));
    let col = bar.cursor_col;
    app.hover = Some(tui_common::app::Hover {
        col,
        text: daybar::tooltip(&bar, col).expect("tooltip"),
    });
    let mut term = Terminal::new(TestBackend::new(120, 2)).expect("terminal");
    term.draw(|f| {
        let area = Rect::new(0, 0, 120, 2);
        daybar::draw(f, area, &app);
        daybar::draw_tooltip(f, area, app.hover.as_ref().expect("hover"));
    })
    .expect("draw");
    insta::assert_snapshot!(term.backend().to_string());
}

#[test]
fn a_click_selects_the_item_under_the_pointer() {
    let mut app = app();
    let area = today::bar_area(&app, Rect::new(0, 0, 120, 30));
    let bar = daybar::bar(&app, daybar::bar_width(area));
    // Click on the cursor column — the running block.
    let col = daybar::hit(area, area.x + u16::try_from(bar.cursor_col).expect("col"), area.y)
        .expect("inside the bar");
    let segment = daybar::segment_at(&bar, col).expect("a segment");
    app.select_segment(segment);
    assert_eq!(
        app.selected_item.as_ref().map(|i| i.to_string()),
        Some("t3".to_string())
    );
}

#[test]
fn the_mouse_misses_outside_the_bar() {
    let app = app();
    let area = today::bar_area(&app, Rect::new(0, 0, 120, 30));
    // Right of the bar, where §12.1 prints `▲ 10:42`.
    assert_eq!(daybar::hit(area, 119, area.y), None);
    // Above the bar: the status line.
    assert_eq!(daybar::hit(area, 4, 0), None);
    // On the ghost row: still the bar.
    assert!(daybar::hit(area, 4, area.y + 1).is_some());
}
