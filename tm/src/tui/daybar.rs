//! The day-bar widget (tm-spec-v1.md §12.1, §17.2).
//!
//! # API overview
//!
//! Two rows of §12.1: the plan row (log left of the cursor, plan right of it)
//! and the ghost row (the plan as it stood at arrival). The *geometry* is
//! [`tm_core::emit::daybar_cells`] — one cell per column over 24 h from wake
//! to wake, the palette hue from the root id, the brightness from `ci` — so
//! the terminal bar, `day/<date>.svg` and the tooltip all measure the same
//! way; this module only turns a [`Cell`] into a character and a colour
//! ([`super::theme::cell_glyph`], [`super::theme::cell_style`]) and answers
//! the mouse.
//!
//! * [`bar`] — the [`DayBar`] for an [`App`] at a given bar width.
//! * [`draw`] — the two rows plus §12.1's `▲ 10:42` / `plan @07:00` suffix.
//! * [`hit`] — the column a mouse position falls in, or `None` when the
//!   pointer is not over the bar (`MouseEventKind::Moved` → tooltip,
//!   `Down(Left)` → select, §17.2).
//! * [`tooltip`] — `title · duration · ci · p · @root` for a column, straight
//!   from the cell `emit` built.
//! * [`draw_tooltip`] — the hover box itself.

use ratatui::layout::Rect;
use ratatui::text::{Line, Span};
use ratatui::widgets::{Clear, Paragraph};
use ratatui::Frame;

use tm_core::emit::{self, Cell, DayBar};

use super::app::{App, Hover};
use super::theme;

/// Columns reserved on the right of each bar row for §12.1's label
/// (`▲ 10:42`, `plan @07:00`).
pub const LABEL_W: u16 = 14;

/// The width of the bar itself inside `area`.
pub fn bar_width(area: Rect) -> usize {
    usize::from(area.width.saturating_sub(LABEL_W)).max(1)
}

/// The day bar for `app`, `cols` columns wide (§12.1).
pub fn bar(app: &App, cols: usize) -> DayBar {
    emit::daybar_cells(
        &app.plan,
        app.ghost.as_ref(),
        &app.tree,
        &app.cfg,
        cols,
        app.wake(),
        app.now,
    )
}

/// The tooltip of one column: `title · duration · ci · p · @root` (§12.1).
///
/// `None` for a column with nothing in it.
pub fn tooltip(bar: &DayBar, col: usize) -> Option<String> {
    let cell = bar.cells.get(col)?;
    (!cell.tooltip.is_empty()).then(|| cell.tooltip.clone())
}

/// The segment a column belongs to, for `Down(Left)` (§17.2).
pub fn segment_at(bar: &DayBar, col: usize) -> Option<usize> {
    bar.cells.get(col).and_then(|c| c.segment)
}

/// The bar column a mouse position falls in, or `None` when the pointer is
/// outside the two bar rows or past the bar's right edge.
pub fn hit(area: Rect, column: u16, row: u16) -> Option<usize> {
    if row < area.y || row >= area.y.saturating_add(area.height) {
        return None;
    }
    if column < area.x {
        return None;
    }
    let x = usize::from(column - area.x);
    (x < bar_width(area)).then_some(x)
}

/// One row of cells as styled spans.
fn row(cells: &[Cell], app: &App, cursor: Option<usize>, ghost: bool) -> Line<'static> {
    let spans: Vec<Span<'static>> = cells
        .iter()
        .enumerate()
        .map(|(i, cell)| {
            let mut style = theme::cell_style(cell, &app.cfg, ghost);
            if Some(i) == cursor {
                style = style.patch(theme::CURSOR);
            }
            Span::styled(theme::cell_glyph(cell).to_string(), style)
        })
        .collect();
    Line::from(spans)
}

/// Draw both rows of §12.1's day bar into `area` (two rows tall).
pub fn draw(f: &mut Frame, area: Rect, app: &App) {
    if area.height == 0 || area.width == 0 {
        return;
    }
    let cols = bar_width(area);
    let bar = bar(app, cols);
    let plan_row = Rect {
        height: 1,
        ..area
    };
    let mut line = row(&bar.cells, app, Some(bar.cursor_col), false);
    line.push_span(Span::styled(
        format!("  ▲ {}", app.now.format("%H:%M")),
        theme::ACCENT,
    ));
    f.render_widget(Paragraph::new(line), plan_row);

    if area.height < 2 {
        return;
    }
    let ghost_row = Rect {
        y: area.y + 1,
        height: 1,
        ..area
    };
    let mut line = if bar.ghost.is_empty() {
        Line::from(Span::styled(
            "·".repeat(cols),
            theme::HINT,
        ))
    } else {
        row(&bar.ghost, app, None, true)
    };
    let label = match app.state.arrival {
        Some(t) => format!("  plan @{}", t.format("%H:%M")),
        None => "  plan —".to_string(),
    };
    line.push_span(Span::styled(label, theme::HINT));
    f.render_widget(Paragraph::new(line), ghost_row);
}

/// Draw the hover tooltip under the column it belongs to (§12.1).
///
/// It is drawn over the ghost row, which is the only place a one-line box
/// fits without moving the panes.
pub fn draw_tooltip(f: &mut Frame, area: Rect, hover: &Hover) {
    if area.height < 2 || hover.text.is_empty() {
        return;
    }
    let text = format!(" {} ", hover.text);
    let width = u16::try_from(emit::display_width(&text)).unwrap_or(u16::MAX);
    let width = width.min(area.width);
    let x = u16::try_from(hover.col)
        .unwrap_or(0)
        .saturating_add(area.x)
        .min(area.x + area.width.saturating_sub(width));
    let rect = Rect {
        x,
        y: area.y + 1,
        width,
        height: 1,
    };
    f.render_widget(Clear, rect);
    f.render_widget(
        Paragraph::new(Line::from(Span::styled(text, theme::TOOLTIP))),
        rect,
    );
}
