//! Colours, glyphs and shared styles for the TUI (tm-spec-v1.md §12).
//!
//! # API overview
//!
//! Everything visual that is *not* a layout decision lives here, so the panes
//! stay readable and a colour is changed in one place:
//!
//! * [`pane`] / [`pane_focused`] — the bordered block every pane of §12.1 is
//!   drawn in, with its title.
//! * [`cell_glyph`] and [`cell_style`] — one day-bar cell (§12.1: "cell colour
//!   = project hue, brightness = `ci`, routines grey, breaks light grey,
//!   Lost/leak hatched orange, interruptions hatched red, optionals dotted,
//!   walls solid dark"). The colour comes from [`emit::Cell::rgb`], so the
//!   terminal bar and `day/<date>.svg` agree; only the *character* is chosen
//!   here, since a terminal cannot hatch.
//! * [`STATUS`], [`HINT`], [`ACCENT`], [`WARN`], [`DIM`], [`SELECTED`] — the
//!   handful of styles the panes share.
//!
//! Nothing here reads the clock, the store or `App`; every function is pure.

use ratatui::style::{Color, Modifier, Style};
use ratatui::widgets::{Block, BorderType, Borders};

use tm_core::config::Config;
use tm_core::emit::{Cell, CellStyle};

/// The status line (§12.1's first row).
pub const STATUS: Style = Style::new().fg(Color::White).add_modifier(Modifier::BOLD);
/// The hint line (§12.1's last row) and every in-pane key hint.
pub const HINT: Style = Style::new().fg(Color::DarkGray);
/// Something the eye should land on: the running block, a pane title.
pub const ACCENT: Style = Style::new().fg(Color::Cyan);
/// HOT, overdue, impossible (§7.2's `p = 0`).
pub const WARN: Style = Style::new().fg(Color::LightRed);
/// Secondary text.
pub const DIM: Style = Style::new().fg(Color::Gray);
/// The selected timeline row.
pub const SELECTED: Style = Style::new()
    .bg(Color::Rgb(0x33, 0x38, 0x44))
    .add_modifier(Modifier::BOLD);
/// A prompt or overlay box (§9.1, §9.2, the help overlay).
pub const OVERLAY: Style = Style::new().fg(Color::White).bg(Color::Rgb(0x18, 0x1c, 0x24));
/// The day bar's cursor column (§12.1's `▲`).
pub const CURSOR: Style = Style::new().fg(Color::White).add_modifier(Modifier::REVERSED);
/// The hover tooltip (§12.1: `title · duration · ci · p · @root`).
pub const TOOLTIP: Style = Style::new()
    .fg(Color::Black)
    .bg(Color::Rgb(0xd8, 0xd8, 0xd8));

/// A pane of §12.1, with its title in the top border.
pub fn pane(title: &str) -> Block<'_> {
    Block::default()
        .borders(Borders::ALL)
        .border_type(BorderType::Plain)
        .border_style(HINT)
        .title(format!(" {title} "))
        .title_style(DIM)
}

/// [`pane`] for the pane that currently owns the selection.
pub fn pane_focused(title: &str) -> Block<'_> {
    pane(title).border_style(ACCENT).title_style(ACCENT)
}

/// The character one day-bar cell is drawn with (§12.1).
///
/// A terminal has no hatching, so the two hatched styles get diagonals
/// (`╱` for lost/leak time, `╳` for an interruption) and optionals get the
/// dotted `∙`; work is shaded by `ci` — the brighter the cell, the fuller the
/// block — which is the readable half of "brightness = ci, 0 black … 5 full".
pub fn cell_glyph(cell: &Cell) -> char {
    match cell.style {
        CellStyle::Work => match cell.brightness {
            0 | 1 => '░',
            2 | 3 => '▓',
            _ => '█',
        },
        CellStyle::Routine => '▒',
        CellStyle::Break => '░',
        CellStyle::Lost => '╱',
        CellStyle::Interrupt => '╳',
        CellStyle::Optional => '∙',
        CellStyle::Wall => '█',
        CellStyle::Rest => '░',
        CellStyle::Sleep => '█',
        CellStyle::Empty => ' ',
    }
}

/// The style of one day-bar cell: [`emit::Cell::rgb`]'s colour, dimmed on the
/// ghost row and reversed under the cursor.
pub fn cell_style(cell: &Cell, cfg: &Config, ghost: bool) -> Style {
    if cell.style == CellStyle::Empty {
        return Style::new();
    }
    let (r, g, b) = cell.rgb(cfg);
    let colour = if ghost {
        // Half brightness: the ghost is context, not content.
        Color::Rgb(r / 2, g / 2, b / 2)
    } else {
        Color::Rgb(r, g, b)
    };
    Style::new().fg(colour)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn work(ci: u8) -> Cell {
        Cell {
            hue: Some(0),
            brightness: ci,
            style: CellStyle::Work,
            tooltip: String::new(),
            segment: Some(0),
        }
    }

    #[test]
    fn work_cells_shade_by_ci() {
        assert_eq!(cell_glyph(&work(0)), '░');
        assert_eq!(cell_glyph(&work(3)), '▓');
        assert_eq!(cell_glyph(&work(5)), '█');
    }

    #[test]
    fn an_empty_cell_is_blank_and_unstyled() {
        let cell = Cell::empty();
        assert_eq!(cell_glyph(&cell), ' ');
        assert_eq!(cell_style(&cell, &Config::default(), false), Style::new());
    }

    #[test]
    fn the_ghost_row_is_dimmer_than_the_plan_row() {
        let cfg = Config::default();
        let cell = work(5);
        assert_ne!(
            cell_style(&cell, &cfg, true).fg,
            cell_style(&cell, &cfg, false).fg
        );
    }
}
