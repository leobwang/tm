//! §9's two prompts and the `?` help overlay (tm-spec-v1.md §9.1, §9.2,
//! §12.6).
//!
//! # API overview
//!
//! Every function here is a pure `state -> Vec<Line>`; [`draw`] puts the
//! lines in a centred, bordered box over the screen.
//!
//! * [`overtime_lines`] — §9.1's box, including the consequence lines the
//!   spec wants computed by re-planning (`x extend +1 block → drops: Review
//!   the drafts (p3)`). The drops come from
//!   [`tm_core::planner::overtime_drops`] via
//!   [`super::app::App::overtime_due`].
//! * [`idle_lines`] — §9.2's box.
//! * [`help_lines`] — §12.6's keymap, including the two keys the table
//!   assigns twice (see [`super::app`]).
//! * [`draw`] / [`draw_help`] — render them.

use ratatui::layout::Rect;
use ratatui::text::Line;
use ratatui::widgets::{Clear, Paragraph};
use ratatui::Frame;

use tm_core::emit;
use tm_core::review::fmt_hm;

use super::app::{Idle, Overtime, Prompt};
use super::theme;

/// `est 2b ×1.6 = 3h12m · elapsed 3h19m` (§9.1's first row).
fn overtime_head(o: &Overtime) -> String {
    let mut est = format!("est {}", o.est);
    if let Some(m) = o.multiplier {
        est.push_str(&format!(" ×{m:.1}"));
    }
    format!(
        "{}     {} = {} · elapsed {}",
        o.title,
        est,
        fmt_hm(o.planned_min),
        fmt_hm(o.elapsed_min)
    )
}

/// §9.1's overtime box, without the border.
pub fn overtime_lines(o: &Overtime) -> Vec<Line<'static>> {
    let drops = if o.drops.is_empty() {
        "→ drops: nothing".to_string()
    } else {
        format!("→ drops: {}", o.drops.join(", "))
    };
    vec![
        Line::from(overtime_head(o)),
        Line::from(format!("  x  extend +1 block      {drops}")),
        Line::from(format!(
            "  s  stop, demote rest    → {} stays in the week queue",
            o.stays
        )),
        Line::from("  d  done".to_string()),
        Line::styled(
            format!("  any other key: ask again in {}m", o.reprompt_min),
            theme::HINT,
        ),
    ]
}

/// §9.1's box title.
pub fn overtime_title(_o: &Overtime) -> String {
    "Overtime".to_string()
}

/// §9.2's idle box, without the border.
pub fn idle_lines(_i: &Idle) -> Vec<Line<'static>> {
    vec![
        Line::from("  w  work (starts next block)   b  break   t  routine".to_string()),
        Line::from("  i  interruption               l  leak (log it, no judgment)".to_string()),
    ]
}

/// §9.2's box title, with the length of the gap.
pub fn idle_title(i: &Idle) -> String {
    format!("Nothing is running ({}m)", i.minutes)
}

/// The lines and title of whichever prompt is open.
pub fn lines(prompt: &Prompt) -> (String, Vec<Line<'static>>) {
    match prompt {
        Prompt::Overtime(o) => (overtime_title(o), overtime_lines(o)),
        Prompt::Idle(i) => (idle_title(i), idle_lines(i)),
    }
}

/// §12.6's keymap, for the `?` overlay.
pub fn help_lines() -> Vec<Line<'static>> {
    let rows: &[(&str, &str)] = &[
        ("1–5", "screens: Today · Queue · Necessities · Review · Inbox"),
        ("?", "this help  ·  :  command line (any tm verb)  ·  q  quit"),
        ("e / Enter", "open the selected line in the editor / drill into it"),
        ("r / R", "replan (resume, when interrupted) · sync calendar + replan"),
        ("j / k", "move the selection  ·  mouse: hover the day bar, click to select"),
        ("d / x / s", "done · extend one block · stop, the remainder re-competes"),
        ("b + w/s/b/p", "break: walk · seat · bed · phone"),
        ("i / r", "interruption starts / ends"),
        ("0 then 0–5", "report energy now (1–5 alone switch screens)"),
        ("l / K / n", "location · skip the selected routine · note"),
        ("Space", "pause or unpause the timer"),
        ("", ""),
        ("overtime", "x extend · s stop · d done · anything else: ask again"),
        ("idle", "w work · b break · t routine · i interruption · l leak"),
    ];
    rows.iter()
        .map(|(k, v)| {
            if k.is_empty() {
                Line::from(String::new())
            } else {
                Line::from(format!("  {k:<12} {v}"))
            }
        })
        .collect()
}

/// A box of `w × h` centred in `area`, clamped to it.
pub fn centred(area: Rect, w: u16, h: u16) -> Rect {
    let w = w.min(area.width);
    let h = h.min(area.height);
    Rect {
        x: area.x + (area.width - w) / 2,
        y: area.y + (area.height - h) / 2,
        width: w,
        height: h,
    }
}

/// How wide one already-built `Line` draws, **by the one table** (D43; README
/// gap **1309**).
///
/// `Line::width` is ratatui's `unicode-width`, which is exactly the second
/// measurement D43 exists to remove: for `\u{1F44D}\u{1F3FD}` it answers 4
/// where `emit`'s `Walk` answers 2 (D44 collapses a skin-tone modifier onto
/// its base), so a box sized with one and filled with the other overflows its
/// own border. It survived [`exactly_one_thing_measures_a_terminal_column`]
/// because `MEASUREMENTS` matched `.width()` — the call form — and this is a
/// **path**, `Line::width`; the needle is the shape now, not the spelling.
fn line_width(line: &Line<'static>) -> usize {
    line.spans.iter().map(|s| emit::display_width(&s.content)).sum()
}

/// Draw a titled box of lines centred in `area`.
fn box_of(f: &mut Frame, area: Rect, title: &str, lines: Vec<Line<'static>>) {
    // The title's own width is the same table's, not `chars().count()` — a
    // third rule on the next line, and the one that decides whether the border
    // clears the title (README gap 1309).
    let width = lines
        .iter()
        .map(line_width)
        .chain(std::iter::once(emit::display_width(title) + 4))
        .max()
        .unwrap_or(0);
    let width = u16::try_from(width + 4).unwrap_or(u16::MAX);
    let height = u16::try_from(lines.len() + 2).unwrap_or(u16::MAX);
    let rect = centred(area, width, height);
    f.render_widget(Clear, rect);
    f.render_widget(
        Paragraph::new(lines)
            .style(theme::OVERLAY)
            .block(theme::pane_focused(title)),
        rect,
    );
}

/// Draw the open prompt (§9.1, §9.2).
pub fn draw(f: &mut Frame, area: Rect, prompt: &Prompt) {
    let (title, lines) = lines(prompt);
    box_of(f, area, &title, lines);
}

/// Draw the `?` help overlay (§12.6).
pub fn draw_help(f: &mut Frame, area: Rect) {
    box_of(f, area, "Keys — tm-spec §12.6", help_lines());
}

#[cfg(test)]
mod tests {
    use super::*;
    use tm_core::model::Id;

    fn overtime() -> Overtime {
        Overtime {
            id: Id::new("t3"),
            title: "Exercises 5.3–5.5".to_string(),
            est: "2b".to_string(),
            multiplier: Some(1.6),
            planned_min: 192,
            elapsed_min: 199,
            drops: vec!["Review the drafts (p3)".to_string()],
            stays: "0.5b".to_string(),
            reprompt_min: 15,
        }
    }

    #[test]
    fn the_overtime_head_is_the_spec_row() {
        assert_eq!(
            overtime_head(&overtime()),
            "Exercises 5.3–5.5     est 2b ×1.6 = 3h12m · elapsed 3h19m"
        );
    }

    #[test]
    fn the_consequences_name_what_is_dropped_and_what_stays() {
        let lines = overtime_lines(&overtime());
        assert!(lines[1].to_string().contains("→ drops: Review the drafts (p3)"));
        assert!(lines[2].to_string().contains("0.5b stays"));
    }
}
