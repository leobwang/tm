//! Screen 1 — Today (tm-spec-v1.md §12.1), and the frame around every screen.
//!
//! # API overview
//!
//! [`draw`] is the whole frame: §12.1's status line, the two day-bar rows,
//! the panes, the hint line, and whatever overlay is open (§9's prompts, the
//! `?` help). Everything below it is a pure function of [`App`], so a
//! `TestBackend` snapshot is the test (§17 M6).
//!
//! Layout (§12): at `cfg.tui.min_width` columns or more the three panes sit
//! side by side — Timeline | (Now over Energy) | Week — exactly as §12.1
//! draws them. Below that they stack: Now on top, Energy, then Timeline,
//! with the Week pane folded into a second status row.
//!
//! * [`draw`] — the frame.
//! * [`timeline_lines`], [`now_lines`], [`energy_lines`], [`week_lines`] —
//!   one pane each, as `Vec<Line>`, so a test can snapshot a pane on its own.
//! * [`status_line`], [`hint_line`], [`week_fold`] — the three single-row
//!   pieces.

use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::Style;
use ratatui::text::{Line, Span};
use ratatui::widgets::Paragraph;
use ratatui::Frame;

use tm_core::emit;
use tm_core::planner::{SegKind, Segment};
use tm_core::review;

use super::app::{App, Mode, Screen};
use super::{daybar, prompts, theme};

/// Rows the day bar takes (§12.1: plan row plus ghost row).
const BAR_ROWS: u16 = 2;
/// Rows the Energy pane takes: three of content plus its border.
const ENERGY_ROWS: u16 = 5;
/// Rows the Now pane takes when the panes are stacked.
const NOW_ROWS: u16 = 8;

/// Truncate to `width` display columns, with `…` when something was cut.
fn clip(s: &str, width: usize) -> String {
    if emit::display_width(s) <= width {
        return s.to_string();
    }
    if width == 0 {
        return String::new();
    }
    let mut out = String::new();
    let mut w = 0usize;
    for c in s.chars() {
        let cw = emit::char_width(c);
        if w + cw > width.saturating_sub(1) {
            break;
        }
        out.push(c);
        w += cw;
    }
    out.push('…');
    out
}

/// §12.1's first line: `tm · Mon 2026-09-07 · 10:42 · lounge · … ● 3/6 · …`.
pub fn status_line(app: &App, width: usize) -> Line<'static> {
    Line::from(Span::styled(
        clip(&review::render_status_full(&app.head, &app.status), width),
        theme::STATUS,
    ))
}

/// The Week pane folded into one row, for narrow terminals (§12).
pub fn week_fold(app: &App, width: usize) -> Line<'static> {
    let w = &app.week;
    let mut parts = vec![format!(
        "{} {}/{}",
        w.week.map(|w| w.short()).unwrap_or_else(|| "week".into()),
        w.done_blocks,
        w.planned_blocks
    )];
    if !w.hot.is_empty() {
        parts.push(format!(
            "⚠ {}",
            w.hot
                .iter()
                .map(|h| h.id.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        ));
    }
    if !w.waiting.is_empty() {
        parts.push(format!("? {}", w.waiting.len()));
    }
    if let Some(first) = w.diagnostics.first() {
        parts.push(first.clone());
    }
    Line::from(Span::styled(clip(&parts.join(" · "), width), theme::DIM))
}

/// The Timeline pane (§12.1): [`tm_core::emit::render_plan_section`]'s rows,
/// scrolled so the selection stays visible, with the selected row marked.
pub fn timeline_lines(app: &App, width: usize, height: usize) -> Vec<Line<'static>> {
    // §4.3's row is `time ci p mark title @parent est (actual) note`; the
    // columns after the title are 28 wide, so the title takes the rest.
    let title_w = width.saturating_sub(28).clamp(4, 40);
    let rows = app.timeline_rows(title_w);
    let top = if height > 0 && app.selection >= height {
        app.selection + 1 - height
    } else {
        0
    };
    rows.iter()
        .enumerate()
        .skip(top)
        .take(height.max(1))
        .map(|(i, row)| {
            let text = clip(&row.text, width);
            let pad = width.saturating_sub(emit::display_width(&text));
            let style = if i == app.selection {
                theme::SELECTED
            } else {
                Style::new()
            };
            Line::from(Span::styled(format!("{text}{}", " ".repeat(pad)), style))
        })
        .collect()
}

/// The segment `now` is inside, preferring the one the planner marked current.
fn current_segment(app: &App) -> Option<&Segment> {
    app.plan
        .segments
        .iter()
        .find(|s| s.flags.current)
        .or_else(|| {
            app.plan
                .segments
                .iter()
                .find(|s| s.start <= app.now && app.now < s.end && !s.flags.done)
        })
}

/// `▐████████░░░░░░░▌` — elapsed against the planned minutes (§12.1).
fn elapsed_bar(elapsed_min: u32, planned_min: u32, width: usize) -> String {
    let width = width.max(1);
    let filled = if planned_min == 0 {
        width
    } else {
        ((f64::from(elapsed_min) / f64::from(planned_min)) * width as f64).round() as usize
    };
    let filled = filled.min(width);
    format!("▐{}{}▌", "█".repeat(filled), "░".repeat(width - filled))
}

/// The Now pane (§12.1): the running block, its elapsed bar, the next
/// segments and the key hints from the mock.
pub fn now_lines(app: &App, width: usize) -> Vec<Line<'static>> {
    let mut out: Vec<Line<'static>> = Vec::new();
    match current_segment(app) {
        Some(seg) => {
            let id = seg.item.clone();
            let mut head = String::new();
            if let Some(ci) = seg
                .item
                .as_ref()
                .and_then(|i| app.tree.get(i))
                .map(|i| i.ci)
                .or(seg.energy)
            {
                head.push_str(&format!("ci{ci} "));
            }
            if let Some(p) = id.as_ref().and_then(|i| app.priority_of(i)) {
                head.push_str(&format!("p{p} "));
            }
            head.push_str(&seg_title(app, seg));
            if let Some(item) = id.as_ref().and_then(|i| app.tree.get(i)) {
                if let Some(parent) = &item.parent {
                    head.push_str(&format!("  {}", parent.token()));
                }
                for tag in &item.tags {
                    head.push_str(&format!(" #{tag}"));
                }
            }
            out.push(Line::from(Span::styled(clip(&head, width), theme::ACCENT)));

            let planned = seg
                .flags
                .planned_min
                .unwrap_or_else(|| seg.minutes())
                .max(1);
            let elapsed = app
                .active_elapsed_min()
                .unwrap_or_else(|| (app.now - seg.start).num_minutes().max(0) as u32);
            let mut second = format!(
                "elapsed {} {}",
                review::fmt_hm(elapsed),
                elapsed_bar(elapsed, planned, 15)
            );
            if let Some(mult) = seg.flags.multiplier {
                // The estimate as written (§4.3's `2b×1.6`), not what is
                // left of it: the multiplier is quoted against the original.
                let est = seg
                    .item
                    .as_ref()
                    .and_then(|i| app.tree.get(i))
                    .and_then(|i| i.est_original.clone().or_else(|| i.own_remaining()))
                    .map(|d| d.to_string())
                    .unwrap_or_else(|| review::fmt_hm(planned));
                second.push_str(&format!(" est {est} ×{mult:.1}"));
            }
            if app.state.active.as_ref().is_some_and(|a| a.paused) {
                second.push_str(" · paused");
            }
            out.push(Line::from(clip(&second, width)));
        }
        None => out.push(Line::from(Span::styled(
            clip(
                &format!("— nothing running ({})", app.now.format("%H:%M")),
                width,
            ),
            theme::DIM,
        ))),
    }

    let next: Vec<String> = app
        .plan
        .segments
        .iter()
        .filter(|s| s.start > app.now && !matches!(s.kind, SegKind::Sleep))
        .take(3)
        .map(|s| format!("{} {}", s.start.format("%H:%M"), seg_title(app, s)))
        .collect();
    out.push(Line::from(Span::styled(
        clip(
            &if next.is_empty() {
                "next —".to_string()
            } else {
                format!("next {}", next.join(" · "))
            },
            width,
        ),
        theme::DIM,
    )));
    out.push(Line::from(String::new()));
    out.push(Line::from(Span::styled(
        clip("d done  x extend  s stop  b break  i interrupt", width),
        theme::HINT,
    )));
    out.push(Line::from(Span::styled(
        clip(
            "0-5 energy  l location  K skip  n note  Space pause",
            width,
        ),
        theme::HINT,
    )));
    out
}

/// A segment's name: the item's title, else the word for its kind.
fn seg_title(app: &App, seg: &Segment) -> String {
    if let Some(title) = seg
        .item
        .as_ref()
        .and_then(|id| app.tree.get(id))
        .map(|i| i.title.clone())
        .filter(|t| !t.is_empty())
    {
        return title;
    }
    match &seg.kind {
        SegKind::Break => "break".to_string(),
        SegKind::Rest => "rest".to_string(),
        SegKind::Lost => "lost".to_string(),
        SegKind::Sleep => "sleep".to_string(),
        SegKind::WindDown => "wind-down".to_string(),
        SegKind::Wall => "interruption".to_string(),
        SegKind::Batch(ids) => format!("batch ({})", ids.len()),
        _ => "—".to_string(),
    }
}

/// The Energy pane (§12.1): the predicted row, the reported row (`·` where
/// you were not asked) and the hour ruler.
pub fn energy_lines(app: &App, width: usize) -> Vec<Line<'static>> {
    let cells = width.saturating_sub(5) / 3;
    let n = app.energy.hours.len().min(cells.max(1));
    let cell = |s: String| format!("{s:>2} ");
    let pred: String = app.energy.pred.iter().take(n).map(|p| cell(p.to_string())).collect();
    let rep: String = app
        .energy
        .rep
        .iter()
        .take(n)
        .map(|r| cell(r.map(|v| v.to_string()).unwrap_or_else(|| "·".into())))
        .collect();
    let hours: String = app
        .energy
        .hours
        .iter()
        .take(n)
        .map(|h| cell(format!("{h:02}")))
        .collect();
    vec![
        Line::from(clip(&format!("pred {}", pred.trim_end()), width)),
        Line::from(Span::styled(
            clip(&format!("rep  {}", rep.trim_end()), width),
            theme::DIM,
        )),
        Line::from(Span::styled(
            clip(&format!("     {}", hours.trim_end()), width),
            theme::HINT,
        )),
    ]
}

/// `▓▓▓░░░` — a milestone's progress (§12.1).
fn progress_bar(done_min: u32, planned_min: u32, width: usize) -> String {
    if planned_min == 0 {
        return "─".repeat(width);
    }
    let filled = ((f64::from(done_min) / f64::from(planned_min)) * width as f64).round() as usize;
    let filled = filled.min(width);
    format!("{}{}", "▓".repeat(filled), "░".repeat(width - filled))
}

/// The Week pane's title (§12.1: `Week W37 · 8/20`).
pub fn week_title(app: &App) -> String {
    format!(
        "Week {} · {}/{}",
        app.week
            .week
            .map(|w| w.short())
            .unwrap_or_else(|| "—".to_string()),
        app.week.done_blocks,
        app.week.planned_blocks
    )
}

/// A `──── Heading ────` separator, filled to `width`.
fn separator(text: &str, width: usize) -> Line<'static> {
    let head = format!("──── {text} ");
    let pad = width.saturating_sub(emit::display_width(&head));
    Line::from(Span::styled(
        format!("{head}{}", "─".repeat(pad)),
        theme::HINT,
    ))
}

/// The Week pane (§12.1): milestones, HOT/overdue, Waiting, Diagnostics.
pub fn week_lines(app: &App, width: usize) -> Vec<Line<'static>> {
    let bm = app.cfg.block_min().max(1);
    let mut out: Vec<Line<'static>> = Vec::new();
    for m in &app.week.milestones {
        let mark = if m.done {
            "✓"
        } else if m.hot {
            "⚠"
        } else if m.done_min > 0 {
            "▶"
        } else {
            " "
        };
        let text = format!(
            "{mark} {} {}",
            m.id,
            clip(&m.title, width.saturating_sub(20).max(4))
        );
        let tail = format!(
            "{} {}/{}",
            progress_bar(m.done_min, m.planned_min, 6),
            m.done_min.div_ceil(bm),
            m.planned_min.div_ceil(bm)
        );
        let pad = width
            .saturating_sub(emit::display_width(&text) + emit::display_width(&tail))
            .max(1);
        out.push(Line::from(vec![
            Span::styled(text, if m.hot { theme::WARN } else { Style::new() }),
            Span::styled(format!("{}{tail}", " ".repeat(pad)), theme::DIM),
        ]));
    }
    if !app.week.hot.is_empty() {
        out.push(separator("HOT / overdue", width));
        for h in &app.week.hot {
            out.push(Line::from(Span::styled(
                clip(&format!("⚠ {} {} · {}", h.id, h.title, h.note), width),
                theme::WARN,
            )));
        }
    }
    if !app.week.waiting.is_empty() {
        out.push(separator("Waiting", width));
        for w in &app.week.waiting {
            out.push(Line::from(clip(
                &format!("? {} {} · {}", w.id, w.title, w.note),
                width,
            )));
        }
    }
    out.push(separator("Diagnostics", width));
    for d in &app.week.diagnostics {
        out.push(Line::from(Span::styled(clip(d, width), theme::DIM)));
    }
    out
}

/// §12.1's last row: the command line on the left, the keys on the right.
pub fn hint_line(app: &App, width: usize) -> Line<'static> {
    let left = match (&app.mode, &app.message) {
        (Mode::Command, _) => format!(":{}█", app.input),
        (Mode::Input(kind), _) => format!("{}: {}█", kind.label(), app.input),
        (Mode::BreakWhere, _) => "break where? w walk · s seat · b bed · p phone".to_string(),
        (Mode::Energy, _) => "energy now? 0–5".to_string(),
        (_, Some(msg)) => msg.clone(),
        _ => ":".to_string(),
    };
    let right = "j/k move · Enter open · e edit · r replan · R sync · ? help";
    let left = clip(&left, width);
    let lw = emit::display_width(&left);
    let rw = emit::display_width(right);
    if lw + rw + 1 > width {
        return Line::from(Span::styled(left, theme::HINT));
    }
    Line::from(vec![
        Span::styled(left, theme::ACCENT),
        Span::styled(" ".repeat(width - lw - rw), theme::HINT),
        Span::styled(right, theme::HINT),
    ])
}

/// True when the terminal is wide enough for §12.1's three-column layout.
pub fn is_wide(app: &App, area: Rect) -> bool {
    u32::from(area.width) >= app.cfg.tui.min_width
}

/// Where the two day-bar rows sit, for hit-testing the mouse (§17.2).
///
/// It mirrors the vertical constraints [`draw`] uses: the status line, then
/// the folded week row on a narrow terminal, then the bar.
pub fn bar_area(app: &App, area: Rect) -> Rect {
    let offset = if is_wide(app, area) { 1 } else { 2 };
    let y = area.y.saturating_add(offset);
    let height = BAR_ROWS.min(area.height.saturating_sub(offset));
    Rect {
        x: area.x,
        y,
        width: area.width,
        height,
    }
}

/// Draw the whole frame.
pub fn draw(f: &mut Frame, app: &App) {
    let area = f.area();
    if area.width == 0 || area.height < 4 {
        return;
    }
    let wide = is_wide(app, area);
    let width = usize::from(area.width);

    let rows = if wide {
        Layout::default()
            .direction(Direction::Vertical)
            .constraints([
                Constraint::Length(1),
                Constraint::Length(BAR_ROWS),
                Constraint::Min(6),
                Constraint::Length(1),
            ])
            .split(area)
    } else {
        Layout::default()
            .direction(Direction::Vertical)
            .constraints([
                Constraint::Length(1),
                Constraint::Length(1),
                Constraint::Length(BAR_ROWS),
                Constraint::Min(6),
                Constraint::Length(1),
            ])
            .split(area)
    };
    let (status, fold, bar, body, hint) = if wide {
        (rows[0], None, rows[1], rows[2], rows[3])
    } else {
        (rows[0], Some(rows[1]), rows[2], rows[3], rows[4])
    };

    f.render_widget(Paragraph::new(status_line(app, width)), status);
    if let Some(fold) = fold {
        f.render_widget(Paragraph::new(week_fold(app, width)), fold);
    }
    daybar::draw(f, bar, app);

    match app.screen {
        Screen::Today => {
            if wide {
                draw_wide(f, body, app);
            } else {
                draw_narrow(f, body, app);
            }
        }
        // screens 2-5: added by the queue agent — one arm each, drawing into
        // `body`; until then the screen says what will live there.
        other => {
            f.render_widget(
                Paragraph::new(vec![
                    Line::from(String::new()),
                    Line::from(Span::styled(
                        format!("  screen {} — {} is not built yet", other.number(), other.title()),
                        theme::DIM,
                    )),
                    Line::from(Span::styled("  press 1 for Today".to_string(), theme::HINT)),
                ])
                .block(theme::pane(other.title())),
                body,
            );
        }
    }

    f.render_widget(Paragraph::new(hint_line(app, width)), hint);

    if let Some(hover) = &app.hover {
        daybar::draw_tooltip(f, bar, hover);
    }
    if let Some(prompt) = &app.prompt {
        prompts::draw(f, area, prompt);
    } else if app.mode == Mode::Help {
        prompts::draw_help(f, area);
    }
}

/// The wide layout of §12.1: Timeline | Now over Energy | Week.
fn draw_wide(f: &mut Frame, area: Rect, app: &App) {
    let cols = Layout::default()
        .direction(Direction::Horizontal)
        .constraints([
            Constraint::Percentage(38),
            Constraint::Min(30),
            Constraint::Percentage(28),
        ])
        .split(area);
    let middle = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Min(4), Constraint::Length(ENERGY_ROWS)])
        .split(cols[1]);
    pane(f, cols[0], "Timeline", timeline_pane(app, cols[0]));
    pane(f, middle[0], "Now", now_lines(app, inner_w(middle[0])));
    pane(
        f,
        middle[1],
        "Energy today",
        energy_lines(app, inner_w(middle[1])),
    );
    let title = week_title(app);
    pane(f, cols[2], &title, week_lines(app, inner_w(cols[2])));
}

/// The stacked layout below `cfg.tui.min_width` (§12).
fn draw_narrow(f: &mut Frame, area: Rect, app: &App) {
    let rows = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(NOW_ROWS),
            Constraint::Length(ENERGY_ROWS),
            Constraint::Min(3),
        ])
        .split(area);
    pane(f, rows[0], "Now", now_lines(app, inner_w(rows[0])));
    pane(
        f,
        rows[1],
        "Energy today",
        energy_lines(app, inner_w(rows[1])),
    );
    pane(f, rows[2], "Timeline", timeline_pane(app, rows[2]));
}

/// The timeline rows sized for the pane it is drawn in.
fn timeline_pane(app: &App, area: Rect) -> Vec<Line<'static>> {
    timeline_lines(
        app,
        inner_w(area),
        usize::from(area.height.saturating_sub(2)),
    )
}

/// The text width inside a bordered pane.
fn inner_w(area: Rect) -> usize {
    usize::from(area.width.saturating_sub(2))
}

/// Draw one bordered pane of lines.
fn pane(f: &mut Frame, area: Rect, title: &str, lines: Vec<Line<'static>>) {
    f.render_widget(Paragraph::new(lines).block(theme::pane(title)), area);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clipping_marks_what_it_cut() {
        assert_eq!(clip("hello", 10), "hello");
        assert_eq!(clip("hello", 5), "hello");
        assert_eq!(clip("hello", 4), "hel…");
        assert_eq!(clip("hello", 0), "");
    }

    #[test]
    fn the_elapsed_bar_fills_with_the_ratio() {
        assert_eq!(elapsed_bar(0, 10, 4), "▐░░░░▌");
        assert_eq!(elapsed_bar(5, 10, 4), "▐██░░▌");
        assert_eq!(elapsed_bar(20, 10, 4), "▐████▌");
    }

    #[test]
    fn a_milestone_with_no_estimate_has_no_bar() {
        assert_eq!(progress_bar(0, 0, 3), "───");
        assert_eq!(progress_bar(3, 6, 6), "▓▓▓░░░");
    }
}
