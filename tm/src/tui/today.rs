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
//! draws them. Below that they stack: Now on top, Energy, then Timeline, and
//! the Week pane is folded *into the status line* — the frame keeps the same
//! four rows (status, bar, body, hint) at either width.
//!
//! * [`draw`] — the frame.
//! * [`timeline_lines`], [`now_lines`], [`energy_lines`], [`week_lines`] —
//!   one pane each, as `Vec<Line>`, so a test can snapshot a pane on its own.
//! * [`status_line`], [`status_row`] (the narrow one, with [`week_fold_text`]
//!   folded into its right-hand end), [`hint_line`] — the single-row pieces.

use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::Style;
use ratatui::text::{Line, Span};
use ratatui::widgets::Paragraph;
use ratatui::Frame;

use tm_core::emit;
use tm_core::model::Id;
use tm_core::dayplan::Segment;
use tm_core::review;

use super::app::{App, Mode, Screen};
use super::review as review_screen;
use super::{daybar, inbox, necessities, prompts, queue, theme};

/// Rows the day bar takes (§12.1: plan row plus ghost row).
const BAR_ROWS: u16 = 2;
/// Rows the Energy pane takes: three of content plus its border.
const ENERGY_ROWS: u16 = 5;
/// Rows the Now pane takes when the panes are stacked.
const NOW_ROWS: u16 = 8;

// `clip` -- which was this module's own copy of a viewport cut -- is GONE with
// D43: its body is `tm_core::emit::clip` now, beside the table it always
// measured with. It is NOT `emit::truncate` (which fits a *cell* and drops the
// spaces in front of the `…`); a pane clip keeps them, because the row it is
// handed is already padded to its columns.

/// §12.1's first line: `tm · Mon 2026-09-07 · 10:42 · lounge · … ● 3/6 · …`.
pub fn status_line(app: &App, width: usize) -> Line<'static> {
    Line::from(Span::styled(
        emit::clip(&review::render_status_full(&app.head, &app.status), width),
        theme::STATUS,
    ))
}

/// §12.1's first line with the Week pane folded into it, for a terminal
/// narrower than `cfg.tui.min_width` (§12: "panes stack (Now on top, Timeline
/// below, **Week folded into the status line**)" — one row, not two).
///
/// The week takes at most half the row, and takes it from the right; the
/// status line keeps the rest and is clipped into it.
pub fn status_row(app: &App, width: usize) -> Line<'static> {
    let fold = week_fold_text(app, width / 2);
    if fold.is_empty() {
        return status_line(app, width);
    }
    let fw = emit::display_width(&fold);
    let left = emit::clip(
        &review::render_status_full(&app.head, &app.status),
        width.saturating_sub(fw + 2),
    );
    let lw = emit::display_width(&left);
    Line::from(vec![
        Span::styled(left, theme::STATUS),
        Span::raw(" ".repeat(width.saturating_sub(lw + fw))),
        Span::styled(fold, theme::DIM),
    ])
}

/// The Week pane's summary, dropping whole parts (never half a word) until it
/// fits `width`: `W37 1/25 · ⚠ a3 · ? 1 · 1 underused (4→3)`.
pub fn week_fold_text(app: &App, width: usize) -> String {
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
    let mut out = String::new();
    for part in parts {
        let next = if out.is_empty() {
            part
        } else {
            format!("{out} · {part}")
        };
        if emit::display_width(&next) > width {
            break;
        }
        out = next;
    }
    emit::clip(&out, width)
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
            // **Cut, then pad — both in `emit`** (D43, the W-22 repair step).
            // This used to cut with `emit::clip` and then fill with its own
            // `" ".repeat`, which is a second padder under no name at all;
            // `one_padder.rs` could not see it and an auditor could. The
            // composition is byte-for-byte what it was: `pad_to` truncates
            // first, and a string `clip` has already fitted is returned by
            // `truncate` unchanged, so only the fill moved.
            let text = emit::pad_to(&emit::clip(&row.text, width), width);
            let style = if i == app.selection {
                theme::SELECTED
            } else {
                Style::new()
            };
            Line::from(Span::styled(text, style))
        })
        .collect()
}

/// The segment `now` is inside, preferring the one the planner marked current.
///
/// **`emit::now_window`'s answer, not a fourth one** (W-23, README gap 1104).
/// This used to take the first segment carrying `flags.current` *anywhere in the
/// day* — with no `start <= now < end` guard at all, so a `▶` the planner left
/// on a finished row kept the pane on it.
fn current_segment(app: &App) -> Option<&Segment> {
    emit::now_window(&app.plan, app.now)
        .0
        .map(|i| &app.plan.segments[i])
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
            head.push_str(&emit::title_cell(seg, &app.tree, &app.cfg));
            if let Some(item) = id.as_ref().and_then(|i| app.tree.get(i)) {
                if let Some(parent) = &item.parent {
                    head.push_str(&format!("  {}", parent.token()));
                }
                for tag in &item.tags {
                    head.push_str(&format!(" #{tag}"));
                }
            }
            out.push(Line::from(Span::styled(emit::clip(&head, width), theme::ACCENT)));

            let planned = seg
                .flags
                .planned_min
                .unwrap_or_else(|| seg.minutes())
                .max(1);
            // **The elapsed is THIS segment's, not another row's** (README gap
            // **1315**). `App::active_elapsed_min` is a fact about
            // `state.active` — the running ITEM — and the head above names the
            // segment containing `now`, which since W-23 is
            // `emit::now_window`'s answer and no longer the `flags.current`
            // row. The two coincided before that and stopped coinciding
            // silently: with a `▶` block ended and a wall covering `now`, the
            // pane drew `ci3 Meeting w/ host` over `elapsed 3h19m` and a full
            // bar — the previous item's run, printed against a 1h meeting —
            // while the overtime prompt three rows down named the right item
            // for the same 3h19m. One pane, two subjects.
            let running = app.state.active.as_ref().map(|a| &a.id);
            let clock = || (app.now - seg.start).num_minutes().max(0) as u32;
            let elapsed = match (seg.item.as_ref(), running) {
                // The log's worked minutes — pauses, breaks and interruptions
                // excluded — but only when the head IS the running block.
                (Some(id), Some(active)) if id == active => {
                    app.active_elapsed_min().unwrap_or_else(clock)
                }
                _ => clock(),
            };
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
            out.push(Line::from(emit::clip(&second, width)));
        }
        None => out.push(Line::from(Span::styled(
            emit::clip(
                &format!("— nothing running ({})", app.now.format("%H:%M")),
                width,
            ),
            theme::DIM,
        ))),
    }

    // The same three the day file, `tm now` and `tm now --json` name — this
    // filtered Sleep out and started at `start > now`, which is a third answer
    // (W-23, README gap 1104).
    let next: Vec<String> = emit::now_window(&app.plan, app.now)
        .1
        .into_iter()
        .map(|i| {
            let s = &app.plan.segments[i];
            format!(
                "{} {}",
                s.start.format("%H:%M"),
                emit::title_cell(s, &app.tree, &app.cfg)
            )
        })
        .collect();
    out.push(Line::from(Span::styled(
        emit::clip(
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
        emit::clip("d done  x extend  s stop  b break  i interrupt", width),
        theme::HINT,
    )));
    out.push(Line::from(Span::styled(
        emit::clip(
            "0-5 energy  l location  K skip  n note  Space pause",
            width,
        ),
        theme::HINT,
    )));
    out
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
        Line::from(emit::clip(&format!("pred {}", pred.trim_end()), width)),
        Line::from(Span::styled(
            emit::clip(&format!("rep  {}", rep.trim_end()), width),
            theme::DIM,
        )),
        Line::from(Span::styled(
            emit::clip(&format!("     {}", hours.trim_end()), width),
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

/// `<id> <title>`, or just the title when the two are the same.
///
/// `tree::key_of` keys an id-less line (a `routines.md` or `optional.md`
/// entry, §4.3) by its title, so printing both would read `lunch lunch`.
fn label(id: &Id, title: &str) -> String {
    if id.as_str() == title {
        title.to_string()
    } else {
        format!("{id} {title}")
    }
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
            emit::clip(&m.title, width.saturating_sub(20).max(4))
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
                emit::clip(&format!("⚠ {} · {}", label(&h.id, &h.title), h.note), width),
                theme::WARN,
            )));
        }
    }
    if !app.week.waiting.is_empty() {
        out.push(separator("Waiting", width));
        for w in &app.week.waiting {
            out.push(Line::from(emit::clip(
                &format!("? {} · {}", label(&w.id, &w.title), w.note),
                width,
            )));
        }
    }
    out.push(separator("Diagnostics", width));
    for d in &app.week.diagnostics {
        out.push(Line::from(Span::styled(emit::clip(d, width), theme::DIM)));
    }
    out
}

/// §12.1's last row: the command line on the left, the keys on the right.
pub fn hint_line(app: &App, width: usize) -> Line<'static> {
    let left = match (&app.mode, &app.message) {
        (Mode::Command, _) => format!(":{}█", app.input),
        (Mode::Input(kind), _) => format!("{}: {}█", kind.label(), app.input),
        // The prompt reads the ONE table of places (D81, gap 3903).
        (Mode::BreakWhere, _) => format!(
            "break where? {}",
            tm_core::store::BreakPlace::all()
                .map(|p| format!("{} {}", p.key(), p.as_str()))
                .collect::<Vec<_>>()
                .join(" · ")
        ),
        (Mode::Energy, _) => "energy now? 0–5".to_string(),
        (_, Some(msg)) => msg.clone(),
        _ => ":".to_string(),
    };
    // The Today row of §12.6; the other screens print their own key row
    // inside their pane, so this one names where you are instead.
    let right = match app.screen {
        Screen::Today => "j/k move · Enter open · e edit · r replan · R sync · ? help".to_string(),
        other => format!(
            "screen {} {} · 1–5 screens · : command · ? help",
            other.number(),
            other.title()
        ),
    };
    let right = right.as_str();
    let left = emit::clip(&left, width);
    let lw = emit::display_width(&left);
    let rw = emit::display_width(right);
    if lw + rw + 1 > width {
        return Line::from(Span::styled(left, theme::HINT));
    }
    Line::from(vec![
        Span::styled(left, theme::ACCENT),
        Span::styled(" ".repeat(width - lw - rw), theme::HINT),
        Span::styled(right.to_string(), theme::HINT),
    ])
}

/// True when the terminal is wide enough for §12.1's three-column layout.
pub fn is_wide(app: &App, area: Rect) -> bool {
    u32::from(area.width) >= app.cfg.tui.min_width
}

/// Where the two day-bar rows sit, for hit-testing the mouse (§17.2).
///
/// It mirrors the vertical constraints [`draw`] uses: one status row — wide or
/// narrow, the week is folded *into* it — and then the bar.
pub fn bar_area(_app: &App, area: Rect) -> Rect {
    let offset = 1u16;
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

    let rows = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(1),
            Constraint::Length(BAR_ROWS),
            Constraint::Min(6),
            Constraint::Length(1),
        ])
        .split(area);
    let (status, bar, body, hint) = (rows[0], rows[1], rows[2], rows[3]);

    // §12: below `min_width` the Week pane is folded into the status line —
    // the same single row, not a second one.
    let head = if wide {
        status_line(app, width)
    } else {
        status_row(app, width)
    };
    f.render_widget(Paragraph::new(head), status);
    daybar::draw(f, bar, app);

    match app.screen {
        Screen::Today => {
            if wide {
                draw_wide(f, body, app);
            } else {
                draw_narrow(f, body, app);
            }
        }
        // §12.2–§12.5: each screen owns its own body.
        Screen::Queue => queue::render(&app.queue, &app.view(), f, body),
        Screen::Necessities => necessities::render(&app.necessities, &app.view(), f, body),
        Screen::Review => review_screen::render(&app.review, &app.reviews(), f, body),
        Screen::Inbox => inbox::render(&app.capture, &app.view(), f, body),
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
        assert_eq!(emit::clip("hello", 10), "hello");
        assert_eq!(emit::clip("hello", 5), "hello");
        assert_eq!(emit::clip("hello", 4), "hel…");
        assert_eq!(emit::clip("hello", 0), "");
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
