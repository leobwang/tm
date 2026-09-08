//! Screen 4 — Review (tm-spec-v1.md §12.4).
//!
//! # API overview
//!
//! * [`ReviewState`] — which period is in front (`day`/`week`/`month`) and
//!   whether the pane is scrolled.
//! * [`on_key`] — §12.4's own keys: `h`/`l` (or `[`/`]`) change the period,
//!   `j`/`k` scroll, `w` writes the review into the file's `tm:review` block,
//!   `c` hands the same numbers to Claude Code for prose.
//! * [`render`] — the pane: the rendered review, wrapped in a titled block,
//!   with §12.4's footer.
//!
//! The numbers are **not** computed here. `tm_core::review` owns every §11
//! monitor, and this screen renders `render_day` / `render_week` /
//! `render_month` — the same text `tm review` prints and `tm review --write`
//! puts in the file, so the screen, the CLI and §17 M8's hand-computed
//! values are one set of numbers.

use crossterm::event::{KeyCode, KeyEvent};
use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::text::{Line, Span};
use ratatui::widgets::Paragraph;
use ratatui::Frame;

use tm_core::review::{
    render_day, render_month, render_week, DayReview, MonthReview, WeekReview,
};

use super::queue::Action;
use super::theme;

/// Which review §12.4 is showing.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Period {
    /// `Day 2026-09-07 · …` — the default.
    #[default]
    Day,
    /// `Week 2026-W37 · …`.
    Week,
    /// `Month 2026-09 · …`.
    Month,
}

impl Period {
    /// The §13 verb argument (`tm review day`).
    pub fn verb(self) -> &'static str {
        match self {
            Period::Day => "day",
            Period::Week => "week",
            Period::Month => "month",
        }
    }

    /// The pane title.
    pub fn title(self) -> &'static str {
        match self {
            Period::Day => "Day",
            Period::Week => "Week",
            Period::Month => "Month",
        }
    }

    /// The next period to the right (`l`), wrapping.
    pub fn right(self) -> Period {
        match self {
            Period::Day => Period::Week,
            Period::Week => Period::Month,
            Period::Month => Period::Day,
        }
    }

    /// The next period to the left (`h`), wrapping.
    pub fn left(self) -> Period {
        match self {
            Period::Day => Period::Month,
            Period::Week => Period::Day,
            Period::Month => Period::Week,
        }
    }
}

/// The three reviews the screen can show, computed by the shell.
pub struct Reviews {
    /// §12.4's day rows.
    pub day: DayReview,
    /// The week review.
    pub week: WeekReview,
    /// The month review.
    pub month: MonthReview,
}

impl Reviews {
    /// The rendered text of one period (§12.4).
    pub fn text(&self, period: Period) -> String {
        match period {
            Period::Day => render_day(&self.day),
            Period::Week => render_week(&self.week),
            Period::Month => render_month(&self.month),
        }
    }
}

/// The Review screen's cursor.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReviewState {
    /// Which review is in front.
    pub period: Period,
    /// First visible line of the pane.
    pub scroll: usize,
}

impl ReviewState {
    /// A fresh screen: today's day review, unscrolled.
    pub fn new() -> ReviewState {
        ReviewState::default()
    }
}

/// §12.4's keys. Anything else is [`Action::Ignored`], so the shell's global
/// row still has it.
pub fn on_key(state: &mut ReviewState, reviews: &Reviews, key: KeyEvent) -> Action {
    let lines = reviews.text(state.period).lines().count();
    match key.code {
        KeyCode::Char('h') | KeyCode::Left | KeyCode::Char('[') => {
            state.period = state.period.left();
            state.scroll = 0;
            Action::Redraw
        }
        KeyCode::Char('l') | KeyCode::Right | KeyCode::Char(']') => {
            state.period = state.period.right();
            state.scroll = 0;
            Action::Redraw
        }
        KeyCode::Char('j') | KeyCode::Down => {
            if state.scroll + 1 < lines {
                state.scroll += 1;
            }
            Action::Redraw
        }
        KeyCode::Char('k') | KeyCode::Up => {
            state.scroll = state.scroll.saturating_sub(1);
            Action::Redraw
        }
        // §12.4's footer: `w write to day file`.
        KeyCode::Char('w') => Action::Note(format!("review {} --write", state.period.verb())),
        // §12.4's footer: `c ask Claude Code for prose`. The review's own
        // `--json` is what §14's `/review-day` skill reads, so the screen
        // hands over the command rather than shelling out to an agent.
        KeyCode::Char('c') => Action::Note(format!(
            "claude /review-{} — or `tm review {} --json`",
            state.period.verb(),
            state.period.verb()
        )),
        _ => Action::Ignored,
    }
}

/// Draw §12.4 into `area`.
pub fn render(state: &ReviewState, reviews: &Reviews, frame: &mut Frame, area: Rect) {
    if area.height == 0 || area.width == 0 {
        return;
    }
    let rows = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Min(3), Constraint::Length(1)])
        .split(area);
    let text = reviews.text(state.period);
    let body: Vec<Line> = text
        .lines()
        .skip(state.scroll)
        .map(|l| Line::from(l.to_string()))
        .collect();
    let key = match state.period {
        Period::Day => reviews.day.date.to_string(),
        Period::Week => reviews.week.week.to_string(),
        Period::Month => reviews.month.month.to_string(),
    };
    let title = format!("Review · {} {key}", state.period.title());
    frame.render_widget(Paragraph::new(body).block(theme::pane(&title)), rows[0]);
    frame.render_widget(
        Paragraph::new(Line::from(Span::styled(
            " h/l period · j/k scroll · w write to the file · c ask Claude Code for prose"
                .to_string(),
            theme::HINT,
        ))),
        rows[1],
    );
}
