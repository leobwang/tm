//! Screen 3 — Necessities (tm-spec-v1.md §12.3).
//!
//! # API overview
//!
//! > Left: this week's walls and routine windows on a 7-column hour grid,
//! > conflicts in red. Right: dated items sorted by `u` with
//! > `need / capacity / u / p`, IMPOSSIBLE first with the shortfall; then
//! > Waiting items with days waiting and timeout; then overdue-persist items.
//! > Keys: `E` estimate, `e` edit, `t` mark event arrived, `k` skip instance.
//!
//! Both halves are pure functions of [`View`]:
//!
//! * [`grid`] / [`Grid`] / [`Cell`] — the left half. Walls come from the
//!   `Shape::Interval` lines whose span touches this ISO week (the synced
//!   `calendar/` file and any exam or meeting written in a week file);
//!   routine windows from [`recur::week_instances`] over `routines.md`. A cell
//!   inside the *overlap* of two walls is a [`Cell::Conflict`] and renders red
//!   (§8.2 step 1: "overlapping walls → diagnostics.conflicts") — two walls in
//!   the same hour that do not overlap are not a conflict, exactly as in
//!   `check.rs`'s `wall-conflict` rule.
//! * [`rows`] / [`Row`] / [`Section`] — the right half, in §12.3's order and
//!   pairwise disjoint: `Impossible`, `Dated` (by `u`, descending), `Waiting`,
//!   `Necessary` (today's mandatory window instances, §5.2, and the
//!   overdue-`persist` items, §5.3 — the two things that must happen today).
//! * [`NecessitiesState`] — the cursor; [`render`] and [`on_key`] are the two
//!   functions `tui/mod.rs` dispatches to, exactly as for
//!   [`crate::tui::queue`].
//!
//! `k` (skip an instance) is §12.6's key for this screen, so the cursor moves
//! on `↑`/`↓` (and `j`, which the keymap leaves free) rather than on `j`/`k`.

use chrono::{Datelike, Duration, NaiveDate, NaiveDateTime, NaiveTime, Timelike};
use crossterm::event::{KeyCode, KeyEvent};
use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, Borders, Paragraph};
use ratatui::Frame;

use tm_core::emit;
use tm_core::ics::ALL_DAY_TAG;
use tm_core::model::{Dep, Id, InstanceKey, Recur, Shape, State};
use tm_core::priority::{self, PrioClass};
use tm_core::recur;
use tm_core::tree::Tree;

use super::queue::{fmt_u, Action, Mutation, Prompt, View};

// ---------------------------------------------------------------------------
// Left half — the week grid
// ---------------------------------------------------------------------------

/// What occupies one hour of one day in the grid.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Cell {
    /// Nothing.
    #[default]
    Free,
    /// A routine's placement window (§5.2).
    Window,
    /// An `at:` interval — a wall (§7.2, §8.2 step 1).
    Wall,
    /// Two or more walls overlap here.
    Conflict,
}

impl Cell {
    /// The three characters the cell is drawn with.
    pub fn glyph(self) -> &'static str {
        match self {
            Cell::Free => "   ",
            Cell::Window => "▒▒▒",
            Cell::Wall => "███",
            Cell::Conflict => "▚▚▚",
        }
    }

    /// The cell's colour (§12.3: "conflicts in red").
    pub fn style(self) -> Style {
        match self {
            Cell::Free => Style::default(),
            Cell::Window => Style::default().fg(Color::DarkGray),
            Cell::Wall => Style::default().fg(Color::Blue),
            Cell::Conflict => Style::default().fg(Color::Red),
        }
    }
}

/// The first hour the grid shows when nothing is scheduled outside it.
pub const FIRST_HOUR: u32 = 6;
/// One past the last hour the grid shows when nothing is scheduled outside it.
pub const LAST_HOUR: u32 = 24;

/// Windows wider than this are placement freedom, not a constraint, and are
/// left out of the grid (§5.1: an `every:week` instance spans the week).
pub const MAX_WINDOW_HOURS: i64 = 12;

/// The grid's width: the hour label plus 7 columns of `▒▒▒ `, plus a border.
pub const GRID_WIDTH: u16 = 3 + 7 * 4 + 2;

/// This week's walls and routine windows, one column per day.
///
/// Rows run from [`Grid::first_hour`] to [`Grid::last_hour`]. That band starts
/// at `FIRST_HOUR..LAST_HOUR` — the night is not drawn by default, because the
/// `sleep` window would otherwise fill every column — and then *grows* to cover
/// every wall of the week, so a 03:00 red-eye and the far half of an overnight
/// `at:` interval are both on screen (§12.3 is the screen that exists to show
/// walls). Routine *windows* stay clamped to `FIRST_HOUR..LAST_HOUR`, so
/// opening a night row for a wall does not drag `sleep` in with it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Grid {
    /// Monday..Sunday of the ISO week.
    pub days: [NaiveDate; 7],
    /// The first hour drawn (`FIRST_HOUR` unless a wall starts earlier).
    pub first_hour: u32,
    /// One past the last hour drawn (`LAST_HOUR` unless a wall ends later).
    pub last_hour: u32,
    /// `cells[hour - first_hour][weekday]`.
    pub cells: Vec<[Cell; 7]>,
    /// The pairs of walls that overlap (§8.2 step 1).
    pub conflicts: Vec<(Id, Id)>,
}

impl Grid {
    /// How many hour rows the grid has.
    pub fn rows(&self) -> usize {
        self.cells.len()
    }
}

/// Build the §12.3 grid for the week `view.today` falls in.
pub fn grid(view: &View<'_>) -> Grid {
    let week = view.week();
    let monday = week.monday();
    let mut days = [monday; 7];
    for (i, d) in days.iter_mut().enumerate() {
        *d = monday + Duration::days(i as i64);
    }

    // Walls: every open `at:` interval touching the week, with its `buffer:`
    // in front — the same set `check.rs`'s `wall-conflict` rule uses, so the
    // grid and `tm check` never disagree: an `#all-day` interval is day-level
    // context, and a zero-length one blocks nothing.
    let mut walls: Vec<(Id, NaiveDateTime, NaiveDateTime)> = Vec::new();
    for item in view.tree.iter() {
        if !item.state.is_open() {
            continue;
        }
        let Shape::Interval { start, end } = item.shape else {
            continue;
        };
        if item.tags.iter().any(|t| t == ALL_DAY_TAG) {
            continue;
        }
        let from = start
            - Duration::minutes(item.buffer.map_or(0, |d| d.as_minutes()) as i64);
        if end <= from {
            continue;
        }
        if end.date() < days[0] || from.date() > days[6] {
            continue;
        }
        walls.push((Tree::key_of(item), from, end));
    }
    walls.sort_by_key(|(_, s, _)| *s);

    // The band: the default working hours, widened to hold every wall.
    let (mut first, mut last) = (FIRST_HOUR, LAST_HOUR);
    for (_, start, end) in &walls {
        // A wall may run into the days on either side of the week; only the
        // part that falls inside a drawn column can widen the band.
        for day in &days {
            let (a, b) = clip_to_day(*start, *end, *day);
            if a >= b {
                continue;
            }
            first = first.min(a.time().hour());
            // `b` is exclusive: an interval ending at 11:00 fills the 10 row.
            let end_hour = (b - Duration::minutes(1)).time().hour();
            last = last.max(end_hour + 1);
        }
    }
    let rows = (last - first) as usize;
    let mut cells = vec![[Cell::Free; 7]; rows];
    let band = Band {
        first_hour: first,
        last_hour: last,
    };

    // Routine windows first, so a wall drawn over one wins.
    let routines: Vec<&tm_core::model::Item> = view
        .tree
        .routine_ids()
        .iter()
        .filter_map(|id| view.tree.get(id))
        .collect();
    let now_naive = view.now.naive_local();
    for (inst, _) in recur::week_instances(
        routines,
        week,
        view.today,
        now_naive,
        view.replay,
        view.cfg,
    ) {
        let Some((from, to)) = inst.window else {
            continue;
        };
        // A window wider than half a day is "any time this week" (§5.1: an
        // `every:week` instance spans Mon..Sun) and says nothing about *when*;
        // drawing it would grey out the whole grid.
        if (to - from) > Duration::hours(MAX_WINDOW_HOURS) {
            continue;
        }
        paint(&mut cells, &band, &days, from, to, Cell::Window, FIRST_HOUR..LAST_HOUR);
    }

    for (_, start, end) in &walls {
        paint(
            &mut cells,
            &band,
            &days,
            *start,
            *end,
            Cell::Wall,
            first..last,
        );
    }

    // §12.3's red is "these two walls collide", which is `check.rs`'s
    // `wall-conflict` rule — a pairwise *overlap*, not two walls that happen
    // to touch the same hour. So the conflict cells are painted from the
    // overlapping spans themselves; counting how often a cell was touched
    // would redden a 10:00–10:20 stand-up next to a 10:40–11:00 sync.
    let mut conflicts = Vec::new();
    for (i, (a, sa, ea)) in walls.iter().enumerate() {
        for (b, sb, eb) in walls.iter().skip(i + 1) {
            if sa < eb && sb < ea {
                conflicts.push((a.clone(), b.clone()));
                paint(
                    &mut cells,
                    &band,
                    &days,
                    *sa.max(sb),
                    *ea.min(eb),
                    Cell::Conflict,
                    first..last,
                );
            }
        }
    }

    Grid {
        days,
        first_hour: first,
        last_hour: last,
        cells,
        conflicts,
    }
}

/// The hour band the grid rows cover.
struct Band {
    first_hour: u32,
    last_hour: u32,
}

/// The part of `[from, to)` that falls on `day`, as a half-open span.
fn clip_to_day(
    from: NaiveDateTime,
    to: NaiveDateTime,
    day: NaiveDate,
) -> (NaiveDateTime, NaiveDateTime) {
    let start = day.and_time(NaiveTime::MIN);
    let end = start + Duration::days(1);
    (from.max(start), to.min(end))
}

/// Fill every grid cell the span `[from, to)` touches, within `hours`.
fn paint(
    cells: &mut [[Cell; 7]],
    band: &Band,
    days: &[NaiveDate; 7],
    from: NaiveDateTime,
    to: NaiveDateTime,
    kind: Cell,
    hours: std::ops::Range<u32>,
) {
    for (col, day) in days.iter().enumerate() {
        for hour in band.first_hour..band.last_hour {
            if !hours.contains(&hour) {
                continue;
            }
            let start = day.and_time(NaiveTime::from_hms_opt(hour, 0, 0).expect("hour"));
            let end = start + Duration::hours(1);
            if from < end && start < to {
                cells[(hour - band.first_hour) as usize][col] = kind;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Right half — the rows
// ---------------------------------------------------------------------------

/// Which §12.3 list a row belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Section {
    /// `need > capacity` before the deadline (§7.3) — listed first.
    Impossible,
    /// Everything else with an effective due, by `u` descending.
    Dated,
    /// `[?]` items (§5.1).
    Waiting,
    /// Today's mandatory window instances (§5.2) and overdue-`persist` items
    /// (§5.3): what must happen today.
    Necessary,
}

impl Section {
    /// The heading drawn above the section.
    pub fn title(self) -> &'static str {
        match self {
            Section::Impossible => "IMPOSSIBLE",
            Section::Dated => "Dated",
            Section::Waiting => "Waiting",
            Section::Necessary => "Necessary today",
        }
    }
}

/// One row of the right half.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Row {
    /// Which list it is in.
    pub section: Section,
    /// The item key (an `^id`, or a routine's title).
    pub id: Id,
    /// The title.
    pub title: String,
    /// `p` from §7, when the item is a candidate today.
    pub p: Option<u8>,
    /// `need` in blocks (§7.1: `remaining × safety`).
    pub need: String,
    /// The capacity the EDF pass found before this item reserved (§7.3).
    pub capacity: String,
    /// `u=0.6`.
    pub u: String,
    /// The right-hand note: the shortfall, `2d / 7d`, `overdue`, `last chance`.
    pub detail: String,
    /// The instance `k` would skip (§5.1).
    pub instance: Option<InstanceKey>,
    /// The event name `t` would mark arrived (§5.1).
    pub event: Option<String>,
}

/// The right half's rows, in §12.3's order.
///
/// The four sections are disjoint: every item appears in exactly one of them.
/// In particular an overdue-`persist` item is *only* under "Necessary today" —
/// its deadline is behind it, so it has no honest `u`, capacity or shortfall to
/// show in the dated list, and priority.rs draws the same line (`deadline_health`
/// counts a past-due item as overdue and never as IMPOSSIBLE).
pub fn rows(view: &View<'_>) -> Vec<Row> {
    let bm = view.block_min();
    let mut out: Vec<Row> = Vec::new();

    // Dated items (impossible ones first), by u descending.
    let mut dated: Vec<Row> = Vec::new();
    let mut sort_u: Vec<f64> = Vec::new();
    for (cand, prio) in view.candidates.iter().zip(view.prios.iter()) {
        if cand.is_wall || cand.is_optional || cand.effective_due.is_none() {
            continue;
        }
        if matches!(prio.class, PrioClass::Wall) {
            continue;
        }
        // A window instance carries a due (its window closing) but it is a
        // placement span, not a deadline — §7.3's EDF pass leaves it out for
        // the same reason, and it belongs under "Necessary today" instead.
        if cand.instance.is_some() {
            continue;
        }
        // §12.3's last group. An overdue item's `u` is ∞ and its "capacity by
        // <deadline>" is a statement about a date in the past, which neither
        // of §7.3's two exits can act on.
        if cand.overdue {
            continue;
        }
        // §5.1: a `[?]` item takes no slot; §12.3 gives it its own list.
        if cand.waiting {
            continue;
        }
        // §7.3's verdict, read the way priority.rs defines it (`u ≥ 1` *and*
        // `need > avail`) rather than off the class, which names the more
        // specific fact first for a `hot`-flagged or mandatory item.
        let impossible = prio.is_impossible();
        let detail = if impossible {
            format!(
                "needs {}, {} available by {}",
                priority::fmt_blocks(prio.need_min, bm),
                priority::fmt_blocks(prio.avail_min, bm),
                prio.until
                    .map(short_date)
                    .unwrap_or_else(|| "the deadline".to_string())
            )
        } else {
            cand.effective_due
                .map(|d| super::queue::due_text(d.date_naive(), view.today))
                .unwrap_or_default()
        };
        dated.push(Row {
            section: if impossible {
                Section::Impossible
            } else {
                Section::Dated
            },
            id: cand.id.clone(),
            title: cand.title.clone(),
            p: Some(prio.p),
            need: priority::fmt_blocks(prio.need_min, bm),
            capacity: priority::fmt_blocks(prio.avail_min, bm),
            u: fmt_u(prio.u),
            detail,
            instance: cand.instance,
            event: None,
        });
        sort_u.push(prio.u.unwrap_or(0.0));
    }
    let mut order: Vec<usize> = (0..dated.len()).collect();
    order.sort_by(|a, b| {
        dated[*a]
            .section
            .cmp(&dated[*b].section)
            .then_with(|| {
                sort_u[*b]
                    .partial_cmp(&sort_u[*a])
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .then_with(|| dated[*a].id.as_str().cmp(dated[*b].id.as_str()))
    });
    out.extend(order.into_iter().map(|i| dated[i].clone()));

    // Waiting (§5.1).
    for id in view.tree.waiting_ids() {
        let Some(item) = view.tree.get(&id) else {
            continue;
        };
        let state = recur::waiting_state(item, view.replay, view.today, view.cfg);
        let timeout = match &item.recur {
            Recur::OnEvent { timeout, .. } => *timeout,
            _ => None,
        };
        let detail = match (&state, timeout) {
            (Some(s), Some(t)) if s.arrived.is_some() => {
                format!("{}d / {t} · arrived", s.days_waiting)
            }
            (Some(s), Some(t)) => format!("{}d / {t}", s.days_waiting),
            (Some(s), None) => format!("{}d", s.days_waiting),
            (None, _) => String::new(),
        };
        out.push(Row {
            section: Section::Waiting,
            p: view.prio(&id).map(|p| p.p),
            need: String::new(),
            capacity: String::new(),
            u: String::new(),
            detail: if state.as_ref().map(|s| s.expired).unwrap_or(false) {
                format!("{detail} · timed out")
            } else {
                detail
            },
            instance: None,
            event: event_name(item),
            title: item.title.clone(),
            id,
        });
    }

    // Necessary today: §5.2's mandatory window instances and §5.3's
    // overdue-`persist` items — the two things that cannot wait. Both flags
    // are computed once, by `priority::collect_candidates`.
    let now_naive = view.now.naive_local();
    for (cand, prio) in view.candidates.iter().zip(view.prios.iter()) {
        if !cand.mandatory && !cand.overdue {
            continue;
        }
        // §5.1: a `[?]` item never takes a slot, so it is never "necessary
        // today"; it is listed above, under Waiting.
        if cand.waiting {
            continue;
        }
        // One row per line: a candidate already listed above (an item can be
        // both dated and mandatory) is not repeated here.
        if out
            .iter()
            .any(|r| r.id == cand.id && r.instance == cand.instance)
        {
            continue;
        }
        let mut detail = Vec::new();
        if cand.overdue {
            // A §5.3 overdue-`persist` item names the deadline it missed —
            // this is the only place it is listed, so the date has to be here.
            // An instance already prints its window, so it stays terse.
            detail.push(match (cand.instance, cand.effective_due) {
                (None, Some(d)) => format!("overdue since {}", short_date(d.date_naive())),
                _ => "overdue".to_string(),
            });
        }
        if cand.mandatory {
            detail.push("mandatory".to_string());
        }
        if let Some((_, close)) = cand.window {
            detail.push(format!("window closes {}", close.format("%a %H:%M")));
        }
        out.push(Row {
            section: Section::Necessary,
            p: Some(prio.p),
            need: priority::fmt_blocks(cand.remaining_min, bm),
            capacity: String::new(),
            u: String::new(),
            detail: detail.join(" · "),
            instance: cand.instance,
            event: None,
            title: cand.title.clone(),
            id: cand.id.clone(),
        });
    }
    for id in view.tree.overdue(now_naive) {
        if out.iter().any(|r| r.id == id) {
            continue;
        }
        let Some(item) = view.tree.get(&id) else {
            continue;
        };
        if item.state == State::Waiting {
            continue;
        }
        let due = view.tree.effective_due(&id);
        out.push(Row {
            section: Section::Necessary,
            p: view.prio(&id).map(|p| p.p),
            need: view
                .tree
                .remaining(&id)
                .map(|m| priority::fmt_blocks(m, bm))
                .unwrap_or_default(),
            capacity: String::new(),
            u: String::new(),
            detail: due
                .map(|d| format!("overdue since {}", short_date(d.date())))
                .unwrap_or_else(|| "overdue".to_string()),
            instance: None,
            event: None,
            title: item.title.clone(),
            id,
        });
    }
    out
}

/// The event a `[?]` item is waiting for: its `on-event:` name, else the first
/// `after:event:<name>` dependency (§5.1, §5.5).
fn event_name(item: &tm_core::model::Item) -> Option<String> {
    if let Recur::OnEvent { name, .. } = &item.recur {
        return Some(name.clone());
    }
    item.after.iter().find_map(|d| match d {
        Dep::Event(n) => Some(n.clone()),
        Dep::Item(_) => None,
    })
}

/// `Sep 11` — a date short enough for the shortfall line (§7.3).
fn short_date(d: NaiveDate) -> String {
    const M: [&str; 12] = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    format!("{} {}", M[(d.month0() as usize).min(11)], d.day())
}

// ---------------------------------------------------------------------------
// State and keys
// ---------------------------------------------------------------------------

/// Screen 3's cursor.
#[derive(Debug, Clone, Default)]
pub struct NecessitiesState {
    /// Index into [`rows`].
    pub sel: usize,
}

impl NecessitiesState {
    /// A fresh cursor.
    pub fn new() -> NecessitiesState {
        NecessitiesState::default()
    }

    /// The selected row.
    pub fn selected(&self, view: &View<'_>) -> Option<Row> {
        rows(view).into_iter().nth(self.sel)
    }
}

/// §12.6's keymap row for this screen.
pub const KEYMAP: &str =
    " ↑/↓ move · E estimate · e edit · t event arrived · k skip instance · 1-5 screens";

/// Handle one key press (§12.6's `necessities` row).
pub fn on_key(state: &mut NecessitiesState, view: &View<'_>, key: KeyEvent) -> Action {
    let rows = rows(view);
    let sel = rows.get(state.sel).cloned();
    match key.code {
        KeyCode::Down | KeyCode::Char('j') => {
            if state.sel + 1 < rows.len() {
                state.sel += 1;
            }
            Action::Redraw
        }
        KeyCode::Up => {
            state.sel = state.sel.saturating_sub(1);
            Action::Redraw
        }
        KeyCode::Char('E') => match sel {
            Some(r) => Action::Prompt(Prompt::Estimate(r.id)),
            None => Action::Note("nothing selected".to_string()),
        },
        KeyCode::Char('e') => match sel {
            // Every row here is a live line addressed by its key, so the
            // editor opens the tree's primary copy.
            Some(r) => Action::Edit {
                id: r.id,
                file: None,
            },
            None => Action::Note("nothing selected".to_string()),
        },
        KeyCode::Char('t') => match sel {
            Some(r) => match r.event {
                Some(name) => Action::Mutate(Mutation::Event {
                    name,
                    id: Some(r.id),
                }),
                None => Action::Note(format!("{} is not waiting for an event", r.id)),
            },
            None => Action::Note("nothing selected".to_string()),
        },
        KeyCode::Char('k') => match sel {
            Some(r) => match r.instance {
                Some(instance) => Action::Mutate(Mutation::Skip {
                    item: r.id,
                    instance,
                }),
                None => Action::Note(format!("{} has no instance to skip", r.id)),
            },
            None => Action::Note("nothing selected".to_string()),
        },
        _ => Action::Ignored,
    }
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

/// Draw Screen 3 into `area` (§12.3).
pub fn render(state: &NecessitiesState, view: &View<'_>, frame: &mut Frame, area: Rect) {
    if area.height == 0 || area.width == 0 {
        return;
    }
    let narrow = (area.width as u32) < view.cfg.tui.min_width;
    let outer = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Min(3), Constraint::Length(1)])
        .split(area);
    let halves = if narrow {
        // Stacked (§12: "below that, panes stack"). The grid asks for the
        // height its hours need and gets at most half the screen — the old
        // fixed 9 rows dropped every wall after 11:00 with nothing to say so,
        // and taking the whole height would starve the list instead. What does
        // not fit is reported by both halves rather than silently cut.
        let g = grid(view);
        let natural = g.rows() as u16 + 3;
        let available = outer[0].height;
        let height = natural
            .min((available / 2).max(MIN_GRID_HEIGHT))
            .clamp(1, available);
        Layout::default()
            .direction(Direction::Vertical)
            .constraints([Constraint::Length(height), Constraint::Min(0)])
            .split(outer[0])
    } else {
        Layout::default()
            .direction(Direction::Horizontal)
            .constraints([Constraint::Length(GRID_WIDTH), Constraint::Min(20)])
            .split(outer[0])
    };
    render_grid(view, frame, halves[0]);
    render_rows(state, view, frame, halves[1]);
    frame.render_widget(
        Paragraph::new(Line::from(Span::styled(
            emit::clip(KEYMAP, outer[1].width as usize),
            Style::default().fg(Color::DarkGray),
        ))),
        outer[1],
    );
}

/// The height the grid keeps for itself in the stacked layout, even when the
/// list below would like all of it.
const MIN_GRID_HEIGHT: u16 = 5;

/// The left half. The grid is a fixed 7 × 3 columns wide, so a stacked
/// (narrow) layout does not stretch it across the terminal.
///
/// When the area is too short for every hour, the last line says how many rows
/// were dropped rather than ending the grid silently at whatever hour fitted.
fn render_grid(view: &View<'_>, frame: &mut Frame, area: Rect) {
    let area = Rect {
        width: area.width.min(GRID_WIDTH),
        ..area
    };
    let g = grid(view);
    let block = Block::default()
        .borders(Borders::ALL)
        .title(format!(" Week {} · walls & windows ", view.week().short()))
        .border_style(Style::default().fg(Color::DarkGray));
    let inner = block.inner(area);
    frame.render_widget(block, area);
    if inner.height == 0 {
        return;
    }
    let mut lines: Vec<Line<'static>> = Vec::new();
    let mut header = String::from("   ");
    for d in &g.days {
        header.push_str(&format!("{} ", weekday3(d)));
    }
    lines.push(Line::from(Span::styled(
        header,
        Style::default().fg(Color::DarkGray),
    )));
    // The header eats one line; a "… N more" marker eats one more, but only
    // when there is something to say.
    let body = inner.height as usize - 1;
    let shown = if g.rows() <= body {
        g.rows()
    } else {
        body.saturating_sub(1)
    };
    for (r, row) in g.cells.iter().take(shown).enumerate() {
        let hour = g.first_hour + r as u32;
        let mut spans = vec![Span::styled(
            format!("{hour:02} "),
            Style::default().fg(Color::DarkGray),
        )];
        for cell in row {
            spans.push(Span::styled(cell.glyph(), cell.style()));
            spans.push(Span::raw(" "));
        }
        lines.push(Line::from(spans));
    }
    if shown < g.rows() {
        lines.push(Line::from(Span::styled(
            format!("…  {} more hours to {:02}:00", g.rows() - shown, g.last_hour),
            Style::default().fg(Color::Yellow),
        )));
    }
    frame.render_widget(Paragraph::new(lines), inner);
}

/// `Mon`…`Sun`, three columns.
fn weekday3(d: &NaiveDate) -> &'static str {
    match d.weekday() {
        chrono::Weekday::Mon => "Mon",
        chrono::Weekday::Tue => "Tue",
        chrono::Weekday::Wed => "Wed",
        chrono::Weekday::Thu => "Thu",
        chrono::Weekday::Fri => "Fri",
        chrono::Weekday::Sat => "Sat",
        chrono::Weekday::Sun => "Sun",
    }
}

/// The right half. The title carries the count of rows the pane could not fit,
/// so a short (stacked) layout never hides a deadline in silence.
fn render_rows(state: &NecessitiesState, view: &View<'_>, frame: &mut Frame, area: Rect) {
    let all = rows(view);
    let inner = Rect {
        x: area.x + 1,
        y: area.y + 1,
        width: area.width.saturating_sub(2),
        height: area.height.saturating_sub(2),
    };
    if inner.height == 0 || inner.width == 0 {
        frame.render_widget(
            Block::default()
                .borders(Borders::ALL)
                .title(" Deadlines · waiting · necessary ")
                .border_style(Style::default().fg(Color::White)),
            area,
        );
        return;
    }
    let w = inner.width as usize;
    let id_w = all
        .iter()
        .map(|r| emit::display_width(r.id.as_str()))
        .max()
        .unwrap_or(2)
        .clamp(2, 12);
    let mut display: Vec<(Option<usize>, Line<'static>)> = Vec::new();
    let mut section: Option<Section> = None;
    for (i, r) in all.iter().enumerate() {
        if section != Some(r.section) {
            section = Some(r.section);
            let style = if r.section == Section::Impossible {
                Style::default().fg(Color::Red)
            } else {
                Style::default().fg(Color::DarkGray)
            };
            let title = r.section.title();
            let rule = "─".repeat(w.saturating_sub(emit::display_width(title) + 6));
            display.push((None, Line::from(Span::styled(format!("──── {title} {rule}"), style))));
        }
        display.push((Some(i), Line::from(emit::clip(&row_text(r, w, id_w), w))));
    }
    if display.is_empty() {
        display.push((
            None,
            Line::from(Span::styled(
                "nothing pressing",
                Style::default().fg(Color::DarkGray),
            )),
        ));
    }
    let cursor = display.iter().position(|(i, _)| *i == Some(state.sel));
    let h = inner.height as usize;
    let offset = match cursor {
        Some(p) if p >= h => p + 1 - h,
        _ => 0,
    };
    let hidden = display.len().saturating_sub(h);
    let title = if hidden == 0 {
        " Deadlines · waiting · necessary ".to_string()
    } else {
        format!(" Deadlines · waiting · necessary · {hidden} more ↓ ")
    };
    frame.render_widget(
        Block::default()
            .borders(Borders::ALL)
            .title(title)
            .border_style(Style::default().fg(Color::White)),
        area,
    );
    let lines: Vec<Line<'static>> = display
        .into_iter()
        .skip(offset)
        .take(h)
        .map(|(i, line)| {
            if i == Some(state.sel) {
                line.style(Style::default().add_modifier(Modifier::REVERSED))
            } else {
                line
            }
        })
        .collect();
    frame.render_widget(Paragraph::new(lines), inner);
}

/// One row as text: `⚠ d1 CS 234 pset 2   need 7.8b cap 5b u=1.6 p0  needs …`.
fn row_text(r: &Row, w: usize, id_w: usize) -> String {
    let mark = match r.section {
        Section::Impossible => "⚠",
        Section::Waiting => "?",
        Section::Necessary => "!",
        Section::Dated => " ",
    };
    let head = format!("{mark} {} ", emit::pad_to(r.id.as_str(), id_w));
    let mut tail: Vec<String> = Vec::new();
    if !r.need.is_empty() {
        tail.push(format!("need {}", r.need));
    }
    if !r.capacity.is_empty() {
        tail.push(format!("cap {}", r.capacity));
    }
    if !r.u.is_empty() {
        tail.push(r.u.clone());
    }
    if let Some(p) = r.p {
        tail.push(format!("p{p}"));
    }
    if !r.detail.is_empty() {
        tail.push(r.detail.clone());
    }
    let tail = tail.join("  ");
    let title_w = w.saturating_sub(emit::display_width(&head) + emit::display_width(&tail) + 2);
    format!("{head}{}  {tail}", emit::pad_to(&r.title, title_w))
}
