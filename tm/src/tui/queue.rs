//! Screen 2 — the Queue (tm-spec-v1.md §12.2), and the plumbing the other two
//! screens in milestone M7 share with it.
//!
//! # API overview
//!
//! Three panes — Month | Week | Tasks-of-the-selection — over one week of the
//! plan, drawn exactly as §12.2's mock:
//!
//! ```text
//! ┌─ Month 2026-09 ─────────────┐┌─ Week W37 · planned 20 / budget 25 ────────┐┌─ Tasks @m2 ──────────┐
//! │ !1 O1 Lean ch.8        ▓▓░  ││ p1 5 6b m1 Finish ch.5 exercises  @O1 ▓▓▓░░││ p3 3 1b CC drafts …  │
//! │ Demoted (1)                 ││ p1 4 6b d1 CS 234 pset 2 due Fri u=0.6 …   ││ p3 3 1b Review …  ⛔  │
//! ```
//!
//! Everything here is a pure function of the state and the [`View`]; the only
//! side effect the screen performs itself is [`reorder`] (§12.6's `J`/`K`,
//! which swaps two item lines in the file the row came from and writes every
//! other byte back unchanged). Every other key returns an [`Action`] the shell
//! carries out.
//!
//! ## Shared types (used by `necessities.rs` and `inbox.rs` too)
//!
//! * [`View`] — the read-only slice of the world the M7 screens render: tree,
//!   files, config, replay, candidates, priorities and capacity, plus `today`
//!   and `now`. The shell builds one per frame.
//! * [`Action`] — what a key press asks the shell to do (`Ignored`, `Redraw`,
//!   `Note`, `Edit`, [`Prompt`], [`Mutation`]).
//! * Small formatting helpers: [`fmt_u`], [`fmt_fits`], [`bar`], [`due_text`],
//!   [`est_text`]. The width ones are `tm_core::emit`'s since D43.
//!
//! ## The screen
//!
//! * [`QueueState`] — pane focus, one cursor per pane, the drill target;
//!   [`Selection`] — the *line* under the cursor (id **and** file: §6.3 leaves
//!   one `^id` on two lines).
//! * [`render`] / [`on_key`] — the two functions `tui/mod.rs` dispatches to.
//! * [`month_rows`], [`week_rows`], [`task_rows`], [`fits_footer`] — the row
//!   model, so the columns can be asserted without a terminal.
//! * [`reorder`] / [`apply_reorder`] — `J`/`K`; [`edit_command`] — `e`
//!   (`cfg.tui.editor`).
//!
//! ## Integration
//!
//! The TUI shell owns `tui/mod.rs` and `App`. The merge is three `mod` lines
//! and, at the `Screen::Queue` arm,
//!
//! ```ignore
//! Screen::Queue => queue::render(&app.queue, &app.view(), frame, area),
//! // and, in the key dispatch:
//! Screen::Queue => queue::on_key(&mut app.queue, &app.view(), key),
//! // …whose `Action::Mutate(m)` arm starts with the one mutation this module
//! // performs itself (every other one is a §13 verb):
//! if let Some(moved) = queue::apply_reorder(store, &m) { moved?; reload(); }
//! ```
//!
//! where `App` gains a `queue: QueueState` field and a `view(&self) -> View<'_>`
//! constructor. `render` draws the §12.6 keymap row on the last line of the
//! area it is given, as the mock does; pass a shorter area to suppress it.

use std::collections::HashMap;

use chrono::{DateTime, Datelike, NaiveDate};
use chrono_tz::Tz;
use crossterm::event::{KeyCode, KeyEvent};
use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, Borders, Paragraph};
use ratatui::Frame;

use tm_core::capacity::{self, UnitCapacity, CAP_DEN};
use tm_core::config::Config;
use tm_core::emit;
use tm_core::grammar::ParsedFile;
use tm_core::log::Replay;
use tm_core::model::{Id, InstanceKey, IsoWeek, State, YearMonth};
use tm_core::priority::{self, Candidate, Prio};
use tm_core::store::{edit, PlanFiles, Store, StoreError};
use tm_core::tree::Tree;

// ---------------------------------------------------------------------------
// The view the M7 screens read
// ---------------------------------------------------------------------------

/// Everything the Queue, Necessities and Inbox screens read.
///
/// The shell builds one per frame from its loaded context; the screens never
/// touch the store through it (§12: "all rendering pure functions of App
/// state").
pub struct View<'a> {
    /// The parsed tree (§6).
    pub tree: &'a Tree,
    /// The parsed files, for front matter and for `inbox.md`'s raw lines.
    pub files: &'a PlanFiles,
    /// Configuration (§16).
    pub cfg: &'a Config,
    /// The log replay (§10.1), for progress and instance status.
    pub replay: &'a Replay,
    /// Today's candidates (§6.2), in `priority::collect_candidates` order.
    pub candidates: &'a [Candidate],
    /// `priority::compute`'s output, 1:1 with `candidates` (§7).
    pub prios: &'a [Prio],
    /// The week lookahead the EDF pass ran on (§8.4): the kernel's days, in
    /// exact units (stage 5 D10 L8).
    pub caps: &'a [UnitCapacity],
    /// Today.
    pub today: NaiveDate,
    /// Now, in `cfg.tz`.
    pub now: DateTime<Tz>,
    /// Done minutes per item (`Replay::done_minutes_map`), for §6.4 progress.
    done: HashMap<Id, u32>,
}

impl<'a> View<'a> {
    /// Bundle the world for one frame.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        tree: &'a Tree,
        files: &'a PlanFiles,
        cfg: &'a Config,
        replay: &'a Replay,
        candidates: &'a [Candidate],
        prios: &'a [Prio],
        caps: &'a [UnitCapacity],
        today: NaiveDate,
        now: DateTime<Tz>,
    ) -> View<'a> {
        View {
            tree,
            files,
            cfg,
            replay,
            candidates,
            prios,
            caps,
            today,
            now,
            done: replay.done_minutes_map(),
        }
    }

    /// The ISO week `today` falls in — the Queue's Week pane.
    pub fn week(&self) -> IsoWeek {
        IsoWeek::from_date(self.today)
    }

    /// The month `today` falls in — the Queue's Month pane.
    pub fn month(&self) -> YearMonth {
        YearMonth::from_date(self.today)
    }

    /// One block in minutes (§16 `day.block_min`).
    pub fn block_min(&self) -> u32 {
        self.cfg.block_min()
    }

    /// The priority computed for `id`, when it is a candidate today.
    ///
    /// A key can appear twice (a carried persist instance and today's); the
    /// first, which is the more urgent one, wins.
    pub fn prio(&self, id: &Id) -> Option<&Prio> {
        self.prios.iter().find(|p| &p.id == id)
    }

    /// The candidate `id` stands for today, when there is one.
    pub fn candidate(&self, id: &Id) -> Option<&Candidate> {
        self.candidates.iter().find(|c| &c.id == id)
    }

    /// Logged block minutes per item (§6.4's `done_minutes` input).
    #[allow(dead_code)] // Read by §17 M7's screen tests.
    pub fn done_minutes(&self) -> &HashMap<Id, u32> {
        &self.done
    }

    /// §6.4 progress for `id`, `None` when nothing is planned for it.
    pub fn progress(&self, id: &Id) -> Option<f64> {
        self.tree.progress(id, &self.done)
    }
}

// ---------------------------------------------------------------------------
// What a key press asks the shell to do
// ---------------------------------------------------------------------------

/// What a key press on an M7 screen asks the shell to do.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Action {
    /// Not one of this screen's keys — let the shell's global map have it.
    Ignored,
    /// The screen state changed; redraw.
    Redraw,
    /// Show this text in the status line (a refusal, or a command to run).
    Note(String),
    /// Open the item in the editor (§12: `code -g file:line`, see
    /// [`edit_command`]).
    Edit {
        /// The item.
        id: Id,
        /// Which copy of a duplicated id the row was read from (§6.3's
        /// `# Demoted` archive shares its id with the live line); `None`
        /// leaves the choice to the tree's primary copy.
        file: Option<String>,
    },
    /// Ask the user for a value, then apply it (§12.6's `a c E P`).
    Prompt(Prompt),
    /// Change a file; the shell runs it and reloads the tree.
    Mutate(Mutation),
}

/// An input the shell must collect before it can act (§12.6).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Prompt {
    /// `a` — add a line to `file`, under `section` (`tm add`).
    Add {
        /// The target file, relative to the plan root.
        file: String,
        /// The heading to insert under, when the pane has one.
        section: Option<String>,
    },
    /// `c` — set `ci` 0..=5 (`tm edit ^id ci=N`).
    Ci(Id),
    /// `E` — set the leading estimate (`tm edit ^id est=2b`).
    Estimate(Id),
    /// `P` — set `!k` on a root (`tm edit ^id p=2`).
    Priority(Id),
}

/// A file change the shell performs (each is one §13 verb).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Mutation {
    /// `J`/`K` — move the line within its section (see [`reorder`]).
    Reorder {
        /// The line to move.
        id: Id,
        /// The file the row was read from. An id can name two lines — §6.3
        /// copies a demoted week line into `month/<m>.md#Demoted` — and the
        /// row the cursor is on decides which one moves. `None` leaves the
        /// choice to [`Store::reorder_line`] (the live line).
        file: Option<String>,
        /// `+1` down, `-1` up.
        delta: i32,
    },
    /// `D` — `tm demote ^id`. Refused on a `# Demoted` archive row, which is
    /// the record of a demotion that already happened (§6.3).
    Demote(Id),
    /// `A` — `tm readopt ^id`.
    Readopt(Id),
    /// `x` — `tm drop ^id`. Like `A`, this addresses the *item*, so on a
    /// `# Demoted` row it drops the item the archive line records, which is
    /// what §13's verb means by the id.
    Drop(Id),
    /// `k` on Necessities — `tm skip <routine>` for one instance (§5.1).
    Skip {
        /// The item (a routine's title key, or an `^id`).
        item: Id,
        /// Which occurrence.
        instance: InstanceKey,
    },
    /// `t` on Necessities — `tm event <name> [^id]` (§5.1).
    Event {
        /// The event name from `on-event:`.
        name: String,
        /// The waiting item, when the row names one.
        id: Option<Id>,
    },
    /// Enter on Inbox capture — `tm add "<text>" --to <file> --section <s>`.
    Capture {
        /// The §4.1 line, exactly as the preview showed it.
        text: String,
        /// The target file.
        file: String,
        /// The target section.
        section: Option<String>,
        /// The `inbox.md` line this came from (`t` triage), to drop once the
        /// add succeeds.
        from_inbox: Option<usize>,
    },
    /// `x` on Inbox — remove one raw line from `inbox.md`.
    DropInboxLine {
        /// 1-based line number in `inbox.md`.
        line: usize,
    },
}

// ---------------------------------------------------------------------------
// Formatting helpers shared by the three screens
// ---------------------------------------------------------------------------

// The three functions that used to live here -- `width`, `truncate` and `pad`
// -- are GONE (the owner's **D43**). They were a second implementation of
// `tm-core::emit`'s padding, measuring with ratatui's `unicode-width` where
// `emit` measures with its own East-Asian table, so one concept had two
// answers (AGENTS 5.3). The screens now call `emit::display_width`,
// `emit::clip` and `emit::pad_to`; `tm/tests/one_padder.rs` is the guard.

/// §12.2's utilization column: `u=0.6`, `u=0.15`, `u=∞`.
pub fn fmt_u(u: Option<f64>) -> String {
    match u {
        None => String::new(),
        Some(u) if !u.is_finite() => "u=∞".to_string(),
        Some(u) => {
            let mut s = format!("{u:.2}");
            while s.contains('.') && (s.ends_with('0') || s.ends_with('.')) {
                s.pop();
            }
            format!("u={s}")
        }
    }
}

/// Blocks without the unit, for §12.2's `fits 6/6` column.
fn blocks_bare(minutes: u32, block_min: u32) -> String {
    let s = priority::fmt_blocks(minutes, block_min);
    s.strip_suffix('b').map(str::to_string).unwrap_or(s)
}

/// §7.2's allocation as the Queue shows it: `fits 6/6` — how much of what is
/// left fits in the capacity the EDF pass reserved for it.
///
/// The numerator is `min(allocation, remaining)`: an allocation carries the
/// `safety` factor (§7.1, `need = remaining × 1.3`), and "fits 7.8 of 6" would
/// read as nonsense.
pub fn fmt_fits(prio: &Prio, remaining_min: u32, block_min: u32) -> String {
    // Only the EDF and floor passes produce an allocation (§7.2); a pure-rank
    // item has no deadline to fit into, so the column stays empty.
    if prio.u.is_none() || remaining_min == 0 {
        return String::new();
    }
    let fits = prio.allocation_min.min(remaining_min);
    format!(
        "fits {}/{}",
        blocks_bare(fits, block_min),
        blocks_bare(remaining_min, block_min)
    )
}

/// A progress bar of `cells` cells: `▓▓▓░░░`.
pub fn bar(progress: Option<f64>, cells: usize) -> String {
    let p = progress.unwrap_or(0.0).clamp(0.0, 1.0);
    let full = (p * cells as f64).round() as usize;
    let full = full.min(cells);
    format!("{}{}", "▓".repeat(full), "░".repeat(cells - full))
}

/// §12.2's deadline column: `due today`, `due Fri` inside this week, else
/// `due Oct 20`.
pub fn due_text(due: NaiveDate, today: NaiveDate) -> String {
    if due == today {
        return "due today".to_string();
    }
    if IsoWeek::from_date(due) == IsoWeek::from_date(today) {
        return format!("due {}", weekday_name(due));
    }
    format!("due {} {}", month_name(due), due.day())
}

/// `Mon`…`Sun`.
fn weekday_name(d: NaiveDate) -> &'static str {
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

/// `Jan`…`Dec`.
fn month_name(d: NaiveDate) -> &'static str {
    const M: [&str; 12] = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    M[(d.month0() as usize).min(11)]
}

/// The estimate column: `est:` as written, else the leading estimate, else the
/// §6.4 rollup over the children.
pub fn est_text(view: &View<'_>, id: &Id) -> String {
    if let Some(item) = view.tree.get(id) {
        if let Some(e) = item.est {
            return e.to_string();
        }
        if let Some(e) = item.est_original {
            return e.to_string();
        }
    }
    match view.tree.remaining(id) {
        Some(m) if m > 0 => priority::fmt_blocks(m, view.block_min()),
        _ => String::new(),
    }
}

/// The `code -g <file>:<line>` command for `id` (§12, `cfg.tui.editor`).
///
/// `file` names which copy of a duplicated id to open — §6.3 leaves the same
/// `^id` on a demoted week line and on its `month/<m>.md#Demoted` archive copy,
/// and `e` must open the line the cursor is on, not the other one. `None` (and
/// a file that holds no copy) falls back to the tree's primary line.
///
/// `None` when the id is not in the tree.
pub fn edit_command(cfg: &Config, tree: &Tree, id: &Id, file: Option<&str>) -> Option<String> {
    let item = file
        .and_then(|f| tree.all(id).into_iter().find(|i| i.src.file == f))
        .or_else(|| tree.get(id))?;
    Some(
        cfg.tui
            .editor
            .replace("{file}", &item.src.file)
            .replace("{line}", &item.src.line.to_string()),
    )
}

// ---------------------------------------------------------------------------
// J/K — the one thing this screen writes itself
// ---------------------------------------------------------------------------

/// §12.6's `J`/`K`: move `id` by `delta` lines within its own section.
///
/// With `file = None` this is [`Store::reorder_line`] verbatim, which re-reads
/// the file, swaps two *item* lines and writes every other byte back unchanged
/// — §12.2's "`J`/`K` rewrite line order in the file" and M7's
/// "byte-faithfully". Returns `false` when the line is already at the end of
/// its section.
///
/// `file` names the copy to move. It matters because an id can name two lines:
/// §6.3 copies a demoted week line into `month/<m>.md#Demoted`, and
/// [`Store::reorder_line`] resolves a bare id to the copy *outside* `# Demoted`
/// — so `J` on the Month pane's archive row would otherwise rewrite the week
/// file the user is not looking at. The rewrite is the same pure
/// [`edit::reorder_line`] transform the store uses, applied to the named file
/// through [`Store::modify_file`], so it stays byte-faithful and race-guarded.
pub fn reorder(
    store: &dyn Store,
    id: &Id,
    file: Option<&str>,
    delta: i32,
) -> Result<bool, StoreError> {
    let Some(rel) = file else {
        return store.reorder_line(id, delta);
    };
    let mut moved = false;
    let mut found = false;
    store.modify_file(rel, &mut |parsed: &ParsedFile| {
        // `modify_file` may re-apply this to a racing writer's text.
        moved = false;
        found = false;
        let Some(idx) = edit::find_line(parsed, id) else {
            return Ok(None);
        };
        found = true;
        match edit::reorder_line(parsed, idx, delta) {
            Some(text) => {
                moved = true;
                Ok(Some(text))
            }
            None => Ok(None),
        }
    })?;
    if !found {
        return Err(StoreError::NotFound(id.clone()));
    }
    Ok(moved)
}

/// Carry out the [`Mutation::Reorder`] that [`on_key`] returns for `J`/`K`.
///
/// This is the whole shell wiring for that key: `Action::Mutate(m)` →
/// `queue::apply_reorder(store, &m)` → reload. Any other mutation is one of
/// §13's verbs and is not this module's to perform, so it returns `None`.
pub fn apply_reorder(store: &dyn Store, m: &Mutation) -> Option<Result<bool, StoreError>> {
    match m {
        Mutation::Reorder { id, file, delta } => {
            Some(reorder(store, id, file.as_deref(), *delta))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Row model
// ---------------------------------------------------------------------------

/// One line of the Month pane: an outcome, or a `# Demoted` archive line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MonthRow {
    /// The item's `^id`.
    pub id: Id,
    /// The file the line was read from — `month/<m>.md` for both the outcomes
    /// and the `# Demoted` archive copies, which share their `^id` with a week
    /// line (§6.3). A mutation on this row must name it.
    pub file: String,
    /// Explicit `!k` (§4.3: roots carry it).
    pub priority: Option<u8>,
    /// The title.
    pub title: String,
    /// `▓▓░` — three cells of §6.4 progress.
    pub bar: String,
    /// True for a line inside `# Demoted` (§6.3).
    pub demoted: bool,
    /// `W36,W37` — the demotion stamps.
    pub stamps: String,
}

/// One line of the Week pane (§12.2's `p<N> <ci> <est> <id> <title> @<parent>`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeekRow {
    /// The item's `^id`.
    pub id: Id,
    /// The file the line was read from.
    pub file: String,
    /// `p` from §7, when the item is a candidate today.
    pub p: Option<u8>,
    /// §7.4 held `p` above its raw value this morning.
    pub hysteresis: bool,
    /// Min-energy 0..=5.
    pub ci: u8,
    /// The estimate column.
    pub est: String,
    /// The title.
    pub title: String,
    /// `@O1`, when the line has a parent.
    pub parent: String,
    /// `due Fri` / `due Oct 20`, for dated items.
    pub due: String,
    /// `u=0.6`, from the EDF pass.
    pub u: String,
    /// `fits 6/6`, §7.2's allocation.
    pub fits: String,
    /// The progress bar, for undated items.
    pub bar: String,
    /// `[x]` — the row renders `✓` instead of a bar.
    pub done: bool,
    /// An `at:` interval — a wall, off the priority scale (§7.2). The `p`
    /// column shows `⏰`.
    pub wall: bool,
}

/// One line of the Tasks pane.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TaskRow {
    /// The item's `^id`.
    pub id: Id,
    /// The file the line was read from.
    pub file: String,
    /// `p` from §7.
    pub p: Option<u8>,
    /// Min-energy.
    pub ci: u8,
    /// The estimate column.
    pub est: String,
    /// The title.
    pub title: String,
    /// `⛔ after t4` when a dependency is unsatisfied (§5.5).
    pub blocked: Option<String>,
    /// `[x]`.
    pub done: bool,
}

/// The Month pane's rows: this month's outcomes, then its `# Demoted` archive
/// (§4.3, §6.3).
pub fn month_rows(view: &View<'_>) -> Vec<MonthRow> {
    let mut rows = Vec::new();
    for item in view.tree.month_items(view.month()) {
        let demoted = item
            .src
            .section
            .as_deref()
            .map(|s| s.trim() == "Demoted")
            .unwrap_or(false);
        let id = Tree::key_of(item);
        rows.push(MonthRow {
            file: item.src.file.clone(),
            priority: item.priority,
            title: item.title.clone(),
            bar: if demoted {
                String::new()
            } else {
                bar(view.progress(&id), 3)
            },
            demoted,
            stamps: item.stamps.demoted_value(),
            id,
        });
    }
    rows.sort_by_key(|r| r.demoted);
    rows
}

/// The Week pane's rows: every line of `week/<this week>.md`, in file order
/// (§7.4: line order is rank).
pub fn week_rows(view: &View<'_>) -> Vec<WeekRow> {
    let block_min = view.block_min();
    view.tree
        .week_items(view.week())
        .into_iter()
        .map(|item| {
            let id = Tree::key_of(item);
            let prio = view.prio(&id);
            let due = view
                .candidate(&id)
                .and_then(|c| c.effective_due)
                .map(|d| d.date_naive())
                .or_else(|| view.tree.effective_due(&id).map(|d| d.date()));
            let remaining = view.tree.remaining(&id).unwrap_or(0);
            WeekRow {
                file: item.src.file.clone(),
                p: prio.map(|p| p.p),
                hysteresis: prio.map(|p| p.hysteresis_applied).unwrap_or(false),
                ci: item.ci,
                est: est_text(view, &id),
                title: item.title.clone(),
                parent: item.parent.as_ref().map(|r| r.token()).unwrap_or_default(),
                due: due.map(|d| due_text(d, view.today)).unwrap_or_default(),
                u: prio.map(|p| fmt_u(p.u)).unwrap_or_default(),
                fits: prio
                    .map(|p| fmt_fits(p, remaining, block_min))
                    .unwrap_or_default(),
                bar: bar(view.progress(&id), blocks_cells(remaining, block_min)),
                done: item.state == State::Done,
                wall: matches!(item.shape, tm_core::model::Shape::Interval { .. }),
                id,
            }
        })
        .collect()
}

/// One bar cell per whole block, 1..=6.
fn blocks_cells(minutes: u32, block_min: u32) -> usize {
    let blocks = (minutes as f64 / block_min.max(1) as f64).ceil() as usize;
    blocks.clamp(1, 6)
}

/// The Tasks pane's rows: the direct children of `parent` (§6.1, §12.2 —
/// "Tasks @m2"), in file order.
///
/// `parent = None` means the cursor is on nothing (both other panes are empty,
/// or the selection index is past the end after a drop or a reload), and the
/// pane is then empty: there is no selection whose children could be listed.
/// The pane title drops the `@<id>` to say so.
pub fn task_rows(view: &View<'_>, parent: Option<&Id>) -> Vec<TaskRow> {
    let ids: Vec<Id> = match parent {
        Some(p) => view.tree.children(p).to_vec(),
        None => Vec::new(),
    };
    ids.into_iter()
        .filter_map(|id| {
            let item = view.tree.get(&id)?;
            let blocked = view.candidate(&id).and_then(|c| {
                if c.blocked_by.is_empty() {
                    None
                } else {
                    let deps: Vec<String> = c
                        .blocked_by
                        .iter()
                        .map(|d| d.to_string().trim_start_matches('^').to_string())
                        .collect();
                    Some(format!("⛔ after {}", deps.join(",")))
                }
            });
            Some(TaskRow {
                file: item.src.file.clone(),
                p: view.prio(&id).map(|p| p.p),
                ci: item.ci,
                est: est_text(view, &id),
                title: item.title.clone(),
                blocked,
                done: item.state == State::Done,
                id,
            })
        })
        .collect()
}

/// §12.2's Tasks footer: `fits this week: 6b of 6b`.
///
/// `of` is what the listed rows still owe (§6.4 remaining); the first number is
/// how much of it this week's lookahead can actually hold, allocated greedily
/// in row order at each row's `ci` — the same reservation §7.3 makes, run over
/// the rest of the week instead of up to a deadline.
///
/// The reservation runs in exact units over the kernel's days (stage 5 D10
/// L8; kernel/README.md gap 94, T16), and `fits` is shown as the floor of the
/// exact units reserved.
pub fn fits_footer(view: &View<'_>, rows: &[TaskRow]) -> String {
    let block_min = view.block_min();
    let week_end = view.week().sunday();
    let n = capacity::upto_units(view.caps, week_end);
    let mut caps: Vec<UnitCapacity> = view.caps[..n].to_vec();
    let mut total = 0;
    let mut fits: u128 = 0;
    for row in rows {
        if row.done {
            continue;
        }
        let remaining = view.tree.remaining(&row.id).unwrap_or(0);
        total += remaining;
        fits += capacity::reserve_units(&mut caps, u128::from(remaining) * CAP_DEN, row.ci);
    }
    format!(
        "fits this week: {} of {}",
        priority::fmt_blocks(capacity::floor_minutes(fits), block_min),
        priority::fmt_blocks(total, block_min)
    )
}

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

/// Which of the three panes has focus.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Pane {
    /// The month's outcomes.
    Month,
    /// This week's milestones and tasks.
    #[default]
    Week,
    /// The children of the selection.
    Tasks,
}

impl Pane {
    /// The pane to the left (`h`), saturating.
    pub fn left(self) -> Pane {
        match self {
            Pane::Month => Pane::Month,
            Pane::Week => Pane::Month,
            Pane::Tasks => Pane::Week,
        }
    }

    /// The pane to the right (`l`), saturating.
    pub fn right(self) -> Pane {
        match self {
            Pane::Month => Pane::Week,
            Pane::Week => Pane::Tasks,
            Pane::Tasks => Pane::Tasks,
        }
    }
}

/// What the cursor is on: the line, not just the item.
///
/// §6.3 leaves the same `^id` on two lines — a demoted week line and its
/// `month/<m>.md#Demoted` archive copy — so a key that rewrites a line has to
/// say *which* line the user is looking at (see [`reorder`], [`edit_command`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Selection {
    /// The item key (an `^id`, or a title for an id-less line).
    pub id: Id,
    /// The file the row was read from.
    pub file: String,
    /// True when the row is a `# Demoted` archive copy (§6.3).
    pub demoted: bool,
}

/// Screen 2's cursor (§12.2). All of it is display state; nothing is stored.
#[derive(Debug, Clone, Default)]
pub struct QueueState {
    /// The focused pane.
    pub pane: Pane,
    /// Cursor in the Month pane.
    pub month_sel: usize,
    /// Cursor in the Week pane.
    pub week_sel: usize,
    /// Cursor in the Tasks pane.
    pub task_sel: usize,
    /// The last of Month/Week that had focus — whose selection the Tasks pane
    /// follows.
    pub anchor: Pane,
    /// `Enter` drilled into this item; the Tasks pane shows its children until
    /// `Esc`/`Backspace`.
    pub focus: Option<Id>,
}

impl QueueState {
    /// A fresh cursor: the Week pane, first row.
    pub fn new() -> QueueState {
        QueueState {
            pane: Pane::Week,
            anchor: Pane::Week,
            ..QueueState::default()
        }
    }

    /// The item whose children the Tasks pane lists (§12.2's `Tasks @m2`).
    pub fn parent(&self, view: &View<'_>) -> Option<Id> {
        if let Some(id) = &self.focus {
            return Some(id.clone());
        }
        match self.anchor {
            Pane::Month => month_rows(view).get(self.month_sel).map(|r| r.id.clone()),
            _ => week_rows(view).get(self.week_sel).map(|r| r.id.clone()),
        }
    }

    /// The selected line in the focused pane: its key, its file and whether it
    /// is a `# Demoted` archive copy (§6.3).
    pub fn selection(&self, view: &View<'_>) -> Option<Selection> {
        match self.pane {
            Pane::Month => month_rows(view).get(self.month_sel).map(|r| Selection {
                id: r.id.clone(),
                file: r.file.clone(),
                demoted: r.demoted,
            }),
            Pane::Week => week_rows(view).get(self.week_sel).map(|r| Selection {
                id: r.id.clone(),
                file: r.file.clone(),
                demoted: false,
            }),
            Pane::Tasks => {
                let parent = self.parent(view);
                task_rows(view, parent.as_ref())
                    .get(self.task_sel)
                    .map(|r| Selection {
                        id: r.id.clone(),
                        file: r.file.clone(),
                        demoted: false,
                    })
            }
        }
    }

    /// The selected item in the focused pane.
    pub fn selected(&self, view: &View<'_>) -> Option<Id> {
        self.selection(view).map(|s| s.id)
    }

    /// How many rows the focused pane has.
    fn len(&self, view: &View<'_>) -> usize {
        match self.pane {
            Pane::Month => month_rows(view).len(),
            Pane::Week => week_rows(view).len(),
            Pane::Tasks => {
                let parent = self.parent(view);
                task_rows(view, parent.as_ref()).len()
            }
        }
    }

    /// The cursor of the focused pane.
    fn cursor(&mut self) -> &mut usize {
        match self.pane {
            Pane::Month => &mut self.month_sel,
            Pane::Week => &mut self.week_sel,
            Pane::Tasks => &mut self.task_sel,
        }
    }
}

// ---------------------------------------------------------------------------
// Keys (§12.6, the `queue` rows)
// ---------------------------------------------------------------------------

/// §12.6's keymap row for this screen.
pub const KEYMAP: &str = " h/l pane · j/k · J/K reorder (rewrites line order) · Enter drill · a add · \
c ci · E estimate · P priority (roots) · D demote · A readopt · x drop · e edit";

/// The same row for a narrow terminal.
pub const KEYMAP_NARROW: &str = " h/l · j/k · J/K reorder · Enter · a c E P D A x e";

/// Handle one key press (§12.6).
pub fn on_key(state: &mut QueueState, view: &View<'_>, key: KeyEvent) -> Action {
    let sel = state.selection(view);
    match key.code {
        KeyCode::Char('h') | KeyCode::Left => {
            state.pane = state.pane.left();
            if state.pane != Pane::Tasks {
                state.anchor = state.pane;
                state.focus = None;
            }
            Action::Redraw
        }
        KeyCode::Char('l') | KeyCode::Right => {
            state.pane = state.pane.right();
            if state.pane != Pane::Tasks {
                state.anchor = state.pane;
            }
            Action::Redraw
        }
        KeyCode::Char('j') | KeyCode::Down => {
            let len = state.len(view);
            let c = state.cursor();
            if len > 0 && *c + 1 < len {
                *c += 1;
            }
            if state.pane != Pane::Tasks {
                state.focus = None;
                state.task_sel = 0;
            }
            Action::Redraw
        }
        KeyCode::Char('k') | KeyCode::Up => {
            let c = state.cursor();
            *c = c.saturating_sub(1);
            if state.pane != Pane::Tasks {
                state.focus = None;
                state.task_sel = 0;
            }
            Action::Redraw
        }
        KeyCode::Char('J') => reorder_action(sel, 1),
        KeyCode::Char('K') => reorder_action(sel, -1),
        KeyCode::Enter => match sel.map(|s| s.id) {
            Some(id) => {
                if state.pane != Pane::Tasks {
                    state.anchor = state.pane;
                }
                state.focus = Some(id);
                state.pane = Pane::Tasks;
                state.task_sel = 0;
                Action::Redraw
            }
            None => Action::Note("nothing to drill into".to_string()),
        },
        KeyCode::Esc | KeyCode::Backspace => {
            if state.focus.take().is_some() {
                state.pane = state.anchor;
                state.task_sel = 0;
                Action::Redraw
            } else {
                Action::Ignored
            }
        }
        KeyCode::Char('a') => {
            let (file, section) = add_target(state, view);
            Action::Prompt(Prompt::Add { file, section })
        }
        KeyCode::Char('c') => prompt_for(sel, Prompt::Ci),
        KeyCode::Char('E') => prompt_for(sel, Prompt::Estimate),
        KeyCode::Char('P') => match sel {
            Some(s) if view.tree.is_root(&s.id) => Action::Prompt(Prompt::Priority(s.id)),
            Some(s) => Action::Note(format!(
                "{}: !k lives on the root ({}) — §7.1",
                s.id,
                view.tree.root(&s.id)
            )),
            None => Action::Note("nothing selected".to_string()),
        },
        // §6.3: the `# Demoted` row *is* the record of a demotion; demoting it
        // again would move the live line a second time behind the user's back.
        KeyCode::Char('D') => match sel {
            Some(s) if s.demoted => Action::Note(format!(
                "{} is already demoted ({} # Demoted) — A readopts it",
                s.id, s.file
            )),
            other => mutate_for(other, Mutation::Demote),
        },
        KeyCode::Char('A') => mutate_for(sel, Mutation::Readopt),
        KeyCode::Char('x') => mutate_for(sel, Mutation::Drop),
        KeyCode::Char('e') => match sel {
            Some(s) => Action::Edit {
                id: s.id,
                file: Some(s.file),
            },
            None => Action::Note("nothing selected".to_string()),
        },
        _ => Action::Ignored,
    }
}

/// `J`/`K` on the selection: the reorder names the file the row came from, so
/// the line that moves is the one under the cursor (§6.3).
fn reorder_action(sel: Option<Selection>, delta: i32) -> Action {
    match sel {
        Some(s) => Action::Mutate(Mutation::Reorder {
            id: s.id,
            file: Some(s.file),
            delta,
        }),
        None => Action::Note("nothing selected".to_string()),
    }
}

/// `Prompt` on the selection, or a refusal.
fn prompt_for(sel: Option<Selection>, f: impl FnOnce(Id) -> Prompt) -> Action {
    match sel {
        Some(s) => Action::Prompt(f(s.id)),
        None => Action::Note("nothing selected".to_string()),
    }
}

/// `Mutate` on the selection, or a refusal.
fn mutate_for(sel: Option<Selection>, f: impl FnOnce(Id) -> Mutation) -> Action {
    match sel {
        Some(s) => Action::Mutate(f(s.id)),
        None => Action::Note("nothing selected".to_string()),
    }
}

/// Where `a` adds: the focused pane's file, under the selection's section
/// (§6.1 — horizon is the file, §4.2 — the section is rank).
fn add_target(state: &QueueState, view: &View<'_>) -> (String, Option<String>) {
    let (file, id) = match state.pane {
        Pane::Month => (
            tm_core::model::Horizon::Month(view.month()).path(),
            month_rows(view).get(state.month_sel).map(|r| r.id.clone()),
        ),
        Pane::Week => (
            tm_core::model::Horizon::Week(view.week()).path(),
            week_rows(view).get(state.week_sel).map(|r| r.id.clone()),
        ),
        Pane::Tasks => {
            let parent = state.parent(view);
            let rows = task_rows(view, parent.as_ref());
            let id = rows
                .get(state.task_sel)
                .map(|r| r.id.clone())
                .or_else(|| parent.clone());
            let file = id
                .as_ref()
                .and_then(|i| view.tree.get(i))
                .map(|i| i.src.file.clone())
                .unwrap_or_else(|| tm_core::model::Horizon::Week(view.week()).path());
            (file, id)
        }
    };
    let section = id
        .and_then(|i| view.tree.get(&i).cloned())
        .and_then(|i| i.src.section.clone());
    (file, section)
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

/// Draw Screen 2 into `area` (§12.2).
///
/// Wide terminals get the mock's three columns; below `cfg.tui.min_width` the
/// panes stack (§12: "below that, panes stack"). The last line of `area` is the
/// §12.6 keymap row.
pub fn render(state: &QueueState, view: &View<'_>, frame: &mut Frame, area: Rect) {
    if area.height == 0 || area.width == 0 {
        return;
    }
    let narrow = (area.width as u32) < view.cfg.tui.min_width;
    let rows = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Min(3), Constraint::Length(1)])
        .split(area);
    let (body, footer) = (rows[0], rows[1]);

    let panes = if narrow {
        Layout::default()
            .direction(Direction::Vertical)
            .constraints([
                Constraint::Length(8),
                Constraint::Min(5),
                Constraint::Length(7),
            ])
            .split(body)
    } else {
        Layout::default()
            .direction(Direction::Horizontal)
            .constraints([
                Constraint::Percentage(25),
                Constraint::Percentage(45),
                Constraint::Percentage(30),
            ])
            .split(body)
    };

    render_month(state, view, frame, panes[0]);
    render_week(state, view, frame, panes[1], narrow);
    render_tasks(state, view, frame, panes[2]);

    let keymap = if narrow { KEYMAP_NARROW } else { KEYMAP };
    frame.render_widget(
        Paragraph::new(Line::from(Span::styled(
            emit::clip(keymap, footer.width as usize),
            Style::default().fg(Color::DarkGray),
        ))),
        footer,
    );
}

/// The Month pane.
fn render_month(state: &QueueState, view: &View<'_>, frame: &mut Frame, area: Rect) {
    let inner = area.width.saturating_sub(2) as usize;
    let rows = month_rows(view);
    let demoted = rows.iter().filter(|r| r.demoted).count();
    let mut lines: Vec<(Option<usize>, Line<'static>)> = Vec::new();
    let mut header_done = false;
    for (i, r) in rows.iter().enumerate() {
        if r.demoted && !header_done {
            header_done = true;
            lines.push((None, Line::from("")));
            lines.push((
                None,
                Line::from(Span::styled(
                    format!("Demoted ({demoted})"),
                    Style::default().fg(Color::DarkGray),
                )),
            ));
        }
        let text = if r.demoted {
            let head = format!("· {} ", r.id);
            let title_w = inner
                .saturating_sub(emit::display_width(&head) + emit::display_width(&r.stamps) + 1)
                .max(4);
            format!("{head}{} {}", emit::pad_to(&r.title, title_w), r.stamps)
        } else {
            let head = format!(
                "{} {} ",
                r.priority.map(|k| format!("!{k}")).unwrap_or("  ".into()),
                r.id
            );
            let title_w = inner.saturating_sub(emit::display_width(&head) + 4);
            format!("{head}{} {}", emit::pad_to(&r.title, title_w), r.bar)
        };
        lines.push((Some(i), Line::from(text)));
    }
    let title = format!(" Month {} ", view.month());
    render_pane(
        frame,
        area,
        &title,
        lines,
        state.month_sel,
        state.pane == Pane::Month,
        None,
    );
}

/// The Week pane.
fn render_week(state: &QueueState, view: &View<'_>, frame: &mut Frame, area: Rect, narrow: bool) {
    let inner = area.width.saturating_sub(2) as usize;
    let rows = week_rows(view);
    let mut any_hysteresis = false;
    let mut lines: Vec<(Option<usize>, Line<'static>)> = Vec::new();
    for (i, r) in rows.iter().enumerate() {
        any_hysteresis |= r.hysteresis;
        let p = if r.wall {
            "⏰".to_string()
        } else {
            match r.p {
                Some(p) => format!("p{p}{}", if r.hysteresis { "*" } else { "" }),
                None => String::new(),
            }
        };
        let head = format!("{} {} {:>2} {} ", emit::pad_to(&p, 3), r.ci, r.est, r.id);
        let tail = if r.done {
            "✓".to_string()
        } else {
            let mut parts: Vec<String> = Vec::new();
            if !r.due.is_empty() {
                parts.push(r.due.clone());
            }
            if !r.u.is_empty() {
                parts.push(r.u.clone());
            }
            if !r.fits.is_empty() {
                parts.push(r.fits.clone());
            }
            if parts.is_empty() {
                r.bar.clone()
            } else {
                parts.join("  ")
            }
        };
        let parent = &r.parent;
        let used = emit::display_width(&head) + emit::display_width(&tail) + emit::display_width(parent) + 2;
        let title_w = inner.saturating_sub(used).max(4);
        let text = format!(
            "{head}{} {} {}",
            emit::pad_to(&r.title, title_w),
            emit::pad_to(parent, emit::display_width(parent)),
            tail
        );
        lines.push((Some(i), Line::from(emit::clip(&text, inner))));
    }
    let footer = if any_hysteresis {
        Some(Line::from(Span::styled(
            emit::clip("* held by hysteresis (≤ 1 bin better per day, §7.4)", inner),
            Style::default().fg(Color::DarkGray),
        )))
    } else {
        None
    };
    let title = week_title(view, narrow);
    render_pane(
        frame,
        area,
        &title,
        lines,
        state.week_sel,
        state.pane == Pane::Week,
        footer,
    );
}

/// `Week W37 · planned 20 / budget 25` — from the week file's front matter
/// (§4.3), falling back to the §6.4 rollup when it has none.
fn week_title(view: &View<'_>, narrow: bool) -> String {
    let week = view.week();
    if narrow {
        return format!(" Week {} ", week.short());
    }
    let path = tm_core::model::Horizon::Week(week).path();
    let front = |k: &str| {
        view.files
            .file(&path)
            .and_then(|f| f.front(k))
            .map(str::to_string)
    };
    let planned = front("planned").unwrap_or_else(|| {
        let total: u32 = view
            .tree
            .week_items(week)
            .iter()
            .filter(|i| !i.state.is_closed())
            .filter_map(|i| view.tree.remaining(&Tree::key_of(i)))
            .sum();
        blocks_bare(total, view.block_min())
    });
    match front("budget") {
        Some(b) => format!(" Week {} · planned {planned} / budget {b} ", week.short()),
        None => format!(" Week {} · planned {planned} ", week.short()),
    }
}

/// The Tasks pane.
fn render_tasks(state: &QueueState, view: &View<'_>, frame: &mut Frame, area: Rect) {
    let inner = area.width.saturating_sub(2) as usize;
    let parent = state.parent(view);
    let rows = task_rows(view, parent.as_ref());
    let lines: Vec<(Option<usize>, Line<'static>)> = rows
        .iter()
        .enumerate()
        .map(|(i, r)| {
            let head = format!(
                "{} {} {:>2} ",
                r.p.map(|p| format!("p{p}")).unwrap_or("  ".into()),
                r.ci,
                r.est
            );
            let mark = if r.done {
                " ✓".to_string()
            } else {
                r.blocked
                    .as_ref()
                    .map(|b| format!(" {b}"))
                    .unwrap_or_default()
            };
            let title_w = inner.saturating_sub(emit::display_width(&head) + emit::display_width(&mark));
            let line = format!("{head}{}{mark}", emit::pad_to(&r.title, title_w));
            (Some(i), Line::from(emit::clip(&line, inner)))
        })
        .collect();
    let title = match &parent {
        Some(p) => format!(" Tasks @{p} "),
        None => " Tasks ".to_string(),
    };
    let footer = Some(Line::from(Span::styled(
        emit::clip(&fits_footer(view, &rows), inner),
        Style::default().fg(Color::DarkGray),
    )));
    render_pane(
        frame,
        area,
        &title,
        lines,
        state.task_sel,
        state.pane == Pane::Tasks,
        footer,
    );
}

/// Draw one bordered pane with a cursor and an optional last line.
fn render_pane(
    frame: &mut Frame,
    area: Rect,
    title: &str,
    lines: Vec<(Option<usize>, Line<'static>)>,
    sel: usize,
    focused: bool,
    footer: Option<Line<'static>>,
) {
    let block = Block::default()
        .borders(Borders::ALL)
        .title(title.to_string())
        .border_style(if focused {
            Style::default().fg(Color::White)
        } else {
            Style::default().fg(Color::DarkGray)
        });
    let inner = block.inner(area);
    frame.render_widget(block, area);
    if inner.height == 0 {
        return;
    }
    let body_h = inner.height as usize - usize::from(footer.is_some().min(inner.height > 1));
    let cursor_at = lines.iter().position(|(i, _)| *i == Some(sel));
    let offset = match cursor_at {
        Some(pos) if body_h > 0 && pos >= body_h => pos + 1 - body_h,
        _ => 0,
    };
    let mut out: Vec<Line<'static>> = Vec::new();
    for (row, line) in lines.iter().skip(offset).take(body_h) {
        if *row == Some(sel) && focused {
            out.push(line.clone().style(Style::default().add_modifier(Modifier::REVERSED)));
        } else if *row == Some(sel) {
            out.push(line.clone().style(Style::default().add_modifier(Modifier::BOLD)));
        } else {
            out.push(line.clone());
        }
    }
    let body = Rect {
        height: body_h as u16,
        ..inner
    };
    frame.render_widget(Paragraph::new(out), body);
    if let Some(f) = footer {
        if inner.height > 1 {
            let at = Rect {
                y: inner.y + inner.height - 1,
                height: 1,
                ..inner
            };
            frame.render_widget(Paragraph::new(f), at);
        }
    }
}
