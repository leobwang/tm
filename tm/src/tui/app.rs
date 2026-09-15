//! The TUI's state, its keymap and its effects (tm-spec-v1.md §9, §12).
//!
//! # API overview
//!
//! This module is **pure**: it never touches the terminal, the store or the
//! clock. Everything it knows arrives as data, and everything it wants done
//! leaves as an [`Effect`] for [`crate::tui`]'s driver to carry out. That is
//! what makes §17's "`ratatui` `TestBackend` snapshots of each pane" possible
//! from a hand-built [`App`].
//!
//! * [`App`] — one loaded plan directory as the TUI sees it: config, tree,
//!   log and its replay, the learned model, `.tm/state.json`, the current
//!   [`DayPlan`] and the **ghost** plan (§12.1: the plan as it stood at
//!   arrival, built from the [`ArrivalBlock`]s `tm arrive` recorded, never
//!   recomputed), plus the UI state (screen, mode, selection, command line,
//!   pending prompt, hover) and the digests the panes read
//!   ([`App::rows`], [`App::status`], [`App::week`], [`App::energy`]).
//!   [`App::new`] plans from `now`; [`App::with_plan`] takes a plan as given
//!   (tests); [`App::replan`] recomputes it — §9's "one keystroke changes one
//!   fact, `plan()` reruns from `now`".
//! * [`Screen`] — §12's five screens. Screens 2–5 live in their own modules
//!   ([`super::queue`], [`super::necessities`], [`super::review`],
//!   [`super::inbox`]); this module owns the enum, holds each screen's cursor
//!   and hands them §12.6's keys ([`Action::ScreenKey`]), turning what they
//!   ask for into [`Effect`]s.
//! * [`Mode`] — what the next keystroke means: normal, the `b` break-where
//!   chord, the `0` energy report, the `:` command line, a one-line text
//!   input (`n` note, `l` location) or the `?` help overlay.
//! * [`Action`] and [`resolve`] — §12.6's keymap as a pure function of
//!   `(screen, mode, prompt, key)`, so every row of the table is unit
//!   testable.
//! * [`Effect`] — the side effects an action asks for: run a CLI verb (every
//!   action goes through the same code path as the §13 verb), open the
//!   editor, reload, replan, quit.
//! * [`Prompt`] — §9.1's overtime box and §9.2's idle box, with the
//!   consequence lines §9.1 wants computed by re-planning
//!   ([`tm_core::planner::overtime_drops`]).
//!
//! ## Two keys §12.6 assigns twice
//!
//! `k` is both "skip routine" (the today row) and half of "j/k move" (the
//! hint line of §12.1's own mock). Movement wins — losing it would leave the
//! Timeline pane unnavigable — and skipping a routine is `K`.
//!
//! `1`–`5` are both the five screens (global) and the energy report (today).
//! The screens win; the energy report is `0` followed by `0`–`5`, which is
//! also the only way to report a `0`. Both are shown in the hint line and the
//! help overlay.
//!
//! `r` is "replan" (global) and "resume" (today). It resumes when an
//! interruption is open (§9) and replans otherwise.

use std::collections::HashMap;

use chrono::{DateTime, Datelike, Duration, NaiveDate, NaiveTime, Timelike};
use chrono_tz::Tz;
use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

use tm_core::capacity::{self, EnergyCtx, UnitCapacity};
use tm_core::config::Config;
use tm_core::emit;
use tm_core::energy::{self, Model, Posterior};
use tm_core::horizon::MIN_REMAINING_MIN;
use tm_core::log::{Log, Replay};
use tm_core::model::{Id, IsoWeek, Loc, Recur};
use tm_core::planner::{self, DayPlan, PlanInput, PlanOverrides, SegFlags, SegKind, Segment};
use tm_core::priority::{Candidate, Prio, PrioClass};
use tm_core::recur;
use tm_core::review::{self, PlannedBlock, StatusHead, StatusLine};
use tm_core::store::{PlanFiles, RuntimeState};
use tm_core::tree::Tree;

use super::inbox;
use super::necessities;
use super::queue;
use super::review as review_screen;

/// §12's five screens.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Screen {
    /// §12.1 — the day.
    #[default]
    Today,
    /// §12.2 — month, week and task queues.
    Queue,
    /// §12.3 — walls, deadlines, waiting.
    Necessities,
    /// §12.4 — day, week and month reviews.
    Review,
    /// §12.5 — inbox and capture.
    Inbox,
}

impl Screen {
    /// Every screen, in `1`–`5` order.
    pub const ALL: [Screen; 5] = [
        Screen::Today,
        Screen::Queue,
        Screen::Necessities,
        Screen::Review,
        Screen::Inbox,
    ];

    /// The screen a `1`–`5` keystroke selects.
    pub fn from_digit(c: char) -> Option<Screen> {
        let n = c.to_digit(10)? as usize;
        (1..=5).contains(&n).then(|| Screen::ALL[n - 1])
    }

    /// Its `1`–`5` number.
    pub fn number(self) -> u8 {
        Screen::ALL.iter().position(|s| *s == self).unwrap_or(0) as u8 + 1
    }

    /// Its title, for the tab strip and the help overlay.
    pub fn title(self) -> &'static str {
        match self {
            Screen::Today => "Today",
            Screen::Queue => "Queue",
            Screen::Necessities => "Necessities",
            Screen::Review => "Review",
            Screen::Inbox => "Inbox",
        }
    }
}

/// What the next keystroke means.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum Mode {
    /// The keymap of §12.6.
    #[default]
    Normal,
    /// `b` was pressed: `w`/`s`/`b`/`p` picks where the break is taken.
    BreakWhere,
    /// `0` was pressed: `0`–`5` reports energy (§8.5).
    Energy,
    /// `:` was pressed: any §13 verb can be typed.
    Command,
    /// A one-line text input.
    Input(InputKind),
    /// `?` — the help overlay.
    Help,
}

/// What a [`Mode::Input`] is collecting.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputKind {
    /// `n` — a note for the day file's `## Log` and the §10.1 `note` event.
    Note,
    /// `l` — the current location (§9: `runtime.loc`, §16's `home_max_ci`).
    Location,
    /// A value one of §12.6's screen keys asked for: `a` add, `c` ci, `E`
    /// estimate, `P` priority (§12.2).
    Screen(queue::Prompt),
}

impl InputKind {
    /// The prompt shown in front of the input.
    pub fn label(&self) -> &'static str {
        match self {
            InputKind::Note => "note",
            InputKind::Location => "location",
            InputKind::Screen(queue::Prompt::Add { .. }) => "add",
            InputKind::Screen(queue::Prompt::Ci(_)) => "ci 0-5",
            InputKind::Screen(queue::Prompt::Estimate(_)) => "est",
            InputKind::Screen(queue::Prompt::Priority(_)) => "!k",
        }
    }
}

/// Where a break was taken (§12.6's `b` + `w`/`s`/`b`/`p`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BreakPlace {
    /// `w` — a walk.
    Walk,
    /// `s` — stayed in the seat.
    Seat,
    /// `b` — lay down.
    Bed,
    /// `p` — the phone.
    Phone,
}

impl BreakPlace {
    /// The `--where` value (§13 `tm break --where walk`).
    pub fn as_str(self) -> &'static str {
        match self {
            BreakPlace::Walk => "walk",
            BreakPlace::Seat => "seat",
            BreakPlace::Bed => "bed",
            BreakPlace::Phone => "phone",
        }
    }

    /// The key that picks it.
    pub fn from_key(c: char) -> Option<BreakPlace> {
        match c {
            'w' => Some(BreakPlace::Walk),
            's' => Some(BreakPlace::Seat),
            'b' => Some(BreakPlace::Bed),
            'p' => Some(BreakPlace::Phone),
            _ => None,
        }
    }
}

/// An answer to the pending prompt (§9.1, §9.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Answer {
    /// Overtime `x` — extend by one block.
    Extend,
    /// Overtime `s` — stop, the remainder re-competes.
    Stop,
    /// Overtime `d` — done.
    Done,
    /// Overtime, any other key — ask again in `overtime_reprompt_min`.
    Later,
    /// Idle `w` — start the next block.
    Work,
    /// Idle `b` — it was a break.
    Break,
    /// Idle `t` — it was a routine.
    Routine,
    /// Idle `i` — it was an interruption.
    Interrupt,
    /// Idle `l` — a leak, logged as Lost.
    Leak,
}

/// One row of §12.6's keymap.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Action {
    /// The key means nothing here.
    None,
    /// `1`–`5`.
    Screen(Screen),
    /// `?`.
    Help,
    /// `:`.
    CommandLine,
    /// `q`.
    Quit,
    /// `e` — open the selected line in `cfg.tui.editor`.
    Edit,
    /// `r` outside the Today screen — replan.
    Replan,
    /// `r` on the Today screen — resume when interrupted, else replan.
    ReplanOrResume,
    /// `R` — sync the calendar, then replan.
    Sync,
    /// `d`.
    Done,
    /// `x`.
    Extend,
    /// `s`.
    Stop,
    /// `b` — ask where.
    Break,
    /// `w`/`s`/`b`/`p` after `b`.
    BreakWhere(BreakPlace),
    /// `i`.
    Interrupt,
    /// `0` — start an energy report.
    EnergyPrompt,
    /// `0`–`5` answering it (§8.5's posterior).
    Energy(u8),
    /// `l`.
    Location,
    /// `K` — skip today's instance of the selected routine.
    SkipRoutine,
    /// `n`.
    Note,
    /// `Space` — pause or unpause the timer.
    Pause,
    /// `j` / `Down`.
    SelectNext,
    /// `k` / `Up`.
    SelectPrev,
    /// `Enter` — drill into the selection (§12.2's Queue).
    Open,
    /// `Esc` — leave the mode, close the overlay.
    Cancel,
    /// `Enter` in the command line or a text input.
    Submit,
    /// A character typed into the command line or a text input.
    Input(char),
    /// `Backspace`.
    Backspace,
    /// An answer to the pending prompt (§9.1, §9.2).
    Answer(Answer),
    /// A key for the screen in front of the Today screen: §12.6's `queue`
    /// row (`h l j k J K Enter`, `a c E P D A x`), its `necessities` row
    /// (`E t k e`), §12.4's `h l j k w c` and §12.5's capture line.
    ///
    /// The screen modules own those keys and their state, so the key itself
    /// travels and [`App::apply`] hands it to the module. A key the module
    /// does not want comes back as [`queue::Action::Ignored`] and falls
    /// through to the global row.
    ScreenKey(KeyEvent),
}

/// A side effect the driver performs (§12: "every action goes through the
/// same code path the CLI verbs use").
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Effect {
    /// Run a §13 verb, e.g. `["done"]`, `["energy", "4"]`.
    Verb(Vec<String>),
    /// Open a file at a line in `cfg.tui.editor` (§12).
    Editor {
        /// The file, relative to the plan root.
        file: String,
        /// The 1-based line.
        line: usize,
    },
    /// Append a §10.1 `note` event and a `## Log` line (§12.6's `n`).
    Note(String),
    /// Set `runtime.loc` (§9's location change, §12.6's `l`).
    SetLocation(String),
    /// A §12.2/§12.5 file change the shell performs directly: `J`/`K`'s
    /// byte-faithful reorder ([`queue::apply_reorder`]) and the `inbox.md`
    /// line a triaged capture consumes.
    Mutate(Box<queue::Mutation>),
    /// Leave the TUI.
    Quit,
}

/// §9.1's overtime prompt.
#[derive(Clone, Debug, PartialEq)]
pub struct Overtime {
    /// The running item.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// The estimate as written (`2b`).
    pub est: String,
    /// The duration multiplier (§8.5).
    pub multiplier: Option<f64>,
    /// `est × multiplier` in minutes — when the prompt fires.
    pub planned_min: u32,
    /// Minutes since the block started.
    pub elapsed_min: u32,
    /// What "extend +1 block" would drop, as `title (pN)` (§9.1).
    pub drops: Vec<String>,
    /// What "stop" would leave in the queue, in blocks (`0.5b`).
    pub stays: String,
    /// Minutes until the next prompt (`cfg.day.overtime_reprompt_min`).
    pub reprompt_min: u32,
}

/// §9.2's idle prompt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Idle {
    /// How long nothing has been running.
    pub minutes: u32,
}

/// Which prompt is open.
#[derive(Clone, Debug, PartialEq)]
pub enum Prompt {
    /// §9.1.
    Overtime(Overtime),
    /// §9.2.
    Idle(Idle),
}

/// The prompt kind, for [`resolve`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PromptKind {
    /// §9.1.
    Overtime,
    /// §9.2.
    Idle,
}

impl Prompt {
    /// Its kind.
    pub fn kind(&self) -> PromptKind {
        match self {
            Prompt::Overtime(_) => PromptKind::Overtime,
            Prompt::Idle(_) => PromptKind::Idle,
        }
    }
}

/// One rendered timeline row and the segment it came from.
#[derive(Clone, Debug, PartialEq)]
pub struct TimelineRow {
    /// The row as [`tm_core::emit::render_plan_section`] wrote it.
    pub text: String,
    /// Index into [`DayPlan::segments`]; `None` for the `─── window ends`
    /// divider, which belongs to no segment.
    pub segment: Option<usize>,
}

/// What the day bar is hovering over (§12.1's tooltip).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hover {
    /// The column under the pointer.
    pub col: usize,
    /// `title · duration · ci · p · @root`.
    pub text: String,
}

/// One milestone row of the Week pane (§12.1).
#[derive(Clone, Debug, PartialEq)]
pub struct Milestone {
    /// The item.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// Minutes logged against it and its descendants.
    pub done_min: u32,
    /// Its estimate (§6.4's `planned_minutes`).
    pub planned_min: u32,
    /// Already finished.
    pub done: bool,
    /// `p = 0` in today's plan (§7.2).
    pub hot: bool,
}

/// One HOT / overdue row of the Week pane.
#[derive(Clone, Debug, PartialEq)]
pub struct HotRow {
    /// The item.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// Why it is here: `overdue`, `due today`, `u=1.2`…
    pub note: String,
}

/// One Waiting row of the Week pane (§11's waiting monitor).
#[derive(Clone, Debug, PartialEq)]
pub struct WaitRow {
    /// The item.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// `2d / 7d` — days waited over the timeout.
    pub note: String,
}

/// The Week pane's data (§12.1's right column).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct WeekPane {
    /// The ISO week.
    pub week: Option<IsoWeek>,
    /// Blocks logged this week.
    pub done_blocks: u32,
    /// Blocks the week's milestones add up to.
    pub planned_blocks: u32,
    /// The milestones, in line order.
    pub milestones: Vec<Milestone>,
    /// `p = 0` items (§7.2).
    pub hot: Vec<HotRow>,
    /// `[?]` items (§5.1).
    pub waiting: Vec<WaitRow>,
    /// [`tm_core::emit::render_diagnostics`].
    pub diagnostics: Vec<String>,
}

/// The Energy pane's two rows (§12.1: "pred … rep … `·` = not asked").
#[derive(Clone, Debug, Default, PartialEq)]
pub struct EnergyPane {
    /// The hours covered, 0..=23.
    pub hours: Vec<u32>,
    /// Predicted energy per hour (§8.5).
    pub pred: Vec<u8>,
    /// Reported energy per hour; `None` when you were not asked.
    pub rep: Vec<Option<u8>>,
}

/// One block start of `.tm/arrival_plan.json` — the record `tm arrive`
/// writes of the plan the day started with (§12.1's ghost row, and §11's
/// adherence denominator).
///
/// The record holds a start and an item per block and nothing else, which is
/// why the ghost blocks are sized from the tree when the row is built
/// ([`crate::cli::ghost`], which both frontends draw their ghost with).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArrivalBlock {
    /// When the block was planned to start (local, on `state.date`).
    pub start: NaiveTime,
    /// The item it was for; `None` for a block the record has no id for.
    pub id: Option<Id>,
}

/// Everything [`App::new`] needs that comes from the plan directory.
pub struct AppData {
    /// `config.toml` (§16).
    pub cfg: Config,
    /// `.tm/model.json` (§8.5).
    pub model: Model,
    /// `.tm/state.json` (§10.2).
    pub state: RuntimeState,
    /// The parsed tree (§6).
    pub tree: Tree,
    /// `.tm/log.jsonl` (§10.1).
    pub log: Log,
    /// Its replay.
    pub replay: Replay,
    /// `.tm/arrival_plan.json` — the block starts as `tm arrive` recorded
    /// them (§12.1's ghost row). Empty when the day has no record yet.
    pub arrival: Vec<ArrivalBlock>,
    /// The parsed files behind the tree — §12.2's Queue reads front matter
    /// and `inbox.md`'s raw lines through them.
    pub files: PlanFiles,
    /// Today's candidates (§6.2), in `priority::collect_candidates` order.
    pub candidates: Vec<Candidate>,
    /// Their priorities (§7), 1:1 with `candidates`.
    pub prios: Vec<Prio>,
    /// The §8.4 lookahead the EDF pass ran on: the kernel's first days, in
    /// exact units (stage 5 D10 L8).
    pub caps: Vec<UnitCapacity>,
    /// The instant the TUI is at, in `cfg.tz`.
    pub now: DateTime<Tz>,
}

/// The whole TUI state.
pub struct App {
    /// §16.
    pub cfg: Config,
    /// §8.5.
    pub model: Model,
    /// §10.2.
    pub state: RuntimeState,
    /// §6.
    pub tree: Tree,
    /// §10.1.
    pub log: Log,
    /// The replay of the log.
    pub replay: Replay,
    /// The plan as `tm arrive` recorded it (`.tm/arrival_plan.json`).
    pub arrival: Vec<ArrivalBlock>,
    /// The parsed files (§12.2's Queue and §12.5's Inbox read them).
    pub files: PlanFiles,
    /// Today's candidates (§6.2).
    pub candidates: Vec<Candidate>,
    /// Their priorities (§7).
    pub prios: Vec<Prio>,
    /// The §8.4 lookahead: the kernel's first days, in exact units.
    pub caps: Vec<UnitCapacity>,
    /// Today's energy reports as §8.5's posterior correction.
    pub posterior: Posterior,
    /// `now`, in `cfg.tz` (§17.2: injected, never read from a clock here).
    pub now: DateTime<Tz>,
    /// The local date.
    pub today: NaiveDate,
    /// Today's plan (§8).
    pub plan: DayPlan,
    /// The plan as it stood at arrival — §12.1's ghost row.
    pub ghost: Option<DayPlan>,
    /// The timeline rows (§4.3's format, from `emit`).
    pub rows: Vec<TimelineRow>,
    /// §11's status line.
    pub status: StatusLine,
    /// The non-monitor half of §12.1's first line.
    pub head: StatusHead,
    /// The Week pane.
    pub week: WeekPane,
    /// The Energy pane.
    pub energy: EnergyPane,
    /// The current screen.
    pub screen: Screen,
    /// What the next keystroke means.
    pub mode: Mode,
    /// The selected timeline row.
    pub selection: usize,
    /// The item the selection names, for the Queue screen to pick up.
    pub selected_item: Option<Id>,
    /// The command line / text input buffer.
    pub input: String,
    /// The last message, shown in the hint line.
    pub message: Option<String>,
    /// The day-bar tooltip (§12.1's hover).
    pub hover: Option<Hover>,
    /// Screen 2's cursor (§12.2).
    pub queue: queue::QueueState,
    /// Screen 3's cursor (§12.3).
    pub necessities: necessities::NecessitiesState,
    /// Screen 4's cursor (§12.4).
    pub review: review_screen::ReviewState,
    /// Screen 5's capture buffer (§12.5).
    pub capture: inbox::CaptureState,
    /// The open prompt (§9.1, §9.2).
    pub prompt: Option<Prompt>,
    /// When the overtime prompt was last raised or answered — §9.1's own
    /// re-prompt clock ("then every `overtime_reprompt_min`").
    pub overtime_at: Option<DateTime<Tz>>,
    /// When the idle prompt was last raised or answered — §9.2's clock. It is
    /// deliberately separate from [`App::overtime_at`]: answering one prompt
    /// must not silence the other.
    pub idle_at: Option<DateTime<Tz>>,
    /// Set once `q` has been pressed.
    pub quit: bool,
}

impl App {
    /// Build the TUI state and plan today from `now` (§8).
    pub fn new(data: AppData) -> App {
        let today = data.now.date_naive();
        let window = (data.now, data.now);
        let mut app = App::with_plan(data, DayPlan::empty(today, window, 0), None);
        app.replan();
        app
    }

    /// Build the TUI state around a plan that is given, not computed — the
    /// constructor the snapshot tests use (§17 M6: "a hand-built `DayPlan`").
    pub fn with_plan(data: AppData, plan: DayPlan, ghost: Option<DayPlan>) -> App {
        let mut app = App::bare(data);
        app.plan = plan;
        app.ghost = ghost;
        app.refresh();
        app
    }

    /// The common half of the two constructors: no plan, no digests.
    fn bare(data: AppData) -> App {
        let today = data.now.date_naive();
        let window = (data.now, data.now);
        let obs: Vec<_> = data.replay.energy_on(today).cloned().collect();
        let posterior = Posterior::from_observations(&obs, data.cfg.tz, &data.cfg);
        let status = review::status_line(&data.replay, &data.cfg, &data.state, &[]);
        App {
            cfg: data.cfg,
            model: data.model,
            state: data.state,
            tree: data.tree,
            log: data.log,
            replay: data.replay,
            arrival: data.arrival,
            files: data.files,
            candidates: data.candidates,
            prios: data.prios,
            caps: data.caps,
            posterior,
            now: data.now,
            today,
            plan: DayPlan::empty(today, window, 0),
            ghost: None,
            rows: Vec::new(),
            status,
            head: StatusHead {
                date: today,
                now: data.now.time(),
                loc: None,
                wake: None,
                slept_min: None,
                pred: None,
                rep: None,
            },
            week: WeekPane::default(),
            energy: EnergyPane::default(),
            screen: Screen::Today,
            queue: queue::QueueState::new(),
            necessities: necessities::NecessitiesState::new(),
            review: review_screen::ReviewState::new(),
            capture: inbox::CaptureState::new(),
            mode: Mode::Normal,
            selection: 0,
            selected_item: None,
            input: String::new(),
            message: None,
            hover: None,
            prompt: None,
            overtime_at: None,
            idle_at: None,
            quit: false,
        }
    }

    // -----------------------------------------------------------------
    // Planning (§8) — pure, so a replan is just data
    // -----------------------------------------------------------------

    /// The planner's input for `now`, ranked by the kernel's priorities and
    /// lookahead of the last load (stage 5 D10 L8, gap 111: the planner reads
    /// no walls of its own and runs no pass of its own; a file change or a verb
    /// reloads them).
    fn input(&self) -> PlanInput<'_> {
        PlanInput::new(
            &self.tree,
            &self.log,
            &self.replay,
            &self.cfg,
            &self.model,
            &self.state,
            self.now,
        )
        .with_caps(&self.caps)
        .with_ranking(&self.candidates, &self.prios)
    }

    /// §9: recompute the plan from `now` and refresh every digest.
    pub fn replan(&mut self) {
        let plan = planner::plan(&self.input());
        self.plan = plan;
        self.ghost = self.arrival_plan();
        self.refresh();
    }

    /// The plan as it stood at arrival (§12.1's ghost row), read back from
    /// the record `tm arrive` wrote (`.tm/arrival_plan.json`, [`AppData`]),
    /// **not** recomputed: a `plan()` re-run at `state.arrival` would be run
    /// with today's runtime state and today's log, so the running block would
    /// be reserved at the arrival instant and everything closed since would be
    /// missing — that is not "the plan as it stood at arrival".
    ///
    /// The record keeps a start and an item per block and nothing else, so the
    /// ghost blocks are sized here: `est × multiplier` as §8.5 sizes a block,
    /// clipped at the next recorded start. The minutes between two blocks —
    /// the breaks, routines and walls the record does not name — stay empty in
    /// the ghost row rather than being painted as work.
    ///
    /// `None` when the day has no record: without an arrival there is no plan
    /// the day started with, and [`daybar`](super::daybar) draws the placeholder row.
    fn arrival_plan(&self) -> Option<DayPlan> {
        if self.arrival.is_empty() {
            return None;
        }
        let starts: Vec<DateTime<Tz>> = self
            .arrival
            .iter()
            .map(|b| self.local(b.start))
            .collect();
        let window = self.arrival_window();
        let mut segments: Vec<Segment> = Vec::new();
        for (i, block) in self.arrival.iter().enumerate() {
            let start = starts[i];
            let planned = self.ghost_block_min(block.id.as_ref());
            let mut end = start + Duration::minutes(i64::from(planned));
            if let Some(next) = starts.get(i + 1) {
                end = end.min(*next);
            }
            if end <= start {
                continue;
            }
            segments.push(Segment {
                start,
                end,
                kind: SegKind::Block,
                energy: block
                    .id
                    .as_ref()
                    .and_then(|id| self.tree.get(id))
                    .map(|i| i.ci),
                item: block.id.clone(),
                instance: None,
                flags: SegFlags {
                    ghost: true,
                    planned_min: Some(planned),
                    ..SegFlags::default()
                },
            });
        }
        Some(DayPlan {
            date: self.state.date.unwrap_or(self.today),
            window,
            budget_blocks: self.state.budget.unwrap_or(self.plan.budget_blocks),
            segments,
            diagnostics: Default::default(),
            priorities: Vec::new(),
        })
    }

    /// The window the ghost row spans: the one arrival computed (§8.1), else
    /// today's.
    fn arrival_window(&self) -> (DateTime<Tz>, DateTime<Tz>) {
        match self.state.window {
            Some((from, to)) => (self.local(from), self.local(to)),
            None => self.plan.window,
        }
    }

    /// How long a ghost block ran for: `est × multiplier`, the way §8.5 sizes
    /// a block, falling back to one block.
    fn ghost_block_min(&self, id: Option<&Id>) -> u32 {
        let block_min = self.cfg.block_min();
        let Some(id) = id else {
            return block_min;
        };
        let Some(item) = self.tree.get(id) else {
            return block_min;
        };
        let est = self
            .tree
            .planned_minutes(id)
            .or_else(|| self.tree.remaining(id))
            .filter(|m| *m > 0)
            .unwrap_or(block_min);
        let multiplier =
            energy::duration_multiplier(&self.model, item.ci, &self.tree.tags_effective(id));
        energy::planned_minutes(est, multiplier).max(MIN_REMAINING_MIN)
    }

    /// A local time on the day the runtime state describes (§10.2: `date`
    /// names the day `arrival`, `window` and `active.started` belong to).
    fn local(&self, t: NaiveTime) -> DateTime<Tz> {
        capacity::local_dt(self.cfg.tz, self.state.date.unwrap_or(self.today), t)
    }

    /// The `PlannedBlock`s the day started with — §11's adherence denominator,
    /// straight from the arrival record.
    fn arrival_blocks(&self) -> Vec<PlannedBlock> {
        self.arrival
            .iter()
            .filter_map(|b| Some(PlannedBlock::new(b.id.clone()?, self.local(b.start))))
            .collect()
    }

    // -----------------------------------------------------------------
    // Digests the panes read
    // -----------------------------------------------------------------

    /// Recompute every derived pane from the plan and the log.
    pub fn refresh(&mut self) {
        let obs: Vec<_> = self.replay.energy_on(self.today).cloned().collect();
        self.posterior = Posterior::from_observations(&obs, self.cfg.tz, &self.cfg);
        self.rows = self.timeline_rows(emit::Layout::default().title_w);
        self.status = review::status_line(
            &self.replay,
            &self.cfg,
            &self.state,
            &self.arrival_blocks(),
        );
        self.head = self.status_head();
        self.week = self.week_pane();
        self.energy = self.energy_pane();
        let len = self.rows.len();
        if self.selection >= len {
            self.selection = len.saturating_sub(1);
        }
        self.selected_item = self.selection_item();
    }

    /// The timeline rows at a given title width (§4.3's row format, straight
    /// from `emit`; the pane re-renders at its own width).
    ///
    /// `emit` writes one row per segment, in segment order, plus at most one
    /// `───` divider row, so the rows are matched to segments by position: the
    /// divider is the single extra row, and it is the only row that carries
    /// `───` in place of the `ci` column ([`emit::TIME_W`] plus two spaces in).
    /// Searching the whole row for `───` would also match a segment whose
    /// *title* or note contains that glyph and would then shift every
    /// following row onto the wrong segment.
    pub fn timeline_rows(&self, title_w: usize) -> Vec<TimelineRow> {
        let layout = emit::Layout::new(title_w);
        let (_, body) =
            emit::render_plan_section_with(&self.plan, &self.tree, &self.cfg, self.now, &layout);
        let lines: Vec<&str> = body.lines().collect();
        let divider = (lines.len() == self.plan.segments.len() + 1)
            .then(|| lines.iter().position(|l| is_divider_row(l)))
            .flatten();
        let mut seg = 0usize;
        lines
            .iter()
            .enumerate()
            .map(|(i, line)| {
                if divider == Some(i) {
                    return TimelineRow {
                        text: (*line).to_string(),
                        segment: None,
                    };
                }
                let idx = seg;
                seg += 1;
                TimelineRow {
                    text: (*line).to_string(),
                    segment: (idx < self.plan.segments.len()).then_some(idx),
                }
            })
            .collect()
    }

    /// §12.1's first line, minus the monitors.
    fn status_head(&self) -> StatusHead {
        let day = self.replay.day(self.today);
        let last = self.replay.energy_on(self.today).last();
        StatusHead {
            date: self.today,
            now: self.now.time(),
            loc: self
                .state
                .loc
                .clone()
                .or_else(|| day.and_then(|d| d.loc.clone())),
            wake: self.state.wake.or_else(|| {
                day.and_then(|d| d.wake.map(|w| w.with_timezone(&self.cfg.tz).time()))
            }),
            slept_min: day.and_then(|d| d.slept_min),
            pred: Some(self.predicted_energy(self.now)),
            rep: last.map(|o| o.rep),
        }
    }

    /// Today's wake instant: `state.wake`, else the expected arrival for the
    /// weekday (§16's `[expected]`).
    pub fn wake(&self) -> DateTime<Tz> {
        let t = self
            .state
            .wake
            .unwrap_or_else(|| *self.cfg.expected.arrival.get(self.today.weekday()));
        capacity::local_dt(self.cfg.tz, self.today, t)
    }

    /// The current location (§8.2 step 3's `runtime.loc`).
    pub fn loc(&self) -> Loc {
        self.state
            .loc
            .as_deref()
            .and_then(|s| Loc::parse(s).ok())
            .unwrap_or(Loc::Lounge)
    }

    /// An [`EnergyCtx`] over today (§8.5's prior plus today's posterior).
    fn energy_ctx(&self) -> EnergyCtx<'_> {
        EnergyCtx::new(
            &self.model,
            &self.cfg,
            &self.posterior,
            self.wake(),
            self.loc(),
        )
            .with_slept(self.replay.day(self.today).and_then(|d| d.slept_min))
            .with_blocks_done(self.replay.blocks_done(self.today))
    }

    /// Predicted energy at an instant (§8.5).
    pub fn predicted_energy(&self, at: DateTime<Tz>) -> u8 {
        let blocks = self.replay.blocks_done(self.today);
        self.energy_ctx().energy_at(at, blocks, 0)
    }

    /// §12.1's energy pane: one column per hour of the window.
    fn energy_pane(&self) -> EnergyPane {
        let (from, to) = (self.plan.window.0, self.plan.window.1);
        let first = from.hour();
        let last = to.hour().max(first);
        let ctx = self.energy_ctx();
        let blocks = self.replay.blocks_done(self.today);
        let mut reps: HashMap<u32, u8> = HashMap::new();
        for o in self.replay.energy_on(self.today) {
            reps.insert(o.t.with_timezone(&self.cfg.tz).hour(), o.rep);
        }
        let mut pane = EnergyPane::default();
        for hour in first..=last {
            let Some(time) = NaiveTime::from_hms_opt(hour, 0, 0) else {
                continue;
            };
            let at = capacity::local_dt(self.cfg.tz, self.today, time);
            pane.hours.push(hour);
            pane.pred.push(ctx.energy_at(at, blocks, 0));
            pane.rep.push(reps.get(&hour).copied());
        }
        pane
    }

    /// §12.1's week pane: milestones, HOT/overdue, waiting, diagnostics.
    fn week_pane(&self) -> WeekPane {
        let week = IsoWeek::from_date(self.today);
        let done_by_item = self.replay.done_minutes_map();
        let items = self.tree.week_items(week);
        let own: Vec<Id> = items.iter().map(|i| Tree::key_of(i)).collect();
        let hot_ids: Vec<&Id> = self
            .plan
            .priorities
            .iter()
            .filter(|(_, p)| p.p == 0)
            .map(|(id, _)| id)
            .collect();
        let milestones = items
            .iter()
            .filter(|item| {
                let id = Tree::key_of(item);
                // A child of another line in the same week file is a task.
                self.tree
                    .parent(&id)
                    .is_none_or(|p| !own.contains(p))
            })
            .map(|item| {
                let id = Tree::key_of(item);
                Milestone {
                    done_min: self.tree.done_minutes(&id, &done_by_item),
                    planned_min: self.tree.planned_minutes(&id).unwrap_or(0),
                    done: item.state.is_closed(),
                    hot: hot_ids.contains(&&id),
                    title: item.title.clone(),
                    id,
                }
            })
            .collect::<Vec<_>>();

        let mut seen: Vec<Id> = Vec::new();
        let mut hot = Vec::new();
        for (id, prio) in &self.plan.priorities {
            if prio.p != 0 || seen.contains(id) {
                continue;
            }
            seen.push(id.clone());
            let note = match &prio.class {
                PrioClass::Overdue => "overdue".to_string(),
                PrioClass::Mandatory => "due today".to_string(),
                PrioClass::HotFlag => "hot".to_string(),
                PrioClass::Impossible => format!(
                    "impossible · short {}",
                    review::fmt_blocks_min(prio.shortfall_min, self.cfg.block_min())
                ),
                _ => match prio.u {
                    Some(u) if u.is_finite() => format!("u={u:.2}"),
                    Some(_) => "u=∞".to_string(),
                    None => prio.class.label().to_string(),
                },
            };
            hot.push(HotRow {
                title: self.title_of(id),
                id: id.clone(),
                note,
            });
        }

        let waiting = self
            .tree
            .waiting_ids()
            .into_iter()
            .filter_map(|id| {
                let item = self.tree.get(&id)?;
                let state = recur::waiting_state(item, &self.replay, self.today, &self.cfg)?;
                let timeout = match &item.recur {
                    Recur::OnEvent {
                        timeout: Some(d), ..
                    } => format!(" / {d}"),
                    _ => String::new(),
                };
                Some(WaitRow {
                    id: id.clone(),
                    title: item.title.clone(),
                    note: format!("{}d{timeout}", state.days_waiting.max(0)),
                })
            })
            .collect();

        WeekPane {
            week: Some(week),
            done_blocks: self.week_blocks_done(week),
            planned_blocks: milestones
                .iter()
                .map(|m| m.planned_min)
                .sum::<u32>()
                .div_ceil(self.cfg.block_min().max(1)),
            milestones,
            hot,
            waiting,
            diagnostics: emit::render_diagnostics(&self.plan.diagnostics, &self.tree, &self.cfg),
        }
    }

    /// Blocks logged over the ISO week (§12.1's `Week W37 · 8/20`).
    fn week_blocks_done(&self, week: IsoWeek) -> u32 {
        week.dates()
            .into_iter()
            .map(|d| self.replay.blocks_done(d))
            .sum()
    }

    /// An item's title, or its id when the tree does not have it.
    pub fn title_of(&self, id: &Id) -> String {
        self.tree
            .get(id)
            .map(|i| i.title.clone())
            .unwrap_or_else(|| id.to_string())
    }

    /// `p` for an item in today's plan (§7).
    pub fn priority_of(&self, id: &Id) -> Option<u8> {
        self.plan
            .priorities
            .iter()
            .find(|(k, _)| k == id)
            .map(|(_, p)| p.p)
    }

    // -----------------------------------------------------------------
    // Selection
    // -----------------------------------------------------------------

    /// The segment the selected row belongs to.
    pub fn selected_segment(&self) -> Option<usize> {
        self.rows.get(self.selection).and_then(|r| r.segment)
    }

    /// The item the selection names.
    fn selection_item(&self) -> Option<Id> {
        let seg = self.selected_segment()?;
        self.plan.segments.get(seg).and_then(|s| s.item.clone())
    }

    /// Move the selection, clamped to the rows.
    pub fn select(&mut self, delta: isize) {
        if self.rows.is_empty() {
            return;
        }
        let last = self.rows.len() - 1;
        let next = (self.selection as isize + delta).clamp(0, last as isize) as usize;
        self.selection = next;
        self.selected_item = self.selection_item();
    }

    /// Put the selection on the row that shows `segment` (the day bar's
    /// `Down(Left)`, §17.2).
    pub fn select_segment(&mut self, segment: usize) {
        if let Some(i) = self.rows.iter().position(|r| r.segment == Some(segment)) {
            self.selection = i;
            self.selected_item = self.selection_item();
        }
    }

    /// The file and 1-based line of the selected item, for `e` (§12).
    pub fn selected_location(&self) -> Option<(String, usize)> {
        let id = self.selected_item.clone()?;
        let item = self.tree.get(&id)?;
        Some((item.src.file.clone(), item.src.line))
    }

    // -----------------------------------------------------------------
    // §9's prompts
    // -----------------------------------------------------------------

    /// Replace the plan-directory half of the state after a write or a file
    /// change, keeping the UI half (screen, mode, selection), then replan.
    pub fn adopt(&mut self, data: AppData) {
        self.cfg = data.cfg;
        self.model = data.model;
        self.state = data.state;
        self.tree = data.tree;
        self.log = data.log;
        self.replay = data.replay;
        self.arrival = data.arrival;
        self.files = data.files;
        self.candidates = data.candidates;
        self.prios = data.prios;
        self.caps = data.caps;
        self.now = data.now;
        self.today = data.now.date_naive();
        self.replan();
    }

    /// Advance to `now`: replan when the minute has moved on (the timeline is
    /// written to the minute) and raise §9's prompts.
    ///
    /// Returns whether anything changed, so the driver can skip a redraw.
    pub fn tick(&mut self, now: DateTime<Tz>) -> bool {
        let moved = now.timestamp().div_euclid(60) != self.now.timestamp().div_euclid(60);
        self.now = now;
        self.today = now.date_naive();
        if moved {
            self.replan();
        }
        self.raise_prompt() || moved
    }

    /// Raise the overtime or idle prompt when it is due (§9.1, §9.2).
    ///
    /// Never while the `:` command line or a one-line input is open: the
    /// prompt would capture the next character typed and run it as an answer
    /// (`s` in `start …` would stop the block). The prompt is not lost — it is
    /// raised on the next tick after `Enter` or `Esc`.
    pub fn raise_prompt(&mut self) -> bool {
        if self.prompt.is_some() || matches!(self.mode, Mode::Command | Mode::Input(_)) {
            return false;
        }
        if let Some(over) = self.overtime_due() {
            self.prompt = Some(Prompt::Overtime(over));
            self.overtime_at = Some(self.now);
            return true;
        }
        if let Some(idle) = self.idle_due() {
            self.prompt = Some(Prompt::Idle(idle));
            self.idle_at = Some(self.now);
            return true;
        }
        false
    }

    /// Minutes the running block has been **worked** — what §9.1's `est × r`
    /// is measured against.
    ///
    /// The log knows it exactly: [`tm_core::log::OpenBlock::worked_min_at`]
    /// excludes the pauses, breaks and interruptions that stop the timer
    /// (§12.6's `Space`, §9's `b` and `i`), which is also what
    /// `planner::active_run` sizes the remaining block from. The clock is only
    /// the fallback for a state whose block the log has no record of, and it
    /// counts from `state.date` — `active.started` is a bare `HH:MM` and the
    /// block may have started before midnight (§10.2).
    pub fn active_elapsed_min(&self) -> Option<u32> {
        let active = self.state.active.as_ref()?;
        if let Some(open) = self
            .replay
            .open_block
            .as_ref()
            .filter(|b| b.id == active.id.as_str())
        {
            return Some(open.worked_min_at(self.now.fixed_offset()));
        }
        let started = self.local(active.started);
        Some((self.now - started).num_minutes().max(0) as u32)
    }

    /// §9.1: the overtime prompt, when the timer has passed `est × r` and the
    /// last overtime prompt is `overtime_reprompt_min` old.
    pub fn overtime_due(&self) -> Option<Overtime> {
        let active = self.state.active.as_ref()?;
        if active.paused {
            return None;
        }
        let elapsed = self.active_elapsed_min()?;
        if elapsed < active.est_min {
            return None;
        }
        let reprompt = i64::from(self.cfg.day.overtime_reprompt_min);
        if let Some(at) = self.overtime_at {
            if (self.now - at) < Duration::minutes(reprompt) {
                return None;
            }
        }
        Some(self.overtime(&active.id.clone(), active.est_min, elapsed))
    }

    /// §9.1's "x extend +1 block → drops: …": the items an extension would
    /// leave no room for.
    ///
    /// [`planner::overtime_drops`] is the intended entry point, but it moves
    /// nothing when the item is the **running** block — which is the only
    /// case §9.1 has: `planner::active_run` sizes that block from
    /// `runtime.active.est_min` and never reads
    /// `PlanOverrides::extra_min` (planner.rs:1419, see the report). So for
    /// the running block the what-if is run here the way `tm extend` actually
    /// changes the world: `active.est_min` grows *and* the item's remaining
    /// estimate grows.
    fn extend_drops(&self, id: &Id, blocks: u32) -> Vec<Id> {
        let minutes = blocks.saturating_mul(self.cfg.block_min());
        if !self.state.active.as_ref().is_some_and(|a| &a.id == id) {
            return planner::overtime_drops(&self.input(), id, blocks);
        }
        let base = planner::plan(&self.input());
        let mut runtime = self.state.clone();
        if let Some(active) = runtime.active.as_mut() {
            active.est_min = active.est_min.saturating_add(minutes);
        }
        let overrides = PlanOverrides::new().extending(id, minutes);
        let alt = planner::plan(
            &PlanInput::new(
                &self.tree,
                &self.log,
                &self.replay,
                &self.cfg,
                &self.model,
                &runtime,
                self.now,
            )
            .with_caps(&self.caps)
            .with_ranking(&self.candidates, &self.prios)
            .with_overrides(&overrides),
        );
        planner::diff(&base, &alt).removed
    }

    /// Build §9.1's box for one running block, consequences included.
    fn overtime(&self, id: &Id, planned_min: u32, elapsed_min: u32) -> Overtime {
        let item = self.tree.get(id);
        let seg = self
            .plan
            .segments
            .iter()
            .find(|s| s.item.as_ref() == Some(id) && s.kind.is_work());
        let drops = self
            .extend_drops(id, 1)
            .into_iter()
            .map(|dropped| match self.priority_of(&dropped) {
                Some(p) => format!("{} (p{p})", self.title_of(&dropped)),
                None => self.title_of(&dropped),
            })
            .collect();
        // Exactly what `tm stop` writes as `est:` (see `cli::day::stop`), so
        // the consequence line promises what the verb actually does.
        let remaining = self
            .tree
            .remaining(id)
            .unwrap_or(planned_min)
            .saturating_sub(elapsed_min)
            .max(MIN_REMAINING_MIN);
        let stays = review::fmt_blocks_min(remaining, self.cfg.block_min());
        Overtime {
            id: id.clone(),
            title: item.map(|i| i.title.clone()).unwrap_or_else(|| id.to_string()),
            // The estimate as written (§9.1's `est 2b ×1.6`), not what is left
            // of it: the multiplier is quoted against the original.
            est: item
                .and_then(|i| i.est_original.clone().or_else(|| i.own_remaining()))
                .map(|d| d.to_string())
                .unwrap_or_else(|| {
                    review::fmt_blocks_min(planned_min, self.cfg.block_min())
                }),
            multiplier: seg.and_then(|s| s.flags.multiplier),
            planned_min,
            elapsed_min,
            drops,
            stays,
            reprompt_min: self.cfg.day.overtime_reprompt_min,
        }
    }

    /// §9.2: nothing has been running for `idle_min`.
    ///
    /// A break that has run past its planned minutes counts as nothing running
    /// (§9's "Break overran" row): the break is over as far as the plan is
    /// concerned, the block it paused is not accruing time, and the minutes
    /// since still have to be attributed — answering `b` gives them to the
    /// break, `w` starts the next block, `l` books them as a leak. Without
    /// this an unended break silences both prompts for the rest of the day.
    pub fn idle_due(&self) -> Option<Idle> {
        // A wall or a routine placed over `now` is "running" too (§9.2) — an
        // overrun break during a meeting is the meeting, not a gap.
        if self.plan.segments.iter().any(|s| {
            s.start <= self.now
                && self.now < s.end
                && matches!(s.kind, SegKind::Wall | SegKind::Routine | SegKind::Sleep)
        }) {
            return None;
        }
        let since = match self.break_overrun_since() {
            Some(end) => end,
            None => {
                if self.state.active.is_some()
                    || self.state.break_.is_some()
                    || self.state.interrupt.is_some()
                {
                    return None;
                }
                self.idle_since()?
            }
        };
        let minutes = (self.now - since).num_minutes();
        if minutes < i64::from(self.cfg.day.idle_min) {
            return None;
        }
        if let Some(at) = self.idle_at {
            if (self.now - at) < Duration::minutes(i64::from(self.cfg.day.idle_min)) {
                return None;
            }
        }
        Some(Idle {
            minutes: minutes as u32,
        })
    }

    /// When the running break was due to end, once it is past (§9's "Break
    /// overran"). `None` while no break is running or it is still inside its
    /// planned minutes.
    pub fn break_overrun_since(&self) -> Option<DateTime<Tz>> {
        let br = self.state.break_.as_ref()?;
        let end = self.local(br.started?) + Duration::minutes(i64::from(br.planned_min));
        (self.now > end).then_some(end)
    }

    /// When the gap started: the last event logged today, else the window
    /// start (there is no gap before the day begins).
    fn idle_since(&self) -> Option<DateTime<Tz>> {
        let last = self
            .log
            .iter_day(self.today, self.cfg.tz)
            .map(|e| e.t.with_timezone(&self.cfg.tz))
            .max();
        let start = self.plan.window.0;
        match last {
            Some(t) if t > start => Some(t),
            _ => (self.now > start).then_some(start),
        }
    }

    // -----------------------------------------------------------------
    // Keys (§12.6)
    // -----------------------------------------------------------------

    /// What a keystroke means in the current state.
    pub fn action_for(&self, key: KeyEvent) -> Action {
        resolve(
            self.screen,
            self.mode.clone(),
            self.prompt.as_ref().map(Prompt::kind),
            key,
        )
    }

    /// Apply an action: change the UI state and return the side effects the
    /// driver should carry out.
    pub fn apply(&mut self, action: Action) -> Vec<Effect> {
        self.message = None;
        match action {
            Action::None => Vec::new(),
            Action::Screen(s) => {
                self.screen = s;
                self.mode = Mode::Normal;
                Vec::new()
            }
            Action::Help => {
                self.mode = if self.mode == Mode::Help {
                    Mode::Normal
                } else {
                    Mode::Help
                };
                Vec::new()
            }
            Action::CommandLine => {
                self.mode = Mode::Command;
                self.input.clear();
                Vec::new()
            }
            Action::Quit => {
                self.quit = true;
                vec![Effect::Quit]
            }
            Action::Edit => match self.selected_location() {
                Some((file, line)) => vec![Effect::Editor { file, line }],
                None => self.note_msg("nothing selected"),
            },
            Action::Replan => vec![Effect::Verb(vec!["plan".into()])],
            Action::ReplanOrResume => {
                if self.state.interrupt.is_some() {
                    vec![Effect::Verb(vec!["resume".into()])]
                } else {
                    vec![Effect::Verb(vec!["plan".into()])]
                }
            }
            Action::Sync => vec![
                Effect::Verb(vec!["sync-cal".into()]),
                Effect::Verb(vec!["plan".into()]),
            ],
            Action::Done => vec![Effect::Verb(vec!["done".into()])],
            Action::Extend => vec![Effect::Verb(vec!["extend".into()])],
            Action::Stop => vec![Effect::Verb(vec!["stop".into()])],
            Action::Break => {
                self.mode = Mode::BreakWhere;
                Vec::new()
            }
            Action::BreakWhere(place) => {
                self.mode = Mode::Normal;
                vec![Effect::Verb(vec![
                    "break".into(),
                    "--where".into(),
                    place.as_str().into(),
                ])]
            }
            Action::Interrupt => vec![Effect::Verb(vec!["interrupt".into()])],
            Action::EnergyPrompt => {
                self.mode = Mode::Energy;
                Vec::new()
            }
            Action::Energy(level) => {
                self.mode = Mode::Normal;
                vec![Effect::Verb(vec!["energy".into(), level.to_string()])]
            }
            Action::Location => {
                self.mode = Mode::Input(InputKind::Location);
                self.input.clear();
                Vec::new()
            }
            Action::SkipRoutine => match self.selected_routine() {
                Some(name) => vec![Effect::Verb(vec!["skip".into(), name])],
                None => self.note_msg("select a routine row to skip it"),
            },
            Action::Note => {
                self.mode = Mode::Input(InputKind::Note);
                self.input.clear();
                Vec::new()
            }
            Action::Pause => vec![Effect::Verb(vec!["pause".into()])],
            Action::SelectNext => {
                self.select(1);
                Vec::new()
            }
            Action::SelectPrev => {
                self.select(-1);
                Vec::new()
            }
            Action::Open => {
                // §12.2: `Enter` on a Today row drills into the Queue, whose
                // panes open on the selected item.
                if self.selected_item.is_some() {
                    self.screen = Screen::Queue;
                }
                Vec::new()
            }
            Action::Cancel => {
                self.mode = Mode::Normal;
                self.input.clear();
                self.hover = None;
                if let Some(prompt) = self.prompt.take() {
                    self.mark_asked(prompt.kind());
                }
                Vec::new()
            }
            Action::Input(c) => {
                self.input.push(c);
                Vec::new()
            }
            Action::Backspace => {
                self.input.pop();
                Vec::new()
            }
            Action::Submit => self.submit(),
            Action::Answer(answer) => self.answer(answer),
            Action::ScreenKey(key) => self.screen_key(key),
        }
    }

    /// A [`queue::View`] over the current state — what §12.2, §12.3 and
    /// §12.5 render from.
    pub fn view(&self) -> queue::View<'_> {
        App::view_of(
            &self.tree,
            &self.files,
            &self.cfg,
            &self.replay,
            &self.candidates,
            &self.prios,
            &self.caps,
            self.today,
            self.now,
        )
    }

    /// §12.4's three reviews, computed from the log the way `tm review` does
    /// (§11 lives in `tm_core::review`, never here).
    pub fn reviews(&self) -> review_screen::Reviews {
        let extras = review::DayExtras {
            plan_at_arrival: self.arrival_blocks(),
            underused: self.plan.diagnostics.underused.len(),
            budget: self.state.budget,
            ..review::DayExtras::default()
        };
        review_screen::Reviews {
            day: review::day_review(
                &self.tree,
                &self.replay,
                &self.cfg,
                &self.model,
                self.today,
                self.cfg.tz,
                &extras,
            ),
            week: review::week_review(
                &self.tree,
                &self.replay,
                &self.cfg,
                &self.model,
                IsoWeek::from_date(self.today),
                self.cfg.tz,
                &review::WeekExtras::default(),
            ),
            month: review::month_review(
                &self.tree,
                &self.replay,
                &self.cfg,
                tm_core::model::YearMonth::from_date(self.today),
                self.cfg.tz,
                &review::MonthExtras::default(),
            ),
        }
    }

    /// Hand a keystroke to the screen in front (§12.2–§12.5), then translate
    /// what it asks for into [`Effect`]s. A key the screen ignores falls
    /// through to §12.6's global row.
    fn screen_key(&mut self, key: KeyEvent) -> Vec<Effect> {
        let (action, selected) = match self.screen {
            Screen::Queue => {
                let view = App::view_of(
                    &self.tree,
                    &self.files,
                    &self.cfg,
                    &self.replay,
                    &self.candidates,
                    &self.prios,
                    &self.caps,
                    self.today,
                    self.now,
                );
                let action = queue::on_key(&mut self.queue, &view, key);
                // §12.2's cursor is what `e` and the Today screen pick up.
                let selected = self.queue.selected(&view);
                (action, selected)
            }
            Screen::Necessities => {
                let view = App::view_of(
                    &self.tree,
                    &self.files,
                    &self.cfg,
                    &self.replay,
                    &self.candidates,
                    &self.prios,
                    &self.caps,
                    self.today,
                    self.now,
                );
                let action = necessities::on_key(&mut self.necessities, &view, key);
                let selected = self.necessities.selected(&view).map(|r| r.id);
                (action, selected)
            }
            Screen::Inbox => {
                let view = App::view_of(
                    &self.tree,
                    &self.files,
                    &self.cfg,
                    &self.replay,
                    &self.candidates,
                    &self.prios,
                    &self.caps,
                    self.today,
                    self.now,
                );
                (inbox::on_key(&mut self.capture, &view, key), None)
            }
            Screen::Review => {
                let reviews = self.reviews();
                (review_screen::on_key(&mut self.review, &reviews, key), None)
            }
            Screen::Today => (queue::Action::Ignored, None),
        };
        if let Some(id) = selected {
            self.selected_item = Some(id);
        }
        self.screen_action(action, key)
    }

    /// [`queue::View::new`] over borrowed parts, so a caller can keep a
    /// disjoint `&mut` on the screen state beside it.
    #[allow(clippy::too_many_arguments)]
    fn view_of<'a>(
        tree: &'a Tree,
        files: &'a PlanFiles,
        cfg: &'a Config,
        replay: &'a Replay,
        candidates: &'a [Candidate],
        prios: &'a [Prio],
        caps: &'a [UnitCapacity],
        today: NaiveDate,
        now: DateTime<Tz>,
    ) -> queue::View<'a> {
        queue::View::new(tree, files, cfg, replay, candidates, prios, caps, today, now)
    }

    /// Turn one screen [`queue::Action`] into the shell's effects.
    fn screen_action(&mut self, action: queue::Action, key: KeyEvent) -> Vec<Effect> {
        match action {
            queue::Action::Ignored => {
                let global = match key.code {
                    // §12.6: `r` is "replan" everywhere but the Today screen.
                    KeyCode::Char('r') => Action::Replan,
                    _ => global_key(key),
                };
                if global == Action::None {
                    Vec::new()
                } else {
                    self.apply(global)
                }
            }
            queue::Action::Redraw => Vec::new(),
            queue::Action::Note(text) => self.note_msg(&text),
            queue::Action::Edit { id, file } => {
                match queue::edit_command(&self.cfg, &self.tree, &id, file.as_deref()) {
                    Some(_) => match self.location_of(&id, file.as_deref()) {
                        Some((file, line)) => vec![Effect::Editor { file, line }],
                        None => self.note_msg("no line to open"),
                    },
                    None => self.note_msg("no line to open"),
                }
            }
            queue::Action::Prompt(prompt) => {
                self.mode = Mode::Input(InputKind::Screen(prompt));
                self.input.clear();
                Vec::new()
            }
            queue::Action::Mutate(m) => self.mutate(m),
        }
    }

    /// The `file:line` of one item, preferring the copy the row was read from
    /// (§6.3: a `# Demoted` archive line shares its id with the live one).
    fn location_of(&self, id: &Id, file: Option<&str>) -> Option<(String, usize)> {
        let node = self.tree.node(id)?;
        match file {
            Some(want) => self
                .files
                .files
                .iter()
                .find(|f| f.path == want)
                .and_then(|f| {
                    f.items()
                        .find(|i| Tree::key_of(i) == *id)
                        .map(|i| (f.path.clone(), i.src.line))
                })
                .or(Some((node.item.src.file.clone(), node.item.src.line))),
            None => Some((node.item.src.file.clone(), node.item.src.line)),
        }
    }

    /// §12.6's file-changing keys, each one a §13 verb (except `J`/`K`, whose
    /// byte-faithful rewrite `queue::apply_reorder` performs).
    fn mutate(&mut self, m: queue::Mutation) -> Vec<Effect> {
        match m {
            queue::Mutation::Reorder { .. } => vec![Effect::Mutate(Box::new(m))],
            queue::Mutation::Demote(id) => {
                vec![Effect::Verb(vec!["demote".into(), id.token()])]
            }
            queue::Mutation::Readopt(id) => {
                vec![Effect::Verb(vec!["readopt".into(), id.token()])]
            }
            queue::Mutation::Drop(id) => vec![Effect::Verb(vec!["drop".into(), id.token()])],
            queue::Mutation::Skip { item, .. } => {
                vec![Effect::Verb(vec!["skip".into(), item.to_string()])]
            }
            queue::Mutation::Event { name, id } => {
                let mut args = vec!["event".into(), name];
                if let Some(id) = id {
                    args.push(id.token());
                }
                vec![Effect::Verb(args)]
            }
            queue::Mutation::Capture {
                ref text,
                ref file,
                ref section,
                from_inbox,
            } => {
                let mut args = vec!["add".into(), text.clone(), "--to".into(), file.clone()];
                if let Some(s) = section {
                    args.push("--section".into());
                    args.push(s.clone());
                }
                let mut out = vec![Effect::Verb(args)];
                if from_inbox.is_some() {
                    out.push(Effect::Mutate(Box::new(m)));
                }
                out
            }
            queue::Mutation::DropInboxLine { .. } => vec![Effect::Mutate(Box::new(m))],
        }
    }

    /// Set the message line and produce no effect.
    fn note_msg(&mut self, text: &str) -> Vec<Effect> {
        self.message = Some(text.to_string());
        Vec::new()
    }

    /// The routine (or optional) the selection names, by the key
    /// `tm skip <name>` takes (`Tree::key_of`, the title for an id-less line).
    fn selected_routine(&self) -> Option<String> {
        let id = self.selected_item.clone()?;
        let item = self.tree.get(&id)?;
        matches!(item.horizon, tm_core::model::Horizon::Routine).then(|| id.to_string())
    }

    /// `Enter` in the command line or a text input.
    fn submit(&mut self) -> Vec<Effect> {
        let text = std::mem::take(&mut self.input);
        let mode = std::mem::replace(&mut self.mode, Mode::Normal);
        let text = text.trim().to_string();
        match mode {
            Mode::Command => {
                if text.is_empty() {
                    return Vec::new();
                }
                match split_args(&text) {
                    Ok(args) if args.is_empty() => Vec::new(),
                    Ok(args) => vec![Effect::Verb(args)],
                    Err(e) => self.note_msg(&e),
                }
            }
            Mode::Input(InputKind::Note) if !text.is_empty() => vec![Effect::Note(text)],
            Mode::Input(InputKind::Location) if !text.is_empty() => vec![Effect::SetLocation(text)],
            // §12.2's `a c E P`: each is one §13 verb with the typed value.
            Mode::Input(InputKind::Screen(p)) if !text.is_empty() => match p {
                queue::Prompt::Add { file, section } => {
                    let mut args = vec!["add".into(), text, "--to".into(), file];
                    if let Some(s) = section {
                        args.push("--section".into());
                        args.push(s);
                    }
                    vec![Effect::Verb(args)]
                }
                queue::Prompt::Ci(id) => vec![Effect::Verb(vec![
                    "edit".into(),
                    id.token(),
                    format!("ci={text}"),
                ])],
                queue::Prompt::Estimate(id) => vec![Effect::Verb(vec![
                    "edit".into(),
                    id.token(),
                    format!("est={text}"),
                ])],
                queue::Prompt::Priority(id) => vec![Effect::Verb(vec![
                    "edit".into(),
                    id.token(),
                    format!("p={text}"),
                ])],
            },
            _ => Vec::new(),
        }
    }

    /// Start the re-prompt clock of one prompt kind (§9.1's
    /// `overtime_reprompt_min`, §9.2's `idle_min`). The two are separate: an
    /// answered idle prompt must not silence the overtime prompt.
    fn mark_asked(&mut self, kind: PromptKind) {
        match kind {
            PromptKind::Overtime => self.overtime_at = Some(self.now),
            PromptKind::Idle => self.idle_at = Some(self.now),
        }
    }

    /// Answer the open prompt (§9.1, §9.2).
    ///
    /// §9.2's keys do two things, in this order: they attribute the gap
    /// (`tm idle …`, which is what keeps the leak ledger honest) and then they
    /// *make the transition the key promises* — `w` starts the next block, `b`
    /// a break, `i` an interruption. `t` only attributes: §13 has no verb that
    /// starts a routine, and its instance is closed with `tm routine done`.
    fn answer(&mut self, answer: Answer) -> Vec<Effect> {
        let prompt = self.prompt.take();
        if let Some(prompt) = &prompt {
            self.mark_asked(prompt.kind());
        }
        let verb = |args: &[&str]| vec![Effect::Verb(args.iter().map(|s| (*s).into()).collect())];
        let idle = |args: &[&str], mut rest: Vec<Effect>| {
            let mut out = verb(args);
            out.append(&mut rest);
            out
        };
        match (prompt, answer) {
            (Some(Prompt::Overtime(_)), Answer::Extend) => verb(&["extend"]),
            (Some(Prompt::Overtime(_)), Answer::Stop) => verb(&["stop"]),
            (Some(Prompt::Overtime(_)), Answer::Done) => verb(&["done"]),
            (_, Answer::Later) => Vec::new(),
            (Some(Prompt::Idle(_)), Answer::Work) => {
                let start = match self.next_block() {
                    Some(id) => verb(&["start", &id.token()]),
                    None => {
                        self.message = Some("nothing left to start".to_string());
                        Vec::new()
                    }
                };
                idle(&["idle", "w"], start)
            }
            (Some(Prompt::Idle(_)), Answer::Break) => idle(&["idle", "b"], verb(&["break"])),
            (Some(Prompt::Idle(_)), Answer::Routine) => verb(&["idle", "t"]),
            (Some(Prompt::Idle(_)), Answer::Interrupt) => {
                idle(&["idle", "i"], verb(&["interrupt"]))
            }
            (Some(Prompt::Idle(_)), Answer::Leak) => verb(&["idle", "l"]),
            _ => Vec::new(),
        }
    }

    /// The next block §9.2's `w` starts: the first work segment of today's
    /// plan that is not finished yet (`tm start` wants the item by name).
    pub fn next_block(&self) -> Option<Id> {
        self.plan
            .segments
            .iter()
            .filter(|s| s.kind.is_work() && !s.flags.done && s.end > self.now)
            .find_map(|s| s.item.clone())
    }
}

/// §12.6's keymap, as a pure function.
///
/// The prompt captures every key while it is open (§9.1: "any other key: ask
/// again in 15m"); otherwise the mode decides, and only [`Mode::Normal`] sees
/// the per-screen rows of the table.
///
/// Typing wins over a prompt: a character typed into the `:` command line or
/// into the `n`/`l` input belongs to the line being typed, never to a prompt
/// that appeared under it — otherwise the `s` of `start …` would answer §9.1
/// with "stop". ([`App::raise_prompt`] does not raise one while a line is open
/// either; this is the second half of the same rule.)
pub fn resolve(screen: Screen, mode: Mode, prompt: Option<PromptKind>, key: KeyEvent) -> Action {
    if key.modifiers.contains(KeyModifiers::CONTROL) && key.code == KeyCode::Char('c') {
        return Action::Quit;
    }
    if matches!(mode, Mode::Command | Mode::Input(_)) {
        return text_key(key);
    }
    if let Some(kind) = prompt {
        return prompt_key(kind, key);
    }
    match mode {
        Mode::Help => Action::Cancel,
        // Both are answered above, before the prompt; this keeps the match
        // exhaustive without an `_` arm that would swallow a new mode.
        Mode::Command | Mode::Input(_) => text_key(key),
        Mode::BreakWhere => match key.code {
            KeyCode::Char(c) => BreakPlace::from_key(c)
                .map(Action::BreakWhere)
                .unwrap_or(Action::Cancel),
            _ => Action::Cancel,
        },
        Mode::Energy => match key.code {
            KeyCode::Char(c @ '0'..='5') => Action::Energy(c as u8 - b'0'),
            _ => Action::Cancel,
        },
        Mode::Normal => normal_key(screen, key),
    }
}

/// §9.1 and §9.2's keys.
fn prompt_key(kind: PromptKind, key: KeyEvent) -> Action {
    let KeyCode::Char(c) = key.code else {
        return match key.code {
            KeyCode::Esc => Action::Cancel,
            _ => Action::Answer(Answer::Later),
        };
    };
    let answer = match (kind, c) {
        (PromptKind::Overtime, 'x') => Answer::Extend,
        (PromptKind::Overtime, 's') => Answer::Stop,
        (PromptKind::Overtime, 'd') => Answer::Done,
        (PromptKind::Idle, 'w') => Answer::Work,
        (PromptKind::Idle, 'b') => Answer::Break,
        (PromptKind::Idle, 't') => Answer::Routine,
        (PromptKind::Idle, 'i') => Answer::Interrupt,
        (PromptKind::Idle, 'l') => Answer::Leak,
        _ => Answer::Later,
    };
    Action::Answer(answer)
}

/// The command line and the one-line text inputs.
fn text_key(key: KeyEvent) -> Action {
    match key.code {
        KeyCode::Enter => Action::Submit,
        KeyCode::Esc => Action::Cancel,
        KeyCode::Backspace => Action::Backspace,
        KeyCode::Char(c) => Action::Input(c),
        _ => Action::None,
    }
}

/// §12.6's global row plus the row of the screen in front.
///
/// The first five keys are the ones no screen may take (`1`–`5` `?` `:` `q`
/// `R`). Everything else on screens 2–5 is offered to that screen first — its
/// `h l j k J K Enter a c E P D A x t w` rows would otherwise be swallowed by
/// the global `j`/`k`/`Enter`/`e` — and comes back through
/// [`Action::ScreenKey`] to the global row when the screen does not want it.
fn normal_key(screen: Screen, key: KeyEvent) -> Action {
    match key.code {
        KeyCode::Char(c @ '1'..='5') => {
            return Screen::from_digit(c).map(Action::Screen).unwrap_or(Action::None)
        }
        KeyCode::Char('?') => return Action::Help,
        KeyCode::Char(':') => return Action::CommandLine,
        KeyCode::Char('q') => return Action::Quit,
        KeyCode::Char('R') => return Action::Sync,
        _ => {}
    }
    if screen != Screen::Today {
        return Action::ScreenKey(key);
    }
    match global_key(key) {
        Action::None => today_key(key),
        action => action,
    }
}

/// §12.6's `global` row, minus the five keys [`normal_key`] resolves first
/// and minus `r`, which the Today screen reads as "resume when interrupted"
/// ([`today_key`]) and every other screen as the global replan
/// ([`App::screen_action`]).
fn global_key(key: KeyEvent) -> Action {
    match key.code {
        KeyCode::Char('e') => Action::Edit,
        KeyCode::Char('j') | KeyCode::Down => Action::SelectNext,
        KeyCode::Char('k') | KeyCode::Up => Action::SelectPrev,
        KeyCode::Enter => Action::Open,
        KeyCode::Esc => Action::Cancel,
        _ => Action::None,
    }
}

/// §12.6's `today` rows.
fn today_key(key: KeyEvent) -> Action {
    match key.code {
        KeyCode::Char('d') => Action::Done,
        KeyCode::Char('x') => Action::Extend,
        KeyCode::Char('s') => Action::Stop,
        KeyCode::Char('b') => Action::Break,
        KeyCode::Char('i') => Action::Interrupt,
        KeyCode::Char('r') => Action::ReplanOrResume,
        KeyCode::Char('0') => Action::EnergyPrompt,
        KeyCode::Char('l') => Action::Location,
        KeyCode::Char('K') => Action::SkipRoutine,
        KeyCode::Char('n') => Action::Note,
        KeyCode::Char(' ') => Action::Pause,
        _ => Action::None,
    }
}

/// True for [`emit::render_plan_section`]'s
/// `15:10  ───     window ends 16:00` row.
///
/// The `───` sits where a segment row keeps its `ci` cell — right after the
/// `HH:MM` time and two spaces ([`emit::TIME_W`]) — and a `ci` cell is always
/// a digit or one of `emit`'s kind glyphs, so the test is exact.
fn is_divider_row(line: &str) -> bool {
    line.get(emit::TIME_W + 2..)
        .is_some_and(|rest| rest.starts_with(emit::DIVIDER))
}

/// Split a `:` command line into arguments, honouring `'` and `"` quotes so
/// `add "- [ ] 2 30m Call the bank"` reaches §13's `tm add` in one piece.
pub fn split_args(line: &str) -> Result<Vec<String>, String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut quote: Option<char> = None;
    let mut any = false;
    for c in line.chars() {
        match (quote, c) {
            (Some(q), c) if c == q => quote = None,
            (Some(_), c) => cur.push(c),
            (None, '\'') | (None, '"') => {
                quote = Some(c);
                any = true;
            }
            (None, c) if c.is_whitespace() => {
                if any || !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                    any = false;
                }
            }
            (None, c) => cur.push(c),
        }
    }
    if quote.is_some() {
        return Err("unbalanced quote".to_string());
    }
    if any || !cur.is_empty() {
        out.push(cur);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(c: char) -> KeyEvent {
        KeyEvent::new(KeyCode::Char(c), KeyModifiers::NONE)
    }

    #[test]
    fn screens_round_trip_through_their_digits() {
        for s in Screen::ALL {
            let digit = char::from_digit(u32::from(s.number()), 10).expect("digit");
            assert_eq!(Screen::from_digit(digit), Some(s));
        }
    }

    #[test]
    fn quoted_arguments_stay_whole() {
        assert_eq!(
            split_args("add \"- [ ] 2 30m Call the bank\" --to backlog").expect("split"),
            vec!["add", "- [ ] 2 30m Call the bank", "--to", "backlog"]
        );
        assert_eq!(split_args("  ").expect("split"), Vec::<String>::new());
        assert_eq!(split_args("add ''").expect("split"), vec!["add", ""]);
        assert!(split_args("add \"oops").is_err());
    }

    #[test]
    fn the_break_chord_takes_a_place_then_returns_to_normal() {
        let action = resolve(Screen::Today, Mode::BreakWhere, None, key('w'));
        assert_eq!(action, Action::BreakWhere(BreakPlace::Walk));
        assert_eq!(
            resolve(Screen::Today, Mode::BreakWhere, None, key('z')),
            Action::Cancel
        );
    }

    #[test]
    fn an_open_prompt_swallows_every_key() {
        assert_eq!(
            resolve(Screen::Today, Mode::Normal, Some(PromptKind::Overtime), key('q')),
            Action::Answer(Answer::Later)
        );
        assert_eq!(
            resolve(Screen::Today, Mode::Normal, Some(PromptKind::Idle), key('l')),
            Action::Answer(Answer::Leak)
        );
    }
}
