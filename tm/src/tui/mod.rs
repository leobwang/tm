//! `tm tui` — the terminal UI of tm-spec-v1.md §12.
//!
//! # API overview
//!
//! [`run`] is the whole frontend: it puts the terminal into raw mode and the
//! alternate screen with `EnableMouseCapture` (§12.1's hover), starts a
//! `notify` watcher on the plan directory with §17.2's 200 ms debounce, and
//! loops over crossterm events plus a tick, redrawing [`today::draw`] from an
//! [`app::App`] each time. The terminal is restored on the way out **and**
//! from a panic hook, so a crash never leaves a raw terminal behind.
//!
//! The split is deliberate and is what makes §17's M6 snapshots possible:
//!
//! * [`app`] — all the state and §12.6's keymap, pure. A keystroke becomes an
//!   [`app::Action`], an action becomes zero or more [`app::Effect`]s.
//! * [`today`], [`daybar`], [`prompts`], [`theme`] — pure rendering.
//! * this file — the only place that touches the terminal, the clock, the
//!   file system and [`crate::cli`]. Every [`app::Effect::Verb`] is parsed by
//!   the *same* clap tree as the command line and run by the *same*
//!   [`crate::cli::run`], so `d` and `tm done` are one code path (§12), and
//!   the `:` command line accepts any §13 verb for free. The two effects with
//!   no verb of their own — `n` note and `l` location — are written here, and
//!   through the same [`crate::cli::undo::Recorder`] every verb uses, so
//!   `tm undo` keeps working across them.
//! * [`crate::cli::ghost`] reads `.tm/arrival_plan.json`, the record §12.1's
//!   ghost row and §11's adherence are measured against — the same reader
//!   `tm plan` writes the SVG's ghost row from.
//!
//! Screens 2–5 (§12.2–§12.5) are the modules [`queue`], [`necessities`],
//! [`review`] and [`inbox`]. [`app`] dispatches their §12.6 key rows and
//! [`today::draw`] gives each of them the body area.

pub mod app;
pub mod daybar;
pub mod inbox;
pub mod necessities;
pub mod prompts;
pub mod queue;
pub mod review;
pub mod theme;
pub mod today;

use std::io::{self, IsTerminal, Stdout};
use std::path::{Component, Path, PathBuf};
use std::sync::mpsc::{self, Receiver};
use std::time::{Duration as StdDuration, Instant};

use chrono::{DateTime, Datelike, FixedOffset, Local, NaiveDate};
use chrono_tz::Tz;
use clap::Parser;
use crossterm::event::{
    self, DisableMouseCapture, EnableMouseCapture, Event, KeyEventKind, MouseButton, MouseEvent,
    MouseEventKind,
};
use crossterm::execute;
use crossterm::terminal::{
    disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen,
};
use notify::{RecommendedWatcher, RecursiveMode, Watcher};
use ratatui::backend::CrosstermBackend;
use ratatui::layout::Rect;
use ratatui::Terminal;

use tm_core::capacity::UnitCapacity;
use tm_core::config::Config;
use tm_core::log::Event as LogEvent;
use tm_core::model::IsoWeek;
use tm_core::priority::{Candidate, Prio};
use tm_core::review::PauseCut;

use crate::cli::ctx::{resolve_dir, Ctx, Globals, ReplayScope};
use crate::cli::ghost;
use crate::cli::out::CliError;
use crate::cli::{dayfile, undo, Cli, Command};

use app::{App, AppData, Effect, Hover, Screen};

/// **A day the App could not plan, as the error a verb gives** — the kernel's
/// own error when the planner carried it ([`kernel_planner`] always does), so a
/// fault ends the TUI with everything it captured and a refusal is the one `tm
/// plan` gives on the same tree.
fn unplanned_error(u: app::Unplanned) -> CliError {
    match u.cause.and_then(|c| c.downcast::<CliError>().ok()) {
        Some(e) => *e,
        None => CliError::msg(u.message),
    }
}

/// **A fault the App's planner answered, ended here** (AGENTS §5.10: a kernel
/// that returned nothing usable ends the TUI, loudly; a refusal stays on the
/// hint line).
fn planner_fault(app: &App) -> Result<(), CliError> {
    match app.take_fault() {
        Some(f) => Err(unplanned_error(f)),
        None => Ok(()),
    }
}

/// **The App's planner over a context** (R3's body swap; the owner's D103): the
/// kernel's day at the instant the App asks for, over the plan directory as
/// `ctx` read it — its documents and log as `tm plan`'s housekeeping would leave
/// them, held in memory past midnight (D84, D91, D96) — and `.tm/state.json` as
/// the App holds it: the one request `tm plan` sends. The planner keeps its own
/// copy of the context ([`Ctx::fork`]), its clock moved to each instant asked,
/// and **the request's inputs as this load read them**
/// (`kernel_capacity::tick_inputs`, read here, once): every ask — the minute
/// tick's, the overtime box's what-if — is built from them and the context
/// alone (`kernel_capacity::plan_day_from`), so a tick reads NOTHING from the
/// plan directory and never mixes newer bytes with the reload's tree, replay
/// and candidates (README gap 4662), as fork 4748911's tick replanned from the
/// App's own data. A re-collection or a reload hands the App a new planner with
/// its data ([`data_with`]), and reads them again. A read that failed here is
/// asked again at the ask, where it fails by name as `tm plan`'s would.
fn kernel_planner(ctx: &Ctx) -> app::Planner {
    let read = std::cell::RefCell::new(ctx.fork());
    let inputs = crate::cli::kernel_capacity::tick_inputs(ctx).ok();
    Box::new(move |ask: &app::Ask<'_>| {
        let mut read = read.borrow_mut();
        read.now = ask.now.fixed_offset();
        read.now_tz = ask.now;
        read.today = ask.now.date_naive();
        read.state = ask.state.clone();
        let planned = match &inputs {
            Some(inputs) => crate::cli::kernel_capacity::plan_day_from(&read, inputs, false, ask.extend),
            None => crate::cli::kernel_capacity::plan_day(&read, false, ask.extend),
        };
        let whatif = ask.extend.is_some();
        planned
            .map(|p| app::Asked {
                day: p.day,
                removed: p.overtime.map(|d| d.removed).unwrap_or_default(),
                // The day's own ranking (README gap 4743): what the Queue shows is what the day
                // was planned by. A what-if's ranks the grown request (P52), never the Queue's.
                ranking: (!whatif).then_some(app::Ranking { candidates: p.cands, prios: p.prios, caps: p.caps }),
            })
            .map_err(|e| app::Unplanned { message: e.to_string(), fault: e.is_kernel_fault(), cause: Some(Box::new(e)) })
    })
}

/// §17.2: "`notify` debounce 200 ms".
const DEBOUNCE: StdDuration = StdDuration::from_millis(200);
/// How long the loop waits for a key before ticking the clock.
const POLL: StdDuration = StdDuration::from_millis(200);

/// Verbs that read from stdin and therefore need the normal screen back
/// while they run: `tm start` asks for an energy report when stdin is a
/// terminal (`cli::day::ask_energy`), which raw mode would swallow. Every
/// other §13 verb only writes.
const INTERACTIVE_VERBS: &[&str] = &["start"];

/// The terminal the TUI draws on.
type Term = Terminal<CrosstermBackend<Stdout>>;

/// Run the TUI (§12, §13's `tm tui`).
pub fn run(g: &Globals) -> Result<i32, CliError> {
    if !io::stdout().is_terminal() {
        return Err(CliError::msg(
            "tm tui needs a terminal (stdout is not a tty) — every verb of §13 also works on its own",
        ));
    }
    let root = resolve_dir(g.dir.as_deref())?;
    // `notify` reports absolute, resolved paths; the root may be relative
    // (`--dir ./plan`) or go through a symlink, so the form the events are
    // matched against is the canonical one (see [`is_watched`]).
    let watch_root = root.canonicalize().unwrap_or_else(|_| root.clone());
    let clock = Clock::of(g);
    let (mut read, mut app) = load(g)?;
    let (watcher, changes) = watch(&root)?;
    install_panic_hook();
    // Panic layer 2 (AGENTS 8.1): while the TUI owns the screen, every
    // kernel call runs with Lean's stderr dup2'd to a pipe, so a runtime
    // backtrace cannot shred the alternate screen — it rides the fault's
    // detail instead, and the fault path below prints it after the terminal
    // is restored.
    crate::cli::kernel_bridge::capture_kernel_stderr(true);
    let mut term = setup()?;
    let result = event_loop(&mut term, &mut app, &mut read, g, &clock, &root, &watch_root, &changes);
    restore();
    crate::cli::kernel_bridge::capture_kernel_stderr(false);
    drop(watcher);
    // A kernel fault propagates out of the loop (layer 3, integrated): the
    // terminal is already restored above, and the caller prints the fault —
    // captured stderr included — and exits 1. Loud and recoverable.
    result?;
    Ok(0)
}

// ---------------------------------------------------------------------------
// Terminal
// ---------------------------------------------------------------------------

/// Raw mode, alternate screen, mouse capture (§12.1's hover).
fn setup() -> Result<Term, CliError> {
    enable_raw_mode().map_err(|e| CliError::io("terminal", e))?;
    let mut out = io::stdout();
    execute!(out, EnterAlternateScreen, EnableMouseCapture)
        .map_err(|e| CliError::io("terminal", e))?;
    Terminal::new(CrosstermBackend::new(out)).map_err(|e| CliError::io("terminal", e))
}

/// Put the terminal back. Safe to call twice, and from a panic hook.
fn restore() {
    let mut out = io::stdout();
    let _ = execute!(out, DisableMouseCapture, LeaveAlternateScreen);
    let _ = disable_raw_mode();
}

/// Take the terminal back after [`restore`] handed it to an interactive verb.
fn resume() -> Result<(), CliError> {
    enable_raw_mode().map_err(|e| CliError::io("terminal", e))?;
    execute!(io::stdout(), EnterAlternateScreen, EnableMouseCapture)
        .map_err(|e| CliError::io("terminal", e))
}

/// Restore the terminal before the default panic message is printed —
/// otherwise a panic leaves the terminal in raw mode on the alternate screen.
fn install_panic_hook() {
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        restore();
        previous(info);
    }));
}

// ---------------------------------------------------------------------------
// Loading and watching
// ---------------------------------------------------------------------------

/// **The TUI's clock RUNS from `--now` when this is set** (W-42 track H,
/// README gap 4127): the TUI starts at the injected instant and advances with
/// the wall clock, so a pty can drive a TUI LEFT OPEN across local midnight —
/// the owner's D84, which nothing could drive while `--now` was fixed for the
/// TUI's life. Opt-in and inert without `--now`, as `TM_TRACE_KERNEL_CALLS`
/// and `TM_KERNEL_FAULT_PROBE` are: the shipped TUI reads the real clock.
pub const CLOCK_RUNS_ENV: &str = "TM_TUI_CLOCK_RUNS";

/// **The TUI's one clock** (§17.2: clocks are injected): the injected `--now`,
/// fixed — or running from it, with [`CLOCK_RUNS_ENV`] — else the real clock.
#[derive(Clone, Copy, Debug)]
struct Clock {
    /// `--now`.
    from: Option<DateTime<FixedOffset>>,
    /// When the TUI started, for a clock that runs.
    started: Instant,
    /// Whether the injected clock runs.
    runs: bool,
}

impl Clock {
    /// The clock `g` asks for.
    fn of(g: &Globals) -> Clock {
        Clock { from: g.now, started: Instant::now(), runs: g.now.is_some() && std::env::var_os(CLOCK_RUNS_ENV).is_some() }
    }

    /// The injected instant now — what a verb run from the TUI is stamped with
    /// (`Globals::now`) — or `None` on the real clock, which the verb reads.
    fn injected(&self) -> Option<DateTime<FixedOffset>> {
        let ran = chrono::Duration::from_std(self.started.elapsed()).unwrap_or_default();
        self.from.map(|from| if self.runs { from + ran } else { from })
    }

    /// `now` in `cfg.tz`.
    fn now(&self, cfg: &Config) -> DateTime<Tz> {
        self.injected().unwrap_or_else(|| Local::now().fixed_offset()).with_timezone(&cfg.tz)
    }
}

/// `g` stamped with `now`: a read at exactly the instant the App is moved to.
fn at(g: &Globals, now: DateTime<Tz>) -> Globals {
    Globals { now: Some(now.fixed_offset()), ..g.clone() }
}

/// Read the plan directory into the shape [`App`] wants. `week_cut` is the
/// heat grid's cut, which [`reload`] reads where the Review screen is shown.
fn data_of(ctx: &Ctx, week_cut: PauseCut) -> AppData {
    // §12.2/§12.3 read §7's numbers, and they are the day's own: the App's first
    // replan ([`App::new`]) asks the kernel for the day and takes its candidates,
    // priorities and lookahead from that one answer (`app::Asked::ranking`), and so
    // does every replan after it. Until the W-45 repair this asked a SECOND request
    // first (`Ctx::priorities`, over `.tm/state.json` unrolled) and the Queue showed
    // that ranking while the Today pane showed the day's (README gap 4743).
    data_with(ctx, Vec::new(), Vec::new(), Vec::new(), week_cut)
}

/// [`data_of`] with the ranking given.
fn data_with(
    ctx: &Ctx,
    candidates: Vec<Candidate>,
    prios: Vec<Prio>,
    caps: Vec<UnitCapacity>,
    week_cut: PauseCut,
) -> AppData {
    AppData {
        cfg: ctx.cfg.clone(),
        model: ctx.model.clone(),
        state: ctx.state.clone(),
        tree: ctx.tree.clone(),
        replay: ctx.replay.clone(),
        arrival: ghost::blocks(ctx),
        files: ctx.files.clone(),
        candidates,
        prios,
        caps,
        week_cut,
        now: ctx.now_tz,
        planner: kernel_planner(ctx),
    }
}

/// The replay scope the TUI asks for on `screen` (design §11.1, step R13;
/// gap 112).
///
/// - **The Review screen** runs the day, week and month reviews, which read
///   every day, duration and demotion: [`ReplayScope::All`].
/// - **Every other screen** shows the week pane, which counts the blocks done
///   on each date of the ISO week so far, and the status line, which reads
///   `state.date`'s day: `Dates` from the earlier of the week's Monday and
///   that date, to today.
/// - **With no `state.date`** the status line falls back to the log's last
///   day, at any age, so the TUI asks [`ReplayScope::All`].
fn tui_scope(
    screen: Screen,
    state: &tm_core::store::RuntimeState,
    today: NaiveDate,
) -> ReplayScope {
    if screen == Screen::Review {
        return ReplayScope::All;
    }
    let Some(date) = state.date else {
        return ReplayScope::All;
    };
    let monday = today - chrono::Duration::days(i64::from(today.weekday().num_days_from_monday()));
    ReplayScope::Dates {
        from: monday.min(date),
        to: today,
    }
}

/// Load the plan directory and plan today (§6.3's auto-close runs first, as
/// for every other verb). The context is kept beside the App: it is what a
/// date change re-collects from (D84, [`recollect`]).
fn load(g: &Globals) -> Result<(Ctx, App), CliError> {
    let ctx = Ctx::load_scoped(g, true, |state, today| tui_scope(Screen::default(), state, today))?;
    let app = App::new(data_of(&ctx, PauseCut::default())).map_err(unplanned_error)?;
    Ok((ctx, app))
}

/// **The plan directory as `tm plan` reads it at the context's instant — in
/// memory**: `.tm/state.json` as its roll leaves it (the owner's D84, W-42
/// track H, README gap 4050, parity P83), the documents as its automatic
/// close leaves them (the owner's D91, W-43 track H, README gap 4342), and —
/// since the owner's D96 (W-44 track H, README gap 4393, parity P94) — as
/// EVERY housekeeping write `tm plan` makes at that instant leaves them:
/// §5.1's waiting timeouts and D61's wall marks too.
///
/// The CLI's housekeeping rolls the state at the first verb of a new local date
/// (`RuntimeState::roll_to`, `ctx.rs`' `roll_day`), runs §6.3's automatic close,
/// then the waiting timeouts and the wall marks (`Ctx::after_the_close`), and
/// writes all of them; the TUI reads its plan directory without housekeeping,
/// so past midnight it held the stale state, the unclosed files, the waiting
/// items whose timeout had elapsed and the block a meeting had paused. Here it
/// lets go of whatever it held before ([`Ctx::release`]: ONE catch-up from the
/// files as read), reads the state through the same one rule, asks the kernel
/// for the documents the close would leave (`closing::close_in_memory`), and
/// runs the rest of `tm plan`'s housekeeping through THE SAME BODY
/// (`Ctx::after_the_close`) while the context holds (`Ctx::hold_begin`), so
/// every write it makes — a line, a journal line, a log line, the state —
/// answers into memory, and writes nothing (D81: nothing writes on a timer);
/// `planwire::plan_date` keeps its meaning, fork `PlanInput::date`. A state of
/// today's date, or of none, is read as it is, and a close that is not due asks
/// nothing; a hold with nothing in it is let go.
///
/// Returns a sentence for the status line: the meeting pause a held wall mark
/// says (D65), and when the close or the rest could not be held — a refusal by
/// name, or a file that could not be read — what was not held, in which case
/// the TUI plans from the files as they stand, as `tm plan` does after a
/// refused close; a kernel fault is an error.
fn read_as_tm_plan(ctx: &mut Ctx) -> Result<Option<String>, CliError> {
    ctx.release();
    ctx.state.roll_to(ctx.today);
    let mut said = Vec::new();
    let refused = match crate::cli::closing::close_in_memory(ctx) {
        Ok(crate::cli::closing::InMemory::Refused(why)) => {
            said.push(format!("the automatic close was refused, so these are the files as they stand: {why}"));
            true
        }
        Ok(_) => false,
        Err(e) if e.is_kernel_fault() => return Err(e),
        Err(e) => {
            said.push(format!("the automatic close could not be asked, so these are the files as they stand: {e}"));
            true
        }
    };
    // §5.1's waiting timeouts and D61's wall marks, HELD: the one body `tm plan`'s housekeeping runs (D96).
    let close_held = ctx.holding();
    let earlier = crate::cli::kernel_bridge::take_notices();
    let held = ctx.hold_begin().and_then(|()| ctx.after_the_close(refused, true));
    let mut notices = crate::cli::kernel_bridge::take_notices();
    match held {
        Ok(()) => {
            let empty = ctx.held.as_ref().is_some_and(|h| h.docs.is_empty() && h.log.is_empty());
            if !close_held && empty {
                ctx.release();
            }
        }
        Err(e) if e.is_kernel_fault() => return Err(e),
        Err(e) => {
            ctx.release();
            notices.clear();
            said.push(format!("the housekeeping could not be held, so these are the files as they stand: {e}"));
        }
    }
    let mut out: Vec<String> = earlier;
    out.extend(notices);
    out.extend(said);
    Ok((!out.is_empty()).then(|| out.join(" · ")))
}

/// **[`read_as_tm_plan`] at `now`, for a context already read** — the date
/// change's whole re-collection of the plan directory (D84): the clock moves,
/// the state is read as `tm plan`'s roll leaves it, and the files and the tree
/// are the ones the automatic close leaves, held in memory (D91); the replay
/// and the model stay as they were read, and nothing touches the disk. The
/// candidates and the kernel's ranking for the new date follow from it in
/// [`adopt_read`].
fn advance(ctx: &mut Ctx, now: DateTime<Tz>) -> Result<Option<String>, CliError> {
    ctx.now = now.fixed_offset();
    ctx.now_tz = now;
    ctx.today = now.date_naive();
    read_as_tm_plan(ctx)
}

/// **The App drawn from `read`** — the ranking is the day's own (README gap
/// 4743): the App adopts the rest with its last ranking and replans, which
/// replaces the ranking with the one the new day was planned by. A refused day
/// (a file saved half-edited into a tree the kernel cannot load, or a configured
/// value it cannot read, parity P26) keeps the last day and the last ranking and
/// says so on the status line (`plan not refreshed: …`); a kernel fault still
/// ends the TUI. One body for [`reload`] and [`recollect`]. `said` is a sentence
/// the read itself raised (an automatic close it could not hold, D91), shown when
/// nothing above it is.
fn adopt_read(app: &mut App, read: &Ctx, week_cut: PauseCut, cut_refused: Option<String>, said: Option<String>) -> Result<(), CliError> {
    let data = data_with(read, app.candidates.clone(), app.prios.clone(), app.caps.clone(), week_cut);
    // The App's replan is the only thing in `adopt` that writes the status line: a sentence
    // there afterwards is the refusal's, and it stands.
    let before = app.message.take();
    app.adopt(data);
    planner_fault(app)?;
    if app.message.is_none() {
        app.message = match (cut_refused, said) {
            (Some(why), _) => Some(format!("week grid not refreshed: {why}")),
            (None, Some(said)) => Some(said),
            (None, None) => before,
        };
    }
    Ok(())
}

/// **A TUI left open past local midnight re-collects its inputs IN MEMORY at
/// the date change** — the owner's D84 (W-42 track H, README gaps 4050 and
/// 4124, parity P83): from the context it last read ([`advance`]), the
/// candidates and the kernel's ranking for `now`'s date, and with the state
/// read as `tm plan`'s roll leaves it, §8.2 step 2's routine instances for that
/// date — and since the owner's D91 (W-43 track H, README gap 4342) from the
/// documents as `tm plan`'s automatic close leaves them, the close asked of the
/// kernel and held ([`read_as_tm_plan`]) — so the request R3's swap sends from
/// here is the one `tm plan` builds at that instant
/// (`kernel_capacity::planner_request`). It WRITES NOTHING: no fresh read of
/// the plan directory, whose replay would reseal `.tm/cache/replay` (the
/// ranking's own `log` section resumes from the checkpoint the process already
/// holds), no roll of `.tm/state.json` and no close written — the CLI's
/// housekeeping's writes on a timer, which the owner declined.
fn recollect(app: &mut App, read: &mut Ctx, now: DateTime<Tz>) -> Result<(), CliError> {
    let said = advance(read, now)?;
    adopt_read(app, read, app.week_cut.clone(), None, said)
}

/// **One turn of the clock**: at a date change the TUI re-collects in memory
/// ([`recollect`], D84), and — since the W-44 repair (README gap 4553) — at the
/// minute a wall of the day begins or ends while a block is open
/// ([`App::crosses_a_wall`]), the one other instant `tm plan`'s housekeeping
/// writes something new (D61's wall marks, held by D96's one body); then
/// [`App::tick`] moves `now`, replans on a new minute and raises §9's prompts.
/// Returns whether anything changed. Every other minute asks the kernel for
/// the day once, through the App's planner and nothing else — the owner's
/// D103 (D38 revised): the minute tick replans through the kernel, as the
/// fork's tick replanned, so the rows move when `tm plan`'s day moves.
fn advance_clock(app: &mut App, read: &mut Ctx, now: DateTime<Tz>) -> Result<bool, CliError> {
    let dated = now.date_naive() != app.today;
    let walled = !dated && app.crosses_a_wall(now);
    if dated || walled {
        recollect(app, read, now)?;
    }
    let changed = app.tick(now) || dated || walled;
    planner_fault(app)?;
    Ok(changed)
}

/// Re-read the plan directory into an existing [`App`], keeping the UI state,
/// in the scope of the screen it shows, at the clock's instant — read as `tm
/// plan` reads it then ([`read_as_tm_plan`], D84: a reload past midnight is the
/// date change's re-collection too) — and keep the context it read in `read`.
///
/// Stage 5 D10 L8: the ranking is the kernel's ([`adopt_read`]).
fn reload(app: &mut App, read: &mut Ctx, g: &Globals, clock: &Clock) -> Result<(), CliError> {
    let screen = app.screen;
    let now = clock.now(&app.cfg);
    let mut ctx = Ctx::load_scoped(&at(g, now), false, |state, today| tui_scope(screen, state, today))?;
    let said = read_as_tm_plan(&mut ctx)?;
    // **The heat grid's Pauses are cut by the kernel** (README gaps 3432 and
    // 3528, W-39 track T), as `tm review week` cuts them — read only where the
    // Review screen is shown, the one screen that draws the grid, because it
    // is one more kernel call. A refusal keeps the last cut and says so, as a
    // refused ranking does; a fault still ends the TUI.
    let (week_cut, cut_refused) = if screen == Screen::Review {
        match crate::cli::day::week_cut(&ctx, IsoWeek::from_date(ctx.today)) {
            Ok(cut) => (cut, None),
            Err(e) if !e.is_kernel_fault() => (app.week_cut.clone(), Some(e.to_string())),
            Err(e) => return Err(e),
        }
    } else {
        (app.week_cut.clone(), None)
    };
    adopt_read(app, &ctx, week_cut, cut_refused, said)?;
    *read = ctx;
    Ok(())
}

/// Watch `plan/` for changes (§17.2). The watcher must stay alive as long as
/// the receiver, so it is returned too.
fn watch(root: &Path) -> Result<(RecommendedWatcher, Receiver<PathBuf>), CliError> {
    let (tx, rx) = mpsc::channel();
    let mut watcher = notify::recommended_watcher(move |res: notify::Result<notify::Event>| {
        if let Ok(ev) = res {
            if !is_a_change(&ev.kind) {
                return;
            }
            for path in ev.paths {
                let _ = tx.send(path);
            }
        }
    })
    .map_err(|e| CliError::msg(format!("watch {}: {e}", root.display())))?;
    watcher
        .watch(root, RecursiveMode::Recursive)
        .map_err(|e| CliError::msg(format!("watch {}: {e}", root.display())))?;
    Ok((watcher, rx))
}

/// **Whether a watcher event says a file CHANGED** — anything but an access.
///
/// `notify` 7's inotify backend watches inotify's open event too, so every READ
/// of a plan file arrives as `EventKind::Access(Open)`. Forwarded, a verb that only reads
/// — above all one that REFUSES and writes nothing, D71's `tm pause` inside an
/// interruption (README gap 3430, W-39 track T) — had its status line replaced
/// by `inbox.md changed`, the last file it opened, and the TUI then re-parsed a
/// tree nothing had touched. DRIVEN under a pty: the Space key's refusal never
/// reached the screen. A read is not a change, so it is not reported as one;
/// a close after WRITING (inotify's close-write event, which `notify` also
/// files under `Access`) still is.
fn is_a_change(kind: &notify::EventKind) -> bool {
    use notify::event::{AccessKind, AccessMode};
    match kind {
        notify::EventKind::Access(AccessKind::Close(AccessMode::Write)) => true,
        notify::EventKind::Access(_) => false,
        _ => true,
    }
}

/// True for a path the tree is parsed from: a `.md` file outside `.tm/`,
/// `.git/` and the other dot directories *of the plan root* (§2). Our own
/// writes to `.tm/` and to `day/<date>.svg` therefore never trigger a
/// re-parse.
///
/// The dot test is applied to the path **below `root`** only. Applied to the
/// whole path it would reject every plan directory that merely *lives* under
/// a dot directory — `~/.local/share/plan`, `~/.config/tm/plan`, a checkout
/// under `.claude/worktrees/…` — and the relative form `./plan/…` (whose
/// first component is `.`), and the §12 watcher would then silently never
/// fire.
fn is_watched(root: &Path, path: &Path) -> bool {
    if path.extension().is_none_or(|e| e != "md") {
        return false;
    }
    match path.strip_prefix(root) {
        Ok(rel) => !rel.components().any(
            |c| matches!(c, Component::Normal(s) if s.to_string_lossy().starts_with('.')),
        ),
        // The event path cannot be related to the root. The watcher is rooted
        // at the plan directory, so trust it and reject only a dot *file* such
        // as an editor's `.#week.md` lock.
        Err(_) => !path
            .file_name()
            .is_some_and(|n| n.to_string_lossy().starts_with('.')),
    }
}

// ---------------------------------------------------------------------------
// The loop
// ---------------------------------------------------------------------------

/// Draw, wait for an event, act, tick — until `q`.
#[allow(clippy::too_many_arguments)]
fn event_loop(
    term: &mut Term,
    app: &mut App,
    read: &mut Ctx,
    g: &Globals,
    clock: &Clock,
    root: &Path,
    watch_root: &Path,
    changes: &Receiver<PathBuf>,
) -> Result<(), CliError> {
    let mut due: Option<Instant> = None;
    loop {
        // The verbs the TUI runs are stamped with its clock's instant (a clock
        // that runs, README gap 4127); on the real clock each reads its own.
        let g = &Globals { now: clock.injected(), ..g.clone() };
        term.draw(|f| today::draw(f, app))
            .map_err(|e| CliError::io("terminal", e))?;
        if app.quit {
            return Ok(());
        }

        if event::poll(POLL).map_err(|e| CliError::io("terminal", e))? {
            let ev = event::read().map_err(|e| CliError::io("terminal", e))?;
            let area = term.size().map_err(|e| CliError::io("terminal", e))?;
            let area = Rect::new(0, 0, area.width, area.height);
            let screen = app.screen;
            let effects = match ev {
                Event::Key(key) if key.kind == KeyEventKind::Press => {
                    let action = app.action_for(key);
                    app.apply(action)
                }
                Event::Mouse(m) => {
                    mouse(app, area, m);
                    Vec::new()
                }
                Event::Resize(..) => {
                    term.clear().map_err(|e| CliError::io("terminal", e))?;
                    Vec::new()
                }
                _ => Vec::new(),
            };
            for effect in effects {
                perform(term, app, read, g, clock, root, effect)?;
                if app.quit {
                    return Ok(());
                }
            }
            // Entering the Review screen widens the scope (§11.1): read the
            // history it needs before it draws — and the kernel's cut of the
            // week's Pauses its heat grid draws (README gaps 3432 and 3528),
            // which is read on entering it even when the scope is already
            // `All` (a state with no date).
            if app.screen != screen
                && (app.screen == Screen::Review
                    || tui_scope(app.screen, &app.state, app.today)
                        != tui_scope(screen, &app.state, app.today))
            {
                reload(app, read, g, clock)?;
            }
        }

        // §17.2: coalesce a burst of file events into one re-parse.
        while let Ok(path) = changes.try_recv() {
            if is_watched(watch_root, &path) {
                due = Some(Instant::now() + DEBOUNCE);
                app.message = Some(format!(
                    "{} changed",
                    path.file_name().unwrap_or_default().to_string_lossy()
                ));
            }
        }
        if due.is_some_and(|at| Instant::now() >= at) {
            due = None;
            reload(app, read, g, clock)?;
        }

        advance_clock(app, read, clock.now(&app.cfg))?;
    }
}

/// §17.2's mouse handling: `Moved` shows the day-bar tooltip, `Down(Left)`
/// selects the item under the pointer. Everything else stays keyboard-only.
fn mouse(app: &mut App, area: Rect, m: MouseEvent) {
    let bar_area = today::bar_area(app, area);
    let col = daybar::hit(bar_area, m.column, m.row);
    match m.kind {
        MouseEventKind::Moved => {
            app.hover = col.and_then(|col| {
                let bar = daybar::bar(app, daybar::bar_width(bar_area));
                daybar::tooltip(&bar, col).map(|text| Hover { col, text })
            });
        }
        MouseEventKind::Down(MouseButton::Left) => {
            if let Some(col) = col {
                let bar = daybar::bar(app, daybar::bar_width(bar_area));
                if let Some(seg) = daybar::segment_at(&bar, col) {
                    app.select_segment(seg);
                }
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Effects
// ---------------------------------------------------------------------------

/// Carry out one [`Effect`].
fn perform(
    term: &mut Term,
    app: &mut App,
    read: &mut Ctx,
    g: &Globals,
    clock: &Clock,
    root: &Path,
    effect: Effect,
) -> Result<(), CliError> {
    match effect {
        Effect::Quit => {}
        Effect::Verb(args) => {
            let interactive = args
                .first()
                .is_some_and(|v| INTERACTIVE_VERBS.contains(&v.as_str()));
            if interactive {
                restore();
            }
            let message = verb(g, &args)?;
            if interactive {
                resume()?;
            }
            // Either way the verb has printed to the real stdout underneath
            // the UI; a full repaint covers it.
            term.clear().map_err(|e| CliError::io("terminal", e))?;
            reload(app, read, g, clock)?;
            app.message = Some(message);
        }
        Effect::Editor { file, line } => {
            let (file, line) = on_disk(read, &file, line);
            let message = editor(app, root, &file, line);
            app.message = Some(message);
        }
        Effect::Note(text) => {
            note(g, &text)?;
            reload(app, read, g, clock)?;
            app.message = Some("note written".to_string());
        }
        Effect::SetLocation(loc) => {
            set_location(g, &loc)?;
            reload(app, read, g, clock)?;
            app.message = Some(format!("location {loc}"));
        }
        Effect::Mutate(m) => {
            if let Some(refused) = held_mutation(read, &m) {
                app.message = Some(refused);
                return Ok(());
            }
            let message = mutate(g, &m)?;
            reload(app, read, g, clock)?;
            app.message = Some(message);
        }
    }
    Ok(())
}

/// §12.2's `J`/`K` and §12.5's inbox line: the two screen mutations that are
/// not one of §13's verbs. Both go through an [`undo::Recorder`], like every
/// verb, so `tm undo` keeps working across them.
fn mutate(g: &Globals, m: &queue::Mutation) -> Result<String, CliError> {
    let mut ctx = Ctx::load(g, false)?;
    crate::cli::kernel_bridge::gate(&ctx, "tui")?;
    let rec = undo::Recorder::start(&ctx, "tui")?;
    let message = match m {
        queue::Mutation::Reorder { id, .. } => match queue::apply_reorder(&ctx.store, m) {
            Some(Ok(true)) => format!("moved ^{id}"),
            Some(Ok(false)) => format!("^{id} is already at the end of its section"),
            Some(Err(e)) => format!("^{id}: {e}"),
            None => String::new(),
        },
        queue::Mutation::Capture {
            from_inbox: Some(line),
            ..
        }
        | queue::Mutation::DropInboxLine { line } => {
            inbox::drop_line(&ctx.store, *line)?;
            format!("inbox line {line} removed")
        }
        _ => String::new(),
    };
    ctx.reload()?;
    rec.finish(&ctx, format!("tui {}", message.trim()))?;
    Ok(message)
}

/// §12.6's `n`: a §10.1 `note` event and a `## Log` line.
///
/// Wrapped in an [`undo::Recorder`] like every §13 verb: without it `tm undo`
/// finds the day file changed under it and refuses with a conflict (exit code
/// 3), which would leave the *previous* command permanently un-undoable.
fn note(g: &Globals, text: &str) -> Result<(), CliError> {
    let mut ctx = Ctx::load(g, false)?;
    crate::cli::kernel_bridge::gate(&ctx, "note")?;
    let rec = undo::Recorder::start(&ctx, "note")?;
    ctx.append_event(LogEvent::Note {
        text: text.to_string(),
    })?;
    dayfile::note(&ctx, ctx.today, ctx.now_tz.time(), &format!("note {text}"))?;
    ctx.reload()?;
    rec.finish(&ctx, format!("note {text}"))
}

/// §12.6's `l`: `runtime.loc` and the §10.1 `loc` event, recorded so `tm undo`
/// can put the location back (and so a later undo does not silently discard
/// it with the rest of `state.json`).
fn set_location(g: &Globals, loc: &str) -> Result<(), CliError> {
    let mut ctx = Ctx::load(g, false)?;
    crate::cli::kernel_bridge::gate(&ctx, "loc")?;
    let rec = undo::Recorder::start(&ctx, "loc")?;
    ctx.state.loc = Some(loc.to_string());
    ctx.save_state()?;
    ctx.append_event(LogEvent::Loc {
        loc: loc.to_string(),
    })?;
    ctx.reload()?;
    rec.finish(&ctx, format!("loc {loc}"))
}

/// Run one §13 verb through the same clap tree and the same dispatcher the
/// command line uses, and describe what happened in one line.
///
/// A verb's ordinary failure — a kernel *refusal* included — is a status
/// message, and the session keeps running. A kernel **fault**
/// (`KernelFault`, or a response that is not a response) is the one error
/// that propagates: [`run`] restores the terminal on the way out, the fault
/// is printed as a bug report (captured stderr included), and the process
/// exits 1 — loud and recoverable, never a shredded screen or a silent
/// wrong answer (AGENTS 8.1, panic layers 2 and 3).
fn verb(g: &Globals, args: &[String]) -> Result<String, CliError> {
    let argv = std::iter::once("tm".to_string()).chain(args.iter().cloned());
    let cli = match Cli::try_parse_from(argv) {
        Ok(cli) => cli,
        Err(e) => {
            return Ok(e
                .to_string()
                .lines()
                .next()
                .unwrap_or("bad command")
                .to_string())
        }
    };
    if matches!(cli.command, Command::Tui) {
        return Ok("already in the TUI".to_string());
    }
    // The TUI's own directory and instant win: `--dir` and `--now` are how
    // *this* session was started.
    let globals = Globals {
        dir: g.dir.clone(),
        json: false,
        now: g.now,
    };
    let name = args.first().cloned().unwrap_or_default();
    // A notice the verb's housekeeping SAID (D65's meeting pause) rides the
    // status line: stderr belongs to the screen (README gap 3339).
    let _ = crate::cli::kernel_bridge::take_notices();
    let status = match crate::cli::run(&globals, cli.command) {
        Ok(0) => format!("{name}: ok"),
        Ok(code) => format!("{name}: exit {code}"),
        Err(e) if e.is_kernel_fault() => return Err(e),
        Err(e) => format!("{name}: {e}"),
    };
    let said = crate::cli::kernel_bridge::take_notices();
    Ok(if said.is_empty() { status } else { format!("{status} · {}", said.join(" · ")) })
}

/// **Where the item the App shows at `file:line` is ON DISK** — the owner's D91 (W-43 track H,
/// README gap 4396). While an automatic close is held in memory past midnight, the App's tree is
/// the plan directory as that close would leave it, and the editor writes to disk: an item in a
/// file the held close changed is found by its key in the tree as read
/// ([`Ctx::tree_as_read`]) and opened there — `^p1` in the day file it still has, not at the line
/// of the week file the close would file it into. Any other location is the disk's already.
fn on_disk(read: &Ctx, file: &str, line: usize) -> (String, usize) {
    let changed = read.held.as_ref().is_some_and(|h| h.docs.contains_key(file));
    let at = read.files.file(file).and_then(|f| f.items().find(|i| i.src.line == line));
    match (changed, at, read.tree_as_read()) {
        (true, Some(item), Some(as_read)) => match as_read.get(&tm_core::tree::Tree::key_of(item)) {
            Some(there) => (there.src.file.clone(), there.src.line),
            None => (file.to_string(), line),
        },
        _ => (file.to_string(), line),
    }
}

/// **A screen mutation that addresses a file whose items the TUI holds MOVED
/// in memory is refused by name** (README gap 4505, the W-43 repair; the owner's
/// D91 — since D96 the hold is every housekeeping write, and of those the close
/// is the one that moves an item from one file to another). Past
/// midnight the App's rows are the held close's tree — `^p1` in the week file —
/// while the file on disk still has it in Monday's day file, and the two screen
/// mutations that are not §13 verbs (`J`/`K`, the inbox line) load the disk
/// WITHOUT housekeeping, so neither writes the close first: `J` on `^p1` read
/// NotFound, and `J`/`K` on a week neighbour moved it among lines the disk does
/// not hold. Gap 4396 mapped the editor (`on_disk`) and only the editor; this is
/// the rest of the class — every mutation whose file a held close changed. A §13
/// verb is not refused: its own housekeeping writes the very close the TUI
/// holds, so the file it addresses is the file the App shows. And a file a held
/// write changed WITHOUT moving its items (D96: a timeout's line rewritten in
/// place, a meeting's journal line) is not refused either — its item lines on
/// disk are the ones the App shows, and a reorder there is the one the user
/// sees. Returns the message, or `None` for a mutation that may run.
fn held_mutation(read: &Ctx, m: &queue::Mutation) -> Option<String> {
    let held = read.held.as_ref()?;
    let (who, files): (String, Vec<String>) = match m {
        queue::Mutation::Reorder { id, file, .. } => {
            let mut files: Vec<String> = file.iter().cloned().collect();
            files.extend(read.tree.get(id).map(|i| i.src.file.clone()));
            files.extend(read.tree_as_read().and_then(|t| t.get(id)).map(|i| i.src.file.clone()));
            (format!("^{id}"), files)
        }
        queue::Mutation::Capture { from_inbox: Some(line), .. } | queue::Mutation::DropInboxLine { line } => {
            (format!("inbox line {line}"), vec!["inbox.md".to_string()])
        }
        _ => return None,
    };
    // A file whose held write MOVED its items — the item lines, in order, are not the disk's (the close
    // took one out or filed one in) — is refused; one whose held write left them where they stand (a
    // timeout's line rewritten in place, a meeting's journal line, D96) reorders on disk as the App shows.
    let ids = |files: Option<&tm_core::store::PlanFiles>, f: &str| -> Vec<tm_core::model::Id> {
        files.and_then(|fs| fs.file(f)).map(|pf| pf.items().map(tm_core::tree::Tree::key_of).collect()).unwrap_or_default()
    };
    let moved = |f: &String| held.docs.contains_key(f) && (f == "inbox.md" || ids(Some(&read.files), f) != ids(read.files_as_read(), f));
    let file = files.into_iter().find(moved)?;
    Some(format!(
        "{who}: {file} is held in memory as `tm plan`'s housekeeping leaves it, and the disk does not hold its \
         lines yet (D91, D96) — a verb (`tm plan`) writes it, and then this reorders it"
    ))
}

/// Open a file at a line in `cfg.tui.editor` (§16's `code -g {file}:{line}`).
fn editor(app: &App, root: &Path, file: &str, line: usize) -> String {
    let path = root.join(file);
    let template = app
        .cfg
        .tui
        .editor
        .replace("{file}", &path.to_string_lossy())
        .replace("{line}", &line.to_string());
    let mut parts = template.split_whitespace();
    let Some(program) = parts.next() else {
        return "config.toml [tui] editor is empty".to_string();
    };
    match std::process::Command::new(program).args(parts).spawn() {
        Ok(_) => format!("{file}:{line}"),
        Err(e) => format!("{program}: {e}"),
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use chrono::DateTime;

    use super::*;
    use crate::cli::WakeArgs;

    /// Held by every test here that runs a verb. The fault probe is a
    /// process-wide environment variable, and since stage 4 step 6 every
    /// housekeeping verb on a fresh tree calls the kernel (the automatic
    /// close) — so a verb running in a sibling test thread while the probe
    /// is set would read it and fault.
    static KERNEL_ENV: std::sync::Mutex<()> = std::sync::Mutex::new(());

    fn kernel_env() -> std::sync::MutexGuard<'static, ()> {
        KERNEL_ENV.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    /// Copy a directory tree.
    fn copy_dir(from: &Path, to: &Path) {
        fs::create_dir_all(to).expect("create dir");
        for entry in fs::read_dir(from).expect("read fixture") {
            let entry = entry.expect("dir entry");
            let target = to.join(entry.file_name());
            if entry.file_type().expect("file type").is_dir() {
                copy_dir(&entry.path(), &target);
            } else {
                fs::copy(entry.path(), &target).expect("copy file");
            }
        }
    }

    /// A temp copy of the `plan-basic` fixture and the globals pointing at it.
    fn fixture() -> (tempfile::TempDir, Globals) {
        let tmp = tempfile::TempDir::new().expect("temp dir");
        let plan = tmp.path().join("plan");
        copy_dir(
            &Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-core/tests/fixtures/plan-basic"),
            &plan,
        );
        let now = DateTime::parse_from_rfc3339("2026-09-07T09:00:00-05:00").expect("now");
        (
            tmp,
            Globals {
                dir: Some(plan),
                json: false,
                now: Some(now),
            },
        )
    }

    fn wake(g: &Globals) {
        crate::cli::run(
            g,
            Command::Wake(WakeArgs {
                time: Some("06:05".to_string()),
                slept: None,
                onset: None,
            }),
        )
        .expect("tm wake");
    }

    #[test]
    fn the_watcher_looks_below_the_plan_root_for_dot_directories() {
        // §12's watcher: `.tm/` and `.git/` *inside* the plan root are ours to
        // ignore; a root that merely lives under a dot directory is not.
        let root = Path::new("/Users/me/.local/share/plan");
        assert!(is_watched(root, &root.join("week/2026-W37.md")));
        assert!(is_watched(root, &root.join("day/2026-09-07.md")));
        assert!(!is_watched(root, &root.join(".git/notes.md")));
        assert!(!is_watched(root, &root.join(".tm/scratch.md")));
        assert!(!is_watched(root, &root.join("day/2026-09-07.svg")));

        let worktree = Path::new("/w/.claude/worktrees/x/plan");
        assert!(is_watched(worktree, &worktree.join("week/2026-W37.md")));

        // `--dir ./plan` (`resolve_dir` keeps it verbatim): the leading `.`
        // component of a relative path is not a dot directory.
        let relative = Path::new("./plan");
        assert!(is_watched(relative, &relative.join("week/2026-W37.md")));

        // A path that cannot be related to the root is trusted — the watcher
        // is rooted at the plan directory — except an editor's dot file.
        assert!(is_watched(Path::new("/other"), Path::new("/p/week/x.md")));
        assert!(!is_watched(
            Path::new("/other"),
            Path::new("/p/week/.#x.md")
        ));
    }

    /// **A read is not a change** (README gap 3430's TUI half, W-39 track T):
    /// `notify` 7 reports every open of a plan file, and a verb that only
    /// reads — a refusal writes nothing — must not have its status line
    /// replaced by `inbox.md changed`. Every kind that can mean the bytes moved
    /// still counts (it does not over-bite, AGENTS §5.8).
    #[test]
    fn a_read_is_not_a_change_and_a_write_is() {
        use notify::event::{
            AccessKind, AccessMode, CreateKind, DataChange, ModifyKind, RemoveKind, RenameMode,
        };
        use notify::EventKind;
        assert!(!is_a_change(&EventKind::Access(AccessKind::Open(AccessMode::Any))));
        assert!(!is_a_change(&EventKind::Access(AccessKind::Close(AccessMode::Read))));
        assert!(!is_a_change(&EventKind::Access(AccessKind::Read)));
        assert!(is_a_change(&EventKind::Access(AccessKind::Close(AccessMode::Write))));
        assert!(is_a_change(&EventKind::Modify(ModifyKind::Data(DataChange::Any))));
        assert!(is_a_change(&EventKind::Modify(ModifyKind::Name(RenameMode::To))));
        assert!(is_a_change(&EventKind::Create(CreateKind::File)));
        assert!(is_a_change(&EventKind::Remove(RemoveKind::File)));
        assert!(is_a_change(&EventKind::Any));
        assert!(is_a_change(&EventKind::Other));
    }

    /// Layer 3, integrated at the TUI's one verb seam: a kernel **fault**
    /// propagates out of [`verb`] as an error — [`run`] then restores the
    /// terminal before it returns, and the caller prints the bug report and
    /// exits 1 — while a kernel *refusal* stays a status-line message and
    /// the session keeps running. The probe is the constructed one
    /// (`TM_KERNEL_FAULT_PROBE`, AGENTS 8.1's named trap): the real kernel
    /// call still runs; only the response bytes are replaced.
    #[test]
    fn a_kernel_fault_propagates_and_a_refusal_stays_a_message() {
        let _env = kernel_env();
        let (_tmp, g) = fixture();
        // The automatic close runs on the first housekeeping verb; let it
        // run unprobed, so the probe faults the edit's own kernel call.
        wake(&g);
        std::env::set_var("TM_KERNEL_FAULT_PROBE", "1");
        let out = verb(
            &g,
            &["edit".to_string(), "^t3".to_string(), "est=45m".to_string()],
        );
        std::env::remove_var("TM_KERNEL_FAULT_PROBE");
        let err = out.expect_err("a fault must propagate, never become a status message");
        assert!(err.is_kernel_fault(), "{err}");
        assert_eq!(err.exit_code(), 1);

        // The single-command A6 reproduction is a *refusal*: named, shown,
        // survivable — the TUI keeps running.
        let msg = verb(
            &g,
            &["move".to_string(), "^m2".to_string(), "month".to_string()],
        )
        .expect("a refusal is a message, not an exit");
        assert!(msg.contains("occupied"), "{msg}");
    }

    /// **The meeting pause D65 says is said in the TUI too** (W-37 repair, README
    /// gap 3339): a verb run from the TUI whose housekeeping logs the wall's
    /// pause shows it on the status line, where stderr belongs to the screen.
    #[test]
    fn the_meeting_pause_is_said_on_the_status_line() {
        let _env = kernel_env();
        let (_tmp, g) = fixture();
        wake(&g);
        let at = |s: &str| Globals {
            dir: g.dir.clone(),
            json: false,
            now: Some(DateTime::parse_from_rfc3339(s).expect("now")),
        };
        verb(&at("2026-09-07T12:00:00-05:00"), &["start".to_string(), "^t4".to_string()])
            .expect("tm start");
        crate::cli::kernel_bridge::capture_kernel_stderr(true);
        let status = verb(&at("2026-09-07T13:20:00-05:00"), &["now".to_string()]);
        crate::cli::kernel_bridge::capture_kernel_stderr(false);
        let status = status.expect("tm now");
        assert!(
            status.contains("paused ^t4 for Meeting w/ host 12:50–13:50"),
            "the status line says the pause: {status:?}"
        );
        assert!(crate::cli::kernel_bridge::take_notices().is_empty(), "the notice was taken once");
    }

    #[test]
    fn a_note_typed_in_the_tui_does_not_block_undo() {
        // §13: `tm undo` restores the file bytes the last verb changed, and
        // refuses with a conflict when the file moved under it. A TUI write
        // outside the recorder is exactly such a move.
        let _env = kernel_env();
        let (_tmp, g) = fixture();
        wake(&g);
        note(&g, "the printer is out of paper").expect("n note");
        crate::cli::run(&g, Command::Undo).expect("undo the note");
        crate::cli::run(&g, Command::Undo).expect("undo the wake underneath it");
    }

    #[test]
    fn a_location_set_in_the_tui_does_not_block_undo() {
        let _env = kernel_env();
        let (_tmp, g) = fixture();
        wake(&g);
        set_location(&g, "home").expect("l home");
        let ctx = Ctx::load(&g, false).expect("load");
        assert_eq!(ctx.state.loc.as_deref(), Some("home"));
        crate::cli::run(&g, Command::Undo).expect("undo the location");
        let ctx = Ctx::load(&g, false).expect("load");
        assert_ne!(ctx.state.loc.as_deref(), Some("home"), "put back");
        crate::cli::run(&g, Command::Undo).expect("undo the wake underneath it");
    }

    /// Every file under `root`, by path, as bytes — `.tm/` and its cache included.
    fn tree_bytes(root: &Path) -> std::collections::BTreeMap<String, Vec<u8>> {
        fn walk(root: &Path, dir: &Path, out: &mut std::collections::BTreeMap<String, Vec<u8>>) {
            for entry in fs::read_dir(dir).expect("read dir") {
                let path = entry.expect("entry").path();
                if path.is_dir() {
                    walk(root, &path, out);
                } else {
                    let rel = path.strip_prefix(root).expect("inside").display().to_string();
                    out.insert(rel, fs::read(&path).expect("bytes"));
                }
            }
        }
        let mut out = std::collections::BTreeMap::new();
        walk(root, root, &mut out);
        out
    }

    /// Every key path at which two JSON values differ (`a.b[2].c`).
    fn json_diff(a: &serde_json::Value, b: &serde_json::Value, path: &str, out: &mut Vec<String>) {
        use serde_json::Value;
        match (a, b) {
            (Value::Object(x), Value::Object(y)) => {
                let keys: std::collections::BTreeSet<&String> = x.keys().chain(y.keys()).collect();
                for k in keys {
                    let p = if path.is_empty() { k.clone() } else { format!("{path}.{k}") };
                    match (x.get(k), y.get(k)) {
                        (Some(u), Some(v)) => json_diff(u, v, &p, out),
                        _ => out.push(p),
                    }
                }
            }
            (Value::Array(x), Value::Array(y)) if x.len() == y.len() => {
                for (i, (u, v)) in x.iter().zip(y).enumerate() {
                    json_diff(u, v, &format!("{path}[{i}]"), out);
                }
            }
            _ if a != b => out.push(path.to_string()),
            _ => {}
        }
    }

    /// The routine instances a planner request sends, as `id@inst`.
    fn routines_of(req: &serde_json::Value) -> Vec<String> {
        req["planner"]["routines"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .map(|r| format!("{}@{}", r["id"].as_str().unwrap_or_default(), r["inst"].as_str().unwrap_or("-")))
            .collect()
    }

    /// `g` at an RFC 3339 instant.
    fn at_str(g: &Globals, s: &str) -> Globals {
        Globals { now: Some(DateTime::parse_from_rfc3339(s).expect("an instant")), ..g.clone() }
    }

    /// **The Midnight world as the shipped binary builds it** — §4.3's tree,
    /// woken Monday 06:05, arrived 07:00 (the window and budget of the day), the
    /// pinned `^p1` done at 22:00 so Monday's close has nothing to move, and
    /// `^t3` started at 23:30 and left running — with the TUI opened on it at
    /// 23:50 (`load`, its housekeeping): the context it read and its App.
    fn midnight_world() -> (tempfile::TempDir, Globals, Ctx, App) {
        let (tmp, g) = fixture();
        for (when, args) in [
            ("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h10m"][..]),
            ("2026-09-07T07:00:00-05:00", &["arrive", "lounge"][..]),
            ("2026-09-07T22:00:00-05:00", &["done", "^p1"][..]),
            ("2026-09-07T23:30:00-05:00", &["start", "^t3", "--energy", "3"][..]),
        ] {
            let argv: Vec<String> = args.iter().map(|a| (*a).to_string()).collect();
            let said = verb(&at_str(&g, when), &argv).expect("a verb of the world");
            assert!(said.ends_with(": ok"), "`tm {}`: {said}", args.join(" "));
        }
        let (read, app) = load(&at_str(&g, "2026-09-07T23:50:00-05:00")).expect("the TUI opens at 23:50");
        (tmp, g, read, app)
    }

    /// **D84: a TUI left open past local midnight re-collects IN MEMORY at the
    /// date change, writes nothing, and the request it would send is `tm plan`'s
    /// at that instant** (the owner's D84, W-42 track H, README gaps 4050 and
    /// 4124, parity P83). The clock moves the TUI from Monday 23:50 to Tuesday
    /// 00:30 through the loop's own step ([`advance_clock`]):
    ///
    /// * every byte of the plan directory, `.tm/` and its replay cache
    ///   included, is the same after the date change (D81: nothing writes on a
    ///   timer);
    /// * the App reads its state as `tm plan`'s roll leaves it — Tuesday, none
    ///   of Monday's window, budget or arrival — and the running block as it
    ///   stands;
    /// * R3's builder over what the TUI re-collected
    ///   (`kernel_capacity::planner_request`) and over `tm plan`'s own load at
    ///   00:30 — its housekeeping run, in a copy — agree KEY FOR KEY but for the
    ///   replay checkpoint's reseal day, which `tm plan`'s read wrote and the
    ///   TUI's, writing nothing, did not; and the kernel plans ONE day from the
    ///   two (the whole `ok.plan`, its hash included);
    /// * a context read WITHOUT the roll — what the TUI built from before D84,
    ///   and what `tm check` holds past midnight — is asked `tm plan`'s day
    ///   too, since the W-42 repair rolls the state inside the builder for every
    ///   caller (README gap 4334); it carried Monday's routine instances and
    ///   planned another day until then.
    #[test]
    fn d84_a_tui_left_open_past_midnight_recollects_in_memory_and_sends_tm_plans_request() {
        let _env = kernel_env();
        let (tmp, g, mut read, mut app) = midnight_world();
        let plan = g.dir.clone().expect("the plan directory");
        assert_eq!(app.state.date, Some(tui_date(2026, 9, 7)), "Monday's state at 23:50");
        assert!(app.state.window.is_some() && app.state.budget.is_some(), "Monday's day facts");

        let before = tree_bytes(&plan);
        let tuesday = DateTime::parse_from_rfc3339("2026-09-08T00:30:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        assert!(advance_clock(&mut app, &mut read, tuesday).expect("the date change"), "the date change changes the App");
        assert!(tree_bytes(&plan) == before, "the date change wrote nothing under the plan directory");

        assert_eq!((app.today, app.state.date), (tui_date(2026, 9, 8), Some(tui_date(2026, 9, 8))));
        assert_eq!((app.state.window, app.state.budget, app.state.arrival), (None, None, None), "read as the roll leaves it");
        assert_eq!(app.state.active.as_ref().map(|a| a.id.as_str()), Some("t3"), "the running block stands");
        assert_eq!(read.today, tui_date(2026, 9, 8));

        // The request R3's swap sends from here, and `tm plan`'s at the same instant.
        let tui: serde_json::Value =
            serde_json::from_str(&crate::cli::kernel_capacity::planner_request(&read, false).expect("the TUI's request")).expect("JSON");
        let copy = tmp.path().join("tm-plan");
        copy_dir(&plan, &copy);
        let plan_g = Globals { dir: Some(copy.clone()), now: Some(tuesday.fixed_offset()), json: false };
        let plan_ctx = Ctx::load(&plan_g, true).expect("tm plan's load, its housekeeping run");
        let plan_text = crate::cli::kernel_capacity::planner_request(&plan_ctx, false).expect("tm plan's request");
        let tm_plan: serde_json::Value = serde_json::from_str(&plan_text).expect("JSON");
        let mut differ = Vec::new();
        json_diff(&tui, &tm_plan, "", &mut differ);
        assert_eq!(differ, ["log.ckpt.resealDay"], "key for key, but for the checkpoint `tm plan`'s read resealed");
        assert!(routines_of(&tui).iter().any(|r| r == "breakfast@2026-09-08"), "{:?}", routines_of(&tui));

        let tui_text = crate::cli::kernel_capacity::planner_request(&read, false).expect("the TUI's request");
        let (tui_resp, _) = crate::cli::kernel_bridge::call_text(&tui_text).expect("the kernel plans the TUI's request");
        let (plan_resp, _) = crate::cli::kernel_bridge::call_text(&plan_text).expect("the kernel plans tm plan's request");
        assert!(tui_resp["ok"]["plan"].is_object(), "a day: {}", tui_resp["ok"]);
        assert_eq!(tui_resp["ok"]["plan"], plan_resp["ok"]["plan"], "one day from the two requests, hash and all");

        // A context read WITHOUT the roll — what the TUI held before D84, and what `tm check`,
        // which writes nothing, holds past midnight (README gaps 4263, 4323 and 4334) — is asked
        // as `tm plan`'s day too: since the W-42 repair the request builder reads the state as
        // the roll leaves it, for every caller.  Until then this read sent Monday's routine
        // instances and the kernel planned another day (in a copy — a fresh read of the
        // directory reseals its cache).
        let stale_dir = tmp.path().join("stale");
        copy_dir(&plan, &stale_dir);
        let stale_g = Globals { dir: Some(stale_dir), now: Some(tuesday.fixed_offset()), json: false };
        let stale_ctx = Ctx::load_scoped(&stale_g, false, |state, today| tui_scope(Screen::Today, state, today)).expect("a read");
        assert_eq!(stale_ctx.state.date, Some(tui_date(2026, 9, 7)), "the file still says Monday");
        let stale_text = crate::cli::kernel_capacity::planner_request(&stale_ctx, false).expect("the stale read's request");
        let stale: serde_json::Value = serde_json::from_str(&stale_text).expect("JSON");
        assert!(routines_of(&stale).iter().any(|r| r == "breakfast@2026-09-08"), "Tuesday's instances: {:?}", routines_of(&stale));
        let mut differ = Vec::new();
        json_diff(&stale, &tm_plan, "", &mut differ);
        // Every key, the checkpoint's reseal day included: this read is a fresh one, and it
        // reseals the replay cache as `tm plan`'s did.
        assert!(differ.is_empty(), "the stale read's request is `tm plan`'s, key for key: {differ:?}");
        let (stale_resp, _) = crate::cli::kernel_bridge::call_text(&stale_text).expect("the kernel plans it");
        assert_eq!(stale_resp["ok"]["plan"], plan_resp["ok"]["plan"], "the stale read is asked `tm plan`'s day");
    }

    /// **The Midnight world with Monday's `^p1` LEFT OPEN in the day file's `# Pinned`** — the tree
    /// README gap 4342 was found on: woken Monday 06:05, arrived 07:00, `^t3` started at 23:30 and
    /// left running, the TUI opened at 23:50 (its housekeeping) — so `tm plan` past midnight first
    /// closes Monday, demoting `^p1` into the week file, and logs it.
    fn unfinished_world() -> (tempfile::TempDir, Globals, Ctx, App) {
        let (tmp, g) = fixture();
        for (when, args) in [
            ("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h10m"][..]),
            ("2026-09-07T07:00:00-05:00", &["arrive", "lounge"][..]),
            ("2026-09-07T23:30:00-05:00", &["start", "^t3", "--energy", "3"][..]),
        ] {
            let argv: Vec<String> = args.iter().map(|a| (*a).to_string()).collect();
            let said = verb(&at_str(&g, when), &argv).expect("a verb of the world");
            assert!(said.ends_with(": ok"), "`tm {}`: {said}", args.join(" "));
        }
        let (read, app) = load(&at_str(&g, "2026-09-07T23:50:00-05:00")).expect("the TUI opens at 23:50");
        (tmp, g, read, app)
    }

    /// `tm plan`'s request at `now`, on a copy of the plan directory as it stands (its housekeeping,
    /// the automatic close included, WRITTEN in the copy), and the copy's root.
    fn tm_plans_request(tmp: &tempfile::TempDir, plan: &Path, now: DateTime<Tz>, name: &str) -> (String, PathBuf) {
        let copy = tmp.path().join(name);
        copy_dir(plan, &copy);
        let plan_g = Globals { dir: Some(copy.clone()), now: Some(now.fixed_offset()), json: false };
        let plan_ctx = Ctx::load(&plan_g, true).expect("tm plan's load, its housekeeping run");
        (crate::cli::kernel_capacity::planner_request(&plan_ctx, false).expect("tm plan's request"), copy)
    }

    /// **D91: on a tree whose Monday still holds unfinished day-file work, the TUI past midnight
    /// CLOSES IN MEMORY and asks the kernel what `tm plan` asks after its own close** (the owner's
    /// D91, W-43 track H, README gap 4342). Until D91 this test PINNED the divergence, as
    /// d84_on_a_day_with_unfinished_work_the_tui_and_tm_plan_ask_about_different_documents: the
    /// TUI re-collected the files as they stood while `tm plan` closed Monday and wrote it. At the
    /// date change (00:30 Tuesday, through the loop's own step, [`advance_clock`]):
    ///
    /// * every byte of the plan directory, `.tm/` and its replay cache included, is the same after
    ///   the date change — the close is asked of the kernel and held, never written;
    /// * what is held is what `tm plan`'s close WRITES: `^p1` demoted into the week file with
    ///   `demoted:D07`, the `demote` and `close` lines it logs, and Monday stamped closed;
    /// * R3's builder over what the TUI holds and over `tm plan`'s own load at 00:30 agree KEY FOR
    ///   KEY but for the replay checkpoint's reseal day, which `tm plan`'s read wrote — the
    ///   documents, and the log section, whose tail carries the close's two lines;
    /// * the kernel plans ONE day from the two (the whole `ok.plan`, its hash included).
    #[test]
    fn d91_on_a_day_with_unfinished_work_the_tui_closes_in_memory_and_asks_what_tm_plan_asks() {
        let _env = kernel_env();
        let (tmp, g, mut read, mut app) = unfinished_world();
        let plan = g.dir.clone().expect("the plan directory");
        assert!(read.held.is_none(), "nothing is held before midnight");
        let before = tree_bytes(&plan);
        let tuesday = DateTime::parse_from_rfc3339("2026-09-08T00:30:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        assert!(advance_clock(&mut app, &mut read, tuesday).expect("the date change"));
        assert!(tree_bytes(&plan) == before, "the date change wrote nothing under the plan directory");

        let held = read.held.as_ref().expect("the automatic close is held");
        let week = held.docs.get("week/2026-W37.md").expect("the close filed into the week");
        assert!(week.lines().any(|l| l.ends_with("^p1") && l.contains("demoted:D07")), "the held week file:\n{week}");
        let lines: Vec<serde_json::Value> = held.log.lines().map(|l| serde_json::from_str(l).expect("a log line")).collect();
        let evs: Vec<&str> = lines.iter().map(|e| e["ev"].as_str().unwrap_or_default()).collect();
        assert_eq!(evs, ["demote", "close"], "{}", held.log);
        assert_eq!((lines[1]["period"].as_str(), lines[1]["key"].as_str()), (Some("day"), Some("2026-09-07")));
        assert_eq!(app.state.closed.day, Some(tui_date(2026, 9, 7)), "Monday is closed in memory");
        assert!(
            app.files.file("week/2026-W37.md").is_some_and(|f| f.items().any(|i| i.id.as_str() == "p1")),
            "the App's files hold the week as the close leaves it"
        );

        let tui_text = crate::cli::kernel_capacity::planner_request(&read, false).expect("the TUI's request");
        let tui: serde_json::Value = serde_json::from_str(&tui_text).expect("JSON");
        let (plan_text, copy) = tm_plans_request(&tmp, &plan, tuesday, "tm-plan");
        let written = std::fs::read_to_string(copy.join("week/2026-W37.md")).expect("the week file tm plan's close wrote");
        assert_eq!(&written, week, "the TUI holds the week file `tm plan`'s close writes, byte for byte");
        let tm_plan: serde_json::Value = serde_json::from_str(&plan_text).expect("JSON");
        let mut differ = Vec::new();
        json_diff(&tui, &tm_plan, "", &mut differ);
        assert_eq!(differ, ["log.ckpt.resealDay"], "key for key, but for the checkpoint `tm plan`'s read resealed");
        let (tui_resp, _) = crate::cli::kernel_bridge::call_text(&tui_text).expect("the kernel plans the TUI's request");
        let (plan_resp, _) = crate::cli::kernel_bridge::call_text(&plan_text).expect("the kernel plans tm plan's request");
        assert!(tui_resp["ok"]["plan"].is_object(), "a day: {}", tui_resp["ok"]);
        assert_eq!(tui_resp["ok"]["plan"], plan_resp["ok"]["plan"], "one day from the two requests, hash and all");
    }

    /// **D91 across two midnights: the TUI holds ONE close, from the files as read** — never a
    /// second stacked on the first. Left open Monday 23:50 to Wednesday 00:30, it closes Monday in
    /// memory at Tuesday's date change and, at Wednesday's, lets that go and asks the kernel again
    /// from the files as they stand — what `tm plan` at Wednesday 00:30 runs: ONE catch-up, its lines
    /// stamped and keyed at that instant (`close` keyed 2026-09-08). Still nothing written, and the
    /// request is `tm plan`'s key for key but for the reseal day. A reload past midnight holds the
    /// same close.
    #[test]
    fn d91_a_tui_open_across_two_midnights_holds_one_close_from_the_files_as_read() {
        let _env = kernel_env();
        let (tmp, g, mut read, mut app) = unfinished_world();
        let plan = g.dir.clone().expect("the plan directory");
        let before = tree_bytes(&plan);
        let tz = app.cfg.tz;
        let tuesday = DateTime::parse_from_rfc3339("2026-09-08T00:30:00-05:00").expect("now").with_timezone(&tz);
        let wednesday = DateTime::parse_from_rfc3339("2026-09-09T00:30:00-05:00").expect("now").with_timezone(&tz);
        assert!(advance_clock(&mut app, &mut read, tuesday).expect("Tuesday"));
        assert!(advance_clock(&mut app, &mut read, wednesday).expect("Wednesday"));
        assert!(tree_bytes(&plan) == before, "two date changes wrote nothing");
        let held = read.held.as_ref().expect("a close is held");
        let lines: Vec<serde_json::Value> = held.log.lines().map(|l| serde_json::from_str(l).expect("a log line")).collect();
        assert_eq!(lines.len(), 2, "one close's lines, not two closes': {}", held.log);
        assert_eq!(lines[1]["key"], "2026-09-08", "keyed at Wednesday, as `tm plan`'s catch-up keys it");
        assert!(lines.iter().all(|e| e["t"].as_str().is_some_and(|t| t.starts_with("2026-09-09T00:30"))), "{}", held.log);
        assert_eq!(app.state.closed.day, Some(tui_date(2026, 9, 8)));

        let tui_text = crate::cli::kernel_capacity::planner_request(&read, false).expect("the TUI's request");
        let tui: serde_json::Value = serde_json::from_str(&tui_text).expect("JSON");
        let (plan_text, _) = tm_plans_request(&tmp, &plan, wednesday, "tm-plan-wed");
        let tm_plan: serde_json::Value = serde_json::from_str(&plan_text).expect("JSON");
        let mut differ = Vec::new();
        json_diff(&tui, &tm_plan, "", &mut differ);
        assert_eq!(differ, ["log.ckpt.resealDay"], "key for key, but for the reseal day");

        // A reload past midnight (a file event, no verb) reads the directory again and holds the
        // same close: its request is the one the date change built, but for the reseal day the
        // reload's own read wrote.
        let g_wed = at_str(&g, "2026-09-09T00:30:00-05:00");
        reload(&mut app, &mut read, &g_wed, &Clock::of(&g_wed)).expect("a reload past midnight");
        let reloaded: serde_json::Value =
            serde_json::from_str(&crate::cli::kernel_capacity::planner_request(&read, false).expect("the reload's request")).expect("JSON");
        let mut differ = Vec::new();
        json_diff(&reloaded, &tm_plan, "", &mut differ);
        assert!(differ.iter().all(|p| p == "log.ckpt.resealDay"), "{differ:?}");
        assert!(read.held.is_some(), "the reload holds the close");
    }

    /// **D91 over a torn log: the held lines are appended as `tm plan`'s close appends them** — after
    /// the last line is ended (`Store::append_text`'s rule, parity P19), so the TUI's log section is
    /// `tm plan`'s byte for byte. The world above with its log's final newline cut off.
    #[test]
    fn d91_a_torn_last_log_line_is_ended_as_tm_plans_append_ends_it() {
        let _env = kernel_env();
        let (tmp, g, mut read, mut app) = unfinished_world();
        let plan = g.dir.clone().expect("the plan directory");
        let log = plan.join(".tm/log.jsonl");
        let bytes = std::fs::read(&log).expect("the log");
        assert_eq!(bytes.last(), Some(&b'\n'));
        std::fs::write(&log, &bytes[..bytes.len() - 1]).expect("tear the last line");
        let tuesday = DateTime::parse_from_rfc3339("2026-09-08T00:30:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        assert!(advance_clock(&mut app, &mut read, tuesday).expect("the date change"));
        let ours = read.log_now().expect("the TUI's log");
        assert_eq!(&ours[..bytes.len()], &bytes[..], "the torn line is ended before the held lines");
        let (plan_text, copy) = tm_plans_request(&tmp, &plan, tuesday, "tm-plan-torn");
        assert_eq!(std::fs::read(copy.join(".tm/log.jsonl")).expect("tm plan's log"), ours, "the log `tm plan`'s close wrote");
        let tui: serde_json::Value =
            serde_json::from_str(&crate::cli::kernel_capacity::planner_request(&read, false).expect("the TUI's request")).expect("JSON");
        let tm_plan: serde_json::Value = serde_json::from_str(&plan_text).expect("JSON");
        let mut differ = Vec::new();
        json_diff(&tui, &tm_plan, "", &mut differ);
        assert!(differ.iter().all(|p| p == "log.ckpt.resealDay"), "{differ:?}");
    }

    /// **D91: the editor opens an item where it is ON DISK** (README gap 4396). Past midnight the
    /// App shows `^p1` where the held close files it — the week file — and the editor writes to
    /// disk, where the close is not written and `^p1` is still in Monday's day file.
    #[test]
    fn d91_the_editor_opens_an_item_where_it_is_on_disk() {
        let _env = kernel_env();
        let (_tmp, _g, mut read, mut app) = unfinished_world();
        let p1 = tm_core::model::Id::new("p1");
        let monday = read.tree.get(&p1).map(|i| (i.src.file.clone(), i.src.line)).expect("^p1 before midnight");
        assert_eq!(monday.0, "day/2026-09-07.md");
        assert_eq!(on_disk(&read, &monday.0, monday.1), monday, "nothing held: the location is the disk's");
        let tuesday = DateTime::parse_from_rfc3339("2026-09-08T00:30:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        advance_clock(&mut app, &mut read, tuesday).expect("the date change");
        let shown = app.tree.get(&p1).map(|i| (i.src.file.clone(), i.src.line)).expect("^p1 in the App");
        assert_eq!(shown.0, "week/2026-W37.md", "the App shows the close's tree");
        assert_eq!(on_disk(&read, &shown.0, shown.1), monday, "the editor opens the line ^p1 has on disk");
        let other = app.tree.get(&tm_core::model::Id::new("t3")).map(|i| (i.src.file.clone(), i.src.line)).expect("^t3");
        assert_eq!(on_disk(&read, &other.0, other.1), other, "an untouched file's location is kept");
    }

    /// **The held close's stamp moves no day the kernel plans** (README gap 4400, the W-43 repair —
    /// its second clearing condition, measured). The TUI holds the close stamped at the date change
    /// (00:30); a request built at a later tick of the same day (R3's per-tick replan) would carry
    /// those lines where `tm plan` at that tick (02:30) stamps its own close at 02:30. This takes `tm
    /// plan`'s own request at 02:30, restamps its `demote` and `close` lines at 00:30 — exactly the
    /// request the held close gives at that tick — and asks the kernel both: ONE day, hash and all.
    /// The bite: the two requests differ (the restamp reached the tail), so the equality is the
    /// kernel's, not the harness's.
    #[test]
    fn d91_the_held_closes_stamp_moves_no_day_the_kernel_plans() {
        let _env = kernel_env();
        let (tmp, g, _read, _app) = unfinished_world();
        let plan = g.dir.clone().expect("the plan directory");
        let tz: Tz = "America/Chicago".parse().expect("a zone");
        let later = DateTime::parse_from_rfc3339("2026-09-08T02:30:00-05:00").expect("now").with_timezone(&tz);
        let (plan_text, _) = tm_plans_request(&tmp, &plan, later, "tm-plan-later");
        // Restamped in the request's TEXT (a re-serialised request reorders the checkpoint's keys,
        // which the kernel refuses by name): each line rides the request as an escaped JSON string.
        let mut held_text = plan_text.clone();
        let mut restamped = 0;
        for ev in ["demote", "close"] {
            let at = |t: &str| format!("\\\"t\\\":\\\"2026-09-08T{t}:00-05:00\\\",\\\"ev\\\":\\\"{ev}\\\"");
            restamped += held_text.matches(&at("02:30")).count();
            held_text = held_text.replace(&at("02:30"), &at("00:30"));
        }
        assert_eq!(restamped, 2, "the close's demote and close lines, stamped at the tick");
        assert_ne!(held_text, plan_text, "the restamp reached the request");
        let (at_tick, _) = crate::cli::kernel_bridge::call_text(&plan_text).expect("tm plan's day at 02:30");
        let (at_change, _) = crate::cli::kernel_bridge::call_text(&held_text).expect("the held close's day at 02:30");
        assert!(at_tick["ok"]["plan"].is_object(), "a day: {}", at_tick["ok"]);
        assert_eq!(at_change["ok"]["plan"], at_tick["ok"]["plan"], "the close's stamp moves no day, hash and all");
        // The control: the same kernel reads a stamp in this tail that DOES carry the day — `^t3`'s
        // `start` moved from Monday 23:30 (three hours worked by 02:30, past its 2b estimate) to
        // Tuesday 02:00 (half an hour) moves the running block's rows — so the equality above is a
        // fact about the close's lines, not a tail the kernel does not read.
        let start = |t: &str| format!("\\\"t\\\":\\\"{t}:00-05:00\\\",\\\"ev\\\":\\\"start\\\"");
        assert_eq!(plan_text.matches(&start("2026-09-07T23:30")).count(), 1, "^t3's start rides the request");
        let moved = plan_text.replace(&start("2026-09-07T23:30"), &start("2026-09-08T02:00"));
        let (at_moved, _) = crate::cli::kernel_bridge::call_text(&moved).expect("the day with a later start");
        assert_ne!(at_moved["ok"]["plan"], at_tick["ok"]["plan"], "a start's stamp moves the day");
    }

    /// **A screen mutation on a file the TUI holds closed in memory is refused by name** (README gap
    /// 4505): past midnight `^p1` is in the week file the App shows and in Monday's day file on disk,
    /// and `J`/`K` — which load the disk with no housekeeping, so they write no close first — would
    /// address the wrong lines. A reorder in a file no close changed runs as before, and so does
    /// everything before midnight, when nothing is held.
    #[test]
    fn d91_a_reorder_on_a_held_file_is_refused_and_one_elsewhere_runs() {
        let _env = kernel_env();
        let (_tmp, _g, mut read, mut app) = unfinished_world();
        let reorder = |id: &str, file: &str| queue::Mutation::Reorder {
            id: tm_core::model::Id::new(id),
            file: Some(file.to_string()),
            delta: 1,
        };
        assert_eq!(held_mutation(&read, &reorder("p1", "day/2026-09-07.md")), None, "nothing held before midnight");
        let tuesday = DateTime::parse_from_rfc3339("2026-09-08T00:30:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        advance_clock(&mut app, &mut read, tuesday).expect("the date change");
        let said = held_mutation(&read, &reorder("p1", "week/2026-W37.md")).expect("refused");
        assert!(said.starts_with("^p1: week/2026-W37.md is held in memory as `tm plan`'s housekeeping leaves it"), "{said}");
        assert!(held_mutation(&read, &queue::Mutation::Reorder { id: tm_core::model::Id::new("p1"), file: None, delta: -1 }).is_some());
        let held = read.held.as_ref().expect("a held close");
        let x2 = read.tree.get(&tm_core::model::Id::new("d2")).map(|i| i.src.file.clone()).expect("^d2");
        assert!(!held.docs.contains_key(&x2), "{x2} is a file the close does not change");
        assert_eq!(held_mutation(&read, &reorder("d2", &x2)), None, "a reorder in {x2} runs");
        assert_eq!(held_mutation(&read, &queue::Mutation::Demote(tm_core::model::Id::new("p1"))), None, "a §13 verb writes the close itself");
    }

    /// A date.
    fn tui_date(y: i32, m: u32, d: u32) -> NaiveDate {
        NaiveDate::from_ymd_opt(y, m, d).expect("a date")
    }

    /// **A reload past midnight reads the state as `tm plan` does too** (D84: the
    /// TUI's reload, which runs no housekeeping, collected on the stale date as
    /// its tick did), and **a turn of the clock within a day re-collects
    /// nothing**: the App's candidates and ranking are the load's until the date
    /// changes.
    #[test]
    fn d84_a_reload_past_midnight_reads_the_roll_and_a_tick_within_the_day_recollects_nothing() {
        let _env = kernel_env();
        let (_tmp, g, mut read, mut app) = midnight_world();
        let cands = app.candidates.clone();
        let later = DateTime::parse_from_rfc3339("2026-09-07T23:58:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        advance_clock(&mut app, &mut read, later).expect("a minute");
        assert_eq!((app.today, read.today), (tui_date(2026, 9, 7), tui_date(2026, 9, 7)), "no date change, no re-collection");
        assert_eq!(app.candidates, cands);

        let tuesday = at_str(&g, "2026-09-08T00:30:00-05:00");
        reload(&mut app, &mut read, &tuesday, &Clock::of(&tuesday)).expect("a reload past midnight");
        assert_eq!(app.state.date, Some(tui_date(2026, 9, 8)), "the reload reads the roll");
        assert_eq!(app.state.window, None);
        let on_disk = Ctx::load(&Globals { now: tuesday.now, ..g.clone() }, false).expect("the file");
        assert_eq!(on_disk.state.date, Some(tui_date(2026, 9, 7)), "and writes nothing to `.tm/state.json`");
    }

    /// **D103: the minute tick asks the KERNEL for the day, built from the read its load made, and
    /// reads nothing from the plan directory** (the owner's D103, D38 revised; README gap 4662, the
    /// W-45 switch). §4.3's morning — woken 06:05, arrived 07:00, `^t3` started at 09:00 — with the
    /// TUI opened at 09:05; the plan directory is then moved away, and the loop's own step
    /// ([`advance_clock`]) moves the clock one minute — no wall, no date change, so nothing is
    /// re-collected. The App replans (the reservation runs from `now`, so the day moves with the
    /// minute) with no file to read, and its day is the one `tm plan` asks the kernel for at that
    /// instant over the same files, hash and all. Fork 4748911's tick replanned from the App's own
    /// data the same way, with its own planner, until R3.
    #[test]
    fn d103_the_minute_tick_replans_through_the_kernel_from_the_loads_read() {
        let _env = kernel_env();
        let (tmp, g) = fixture();
        for (when, args) in [
            ("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h10m"][..]),
            ("2026-09-07T07:00:00-05:00", &["arrive", "lounge"][..]),
            ("2026-09-07T09:00:00-05:00", &["start", "^t3", "--energy", "3"][..]),
        ] {
            let argv: Vec<String> = args.iter().map(|a| (*a).to_string()).collect();
            let said = verb(&at_str(&g, when), &argv).expect("a verb of the world");
            assert!(said.ends_with(": ok"), "`tm {}`: {said}", args.join(" "));
        }
        let (mut read, mut app) = load(&at_str(&g, "2026-09-07T09:05:00-05:00")).expect("the TUI opens at 09:05");
        let opened = app.plan.clone();
        let plan = g.dir.clone().expect("the plan directory");
        let away = tmp.path().join("away");
        fs::rename(&plan, &away).expect("the plan directory moved away");
        let minute = DateTime::parse_from_rfc3339("2026-09-07T09:06:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        let ticked = advance_clock(&mut app, &mut read, minute);
        fs::rename(&away, &plan).expect("and back");
        assert!(ticked.expect("a tick with no plan directory to read"), "a new minute changes the App");
        assert!(
            !app.message.as_deref().is_some_and(|m| m.starts_with("plan not refreshed")),
            "the tick planned from the load's read: {:?}",
            app.message
        );
        assert_eq!((app.today, read.today), (tui_date(2026, 9, 7), tui_date(2026, 9, 7)), "no re-collection");
        assert_ne!(app.plan, opened, "the tick replanned: the day runs from 09:06 now");

        let copy = tmp.path().join("tm-plan");
        copy_dir(&plan, &copy);
        let plan_g = Globals { dir: Some(copy), now: Some(minute.fixed_offset()), json: false };
        let plan_ctx = Ctx::load(&plan_g, true).expect("tm plan's load, its housekeeping run");
        let day = crate::cli::kernel_capacity::plan_day(&plan_ctx, false, None).expect("tm plan's day").day;
        assert_eq!(app.plan, day, "the tick's day is the one `tm plan` asks the kernel for at 09:06");
        assert_eq!(app.plan.hash(), day.hash());
    }

    /// **The Queue ranks by the day's own answer, at the load and at every tick** (README gap 4743,
    /// the W-45 repair). The App's candidates, priorities and lookahead — what the Queue,
    /// Necessities and Inbox screens read — are the ones the Today pane's day was planned by: the
    /// TUI opened at 09:05 holds `tm plan`'s ranking at 09:05, and the loop's step to 16:00 holds
    /// `tm plan`'s at 16:00, which is a DIFFERENT ranking (the capacity left shrinks with the day).
    /// Until the repair the load asked a second request for them (`Ctx::priorities`, over
    /// `.tm/state.json` unrolled) and a tick never replaced them, so the Queue ranked by the load's
    /// instant while the Today pane re-ranked every minute.
    #[test]
    fn the_queue_ranks_by_the_days_own_answer_at_every_tick() {
        let _env = kernel_env();
        let (tmp, g) = fixture();
        for (when, args) in [
            ("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h10m"][..]),
            ("2026-09-07T07:00:00-05:00", &["arrive", "lounge"][..]),
        ] {
            let argv: Vec<String> = args.iter().map(|a| (*a).to_string()).collect();
            let said = verb(&at_str(&g, when), &argv).expect("a verb of the world");
            assert!(said.ends_with(": ok"), "`tm {}`: {said}", args.join(" "));
        }
        let ranking_at = |when: &str, name: &str| {
            let copy = tmp.path().join(name);
            copy_dir(g.dir.as_ref().expect("the plan directory"), &copy);
            let at = DateTime::parse_from_rfc3339(when).expect("now");
            let ctx = Ctx::load(&Globals { dir: Some(copy), now: Some(at), json: false }, true).expect("tm plan's load");
            let p = crate::cli::kernel_capacity::plan_day(&ctx, false, None).expect("tm plan's day");
            (p.cands.iter().map(|c| c.id.clone()).collect::<Vec<_>>(), p.prios, p.caps)
        };
        let opened = ranking_at("2026-09-07T09:05:00-05:00", "at-0905");
        let (mut read, mut app) = load(&at_str(&g, "2026-09-07T09:05:00-05:00")).expect("the TUI opens at 09:05");
        let held = |app: &App| (app.candidates.iter().map(|c| c.id.clone()).collect::<Vec<_>>(), app.prios.clone(), app.caps.clone());
        assert_eq!(held(&app), opened, "the opened App ranks by `tm plan`'s answer at 09:05");
        let later = ranking_at("2026-09-07T16:00:00-05:00", "at-1600");
        assert_ne!(later.1, opened.1, "the world must re-rank between 09:05 and 16:00, or this proves nothing");
        let four = DateTime::parse_from_rfc3339("2026-09-07T16:00:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        assert!(advance_clock(&mut app, &mut read, four).expect("the tick"), "a new minute changes the App");
        assert_eq!(held(&app), later, "the ticked App ranks by `tm plan`'s answer at 16:00, as its day is planned by it");
    }

    /// **§9.1's "extend → drops" line is the KERNEL's what-if, and it names what it drops** (README
    /// gap 4631, the W-45 switch): since R3 the box's consequence line is `Planner.overtimeDiff`'s
    /// answer, asked through the App's planner, and the one test that drew a drop — `tui_today_prompts`'
    /// overtime box — shows "nothing" since P46. §4.3's morning with `^t3` (est 2b = 1h) started at
    /// 09:00 and still running: the loop's own step to 10:00 replans and raises §9.1's box, whose drops
    /// are the kernel's answer to one more block on `^t3` — the item the extension leaves no room for —
    /// and that answer is the one `tm plan`'s own request carries at 10:00
    /// (`kernel_capacity::plan_day` with the what-if). Fork 4748911 dropped nothing here (P46: it
    /// refused the overtime block and spent the block elsewhere), as track D's pty drive measured.
    #[test]
    fn the_overtime_box_names_what_the_kernels_what_if_drops() {
        let _env = kernel_env();
        let (tmp, g) = fixture();
        for (when, args) in [
            ("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h10m"][..]),
            ("2026-09-07T07:00:00-05:00", &["arrive", "lounge"][..]),
            ("2026-09-07T09:00:00-05:00", &["start", "^t3", "--energy", "4"][..]),
        ] {
            let argv: Vec<String> = args.iter().map(|a| (*a).to_string()).collect();
            let said = verb(&at_str(&g, when), &argv).expect("a verb of the world");
            assert!(said.ends_with(": ok"), "`tm {}`: {said}", args.join(" "));
        }
        let (mut read, mut app) = load(&at_str(&g, "2026-09-07T09:59:00-05:00")).expect("the TUI opens at 09:59");
        assert!(app.prompt.is_none(), "no prompt before the estimate runs out: {:?}", app.prompt.as_ref().map(app::Prompt::kind));
        let ten = DateTime::parse_from_rfc3339("2026-09-07T10:00:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        advance_clock(&mut app, &mut read, ten).expect("the 10:00 tick");
        let Some(app::Prompt::Overtime(over)) = app.prompt.as_ref() else {
            panic!("§9.1's box is raised at 10:00: {:?}", app.prompt.as_ref().map(app::Prompt::kind));
        };
        assert_eq!((over.id.as_str(), over.elapsed_min), ("t3", 60));
        assert_eq!(over.drops, vec!["Rollback path passes tests (p3)".to_string()], "the kernel's what-if names its drop");

        let plan = g.dir.clone().expect("the plan directory");
        let copy = tmp.path().join("tm-plan");
        copy_dir(&plan, &copy);
        let plan_ctx = Ctx::load(&Globals { dir: Some(copy), now: Some(ten.fixed_offset()), json: false }, true)
            .expect("tm plan's load, its housekeeping run");
        let t3 = tm_core::model::Id::new("t3");
        let planned = crate::cli::kernel_capacity::plan_day(&plan_ctx, false, Some((&t3, 1))).expect("tm plan's request with the what-if");
        let removed = planned.overtime.expect("the what-if was asked").removed;
        assert_eq!(removed.len(), 1, "one item dropped: {removed:?}");
        assert_eq!(
            plan_ctx.tree.get(&removed[0]).map(|i| i.title.as_str()),
            Some("Rollback path passes tests"),
            "the drop the box names is the what-if's"
        );
    }

    /// **The TUI's world at 09:05 with `^t3` running since 09:00** (wake, arrive, start), and the
    /// App's data read from it — for the planner's refusal and fault paths below.
    fn running_data() -> (tempfile::TempDir, Globals, Ctx, AppData) {
        let (tmp, g) = fixture();
        for (when, args) in [
            ("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h10m"][..]),
            ("2026-09-07T07:00:00-05:00", &["arrive", "lounge"][..]),
            ("2026-09-07T09:00:00-05:00", &["start", "^t3", "--energy", "3"][..]),
        ] {
            let argv: Vec<String> = args.iter().map(|a| (*a).to_string()).collect();
            let said = verb(&at_str(&g, when), &argv).expect("a verb of the world");
            assert!(said.ends_with(": ok"), "`tm {}`: {said}", args.join(" "));
        }
        let at = at_str(&g, "2026-09-07T09:05:00-05:00");
        let ctx = Ctx::load_scoped(&at, true, |state, today| tui_scope(Screen::default(), state, today)).expect("the TUI's read");
        let data = data_of(&ctx, PauseCut::default());
        (tmp, g, ctx, data)
    }

    /// **A day the kernel refuses at a tick keeps the last day and says why; a FAULT is held for the
    /// driver** (R3, the W-45 switch; README gap 4712): the App's planner since the body swap can
    /// answer what fork 4748911's total planner never did — a refusal by name, or a response the
    /// codec cannot read. The App is handed a planner that plans the load and then answers the
    /// tick's ask with a refusal, and then with a fault: the refusal leaves the day as it stood and
    /// puts `plan not refreshed: <why>` on the hint line, holding no fault; the fault leaves the day
    /// too and is held for [`App::take_fault`], once.
    #[test]
    fn r3_a_refused_tick_keeps_the_last_day_and_a_fault_is_held_for_the_driver() {
        let _env = kernel_env();
        let (_tmp, _g, _ctx, mut data) = running_data();
        let real = std::mem::replace(&mut data.planner, Box::new(|_: &app::Ask<'_>| unreachable!()));
        let asks = std::sync::atomic::AtomicUsize::new(0);
        data.planner = Box::new(move |ask: &app::Ask<'_>| match asks.fetch_add(1, std::sync::atomic::Ordering::SeqCst) {
            0 => real(ask),
            1 => Err(app::Unplanned { message: "a refusal by name".to_string(), fault: false, cause: None }),
            _ => Err(app::Unplanned { message: "a response the codec cannot read".to_string(), fault: true, cause: None }),
        });
        let mut app = App::new(data).unwrap_or_else(|e| panic!("the load plans: {}", e.message));
        let opened = app.plan.clone();
        assert!(!opened.segments.is_empty(), "the load's day has rows");
        let tz = app.cfg.tz;
        let minute = |m: u32| DateTime::parse_from_rfc3339(&format!("2026-09-07T09:{m:02}:00-05:00")).expect("now").with_timezone(&tz);
        assert!(app.tick(minute(6)), "a new minute");
        assert_eq!(app.plan, opened, "a refused tick keeps the day as it stood");
        assert_eq!(app.message.as_deref(), Some("plan not refreshed: a refusal by name"));
        assert!(app.take_fault().is_none(), "a refusal is not a fault");
        app.tick(minute(7));
        assert_eq!(app.plan, opened, "a faulted tick keeps the day as it stood");
        let fault = app.take_fault().expect("the fault is held for the driver");
        assert_eq!(fault.message, "a response the codec cannot read");
        assert!(app.take_fault().is_none(), "and taken once");
    }

    /// **A day the kernel refuses when the TUI opens is the TUI's to refuse to open on**, with the
    /// planner's reason (README gap 4633, the W-45 switch): `App::new` returns it, as `tm plan`
    /// refuses the same tree, and fork 4748911's total planner never did.
    #[test]
    fn r3_the_tui_refuses_to_open_on_a_day_the_kernel_refuses() {
        let _env = kernel_env();
        let (_tmp, _g, _ctx, mut data) = running_data();
        data.planner = Box::new(|_: &app::Ask<'_>| Err(app::Unplanned { message: "a refusal by name".to_string(), fault: false, cause: None }));
        let refused = App::new(data).err().expect("the App does not open on a refused day");
        assert_eq!((refused.message.as_str(), refused.fault), ("a refusal by name", false));
    }

    /// **A kernel FAULT at the minute tick ends the TUI, loudly** (R3, the W-45 switch; README gap
    /// 4712; AGENTS §5.10): the constructed probe (`TM_KERNEL_FAULT_PROBE`, the real call made and its
    /// bytes replaced) set after the TUI opened, the loop's own step one minute on returns the
    /// kernel's fault — never a day kept quietly — as every verb's seam does.
    #[test]
    fn r3_a_kernel_fault_at_the_minute_tick_ends_the_tui_loudly() {
        let _env = kernel_env();
        let (_tmp, g, _ctx, _data) = running_data();
        let (mut read, mut app) = load(&at_str(&g, "2026-09-07T09:05:00-05:00")).expect("the TUI opens at 09:05");
        let minute = DateTime::parse_from_rfc3339("2026-09-07T09:06:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        std::env::set_var("TM_KERNEL_FAULT_PROBE", "1");
        let ticked = advance_clock(&mut app, &mut read, minute);
        std::env::remove_var("TM_KERNEL_FAULT_PROBE");
        let err = ticked.expect_err("a fault at the tick ends the TUI");
        assert!(err.is_kernel_fault(), "{err}");
    }

    /// **The TUI's clock runs from `--now` only when asked** (README gap 4127):
    /// fixed by default, the real clock with no `--now`, and with
    /// [`CLOCK_RUNS_ENV`] the injected instant plus the time since the TUI started.
    #[test]
    fn the_tuis_clock_is_fixed_unless_it_is_asked_to_run() {
        let from = DateTime::parse_from_rfc3339("2026-09-07T23:59:59-05:00").expect("now");
        let started = Instant::now() - StdDuration::from_secs(90);
        let fixed = Clock { from: Some(from), started, runs: false };
        assert_eq!(fixed.injected(), Some(from));
        let running = Clock { from: Some(from), started, runs: true };
        let ran = running.injected().expect("injected") - from;
        assert!(ran >= chrono::Duration::seconds(90) && ran < chrono::Duration::seconds(120), "{ran}");
        let real = Clock { from: None, started, runs: true };
        assert_eq!(real.injected(), None, "no `--now`: the verbs read the real clock");
    }

    /// Design §11.1, step R13, gap 112: the TUI asks for the scope of the
    /// screen it shows. The Review screen reads every day (`All`); every other
    /// screen reads the ISO week so far and `state.date`'s day (`Dates`); a
    /// missing `state.date` sends the status line to the log's last day, at
    /// any age (`All`).
    #[test]
    fn the_tui_asks_for_the_scope_of_the_screen_it_shows() {
        let d = |s: &str| tm_core::model::parse_date(s).expect("date");
        let state = |date: Option<&str>| tm_core::store::RuntimeState {
            date: date.map(d),
            ..tm_core::store::RuntimeState::default()
        };
        let wednesday = d("2026-09-09");
        for screen in [Screen::Today, Screen::Queue, Screen::Necessities, Screen::Inbox] {
            assert_eq!(
                tui_scope(screen, &state(Some("2026-09-09")), wednesday),
                ReplayScope::Dates { from: d("2026-09-07"), to: wednesday },
                "{screen:?}"
            );
            // A date not yet rolled (a reload without housekeeping) reaches back to it.
            assert_eq!(
                tui_scope(screen, &state(Some("2026-09-04")), wednesday),
                ReplayScope::Dates { from: d("2026-09-04"), to: wednesday },
                "{screen:?}"
            );
            assert_eq!(tui_scope(screen, &state(None), wednesday), ReplayScope::All, "{screen:?}");
        }
        // On a Monday the week so far is today.
        assert_eq!(
            tui_scope(Screen::Today, &state(Some("2026-09-07")), d("2026-09-07")),
            ReplayScope::Dates { from: d("2026-09-07"), to: d("2026-09-07") }
        );
        assert_eq!(tui_scope(Screen::Review, &state(Some("2026-09-09")), wednesday), ReplayScope::All);
        let today = state(Some("2026-09-09"));
        assert_eq!(
            tui_scope(Screen::default(), &today, wednesday),
            tui_scope(Screen::Today, &today, wednesday),
            "the TUI opens on Today"
        );
    }


    /// **The D96 world** — the D91 world (`^p1` left open in Monday's `# Pinned`, `^t3` started at
    /// 23:30 and left running, the TUI opened at 23:50, its housekeeping run) with two more things
    /// `tm plan`'s housekeeping does at Tuesday's first instant: `^a4`'s wait begun 2026-08-31
    /// (`on-event:reply/7d`, so its timeout elapses at Tuesday's date, §5.1) and a call
    /// `at:2026-09-08T00:05/00:20` in the calendar (D61: it begins and ends while `^t3` runs). On
    /// Monday at 23:50 none of the three is due.
    fn housekeeping_world() -> (tempfile::TempDir, Globals, Ctx, App) {
        housekeeping_world_with(|_| {})
    }

    /// [`housekeeping_world`] with `edit` run on the plan directory after its verbs and before the
    /// TUI opens — a hand edit of the world's files (the W-44 land's composition test).
    fn housekeeping_world_with(edit: impl FnOnce(&Path)) -> (tempfile::TempDir, Globals, Ctx, App) {
        let (tmp, g) = fixture();
        let plan = g.dir.clone().expect("the plan directory");
        let backlog = plan.join("backlog.md");
        let text = fs::read_to_string(&backlog).expect("backlog");
        assert_eq!(text.matches("waiting:2026-09-05 ^a4").count(), 1, "{text}");
        fs::write(&backlog, text.replace("waiting:2026-09-05 ^a4", "waiting:2026-08-31 ^a4")).expect("write the backlog");
        let calendar = plan.join("calendar/2026-W37.md");
        let mut text = fs::read_to_string(&calendar).expect("calendar");
        text.push_str("- [ ] 3 Late call         at:2026-09-08T00:05/00:20 ^g7\n");
        fs::write(&calendar, text).expect("write the calendar");
        for (when, args) in [
            ("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h10m"][..]),
            ("2026-09-07T07:00:00-05:00", &["arrive", "lounge"][..]),
            ("2026-09-07T23:30:00-05:00", &["start", "^t3", "--energy", "3"][..]),
        ] {
            let argv: Vec<String> = args.iter().map(|a| (*a).to_string()).collect();
            let said = verb(&at_str(&g, when), &argv).expect("a verb of the world");
            assert!(said.ends_with(": ok"), "`tm {}`: {said}", args.join(" "));
        }
        edit(&plan);
        let (read, app) = load(&at_str(&g, "2026-09-07T23:50:00-05:00")).expect("the TUI opens at 23:50");
        (tmp, g, read, app)
    }

    /// **D96: a TUI past midnight holds EVERY housekeeping write `tm plan` makes at that instant,
    /// in memory, and asks the kernel what `tm plan` asks** (the owner's D96, W-44 track H, README
    /// gap 4393, parity P94). At the date change (Tuesday 00:30, through the loop's own step,
    /// [`advance_clock`]) the TUI runs `tm plan`'s housekeeping through its one body
    /// (`closing::close_in_memory`, then `Ctx::after_the_close`) while it holds:
    ///
    /// * every byte of the plan directory, `.tm/` and its replay cache included, is the same after
    ///   the date change;
    /// * what is held is what `tm plan`'s housekeeping WRITES, file for file and line for line: the
    ///   close's week file, `^a4` back to `[ ]` in the backlog (§5.1), and Tuesday's day file with the
    ///   journal lines of the call's pause and unpause (D61, D65) — and the log lines `demote`,
    ///   `close`, `edit`, `pause`, `unpause`, in `tm plan`'s order;
    /// * the App reads them: `^a4` is open, `^t3` runs unpaused, and the status line says the pause;
    /// * R3's builder over what the TUI holds and over `tm plan`'s own load at 00:30 agree KEY FOR
    ///   KEY but for the replay checkpoint's reseal day — the documents, the log section, the
    ///   candidates and the running block's worked minutes, which read the held pause through a
    ///   replay that writes nothing — and the kernel plans ONE day from the two.
    #[test]
    fn d96_a_tui_past_midnight_holds_every_housekeeping_write_and_asks_what_tm_plan_asks() {
        let _env = kernel_env();
        let (tmp, g, mut read, mut app) = housekeeping_world();
        let plan = g.dir.clone().expect("the plan directory");
        assert!(read.held.is_none(), "nothing is held before midnight");
        let before = tree_bytes(&plan);
        let (state0, replay0) = (read.state.clone(), read.replay.clone());
        let tuesday = DateTime::parse_from_rfc3339("2026-09-08T00:30:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        crate::cli::kernel_bridge::capture_kernel_stderr(true);
        let changed = advance_clock(&mut app, &mut read, tuesday);
        crate::cli::kernel_bridge::capture_kernel_stderr(false);
        assert!(changed.expect("the date change"));
        assert!(tree_bytes(&plan) == before, "the date change wrote nothing under the plan directory");

        let held = read.held.as_ref().expect("the housekeeping is held");
        let evs: Vec<String> = held
            .log
            .lines()
            .map(|l| serde_json::from_str::<serde_json::Value>(l).expect("a log line")["ev"].as_str().unwrap_or_default().to_string())
            .collect();
        assert_eq!(evs, ["demote", "close", "edit", "pause", "unpause"], "{}", held.log);
        let mut paths: Vec<&str> = held.docs.keys().map(String::as_str).collect();
        paths.sort_unstable();
        assert_eq!(paths, ["backlog.md", "day/2026-09-07.md", "day/2026-09-08.md", "week/2026-W37.md"], "the held documents");
        assert!(held.docs["backlog.md"].lines().any(|l| l.starts_with("- [ ]") && l.ends_with("^a4")), "{}", held.docs["backlog.md"]);
        let tuesday_file = &held.docs["day/2026-09-08.md"];
        assert!(tuesday_file.contains("00:05 pause ^t3") && tuesday_file.contains("00:20 unpause ^t3"), "{tuesday_file}");

        assert!(app.tree.get(&tm_core::model::Id::new("a4")).is_some_and(|i| i.state == tm_core::model::State::Todo), "the App reads ^a4 open");
        assert_eq!(app.state.active.as_ref().map(|a| (a.id.as_str(), a.paused)), Some(("t3", false)), "the call has ended");
        assert!(
            app.message.as_deref().is_some_and(|m| m.contains("paused ^t3 for Late call 00:05–00:20")),
            "the status line says the held pause: {:?}",
            app.message
        );

        // A held write that leaves a file's items where they stand does not refuse a reorder there; the close's
        // files, whose items it moved, still do.
        let reorder = |id: &str, file: &str| queue::Mutation::Reorder { id: tm_core::model::Id::new(id), file: Some(file.to_string()), delta: 1 };
        assert_eq!(held_mutation(&read, &reorder("a1", "backlog.md")), None, "^a4's line rewritten in place moves no item");
        assert!(held_mutation(&read, &reorder("p1", "week/2026-W37.md")).is_some(), "the close filed ^p1 into the week");

        // `tm plan` at the same instant, in a copy: its housekeeping WRITTEN.
        let (plan_text, copy) = tm_plans_request(&tmp, &plan, tuesday, "tm-plan");
        for (rel, text) in &held.docs {
            let written = fs::read_to_string(copy.join(rel)).unwrap_or_else(|e| panic!("{rel}: {e}"));
            assert_eq!(&written, text, "{rel}: the TUI holds the file `tm plan` writes, byte for byte");
        }
        let log = fs::read_to_string(copy.join(".tm/log.jsonl")).expect("tm plan's log");
        assert!(log.ends_with(&held.log), "the held lines are the lines `tm plan` appends, in its order");
        let tui_text = crate::cli::kernel_capacity::planner_request(&read, false).expect("the TUI's request");
        let tui: serde_json::Value = serde_json::from_str(&tui_text).expect("JSON");
        let tm_plan: serde_json::Value = serde_json::from_str(&plan_text).expect("JSON");
        let mut differ = Vec::new();
        json_diff(&tui, &tm_plan, "", &mut differ);
        assert_eq!(differ, ["log.ckpt.resealDay"], "key for key, but for the checkpoint `tm plan`'s read resealed");
        // The running block's worked minutes net the held call: 23:30 to 00:30 less 00:05-00:20.
        assert!(tui.to_string().contains("\"workedMin\":45"), "the worked minutes net the held call: {}", tui["planner"]);
        let (tui_resp, _) = crate::cli::kernel_bridge::call_text(&tui_text).expect("the kernel plans the TUI's request");
        let (plan_resp, _) = crate::cli::kernel_bridge::call_text(&plan_text).expect("the kernel plans tm plan's request");
        assert!(tui_resp["ok"]["plan"].is_object(), "a day: {}", tui_resp["ok"]);
        assert_eq!(tui_resp["ok"]["plan"], plan_resp["ok"]["plan"], "one day from the two requests, hash and all");

        // Letting go puts back what was read: the state as read (rolled to Tuesday, as the read rolls it before
        // it holds), the replay as read, and nothing held.
        read.release();
        let mut rolled = state0;
        rolled.roll_to(tui_date(2026, 9, 8));
        assert!(read.held.is_none());
        assert_eq!(read.state, rolled, "release puts back the state as read");
        assert!(read.replay == replay0, "release puts back the replay as read");
    }

    /// **A wall that begins within the day is held at its minute** (the owner's D96, the W-44 repair,
    /// README gap 4553). `^t3` started at 12:00 on Monday and left running, a call at 12:20-12:40 in the
    /// calendar, the TUI opened at 12:10 — and its clock run through the loop's own step
    /// ([`advance_clock`]) with no date change and no file changed:
    ///
    /// * at 12:15 nothing is crossed and nothing is asked (D38: the TUI replans on reload, not on a tick);
    /// * at 12:21 the call has begun while `^t3` runs, and the TUI holds what `tm plan` writes at that
    ///   instant — the `pause` at 12:20 and its journal line — writes nothing, draws `^t3` paused and says
    ///   so, and asks the kernel what `tm plan` asks (key for key but for the checkpoint's reseal day);
    /// * at 12:41 the call has ended, and it holds the `unpause` too.
    ///
    /// Until the repair the hold was asked only at a date change or a reload, so between them the TUI's
    /// timer counted a meeting that began after its last read as work: driven through a pty, `elapsed`
    /// ran on through the call while `tm now` at the same instant printed `paused ^m1 for …`.
    #[test]
    fn w44_repair_a_wall_that_begins_within_the_day_is_held_at_its_minute() {
        let _env = kernel_env();
        let (tmp, g) = fixture();
        let plan = g.dir.clone().expect("the plan directory");
        let calendar = plan.join("calendar/2026-W37.md");
        let mut text = fs::read_to_string(&calendar).expect("calendar");
        text.push_str("- [ ] 3 Noon call         at:2026-09-07T12:20/12:40 ^g7\n");
        fs::write(&calendar, text).expect("write the calendar");
        for (when, args) in [
            ("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h10m"][..]),
            ("2026-09-07T07:00:00-05:00", &["arrive", "lounge"][..]),
            ("2026-09-07T12:00:00-05:00", &["start", "^t3", "--energy", "3"][..]),
        ] {
            let argv: Vec<String> = args.iter().map(|a| (*a).to_string()).collect();
            let said = verb(&at_str(&g, when), &argv).expect("a verb of the world");
            assert!(said.ends_with(": ok"), "`tm {}`: {said}", args.join(" "));
        }
        let (mut read, mut app) = load(&at_str(&g, "2026-09-07T12:10:00-05:00")).expect("the TUI opens at 12:10");
        let tz = app.cfg.tz;
        let at = |s: &str| DateTime::parse_from_rfc3339(s).expect("now").with_timezone(&tz);
        let before = tree_bytes(&plan);

        assert!(!app.crosses_a_wall(at("2026-09-07T12:15:00-05:00")), "nothing is crossed by 12:15");
        assert!(advance_clock(&mut app, &mut read, at("2026-09-07T12:15:00-05:00")).expect("12:15"));
        assert!(read.held.is_none(), "a minute that crosses no wall asks nothing");

        assert!(app.crosses_a_wall(at("2026-09-07T12:21:00-05:00")), "the call began at 12:20");
        crate::cli::kernel_bridge::capture_kernel_stderr(true);
        let changed = advance_clock(&mut app, &mut read, at("2026-09-07T12:21:00-05:00"));
        crate::cli::kernel_bridge::capture_kernel_stderr(false);
        assert!(changed.expect("12:21"));
        assert!(tree_bytes(&plan) == before, "the hold wrote nothing under the plan directory");
        let held = read.held.as_ref().expect("the wall's pause is held");
        let evs: Vec<String> = held
            .log
            .lines()
            .map(|l| serde_json::from_str::<serde_json::Value>(l).expect("a log line")["ev"].as_str().unwrap_or_default().to_string())
            .collect();
        assert_eq!(evs, ["pause"], "{}", held.log);
        assert!(held.docs.get("day/2026-09-07.md").is_some_and(|t| t.contains("12:20 pause ^t3")), "the journal line is held");
        assert_eq!(app.state.active.as_ref().map(|a| (a.id.as_str(), a.paused)), Some(("t3", true)), "^t3 is drawn paused");
        assert!(
            app.message.as_deref().is_some_and(|m| m.contains("paused ^t3 for Noon call 12:20–12:40")),
            "the status line says the held pause: {:?}",
            app.message
        );
        let (plan_text, _copy) = tm_plans_request(&tmp, &plan, at("2026-09-07T12:21:00-05:00"), "tm-plan-1221");
        let tui: serde_json::Value =
            serde_json::from_str(&crate::cli::kernel_capacity::planner_request(&read, false).expect("the TUI's request")).expect("JSON");
        let tm_plan: serde_json::Value = serde_json::from_str(&plan_text).expect("JSON");
        let mut differ = Vec::new();
        json_diff(&tui, &tm_plan, "", &mut differ);
        differ.retain(|k| k != "log.ckpt.resealDay");
        assert!(differ.is_empty(), "the TUI asks what `tm plan` asks at 12:21: {differ:?}");

        assert!(advance_clock(&mut app, &mut read, at("2026-09-07T12:41:00-05:00")).expect("12:41"));
        assert!(tree_bytes(&plan) == before, "nothing written at the call's end either");
        let held = read.held.as_ref().expect("the call's marks are held");
        assert_eq!(held.log.lines().filter(|l| l.contains("\"ev\":\"unpause\"")).count(), 1, "{}", held.log);
        assert_eq!(app.state.active.as_ref().map(|a| a.paused), Some(false), "the call has ended");
    }

    /// **D96 is one catch-up from the files as read, at every date change and every reload** — never
    /// a second set of housekeeping stacked on the first: across a second midnight the held `edit` of
    /// `^a4` is asked again (one line, stamped at Wednesday's instant), and a reload past midnight holds
    /// the same. And with nothing to hold, nothing is held.
    #[test]
    fn d96_the_housekeeping_is_held_once_from_the_files_as_read() {
        let _env = kernel_env();
        let (_tmp, g, mut read, mut app) = housekeeping_world();
        let plan = g.dir.clone().expect("the plan directory");
        let before = tree_bytes(&plan);
        let tz = app.cfg.tz;
        let wednesday = DateTime::parse_from_rfc3339("2026-09-09T00:30:00-05:00").expect("now").with_timezone(&tz);
        let tuesday = DateTime::parse_from_rfc3339("2026-09-08T00:30:00-05:00").expect("now").with_timezone(&tz);
        assert!(advance_clock(&mut app, &mut read, tuesday).expect("Tuesday"));
        assert!(advance_clock(&mut app, &mut read, wednesday).expect("Wednesday"));
        assert!(tree_bytes(&plan) == before, "nothing written across two midnights");
        let held = read.held.as_ref().expect("held");
        let edits: Vec<serde_json::Value> = held
            .log
            .lines()
            .map(|l| serde_json::from_str::<serde_json::Value>(l).expect("a log line"))
            .filter(|e| e["ev"] == "edit")
            .collect();
        assert_eq!(edits.len(), 1, "one timeout, not one per midnight: {}", held.log);
        assert!(edits[0]["t"].as_str().is_some_and(|t| t.starts_with("2026-09-09T00:30")), "{}", edits[0]);
        // A reload is a fresh read of the directory (a file changed), whose replay may reseal the derived
        // cache as any read does (D13); no housekeeping write is made — every other byte stands.
        let g_wed = at(&g, wednesday);
        reload(&mut app, &mut read, &g_wed, &Clock::of(&g_wed)).expect("a reload past midnight");
        let uncached = |t: std::collections::BTreeMap<String, Vec<u8>>| {
            t.into_iter().filter(|(rel, _)| !rel.starts_with(".tm/cache/")).collect::<std::collections::BTreeMap<_, _>>()
        };
        assert!(uncached(tree_bytes(&plan)) == uncached(before), "no housekeeping written by the reload");
        let again = read.held.as_ref().expect("the reload holds the housekeeping");
        assert_eq!(again.log.lines().filter(|l| l.contains("\"ev\":\"edit\"")).count(), 1, "{}", again.log);
    }

    /// **With nothing to hold, nothing is held** (D96): a reload within Monday, before the call, the
    /// timeout and the close are due, leaves `read.held` empty — the context reads the disk as it is,
    /// and the editor and the screen mutations address the disk's lines.
    #[test]
    fn d96_with_nothing_to_hold_nothing_is_held() {
        let _env = kernel_env();
        let (_tmp, g, mut read, mut app) = housekeeping_world();
        let monday = DateTime::parse_from_rfc3339("2026-09-07T23:55:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        let g_mon = at(&g, monday);
        reload(&mut app, &mut read, &g_mon, &Clock::of(&g_mon)).expect("a reload within the day");
        assert!(read.held.is_none(), "an empty hold is let go");
        assert_eq!(app.state.active.as_ref().map(|a| (a.id.as_str(), a.paused)), Some(("t3", false)));
    }


    /// **The W-44 land's composition: the held housekeeping (D96, track H) over a break the clock
    /// meets AHEAD of where it was logged (D94, track K), spelled without `actual_min` (D95, track
    /// H), reads ONE number.** [`housekeeping_world`] with one hand-edited line inserted before
    /// `^t3`'s `start` at 23:30: a `break` stamped 23:35, planned 10 minutes, no `actual_min` — a
    /// clock behind the log (README gaps 4361, 4360). Past midnight (Tuesday 00:30) the TUI holds
    /// the close, `^a4`'s timeout and the call's pause/unpause as before, and:
    ///
    /// * its request and `tm plan`'s at the same instant agree key for key but for the reseal day,
    ///   and the kernel plans one day from the two;
    /// * the running block's worked minutes are 35 — 23:30 to 00:30, less the planned-only break
    ///   (23:35-23:45) and the held call (00:05-00:20) — read so by the request the TUI sends
    ///   (`workedMin`), by the host's union over the held log (`Replay::running_worked_min`) and by
    ///   the kernel replay's own open block (its `worked_min` and `since`, `Replay.openOf`).
    ///
    /// Without D94 the replay's open block credits the break (45); without D95 the host's union
    /// does not net it (45).
    #[test]
    fn w44_land_the_held_housekeeping_reads_a_planned_only_break_ahead_of_the_clock_one_way() {
        let _env = kernel_env();
        let (tmp, g, mut read, mut app) = housekeeping_world_with(|plan| {
            let path = plan.join(".tm/log.jsonl");
            let text = fs::read_to_string(&path).expect("the log");
            let start = text.find("\"ev\":\"start\"").expect("the start line");
            let at = text[..start].rfind('\n').map_or(0, |i| i + 1);
            let brk = "{\"t\":\"2026-09-07T23:35:00-05:00\",\"ev\":\"break\",\"planned_min\":10}\n";
            fs::write(&path, format!("{}{brk}{}", &text[..at], &text[at..])).expect("write the log");
        });
        let plan = g.dir.clone().expect("the plan directory");
        let before = tree_bytes(&plan);
        let tuesday = DateTime::parse_from_rfc3339("2026-09-08T00:30:00-05:00").expect("now").with_timezone(&app.cfg.tz);
        crate::cli::kernel_bridge::capture_kernel_stderr(true);
        let changed = advance_clock(&mut app, &mut read, tuesday);
        crate::cli::kernel_bridge::capture_kernel_stderr(false);
        assert!(changed.expect("the date change"));
        assert!(tree_bytes(&plan) == before, "the date change wrote nothing under the plan directory");
        let held = read.held.as_ref().expect("the housekeeping is held");
        let evs: Vec<String> = held
            .log
            .lines()
            .map(|l| serde_json::from_str::<serde_json::Value>(l).expect("a log line")["ev"].as_str().unwrap_or_default().to_string())
            .collect();
        assert_eq!(evs, ["demote", "close", "edit", "pause", "unpause"], "{}", held.log);

        let now = tuesday.fixed_offset();
        let host = read.replay.running_worked_min("t3", read.today, now, None);
        let open = read.replay.open_block.as_ref().filter(|b| b.id == "t3").map(|b| b.worked_min + b.since.map_or(0, |s| now.signed_duration_since(s).num_minutes().max(0) as u32));
        assert_eq!((host, open), (Some(35), Some(35)), "the host's union and the replay's open block read ^t3 one way");

        let (plan_text, _copy) = tm_plans_request(&tmp, &plan, tuesday, "tm-plan");
        let tui_text = crate::cli::kernel_capacity::planner_request(&read, false).expect("the TUI's request");
        let tui: serde_json::Value = serde_json::from_str(&tui_text).expect("JSON");
        let tm_plan: serde_json::Value = serde_json::from_str(&plan_text).expect("JSON");
        let mut differ = Vec::new();
        json_diff(&tui, &tm_plan, "", &mut differ);
        assert_eq!(differ, ["log.ckpt.resealDay"], "key for key, but for the checkpoint `tm plan`'s read resealed");
        assert!(tui.to_string().contains("\"workedMin\":35"), "the request's worked minutes: {}", tui["planner"]);
        let (tui_resp, _) = crate::cli::kernel_bridge::call_text(&tui_text).expect("the kernel plans the TUI's request");
        let (plan_resp, _) = crate::cli::kernel_bridge::call_text(&plan_text).expect("the kernel plans tm plan's request");
        assert!(tui_resp["ok"]["plan"].is_object(), "a day: {}", tui_resp["ok"]);
        assert_eq!(tui_resp["ok"]["plan"], plan_resp["ok"]["plan"], "one day from the two requests, hash and all");
    }

    /// Every function of a source file, `(name, body)`, cut at its `fn` lines, `//` comments dropped.
    fn source_bodies(text: &str) -> Vec<(String, String)> {
        let lines: Vec<&str> = text.lines().map(|l| l.find("//").map_or(l, |i| &l[..i])).collect();
        let starts: Vec<(usize, String)> = lines
            .iter()
            .enumerate()
            .filter_map(|(i, l)| {
                let t = l.trim_start();
                let rest = ["pub(crate) fn ", "pub(super) fn ", "pub fn ", "fn "].iter().find_map(|p| t.strip_prefix(p))?;
                Some((i, rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect()))
            })
            .collect();
        starts
            .iter()
            .enumerate()
            .map(|(n, (i, name))| {
                let end = starts.get(n + 1).map_or(lines.len(), |(j, _)| *j);
                (name.clone(), lines[*i + 1..end].join("\n"))
            })
            .collect()
    }

    /// The binary's own functions `body` (in source file `file`, relative to `src/`) calls, resolved the
    /// ways the binary calls one: bare (`name(`, a function of the same file), by a module path
    /// (`super::day::name(`, `crate::cli::day::name(`, `day::name(`: that module's file), or as a method of
    /// the context (`Ctx::name(`, `ctx.name(`, `cx.name(`, and `self.name(` inside `cli/ctx.rs`) — and not a
    /// method of any other value (`.insert(` on a map is not the binary's `insert`). Each as `(file, name)`.
    fn callees(file: &str, body: &str, defined: &std::collections::BTreeSet<(String, String)>) -> Vec<(String, String)> {
        let ident = |c: char| c.is_alphanumeric() || c == '_';
        let mut out = Vec::new();
        for (i, _) in body.match_indices('(') {
            let before = &body[..i];
            let name: String = before.chars().rev().take_while(|c| ident(*c)).collect::<Vec<_>>().into_iter().rev().collect();
            if name.is_empty() {
                continue;
            }
            let head = &before[..before.len() - name.len()];
            let target = if let Some(path) = head.strip_suffix("::") {
                let module: String = path.chars().rev().take_while(|c| ident(*c)).collect::<Vec<_>>().into_iter().rev().collect();
                match module.as_str() {
                    "Ctx" => Some("cli/ctx.rs".to_string()),
                    "" => None,
                    m => ["cli/", "tui/", ""].iter().map(|d| format!("{d}{m}.rs")).find(|f| defined.contains(&(f.clone(), name.clone()))),
                }
            } else if let Some(recv) = head.strip_suffix('.') {
                let r: String = recv.chars().rev().take_while(|c| ident(*c)).collect::<Vec<_>>().into_iter().rev().collect();
                let lone = !recv[..recv.len() - r.len()].ends_with(|c: char| ident(c) || c == '.');
                match r.as_str() {
                    "ctx" | "cx" if lone => Some("cli/ctx.rs".to_string()),
                    "self" if lone && file == "cli/ctx.rs" => Some("cli/ctx.rs".to_string()),
                    _ => None,
                }
            } else if head.ends_with(|c: char| ident(c)) {
                None
            } else {
                Some(file.to_string())
            };
            if let Some(t) = target {
                if defined.contains(&(t.clone(), name.clone())) {
                    out.push((t, name));
                }
            }
        }
        out
    }

    /// **The class, read off the code** (the owner's D96, README gap 4393): what `tm plan`'s
    /// housekeeping writes, and that the TUI holds every bit of it.
    ///
    /// * `Ctx::load_with` — every verb's housekeeping — runs the automatic close and then
    ///   `Ctx::after_the_close` (the waiting timeouts and the wall marks), and the TUI's read runs the
    ///   close in memory (`closing::close_in_memory`) and THE SAME `after_the_close`, holding.
    /// * Every function the CLI holds a disk write in — a `.store.` call that writes, over every source
    ///   file of the binary — is out of reach of `after_the_close` (the closure of the calls its body
    ///   makes, over the functions those files define), so every write `after_the_close` makes goes
    ///   through `Ctx::writes`, `Ctx::append_line` or `Ctx::save_state`, which answer into the hold;
    ///   and the one rebase of the undo stack it reaches (`dayfile::note_underneath`) is behind the hold.
    #[test]
    fn d96_every_housekeeping_write_goes_through_the_hold() {
        let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut bodies: Vec<(String, String, String)> = Vec::new();
        let mut stack = vec![src.clone()];
        while let Some(dir) = stack.pop() {
            for e in fs::read_dir(&dir).expect("a source directory").flatten() {
                let p = e.path();
                if p.is_dir() {
                    stack.push(p);
                } else if p.extension().is_some_and(|x| x == "rs") {
                    let rel = p.strip_prefix(&src).expect("inside").display().to_string();
                    let text = fs::read_to_string(&p).expect("a source file");
                    // The tests of a file are not the binary: cut at its test module.
                    let text = text.split("#[cfg(test)]").next().unwrap_or_default().to_string();
                    for (name, body) in source_bodies(&text) {
                        bodies.push((rel.clone(), name, body));
                    }
                }
            }
        }
        let body_of = |file: &str, name: &str| -> String {
            let hits: Vec<&String> = bodies.iter().filter(|(f, n, _)| f == file && n == name).map(|(_, _, b)| b).collect();
            assert_eq!(hits.len(), 1, "{file}: {name}");
            hits[0].clone()
        };
        let load_with = body_of("cli/ctx.rs", "load_with");
        let defined: std::collections::BTreeSet<(String, String)> = bodies.iter().map(|(f, n, _)| (f.clone(), n.clone())).collect();
        let named = |b: &str, file: &str, name: &str| callees(file, b, &defined).contains(&(file.to_string(), name.to_string()))
            || callees("cli/ctx.rs", b, &defined).iter().any(|(_, n)| n == name);
        assert!(
            named(&load_with, "cli/closing.rs", "auto_close") && callees("cli/ctx.rs", &load_with, &defined).contains(&("cli/ctx.rs".to_string(), "after_the_close".to_string())),
            "tm plan's housekeeping is the automatic close and after_the_close"
        );
        let tui = body_of("tui/mod.rs", "read_as_tm_plan");
        let tui_calls = callees("tui/mod.rs", &tui, &defined);
        for want in [("cli/closing.rs", "close_in_memory"), ("cli/ctx.rs", "hold_begin"), ("cli/ctx.rs", "after_the_close")] {
            assert!(tui_calls.contains(&(want.0.to_string(), want.1.to_string())), "the TUI's read calls {want:?}: {tui_calls:?}");
        }

        // The writers: a function whose body writes through the store directly.
        let writes = [".store.write_", ".store.append", ".store.ensure_file", ".store.modify_", ".store.save_state", ".store.insert_line",
            ".store.remove_line", ".store.move_line", ".store.replace_generated", ".store.delete_file", "fs::write("];
        let writers: Vec<(String, String)> = bodies
            .iter()
            .filter(|(_, _, b)| writes.iter().any(|w| b.contains(w)))
            .map(|(f, n, _)| (f.clone(), n.clone()))
            .collect();
        assert!(writers.iter().any(|(f, n)| f == "cli/ctx.rs" && n == "save_state"), "the scan sees a writer: {writers:?}");

        // The closure of `after_the_close`'s calls, each call resolved to its file.
        let root = ("cli/ctx.rs".to_string(), "after_the_close".to_string());
        let mut reached: std::collections::BTreeSet<(String, String)> = [root.clone()].into();
        let mut work = vec![root];
        while let Some((f, n)) = work.pop() {
            for (_, _, b) in bodies.iter().filter(|(bf, bn, _)| *bf == f && *bn == n) {
                for c in callees(&f, b, &defined) {
                    if reached.insert(c.clone()) {
                        work.push(c);
                    }
                }
            }
        }
        let has = |f: &str, n: &str| reached.contains(&(f.to_string(), n.to_string()));
        for (f, n) in [("cli/ctx.rs", "resolve_timeouts"), ("cli/day.rs", "stop_the_timer_at_walls"), ("cli/dayfile.rs", "note_underneath"),
            ("cli/dayfile.rs", "note"), ("cli/dayfile.rs", "ensure"), ("cli/kernel_bridge.rs", "tree_refusal"), ("cli/ctx.rs", "append_line"),
            ("cli/ctx.rs", "settle"), ("cli/ctx.rs", "save_state")] {
            assert!(has(f, n), "{f}:{n} is reached from after_the_close: {reached:?}");
        }
        // `save_state` writes the disk unless the context holds, `reload` reads it unless it holds, and
        // `note_underneath` rebases the undo stack unless it holds; every other writer is out of reach.
        let held_first = |file: &str, name: &str, write: &str| {
            let b = body_of(file, name);
            let (h, w) = (b.find("holding()"), b.find(write));
            assert!(h.is_some() && h < w, "{name}: the hold is asked before {write}");
        };
        held_first("cli/ctx.rs", "save_state", ".store.save_state");
        held_first("cli/ctx.rs", "reload", "replay_with");
        held_first("cli/dayfile.rs", "note_underneath", "rebase_underneath");
        // `tz_table::wire_for` writes the zone table's cache — D13's derived cache, under `.tm/cache/` — and
        // only when it is absent or of another zone; the TUI's own opening read has written it before any hold.
        let stray: Vec<&(String, String)> = writers
            .iter()
            .filter(|w| reached.contains(*w))
            .filter(|w| !(w.0 == "cli/ctx.rs" && w.1 == "save_state") && !(w.0 == "cli/tz_table.rs" && w.1 == "wire_for"))
            .collect();
        assert!(stray.is_empty(), "a housekeeping write that does not go through the hold: {stray:?}");
    }
}
