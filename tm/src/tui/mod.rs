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
fn data_of(ctx: &Ctx, week_cut: PauseCut) -> Result<AppData, CliError> {
    // §12.2/§12.3 read §7's numbers; they are the same pass `tm plan` runs —
    // the kernel's since stage 5 D10 L8, and the minute replan ranks by them.
    let (cands, prios, caps) = ctx.priorities(false)?;
    Ok(data_with(ctx, cands, prios, caps, week_cut))
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
    let app = App::new(data_of(&ctx, PauseCut::default())?);
    Ok((ctx, app))
}

/// **The plan directory as `tm plan` reads it at the context's instant — in
/// memory**: `.tm/state.json` as its roll leaves it (the owner's D84, W-42
/// track H, README gap 4050, parity P83) and the documents as its automatic
/// close leaves them (the owner's D91, W-43 track H, README gap 4342).
///
/// The CLI's housekeeping rolls the state at the first verb of a new local date
/// (`RuntimeState::roll_to`, `ctx.rs`' `roll_day`) and then runs §6.3's
/// automatic close, and writes both; the TUI reads its plan directory without
/// housekeeping, so past midnight it held the stale state and the unclosed
/// files. It reads the state through the same one rule here, and asks the
/// kernel for the documents the close would leave
/// (`closing::close_in_memory`: the same request, held — the log lines and the
/// stamps too), and writes nothing (D81: nothing writes on a timer);
/// `planwire::plan_date` keeps its meaning, fork `PlanInput::date`. A state of
/// today's date, or of none, is read as it is, and a close that is not due asks
/// nothing.
///
/// Returns a sentence for the status line when the close could not be held — a
/// refusal by name, or a file that could not be read — in which case the TUI
/// plans from the files as they stand, as `tm plan` does after a refused close;
/// a kernel fault is an error.
fn read_as_tm_plan(ctx: &mut Ctx) -> Result<Option<String>, CliError> {
    ctx.state.roll_to(ctx.today);
    match crate::cli::closing::close_in_memory(ctx) {
        Ok(crate::cli::closing::InMemory::Refused(why)) => {
            Ok(Some(format!("the automatic close was refused, so these are the files as they stand: {why}")))
        }
        Ok(_) => Ok(None),
        Err(e) if e.is_kernel_fault() => Err(e),
        Err(e) => Ok(Some(format!("the automatic close could not be asked, so these are the files as they stand: {e}"))),
    }
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

/// **The App drawn from `read`** — the ranking is the kernel's, and a refused
/// capacity request (a file saved half-edited into a tree the kernel cannot
/// load, or a configured value it cannot read, parity P26) keeps the last
/// ranking, adopts the rest, and says so on the status line; a kernel fault
/// still ends the TUI. One body for [`reload`] and [`recollect`]. `said` is a
/// sentence the read itself raised (an automatic close it could not hold, D91),
/// shown when nothing above it is.
fn adopt_read(app: &mut App, read: &Ctx, week_cut: PauseCut, cut_refused: Option<String>, said: Option<String>) -> Result<(), CliError> {
    let (data, refused) = match data_of(read, week_cut.clone()) {
        Ok(data) => (data, None),
        Err(e) if !e.is_kernel_fault() => {
            let data = data_with(read, app.candidates.clone(), app.prios.clone(), app.caps.clone(), week_cut);
            (data, Some(e.to_string()))
        }
        Err(e) => return Err(e),
    };
    app.adopt(data);
    if let Some(why) = refused {
        app.message = Some(format!("priorities not refreshed: {why}"));
    } else if let Some(why) = cut_refused {
        app.message = Some(format!("week grid not refreshed: {why}"));
    } else if let Some(said) = said {
        app.message = Some(said);
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
/// ([`recollect`], D84), then [`App::tick`] moves `now`, replans on a new
/// minute and raises §9's prompts. Returns whether anything changed.
fn advance_clock(app: &mut App, read: &mut Ctx, now: DateTime<Tz>) -> Result<bool, CliError> {
    let dated = now.date_naive() != app.today;
    if dated {
        recollect(app, read, now)?;
    }
    Ok(app.tick(now) || dated)
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

/// **A screen mutation that addresses a file the TUI holds closed in memory is
/// refused by name** (README gap 4505, the W-43 repair; the owner's D91). Past
/// midnight the App's rows are the held close's tree — `^p1` in the week file —
/// while the file on disk still has it in Monday's day file, and the two screen
/// mutations that are not §13 verbs (`J`/`K`, the inbox line) load the disk
/// WITHOUT housekeeping, so neither writes the close first: `J` on `^p1` read
/// NotFound, and `J`/`K` on a week neighbour moved it among lines the disk does
/// not hold. Gap 4396 mapped the editor (`on_disk`) and only the editor; this is
/// the rest of the class — every mutation whose file a held close changed. A §13
/// verb is not refused: its own housekeeping writes the very close the TUI
/// holds, so the file it addresses is the file the App shows. Returns the
/// message, or `None` for a mutation that may run.
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
    let file = files.into_iter().find(|f| held.docs.contains_key(f))?;
    Some(format!(
        "{who}: {file} is held closed in memory past midnight and is not yet on disk (D91) — \
         a verb (`tm plan`) writes the close, and then this reorders it"
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
        assert!(said.starts_with("^p1: week/2026-W37.md is held closed in memory past midnight"), "{said}");
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
}
