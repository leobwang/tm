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
//!   the `:` command line accepts any §13 verb for free.
//!
//! Screens 2–5 (§12.2–§12.5) are a separate module set; this file leaves the
//! `mod` list and the screen dispatch marked for them.

pub mod app;
pub mod daybar;
pub mod prompts;
pub mod theme;
pub mod today;
// screens 2-5: added by the queue agent —
//   pub mod queue;  pub mod necessities;  pub mod inbox;

use std::io::{self, IsTerminal, Stdout};
use std::path::{Path, PathBuf};
use std::sync::mpsc::{self, Receiver};
use std::time::{Duration as StdDuration, Instant};

use chrono::{DateTime, Local};
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

use tm_core::config::Config;
use tm_core::log::Event as LogEvent;

use crate::cli::ctx::{resolve_dir, Ctx, Globals};
use crate::cli::out::CliError;
use crate::cli::{dayfile, Cli, Command};

use app::{App, AppData, Effect, Hover};

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
    let mut app = load(g)?;
    let (watcher, changes) = watch(&root)?;
    install_panic_hook();
    let mut term = setup()?;
    let result = event_loop(&mut term, &mut app, g, &root, &changes);
    restore();
    drop(watcher);
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

/// `now` in `cfg.tz`: the injected `--now` when there is one (§17.2: clocks
/// are injected), else the real clock.
fn now_of(g: &Globals, cfg: &Config) -> DateTime<Tz> {
    g.now
        .unwrap_or_else(|| Local::now().fixed_offset())
        .with_timezone(&cfg.tz)
}

/// Read the plan directory into the shape [`App`] wants.
fn data_of(ctx: &Ctx) -> AppData {
    AppData {
        cfg: ctx.cfg.clone(),
        model: ctx.model.clone(),
        state: ctx.state.clone(),
        tree: ctx.tree.clone(),
        log: ctx.log.clone(),
        replay: ctx.replay.clone(),
        now: ctx.now_tz,
    }
}

/// Load the plan directory and plan today (§6.3's auto-close runs first, as
/// for every other verb).
fn load(g: &Globals) -> Result<App, CliError> {
    let ctx = Ctx::load(g, true)?;
    Ok(App::new(data_of(&ctx)))
}

/// Re-read the plan directory into an existing [`App`], keeping the UI state.
fn reload(app: &mut App, g: &Globals) -> Result<(), CliError> {
    let ctx = Ctx::load(g, false)?;
    let mut data = data_of(&ctx);
    data.now = now_of(g, &data.cfg);
    app.adopt(data);
    Ok(())
}

/// Watch `plan/` for changes (§17.2). The watcher must stay alive as long as
/// the receiver, so it is returned too.
fn watch(root: &Path) -> Result<(RecommendedWatcher, Receiver<PathBuf>), CliError> {
    let (tx, rx) = mpsc::channel();
    let mut watcher = notify::recommended_watcher(move |res: notify::Result<notify::Event>| {
        if let Ok(ev) = res {
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

/// True for a path the tree is parsed from: a `.md` file outside `.tm/`,
/// `.git/` and the other dot directories (§2). Our own writes to `.tm/` and
/// to `day/<date>.svg` therefore never trigger a re-parse.
fn is_watched(path: &Path) -> bool {
    if path.extension().is_none_or(|e| e != "md") {
        return false;
    }
    !path
        .components()
        .any(|c| c.as_os_str().to_string_lossy().starts_with('.'))
}

// ---------------------------------------------------------------------------
// The loop
// ---------------------------------------------------------------------------

/// Draw, wait for an event, act, tick — until `q`.
fn event_loop(
    term: &mut Term,
    app: &mut App,
    g: &Globals,
    root: &Path,
    changes: &Receiver<PathBuf>,
) -> Result<(), CliError> {
    let mut due: Option<Instant> = None;
    loop {
        term.draw(|f| today::draw(f, app))
            .map_err(|e| CliError::io("terminal", e))?;
        if app.quit {
            return Ok(());
        }

        if event::poll(POLL).map_err(|e| CliError::io("terminal", e))? {
            let ev = event::read().map_err(|e| CliError::io("terminal", e))?;
            let area = term.size().map_err(|e| CliError::io("terminal", e))?;
            let area = Rect::new(0, 0, area.width, area.height);
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
                perform(term, app, g, root, effect)?;
                if app.quit {
                    return Ok(());
                }
            }
        }

        // §17.2: coalesce a burst of file events into one re-parse.
        while let Ok(path) = changes.try_recv() {
            if is_watched(&path) {
                due = Some(Instant::now() + DEBOUNCE);
                app.message = Some(format!(
                    "{} changed",
                    path.file_name().unwrap_or_default().to_string_lossy()
                ));
            }
        }
        if due.is_some_and(|at| Instant::now() >= at) {
            due = None;
            reload(app, g)?;
        }

        app.tick(now_of(g, &app.cfg));
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
    g: &Globals,
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
            let message = verb(g, &args);
            if interactive {
                resume()?;
            }
            // Either way the verb has printed to the real stdout underneath
            // the UI; a full repaint covers it.
            term.clear().map_err(|e| CliError::io("terminal", e))?;
            reload(app, g)?;
            app.message = Some(message);
        }
        Effect::Editor { file, line } => {
            let message = editor(app, root, &file, line);
            app.message = Some(message);
        }
        Effect::Note(text) => {
            let ctx = Ctx::load(g, false)?;
            ctx.append_event(LogEvent::Note { text: text.clone() })?;
            dayfile::note(&ctx, ctx.today, ctx.now_tz.time(), &format!("note {text}"))?;
            reload(app, g)?;
            app.message = Some("note written".to_string());
        }
        Effect::SetLocation(loc) => {
            let mut ctx = Ctx::load(g, false)?;
            ctx.state.loc = Some(loc.clone());
            ctx.save_state()?;
            ctx.append_event(LogEvent::Loc { loc: loc.clone() })?;
            reload(app, g)?;
            app.message = Some(format!("location {loc}"));
        }
    }
    Ok(())
}

/// Run one §13 verb through the same clap tree and the same dispatcher the
/// command line uses, and describe what happened in one line.
fn verb(g: &Globals, args: &[String]) -> String {
    let argv = std::iter::once("tm".to_string()).chain(args.iter().cloned());
    let cli = match Cli::try_parse_from(argv) {
        Ok(cli) => cli,
        Err(e) => {
            return e
                .to_string()
                .lines()
                .next()
                .unwrap_or("bad command")
                .to_string()
        }
    };
    if matches!(cli.command, Command::Tui) {
        return "already in the TUI".to_string();
    }
    // The TUI's own directory and instant win: `--dir` and `--now` are how
    // *this* session was started.
    let globals = Globals {
        dir: g.dir.clone(),
        json: false,
        now: g.now,
    };
    let name = args.first().cloned().unwrap_or_default();
    match crate::cli::run(&globals, cli.command) {
        Ok(0) => format!("{name}: ok"),
        Ok(code) => format!("{name}: exit {code}"),
        Err(e) => format!("{name}: {e}"),
    }
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
