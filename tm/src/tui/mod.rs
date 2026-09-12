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
use crate::cli::ghost;
use crate::cli::out::CliError;
use crate::cli::{dayfile, undo, Cli, Command};

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
    // `notify` reports absolute, resolved paths; the root may be relative
    // (`--dir ./plan`) or go through a symlink, so the form the events are
    // matched against is the canonical one (see [`is_watched`]).
    let watch_root = root.canonicalize().unwrap_or_else(|_| root.clone());
    let mut app = load(g)?;
    let (watcher, changes) = watch(&root)?;
    install_panic_hook();
    // Panic layer 2 (AGENTS 8.1): while the TUI owns the screen, every
    // kernel call runs with Lean's stderr dup2'd to a pipe, so a runtime
    // backtrace cannot shred the alternate screen — it rides the fault's
    // detail instead, and the fault path below prints it after the terminal
    // is restored.
    crate::cli::kernel_bridge::capture_kernel_stderr(true);
    let mut term = setup()?;
    let result = event_loop(&mut term, &mut app, g, &root, &watch_root, &changes);
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

/// `now` in `cfg.tz`: the injected `--now` when there is one (§17.2: clocks
/// are injected), else the real clock.
fn now_of(g: &Globals, cfg: &Config) -> DateTime<Tz> {
    g.now
        .unwrap_or_else(|| Local::now().fixed_offset())
        .with_timezone(&cfg.tz)
}

/// Read the plan directory into the shape [`App`] wants.
fn data_of(ctx: &Ctx) -> AppData {
    // §12.2/§12.3 read §7's numbers; they are the same pass `tm plan` runs.
    let (cands, prios, caps) = ctx.priorities(false);
    AppData {
        cfg: ctx.cfg.clone(),
        model: ctx.model.clone(),
        state: ctx.state.clone(),
        tree: ctx.tree.clone(),
        log: ctx.log.clone(),
        replay: ctx.replay.clone(),
        arrival: ghost::blocks(ctx),
        files: ctx.files.clone(),
        candidates: cands,
        prios,
        caps,
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
fn event_loop(
    term: &mut Term,
    app: &mut App,
    g: &Globals,
    root: &Path,
    watch_root: &Path,
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
            let message = verb(g, &args)?;
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
            note(g, &text)?;
            reload(app, g)?;
            app.message = Some("note written".to_string());
        }
        Effect::SetLocation(loc) => {
            set_location(g, &loc)?;
            reload(app, g)?;
            app.message = Some(format!("location {loc}"));
        }
        Effect::Mutate(m) => {
            let message = mutate(g, &m)?;
            reload(app, g)?;
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
    Ok(match crate::cli::run(&globals, cli.command) {
        Ok(0) => format!("{name}: ok"),
        Ok(code) => format!("{name}: exit {code}"),
        Err(e) if e.is_kernel_fault() => return Err(e),
        Err(e) => format!("{name}: {e}"),
    })
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

    /// Layer 3, integrated at the TUI's one verb seam: a kernel **fault**
    /// propagates out of [`verb`] as an error — [`run`] then restores the
    /// terminal before it returns, and the caller prints the bug report and
    /// exits 1 — while a kernel *refusal* stays a status-line message and
    /// the session keeps running. The probe is the constructed one
    /// (`TM_KERNEL_FAULT_PROBE`, AGENTS 8.1's named trap): the real kernel
    /// call still runs; only the response bytes are replaced.
    #[test]
    fn a_kernel_fault_propagates_and_a_refusal_stays_a_message() {
        let (_tmp, g) = fixture();
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

    #[test]
    fn a_note_typed_in_the_tui_does_not_block_undo() {
        // §13: `tm undo` restores the file bytes the last verb changed, and
        // refuses with a conflict when the file moved under it. A TUI write
        // outside the recorder is exactly such a move.
        let (_tmp, g) = fixture();
        wake(&g);
        note(&g, "the printer is out of paper").expect("n note");
        crate::cli::run(&g, Command::Undo).expect("undo the note");
        crate::cli::run(&g, Command::Undo).expect("undo the wake underneath it");
    }

    #[test]
    fn a_location_set_in_the_tui_does_not_block_undo() {
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
}
