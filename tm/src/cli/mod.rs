//! The `tm` command line: every verb of tm-spec-v1.md §13.
//!
//! # API overview
//!
//! * [`Cli`] — the clap derive root: the global `--json` (§13: every verb
//!   accepts it), `--dir <plan dir>` and the hidden `--now <RFC3339>` that
//!   makes every verb deterministic in tests (§17.2: clocks are injected).
//! * [`Command`] — one variant per §13 verb.
//! * [`main`] — parse, dispatch, map the result to §13's exit codes:
//!   `0` ok, `1` error, `2` validation problems (`tm check`), `3` a write
//!   conflict (§1.3).
//! * The verbs themselves live next door: [`init`], [`day`] (the clock verbs
//!   of §9), [`planning`] (`plan`, `now`), [`items`] (the file verbs of §6.3
//!   and §13), [`lifecycle`] (`close`, `review`, `sync-cal`, `model`, `log`,
//!   `check`, `undo`, `tui`), with [`render`] turning a `DayPlan` into the
//!   generated day section and the day-bar SVG and [`dayfile`] keeping §4.3's
//!   day-file front matter and `## Log`.
//!
//! Housekeeping: every verb but `init`, `check`, `log`, `undo` and `tui`
//! loads the plan directory through [`ctx::Ctx::load`], which first runs the
//! §6.3 auto-close ("`tm close` runs automatically on the first command after
//! the period ends") and flips `[?]` items whose `on-event:` timeout has
//! elapsed back to `[ ]` (§5.1).

pub mod ctx;
pub mod day;
pub mod dayfile;
pub mod ghost;
pub mod init;
pub mod items;
pub mod lifecycle;
pub mod out;
pub mod planning;
pub mod render;
pub mod undo;

use std::path::PathBuf;

use chrono::DateTime;
use clap::{Args, Parser, Subcommand, ValueEnum};
use tm_core::model::Period;

use ctx::Globals;
use out::CliError;

/// `tm` — a personal planner whose database is Markdown (§0).
#[derive(Debug, Parser)]
#[command(name = "tm", version, about = "tm — personal planner (spec v1.0)")]
pub struct Cli {
    /// Machine-readable output (§13: every verb accepts it).
    #[arg(long, global = true)]
    pub json: bool,
    /// The plan directory (default: found by walking up from the working
    /// directory; `$TM_DIR` overrides).
    #[arg(long, global = true, value_name = "DIR")]
    pub dir: Option<PathBuf>,
    /// The instant to run at, RFC 3339 (tests; default: the real clock).
    #[arg(long, global = true, hide = true, value_name = "RFC3339")]
    pub now: Option<String>,
    /// The verb.
    #[command(subcommand)]
    pub command: Command,
}

/// A period argument (`day`, `week`, `month`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum PeriodArg {
    /// One day.
    Day,
    /// One ISO week.
    Week,
    /// One calendar month.
    Month,
}

impl From<PeriodArg> for Period {
    fn from(p: PeriodArg) -> Period {
        match p {
            PeriodArg::Day => Period::Day,
            PeriodArg::Week => Period::Week,
            PeriodArg::Month => Period::Month,
        }
    }
}

/// Every §13 verb.
#[derive(Debug, Subcommand)]
pub enum Command {
    /// Create a plan directory: config, CLAUDE.md, skills, hooks, files.
    Init(InitArgs),
    /// Record the wake time (§10.1 `wake`).
    Wake(WakeArgs),
    /// Set the location, sync the calendar, compute window and budget (§8.1).
    Arrive(ArriveArgs),
    /// Plan today (or the week), and write the day file's generated section.
    Plan(PlanArgs),
    /// The current block and the next three segments.
    Now,
    /// Start a block on an item.
    Start(StartArgs),
    /// Finish the running block (or an item, retro).
    Done(DoneArgs),
    /// Extend the running block.
    Extend(ExtendArgs),
    /// Stop the running block; the remainder re-competes.
    Stop,
    /// Take a break.
    Break(BreakArgs),
    /// An interruption began.
    Interrupt,
    /// The interruption ended.
    Resume,
    /// Pause or unpause the running block's timer.
    Pause,
    /// Report energy 0–5 (§8.5's posterior).
    Energy(EnergyArgs),
    /// Attribute an idle gap (§9.2).
    Idle(IdleArgs),
    /// Add a line to a file.
    Add(AddArgs),
    /// Edit fields of an item, byte-faithfully.
    Edit(EditArgs),
    /// Move an item between horizon files (§6.3).
    #[command(name = "move")]
    MoveItem(MoveArgs),
    /// Move an item to position N of its section (rank = line order, §7.4).
    Rank(RankArgs),
    /// Demote a week item to the month's `# Demoted` (§6.3).
    Demote(IdArgs),
    /// Bring a demoted item back into a horizon (§6.3).
    Readopt(ReadoptArgs),
    /// Drop an item (`[~]`).
    Drop(IdArgs),
    /// Record a named event: resolves `on-event:` and `after:event:` (§5.1).
    Event(EventArgs),
    /// Skip today's instance of a routine (§5.3).
    Skip(SkipArgs),
    /// Routine instance verbs.
    Routine(RoutineArgs),
    /// Close a period (§6.3).
    Close(CloseArgs),
    /// Sync the calendar feeds into `calendar/` (§15).
    #[command(name = "sync-cal")]
    SyncCal,
    /// Day, week or month review (§11, §12.4).
    Review(ReviewArgs),
    /// The learned model (§8.5).
    Model(ModelArgs),
    /// Read the log (§10.1).
    Log(LogArgs),
    /// Undo the last state change (§13).
    Undo,
    /// Inbox lines with parse previews (§12.5).
    Triage,
    /// Validate the tree (§1.3); exit 2 when it has errors.
    Check(CheckArgs),
    /// The terminal UI (§12).
    Tui,
}

/// `tm init [dir]`.
#[derive(Debug, Args)]
pub struct InitArgs {
    /// Where to create the tree (default: `--dir`, else `./plan`).
    pub dir: Option<PathBuf>,
    /// Fill the files with the §4.3 example tree instead of guidance.
    #[arg(long)]
    pub example: bool,
    /// Overwrite files that already exist.
    #[arg(long)]
    pub force: bool,
}

/// `tm wake [HH:MM] [--slept 8h10m] [--onset 25m]`.
#[derive(Debug, Args)]
pub struct WakeArgs {
    /// The wake time (default: now).
    pub time: Option<String>,
    /// How long you slept.
    #[arg(long)]
    pub slept: Option<String>,
    /// How long it took to fall asleep.
    #[arg(long)]
    pub onset: Option<String>,
}

/// `tm arrive [lounge|home|<name>]`.
#[derive(Debug, Args)]
pub struct ArriveArgs {
    /// Where you are (default: the last location, else `lounge`).
    pub loc: Option<String>,
    /// The arrival time (default: now).
    #[arg(long)]
    pub at: Option<String>,
}

/// `tm plan [--week] [--allow-home] [--diff] [--explain ^id]`.
#[derive(Debug, Args)]
pub struct PlanArgs {
    /// The week's capacity grid instead of today's plan (§8.4).
    #[arg(long)]
    pub week: bool,
    /// Do not cap slot energy at `home_max_ci` (§8.2 step 3).
    #[arg(long = "allow-home")]
    pub allow_home: bool,
    /// Show what moved since the last plan.
    #[arg(long)]
    pub diff: bool,
    /// Explain one item's priority (§7, §13).
    #[arg(long, value_name = "^ID")]
    pub explain: Option<String>,
}

/// `tm start ^id`.
#[derive(Debug, Args)]
pub struct StartArgs {
    /// The item.
    pub id: String,
    /// Your energy right now, 0–5 (default: ask on a terminal).
    #[arg(long)]
    pub energy: Option<u8>,
}

/// `tm done [--partial] [^id]`.
#[derive(Debug, Args)]
pub struct DoneArgs {
    /// The item (default: the running block; with an id and no block this is
    /// a retro done, §13).
    pub id: Option<String>,
    /// The block is done but the item is not: `est:` keeps the remainder.
    #[arg(long)]
    pub partial: bool,
    /// How it went: 1 fine, 2 hard, 3 collapsed (§8.5).
    #[arg(long)]
    pub went: Option<u8>,
}

/// `tm extend [1b]`.
#[derive(Debug, Args)]
pub struct ExtendArgs {
    /// How much to add (default: one block).
    pub by: Option<String>,
}

/// `tm break [20m] [--where walk]`.
#[derive(Debug, Args)]
pub struct BreakArgs {
    /// How long (default: `config.day.break_min`).
    pub dur: Option<String>,
    /// Where: walk, seat, bed, phone.
    #[arg(long = "where")]
    pub place: Option<String>,
}

/// `tm energy 0-5 [--at HH:MM]`.
#[derive(Debug, Args)]
pub struct EnergyArgs {
    /// The reported level, 0–5.
    pub level: u8,
    /// When (default: now).
    #[arg(long)]
    pub at: Option<String>,
}

/// `tm idle <w|b|t|i|l>`.
#[derive(Debug, Args)]
pub struct IdleArgs {
    /// What the gap was: `w` work, `b` break, `t` routine, `i` interruption,
    /// `l` leak (§9.2).
    pub kind: String,
    /// How long the gap was (default: since the last logged event).
    #[arg(long)]
    pub min: Option<u32>,
}

/// `tm add "<line>" [--to <file>] [--section <name>]`.
#[derive(Debug, Args)]
pub struct AddArgs {
    /// The line, in the §4.1 grammar (the `- [ ] ` prefix is optional).
    ///
    /// `allow_hyphen_values`: a pasted line starts `- [ ] …` (§4.1), which
    /// clap would otherwise read as a flag.
    #[arg(allow_hyphen_values = true)]
    pub line: String,
    /// Where: a path (`week/2026-W37.md`) or a horizon word (`backlog`,
    /// `week`, `month`, `day`, `inbox`, `routines`, `optional`).
    #[arg(long)]
    pub to: Option<String>,
    /// The section heading to append under.
    #[arg(long)]
    pub section: Option<String>,
}

/// `tm edit ^id [k=v …] [--set k=v] [--unset k]`.
#[derive(Debug, Args)]
pub struct EditArgs {
    /// The item.
    pub id: String,
    /// `ci=4`, `est=2b`, `due=…`, `title=…`, `p=2`, or any `key=value`.
    #[arg(value_name = "K=V")]
    pub pairs: Vec<String>,
    /// Set a raw `key:value` token.
    #[arg(long = "set", value_name = "K=V")]
    pub set: Vec<String>,
    /// Remove a `key:` token.
    #[arg(long = "unset", value_name = "KEY")]
    pub unset: Vec<String>,
}

/// `tm move ^id <backlog|month|week|day>`.
#[derive(Debug, Args)]
pub struct MoveArgs {
    /// The item.
    pub id: String,
    /// The destination horizon or file path.
    pub to: String,
    /// The section heading in the destination.
    #[arg(long)]
    pub section: Option<String>,
}

/// `tm rank ^id <n>`.
#[derive(Debug, Args)]
pub struct RankArgs {
    /// The item.
    pub id: String,
    /// 1-based position within its section.
    pub n: usize,
}

/// A verb that takes only an id.
#[derive(Debug, Args)]
pub struct IdArgs {
    /// The item.
    pub id: String,
}

/// `tm readopt ^id [--to week]`.
#[derive(Debug, Args)]
pub struct ReadoptArgs {
    /// The item.
    pub id: String,
    /// The destination horizon (default: this week).
    #[arg(long)]
    pub to: Option<String>,
}

/// `tm event <name> [^id]`.
#[derive(Debug, Args)]
pub struct EventArgs {
    /// The event name.
    pub name: String,
    /// Restrict the resolution to one item.
    pub id: Option<String>,
}

/// `tm skip <routine>`.
#[derive(Debug, Args)]
pub struct SkipArgs {
    /// The routine's name (its title) or an `^id`.
    pub name: String,
}

/// `tm routine done <name> [--min 18]`.
#[derive(Debug, Args)]
pub struct RoutineArgs {
    /// The routine verb.
    #[command(subcommand)]
    pub cmd: RoutineCmd,
}

/// Routine instance verbs.
#[derive(Debug, Subcommand)]
pub enum RoutineCmd {
    /// Mark today's instance done.
    Done {
        /// The routine's name.
        name: String,
        /// How long it took.
        #[arg(long)]
        min: Option<u32>,
    },
}

/// `tm close <day|week|month> [--drop ^id …]`.
#[derive(Debug, Args)]
pub struct CloseArgs {
    /// Which period.
    pub period: PeriodArg,
    /// Drop these items instead of carrying them (month close, §6.3).
    #[arg(long = "drop", value_name = "^ID")]
    pub drop: Vec<String>,
    /// The period to close (default: the current one).
    #[arg(long)]
    pub date: Option<String>,
}

/// `tm review <day|week|month> [--write] [--date …]`.
#[derive(Debug, Args)]
pub struct ReviewArgs {
    /// Which period.
    pub period: PeriodArg,
    /// Write the review into the file's `tm:review` section.
    #[arg(long)]
    pub write: bool,
    /// The period to review (default: the current one).
    #[arg(long)]
    pub date: Option<String>,
}

/// `tm model --fit | --show | --compare`.
#[derive(Debug, Args)]
pub struct ModelArgs {
    /// Refit `.tm/model.json` from the log (§8.5).
    #[arg(long)]
    pub fit: bool,
    /// Print the current model (the default).
    #[arg(long)]
    pub show: bool,
    /// Compare the stored model with a fresh fit.
    #[arg(long)]
    pub compare: bool,
}

/// `tm log --tail 20 | --since 7d | --item ^id`.
#[derive(Debug, Args)]
pub struct LogArgs {
    /// The last N entries (default: 20).
    #[arg(long)]
    pub tail: Option<usize>,
    /// Entries from the last N days (`7d`) or since a date.
    #[arg(long)]
    pub since: Option<String>,
    /// Entries about one item.
    #[arg(long, value_name = "^ID")]
    pub item: Option<String>,
}

/// `tm check [--fix-ids]`.
#[derive(Debug, Args)]
pub struct CheckArgs {
    /// Append a `^id` to every line that lacks one (§17.2).
    #[arg(long = "fix-ids")]
    pub fix_ids: bool,
}

/// Parse, dispatch, and return the process exit code (§13).
pub fn main() -> i32 {
    // A usage error is an error (exit 1), not a validation problem (which is
    // what §13 reserves 2 for); `--help` and `--version` are a success.
    let cli = match Cli::try_parse() {
        Ok(cli) => cli,
        Err(e) => {
            let _ = e.print();
            return if e.use_stderr() { out::EXIT_ERROR } else { 0 };
        }
    };
    let now = match cli.now.as_deref().map(DateTime::parse_from_rfc3339) {
        Some(Ok(t)) => Some(t),
        Some(Err(e)) => {
            CliError::msg(format!("--now: {e}")).report();
            return out::EXIT_ERROR;
        }
        None => None,
    };
    let g = Globals {
        dir: cli.dir.clone(),
        json: cli.json,
        now,
    };
    match run(&g, cli.command) {
        Ok(code) => code,
        Err(e) => {
            e.report();
            e.exit_code()
        }
    }
}

/// Run one verb.
///
/// `pub(crate)` because the TUI's `:` command line runs any §13 verb through
/// exactly this dispatcher (§12: one code path for a keystroke and a verb).
pub(crate) fn run(g: &Globals, cmd: Command) -> Result<i32, CliError> {
    match cmd {
        Command::Init(a) => init::run(g, &a),
        Command::Wake(a) => day::wake(g, &a),
        Command::Arrive(a) => day::arrive(g, &a),
        Command::Plan(a) => planning::plan(g, &a),
        Command::Now => planning::now(g),
        Command::Start(a) => day::start(g, &a),
        Command::Done(a) => day::done(g, &a),
        Command::Extend(a) => day::extend(g, &a),
        Command::Stop => day::stop(g),
        Command::Break(a) => day::take_break(g, &a),
        Command::Interrupt => day::interrupt(g),
        Command::Resume => day::resume(g),
        Command::Pause => day::pause(g),
        Command::Energy(a) => day::energy(g, &a),
        Command::Idle(a) => day::idle(g, &a),
        Command::Add(a) => items::add(g, &a),
        Command::Edit(a) => items::edit(g, &a),
        Command::MoveItem(a) => items::move_item(g, &a),
        Command::Rank(a) => items::rank(g, &a),
        Command::Demote(a) => items::demote(g, &a),
        Command::Readopt(a) => items::readopt(g, &a),
        Command::Drop(a) => items::drop_item(g, &a),
        Command::Event(a) => items::event(g, &a),
        Command::Skip(a) => items::skip(g, &a),
        Command::Routine(a) => items::routine(g, &a),
        Command::Triage => items::triage(g),
        Command::Close(a) => lifecycle::close(g, &a),
        Command::SyncCal => lifecycle::sync_cal(g),
        Command::Review(a) => lifecycle::review(g, &a),
        Command::Model(a) => lifecycle::model(g, &a),
        Command::Log(a) => lifecycle::log(g, &a),
        Command::Undo => lifecycle::undo(g),
        Command::Check(a) => lifecycle::check(g, &a),
        Command::Tui => lifecycle::tui(g),
    }
}
