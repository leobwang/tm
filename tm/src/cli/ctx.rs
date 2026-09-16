//! One loaded plan directory, and the housekeeping every verb runs first.
//!
//! # API overview
//!
//! * [`Globals`] — the flags every verb shares: `--dir`, `--json`, `--now`.
//!   [`resolve_dir`] implements the search: `--dir`, else `$TM_DIR`, else the
//!   first ancestor of the working directory that looks like a plan root
//!   (`config.toml` plus `.tm/` or a plan file) or has a `plan/` child that
//!   does.
//! * [`Ctx`] — the loaded directory: [`Config`], an [`FsStore`], the parsed
//!   [`PlanFiles`] and their [`Tree`], the log's [`Replay`] and the lines the
//!   log's [`Replay`] ([`LogRead`], asked for with the verb's [`ReplayScope`]
//!   through [`Ctx::replay_with`] — **the kernel**, since the switch, and the
//!   one reader of `.tm/log.jsonl`), the
//!   learned [`Model`] and `.tm/state.json` ([`RuntimeState`]), plus `now` in
//!   both `FixedOffset` (log timestamps) and `cfg.tz` (everything else).
//!   [`Ctx::load`] runs the housekeeping of §6.3 (the automatic close —
//!   one kernel `autoClose` call, [`super::closing::auto_close`], when a
//!   period has ended since `state.closed` or no kernel sweep has vouched
//!   for its stamps yet, [`super::closing::due`]) and §5.1 (waiting items whose
//!   timeout has elapsed) unless the verb opts out, and rolls the day-scoped
//!   fields of `state.json` when the date has moved on ([`roll_day`]).
//!   [`Ctx::load_for_close`] is the same minus the automatic close, for
//!   `tm close`, which *is* the close.
//! * Helpers the verbs share: [`Ctx::append_event`] (§10.1),
//!   [`Ctx::save_state`] (§10.2), [`Ctx::item`] / [`Ctx::line`] /
//!   [`Ctx::write_line`] (byte-faithful edits through
//!   [`tm_core::grammar::ItemLine`]), [`Ctx::hz`] (a [`horizon::Ctx`]),
//!   [`Ctx::walls_today`] / [`Ctx::window`] / [`Ctx::today_slots`] (§8.1,
//!   §8.2 step 3) and [`Ctx::priorities`] (§7 and the §8.4 lookahead, the
//!   kernel's since stage 5 D10 L8).
//! * Sidecars `.tm/` grew for state §10.2 does not model:
//!   [`LAST_PLAN_PATH`] (`tm plan --diff` and the hysteresis roll),
//!   [`ARRIVAL_PLAN_PATH`] (§9's ghost row: the plan as it stood at arrival)
//!   and `.tm/undo.json` (see [`crate::cli::undo`]).

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::env;
use std::path::{Path, PathBuf};

use chrono::{DateTime, Datelike, FixedOffset, Local, NaiveDate, NaiveDateTime, NaiveTime};
use chrono_tz::Tz;
use serde::{Deserialize, Serialize};
use serde_json::value::RawValue;
use serde_json::Value;

use tm_core::capacity::{self, EnergyCtx, Slot, UnitCapacity, Wall};
use tm_core::config::Config;
use tm_core::energy::{Model, Posterior};
use tm_core::grammar::ItemLine;
use tm_core::horizon;
use tm_core::log::{Event, LogEntry, Replay};
use tm_core::model::{Id, Item, Loc, Shape, State};
use tm_core::priority::{self, Candidate, Prio};
use tm_core::store::{
    self, FsStore, PlanFiles, RuntimeState, Store, StoreExt, LOG_PATH, MODEL_PATH,
};
use tm_core::tree::Tree;
use tm_core::recur;

use super::kernel_bridge;
use super::kernel_capacity;
use super::kernel_log;
use super::out::CliError;

/// `.tm/last_plan.json` — the plan `tm plan --diff` compares against and the
/// priorities §7.4's hysteresis reads (`state.json` keeps only *yesterday's*
/// map, so the roll needs to know which day the stored one belongs to).
pub const LAST_PLAN_PATH: &str = ".tm/last_plan.json";
/// `.tm/arrival_plan.json` — the block starts as they stood at `tm arrive`
/// (§12.1's ghost row). [`RuntimeState`] has no field for it.
pub const ARRIVAL_PLAN_PATH: &str = ".tm/arrival_plan.json";

/// The flags every verb shares.
#[derive(Clone, Debug, Default)]
pub struct Globals {
    /// `--dir <plan dir>`.
    pub dir: Option<PathBuf>,
    /// `--json`.
    pub json: bool,
    /// `--now <RFC3339>` (hidden; deterministic tests).
    pub now: Option<DateTime<FixedOffset>>,
}

/// True when `dir` looks like a plan root (§2).
fn is_plan_root(dir: &Path) -> bool {
    dir.join("config.toml").is_file()
        && (dir.join(".tm").is_dir()
            || dir.join("backlog.md").is_file()
            || dir.join("week").is_dir()
            || dir.join("month").is_dir())
}

/// Find the plan directory: `--dir`, else `$TM_DIR`, else the nearest
/// ancestor of the working directory that is a plan root or has a `plan/`
/// child that is one.
pub fn resolve_dir(explicit: Option<&Path>) -> Result<PathBuf, CliError> {
    if let Some(d) = explicit {
        return Ok(d.to_path_buf());
    }
    if let Some(d) = env::var_os("TM_DIR").filter(|v| !v.is_empty()) {
        return Ok(PathBuf::from(d));
    }
    let cwd = env::current_dir().map_err(|e| CliError::io(".", e))?;
    for dir in cwd.ancestors() {
        if is_plan_root(dir) {
            return Ok(dir.to_path_buf());
        }
        let child = dir.join("plan");
        if is_plan_root(&child) {
            return Ok(child);
        }
    }
    Err(CliError::msg(
        "no plan directory found (looked for config.toml next to .tm/, here and in every parent); \
         use --dir <path> or set TM_DIR",
    ))
}

/// Drop the day-scoped fields of `state` when the local date has moved on
/// (§10.2: `date` says which day `window`, `budget` and `last_plan_hash`
/// belong to). Without this the first command of a new day — which need not
/// be `tm wake` or `tm arrive`, since §6.3's auto-close exists precisely for
/// the days you run neither — would plan and rewrite *yesterday's* day file
/// with yesterday's window (§8.1). Returns whether anything changed.
///
/// `active`, `break` and `interrupt` are deliberately left alone: a block
/// started before midnight is still running, and it is `tm wake` that ends
/// the night (§10.1). `tm done`/`tm stop` close them as usual.
fn roll_day(state: &mut RuntimeState, today: NaiveDate) -> bool {
    if !matches!(state.date, Some(d) if d != today) {
        return false;
    }
    state.date = Some(today);
    state.arrival = None;
    state.window = None;
    state.budget = None;
    state.last_plan_hash = None;
    true
}

/// The stored plan behind `--diff` and the hysteresis roll.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(default)]
pub struct StoredPlan {
    /// The day it planned.
    pub date: Option<NaiveDate>,
    /// [`tm_core::planner::DayPlan::hash`].
    pub hash: String,
    /// Every candidate's `p` when it was written (§7.4).
    pub priorities: BTreeMap<Id, u8>,
    /// The timeline, flattened for the diff.
    pub segments: Vec<StoredSegment>,
}

/// One row of a [`StoredPlan`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StoredSegment {
    /// `HH:MM`.
    pub start: String,
    /// `HH:MM`.
    pub end: String,
    /// [`tm_core::planner::SegKind`], lowercased.
    pub kind: String,
    /// The item, when the segment has one.
    pub item: Option<String>,
}

/// **What one read of `.tm/log.jsonl` gives a verb**: the replay, and the
/// lines the reader refused.
///
/// The pair is the shape the kernel's `log` answer already has — `facts`
/// beside `warnings` (design §10.2) — so the switch changes
/// [`Ctx::replay_of`]'s body and not this type. Before the repair the
/// warnings were computed and dropped on the floor, which is why `tm check`
/// could say `no problems` about a log with two unreadable lines in it.
#[derive(Clone, Debug)]
pub struct LogRead {
    /// Every fact the log yields (§10.1).
    pub replay: Replay,
}

/// **One line's header**, as `tm undo`'s recorder reads it (design §14.3 row
/// R6, §11.4): the physical line, the entry's tag and its primary id.
///
/// The wake-attributed day is deliberately **not** here. A tail read decides
/// days from the wakes it can see, and a tail that starts after the day's
/// `wake` would attribute its lines differently from the whole replay; the
/// recorder reads a tag and an id and nothing else, so the field it cannot
/// answer honestly is absent rather than wrong.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogHeader {
    /// The 1-based physical line.
    pub line: u64,
    /// The entry's tag ([`tm_core::log::Event::name`]).
    pub tag: String,
    /// Its primary id, when it has one.
    pub id: Option<String>,
}

/// How much history a verb's [`Replay`] must hold (design §11.1).
///
/// After the switch the kernel's answer covers the open days and the recent
/// window (`Hot`); a wider scope merges the sealed day and window records it
/// names. **Before the switch every scope is the whole log in memory**, but
/// every verb family already asks for its own, so the switch changes only
/// [`Ctx::replay_with`]'s body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReplayScope {
    /// The answer only: today's periods, the auto-close catch-up, id-keyed
    /// facts. Every verb not named below.
    Hot,
    /// The answer plus the day records of `[from − 1, to + 1]` and the window
    /// records of `[from, to]`: a verb that names old dates (`tm log --since`,
    /// `tm close day <date>`, the TUI's week pane).
    Dates {
        /// The first date asked for.
        from: NaiveDate,
        /// The last date asked for.
        to: NaiveDate,
    },
    /// The answer plus every sealed record: the reviews, the model fit,
    /// `tm log --item`, the TUI's Review screen.
    All,
}

impl std::fmt::Display for ReplayScope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReplayScope::Hot => write!(f, "hot"),
            ReplayScope::Dates { from, to } => write!(f, "dates {from}..{to}"),
            ReplayScope::All => write!(f, "all"),
        }
    }
}

/// When set, [`Ctx::replay_with`] writes the scope it was asked for to stderr
/// as `replay scope: <scope>` (the verb-family test reads it).
pub const TRACE_SCOPE_ENV: &str = "TM_TRACE_REPLAY_SCOPE";

/// The named fault of OWNER Q9 (iii) / D18 / parity **P31**: a hand edit no
/// rebuild can window inside the memory gate. Spelled once, because
/// [`Ctx::load_tolerant`] matches on it and `tm check` prints it.
pub const REACH_TOO_FAR: &str = "reachTooFar";

impl ReplayScope {
    /// The kernel's own scope (design §11.1). The two enums are deliberately
    /// separate types: this one is the *verb family's* request, `kernel_log`'s
    /// is the wire's, and only this function relates them.
    fn to_kernel(self) -> kernel_log::Scope {
        match self {
            ReplayScope::Hot => kernel_log::Scope::Hot,
            ReplayScope::Dates { from, to } => kernel_log::Scope::Dates { from, to },
            ReplayScope::All => kernel_log::Scope::All,
        }
    }
}

/// **Why the kernel could not answer for the log**, as a named [`CliError`]
/// (design §10.3, §14.6 item 5: `kernel_bridge::refusal` gains the `log`
/// names).
///
/// [`kernel_log::GenesisError::ReachTooFar`] is the one the *user* can act on,
/// so it is the one spelled out: it names the line, the guard that refused it
/// and how far the rebuild would have had to reach, and it says which verb
/// still works. **The memory cap is never raised to make it go away** (D18);
/// the line is moved or removed instead.
fn genesis_error(e: kernel_log::GenesisError) -> CliError {
    match e {
        kernel_log::GenesisError::ReachTooFar { line, kind, reach, bytes } => {
            let mut detail = serde_json::Map::new();
            detail.insert("refusal".into(), Value::String(REACH_TOO_FAR.into()));
            detail.insert("line".into(), Value::from(line));
            detail.insert("guard".into(), Value::String(kind.clone()));
            detail.insert("reach".into(), Value::from(reach));
            detail.insert("bytes".into(), Value::from(bytes));
            CliError::Kernel(super::out::KernelIssue {
                name: REACH_TOO_FAR.into(),
                message: format!(
                    "{REACH_TOO_FAR}: {LOG_PATH} line {line} cannot be windowed — answering it would \
                     resend {reach} lines ({bytes} bytes), past the memory gate, and the guard that \
                     refused it is {kind}. Move or remove that line; `tm check` still runs and names it"
                ),
                detail,
            })
        }
        kernel_log::GenesisError::Refused(r) => {
            CliError::msg(format!("{LOG_PATH}: the kernel refused the replay ({r:?})"))
        }
        kernel_log::GenesisError::Fault(why) => {
            CliError::Kernel(kernel_bridge::fault_issue(&format!("the log replay: {why}"), ""))
        }
    }
}

/// One loaded plan directory.
pub struct Ctx {
    /// The store over the plan root ([`FsStore::root`] is the directory).
    pub store: FsStore,
    /// `config.toml` (§16).
    pub cfg: Config,
    /// `--json`.
    pub json: bool,
    /// The instant every log event is stamped with.
    pub now: DateTime<FixedOffset>,
    /// The same instant in `cfg.tz` — what the planner works in (§17.2).
    pub now_tz: DateTime<Tz>,
    /// The local date.
    pub today: NaiveDate,
    /// `.tm/state.json` (§10.2).
    pub state: RuntimeState,
    /// Every parsed file.
    pub files: PlanFiles,
    /// The tree over them (§6).
    pub tree: Tree,
    /// The replay of `.tm/log.jsonl` (§10.1) in [`Ctx::scope`], from
    /// [`Ctx::replay_with`].
    pub replay: Replay,
    /// **The named fault the replay refused with**, when this `Ctx` was loaded
    /// tolerantly and the kernel could not window the log (gap 145, D18 (iii)).
    ///
    /// `None` for every ordinary load, because a refusal is then the verb's
    /// error. Only [`Ctx::load_tolerant`] sets it, only `tm check` calls that,
    /// and `tm check` turns it into a named problem — which is the whole of
    /// D18's "every verb **except** `tm check`": the one verb that exists to
    /// find the bad line must survive it.
    ///
    /// The line is carried beside the sentence rather than parsed back out of
    /// it (§5.3: one reader of a fact, not two).
    pub replay_fault: Option<(usize, String)>,
    /// The scope the verb asked its replay for; [`Ctx::reload`] asks again.
    pub scope: ReplayScope,
    /// `.tm/model.json` (§8.5).
    pub model: Model,
    /// Items whose `on-event:` timeout elapsed and went back to `[ ]` (§5.1).
    pub timed_out: Vec<Id>,
}

impl Ctx {
    /// Load the plan directory named by `g`. `housekeeping` runs §6.3's
    /// automatic close and §5.1's waiting timeouts first (every verb but
    /// `init`, `check`, `log`, `undo` and `tui`).
    ///
    /// The replay is asked for in [`ReplayScope::Hot`]; a verb that reads
    /// older history loads through [`Ctx::load_scoped`].
    pub fn load(g: &Globals, housekeeping: bool) -> Result<Ctx, CliError> {
        Ctx::load_with(g, housekeeping, housekeeping, false, |_, _| ReplayScope::Hot)
    }

    /// **[`Ctx::load`] for the one verb that must survive a log no rebuild can
    /// window** (gap 145; OWNER Q9 (iii), D18, parity P31).
    ///
    /// D18 (iii) makes a hand edit beyond the rebuild bound a **named fault**
    /// that fails every verb by name — *except* `tm check`, because `tm check`
    /// is how the offending line is found. The fault reaches the user either
    /// way; what this changes is that here it becomes a
    /// [`Ctx::replay_fault`] and an empty [`Replay`] instead of an error, so
    /// the verb goes on to check the tree and to name the line.
    ///
    /// It tolerates **only** that fault. Every other refusal, and every I/O
    /// failure, is still an error: a `tm check` that answered "no problems"
    /// over a log it could not read would be the exact defect D18 exists to
    /// prevent.
    pub fn load_tolerant(g: &Globals) -> Result<Ctx, CliError> {
        Ctx::load_with(g, false, false, true, |_, _| ReplayScope::Hot)
    }

    /// [`Ctx::load`] with the replay asked for in the scope `scope` returns,
    /// given `.tm/state.json` as read and today's date (§11.1).
    pub fn load_scoped(
        g: &Globals,
        housekeeping: bool,
        scope: impl FnOnce(&RuntimeState, NaiveDate) -> ReplayScope,
    ) -> Result<Ctx, CliError> {
        Ctx::load_with(g, housekeeping, housekeeping, false, scope)
    }

    /// [`Ctx::load`] with housekeeping but without the automatic close — for
    /// `tm close`, whose own kernel call is the close: running the automatic
    /// one first would leave the verb reporting an empty close over a tree it
    /// had just rewritten.
    pub fn load_for_close(
        g: &Globals,
        scope: impl FnOnce(&RuntimeState, NaiveDate) -> ReplayScope,
    ) -> Result<Ctx, CliError> {
        Ctx::load_with(g, true, false, false, scope)
    }

    fn load_with(
        g: &Globals,
        housekeeping: bool,
        auto_close: bool,
        tolerate: bool,
        scope: impl FnOnce(&RuntimeState, NaiveDate) -> ReplayScope,
    ) -> Result<Ctx, CliError> {
        let dir = resolve_dir(g.dir.as_deref())?;
        if !dir.join(store::CONFIG_PATH).is_file() {
            return Err(CliError::msg(format!(
                "{}: not a plan directory (no config.toml) — run `tm init` first",
                dir.display()
            )));
        }
        let store = FsStore::new(dir.clone());
        let cfg = store.read_config()?;
        let now = g.now.unwrap_or_else(|| Local::now().fixed_offset());
        let now_tz = now.with_timezone(&cfg.tz);
        let today = now_tz.date_naive();
        let mut state = store.load_state()?;
        let scope = scope(&state, today);
        // Gap 145: `tm check` alone loads tolerantly, and only `reachTooFar` is
        // tolerated — see `Ctx::load_tolerant`.
        let (replay, replay_fault) = match Ctx::replay_with(&store, &cfg, now, today, scope) {
            Ok(read) => (read.replay, None),
            Err(CliError::Kernel(issue)) if tolerate && issue.name == REACH_TOO_FAR => {
                let line = issue
                    .detail
                    .get("line")
                    .and_then(Value::as_u64)
                    .and_then(|l| usize::try_from(l).ok())
                    .unwrap_or(1);
                let tz = Ctx::tz_wire(&store, &cfg);
                (Ctx::empty_replay(&cfg, &tz, today)?, Some((line, issue.message)))
            }
            Err(e) => return Err(e),
        };

        if housekeeping && roll_day(&mut state, today) {
            store.save_state(&state)?;
        }

        let files = store.read_tree()?;
        let tree = files.tree();
        let model = store.read_json::<Model>(MODEL_PATH)?.unwrap_or_default();
        let mut cx = Ctx {
            store,
            cfg,
            json: g.json,
            now,
            now_tz,
            today,
            state,
            files,
            tree,
            replay,
            replay_fault,
            scope,
            model,
            timed_out: Vec::new(),
        };
        let mut refused = false;
        if auto_close {
            // Writes, logs, stamps `state.closed` and reloads when it closed
            // anything; a refusal is printed and the verb goes on — but
            // nothing below writes to the tree the kernel just refused.
            refused = super::closing::auto_close(&mut cx)? == super::closing::AutoClosed::Refused;
        }
        if housekeeping {
            cx.timed_out = cx.resolve_timeouts(refused)?;
            if !cx.timed_out.is_empty() {
                cx.reload()?;
            }
        }
        Ok(cx)
    }

    /// Re-read files, tree, log and replay after a write, in the same scope.
    pub fn reload(&mut self) -> Result<(), CliError> {
        self.files = self.store.read_tree()?;
        self.tree = self.files.tree();
        let read = Ctx::replay_with(&self.store, &self.cfg, self.now, self.today, self.scope)?;
        self.replay = read.replay;
        Ok(())
    }

    /// **The replay a verb family asks for** (design §11.1, step R13): the
    /// [`Replay`] holding every fact `scope` covers.
    ///
    /// **This is the switch** (design §14.6 item 1). The body is
    /// [`kernel_log::replay_scoped`]: the Lean kernel derives every replay
    /// fact from `.tm/log.jsonl`, resuming the checkpoint under
    /// `.tm/cache/replay` (D13) and merging the sealed records `scope` names
    /// (§11.1). Until S this delegated to `Ctx::replay_of`, the in-tree Rust
    /// reader, which design §12 has now deleted — **one reader, and it is the
    /// proved one** (D9). No caller's shape changed, which is what made S a
    /// body swap rather than a rewrite.
    ///
    /// `now` is the undo stack's clock, not the replay's: §9.6 pins the tail
    /// at the smallest `UndoEntry.log_line` younger than 14 days, so a reseal
    /// never folds away an entry `tm undo` can still reach. With
    /// [`TRACE_SCOPE_ENV`] set it names the scope on stderr.
    ///
    /// **A missing file is an empty log, and only an I/O failure is an error.**
    /// Every unreadable line — malformed JSON, an unknown field type, a bad
    /// timestamp, or bytes that are not UTF-8 — is a per-line warning the
    /// kernel carries and the verb runs anyway (design §17's parity P13, the
    /// owner's D18 (i)). `tm check` names them through its own read-only sweep
    /// ([`kernel_log::line_warnings`]), because an answer's `warnings` array is
    /// per call.
    pub fn replay_with(
        store: &FsStore,
        cfg: &Config,
        now: DateTime<FixedOffset>,
        today: NaiveDate,
        scope: ReplayScope,
    ) -> Result<LogRead, CliError> {
        if env::var_os(TRACE_SCOPE_ENV).is_some() {
            eprintln!("replay scope: {scope}");
        }
        let bytes = Ctx::log_bytes(store)?;
        let tz = Ctx::tz_wire(store, cfg);
        let pin = kernel_log::max_line_of(
            &store.read_text(super::undo::UNDO_PATH).unwrap_or_default(),
            now,
        );
        let read = kernel_log::replay_scoped(
            store.root(),
            &bytes,
            cfg.tz,
            &tz,
            today,
            scope.to_kernel(),
            pin,
        )
        .map_err(genesis_error)?;
        // CRIT 26: an unwritable or moved cache is a notice, never a failure.
        for notice in &read.notices {
            eprintln!("{notice}");
        }
        Ok(LogRead { replay: read.replay })
    }

    /// The log's bytes as they are on disk now; a missing file is an empty log.
    fn log_bytes(store: &FsStore) -> Result<Vec<u8>, CliError> {
        if store.exists(LOG_PATH) {
            Ok(store.read_bytes(LOG_PATH)?)
        } else {
            Ok(Vec::new())
        }
    }

    /// The zone table the kernel attributes days with (§6.1), from the cache
    /// under the plan root when its key still matches, else probed (D13).
    fn tz_wire(store: &FsStore, cfg: &Config) -> Value {
        super::tz_table::wire_for(Some(&store.root().join(kernel_log::CACHE_DIR)), cfg.tz)
    }

    /// **The empty replay**, for the one verb that answers over a log no
    /// rebuild can window (gap 145, D18 (iii)).
    ///
    /// It is the *kernel's* answer for a log of no lines, not a hand-built
    /// value: §5.3's rule — a second definition of "an empty replay" would be
    /// a second reader of the same concept. It never touches the checkpoint on
    /// disk, because genesis over zero lines seals nothing.
    fn empty_replay(cfg: &Config, tz: &Value, today: NaiveDate) -> Result<Replay, CliError> {
        let want = kernel_log::Want { facts: true, headers_from: None, render: vec![] };
        let policy = kernel_log::Policy { keep_days: kernel_log::KEEP_DAYS, max_line: None };
        let now = today.format("%Y-%m-%d").to_string();
        let g = kernel_log::genesis(&now, tz, &kernel_log::split(&[]), policy, &want)
            .map_err(genesis_error)?;
        let answer = serde_json::json!({
            "lines": g.answer.lines,
            "facts": g.answer.facts.clone().unwrap_or(Value::Null),
            "headers": g.answer.headers.clone(),
        });
        kernel_log::decode_facts(&answer, cfg.tz)
            .map_err(|why| CliError::msg(format!("the kernel's empty replay: {why}")))
    }

    /// **What the undo recorder reads, through the same door** (design §14.3
    /// rows R6 and R8): the log's physical line count on disk now and, when
    /// `after` is given, the entries on the physical lines after it, each with
    /// its line, in file order. The count is exactly
    /// the whole replay's line count, and the headers are exactly the whole
    /// replay's from `after + 1` (design §14.3 row R6), without replaying the
    /// lines before `after`: a mutating verb used to replay the whole log twice
    /// more for its undo entry (W-3's audit: 4 replays a verb, ≈ 110 ms each on
    /// three years of log). A log with fewer lines than `after` (rewritten under
    /// the verb) has no tail and yields none.
    ///
    /// **This is the switch** (design §14.6 item 1): the body is the kernel's
    /// `headersFrom` ([`kernel_log::headers_after`]), which replays the tail
    /// alone from the empty checkpoint and shifts each header's line back into
    /// the whole file's numbering — exactly what the in-tree reader did here
    /// before §12 deleted it.
    pub fn log_tail_of(
        store: &FsStore,
        cfg: &Config,
        today: NaiveDate,
        after: Option<u64>,
    ) -> Result<(u64, Vec<LogHeader>), CliError> {
        let bytes = Ctx::log_bytes(store)?;
        let count = tm_core::log::physical_line_count(&bytes);
        let Some(after) = after else {
            return Ok((count, Vec::new()));
        };
        let tz = Ctx::tz_wire(store, cfg);
        let now = today.format("%Y-%m-%d").to_string();
        let rows = kernel_log::headers_after(&bytes, &now, &tz, after)
            .map_err(|why| CliError::msg(format!("{LOG_PATH}: the kernel could not read the tail ({why})")))?
            .into_iter()
            .map(|(line, tag, id)| LogHeader { line, tag, id })
            .collect();
        Ok((count, rows))
    }

    /// **The payload of the lines a verb selected** (design §11.4 step 3): the
    /// raw bytes of each line of `lines`, read from `.tm/log.jsonl` by physical
    /// line number and parsed.
    ///
    /// `tm log` is the one verb that shows a line's payload rather than its
    /// header. §11.4 gives it this order — select headers, then read the bytes
    /// of the selected lines, then render them — and this is that read: the
    /// selection comes from [`Replay::view`], and only the selected lines are
    /// parsed. A line the reader refuses has no [`tm_core::log::ViewRow`]
    /// either, so it cannot be selected and is simply absent from the map.
    ///
    /// **This is the switch** (§11.4 step 4): the body is the kernel's `render`
    /// op ([`kernel_log::render_lines`]), which returns each line's canonical
    /// rendering — **as the line's own bytes** (D22) — and its display, from the
    /// same bytes on disk. Until S the bytes were parsed here with
    /// `LogEntry::parse`, which design §12 has deleted.
    pub fn entries_at(
        store: &FsStore,
        cfg: &Config,
        today: NaiveDate,
        lines: &[u64],
    ) -> Result<BTreeMap<u64, (Box<RawValue>, String)>, CliError> {
        let mut out = BTreeMap::new();
        if lines.is_empty() {
            return Ok(out);
        }
        let bytes = Ctx::log_bytes(store)?;
        let wanted: BTreeSet<u64> = lines.iter().copied().collect();
        let tz = Ctx::tz_wire(store, cfg);
        let now = today.format("%Y-%m-%d").to_string();
        out.extend(
            kernel_log::render_lines(&bytes, &now, &tz, lines).map_err(|why| {
                CliError::msg(format!("{LOG_PATH}: the kernel could not render the selected lines ({why})"))
            })?,
        );
        // **Every asked line comes back, or this read fails by name.** The
        // paragraph above is an invariant, not a hope: `Log::parse_bytes`
        // pushes a line into `Log::lines` — and so gives it a `ViewRow` —
        // in exactly the case this loop inserts it, off the same bytes. But
        // these are two reads of one file at two instants, so a writer that
        // truncates or rewrites `.tm/log.jsonl` between them can take away a
        // line the selection has already made. Unguarded, that line was
        // absent from `--json`'s `entries` while `log_human` still printed
        // its header from the row, and the two outputs disagreed in silence.
        // Naming it costs nothing on a file nobody rewrites mid-command,
        // which is why no behaviour moves; at S the kernel's `render` op
        // answers the same lines and this guard goes with the body.
        if out.len() != wanted.len() {
            let missing = lines.iter().find(|l| !out.contains_key(l)).copied().unwrap_or(0);
            return Err(CliError::msg(format!(
                "{LOG_PATH} changed while this command was reading it: line {missing} did not \
                 read back; run the command again"
            )));
        }
        Ok(out)
    }

    /// A [`horizon::Ctx`] over the current snapshot (§6.3).
    pub fn hz(&self) -> horizon::Ctx<'_> {
        horizon::Ctx::new(&self.store, &self.files, &self.tree, self.now).with_replay(&self.replay)
    }

    /// Append one event to `.tm/log.jsonl` (§10.1).
    pub fn append_event(&self, ev: Event) -> Result<(), CliError> {
        self.append_entry(&LogEntry::new(self.now, ev))
    }

    /// Append one already-timestamped entry.
    pub fn append_entry(&self, entry: &LogEntry) -> Result<(), CliError> {
        let line = format!("{}\n", entry.to_json()?);
        self.store.append_text(LOG_PATH, &line)?;
        Ok(())
    }

    /// Write `.tm/state.json` (§10.2).
    pub fn save_state(&self) -> Result<(), CliError> {
        self.store.save_state(&self.state)?;
        Ok(())
    }

    /// The key an id-ish argument names: `^t3`, `t3` or the title of an
    /// id-less routine/optional line.
    pub fn key(arg: &str) -> Id {
        Id::new(arg.trim().trim_start_matches('^'))
    }

    /// The item behind an argument, or a "no such item" error.
    pub fn item(&self, id: &Id) -> Result<&Item, CliError> {
        self.tree
            .get(id)
            .ok_or_else(|| CliError::NotFound(id.clone()))
    }

    /// The item's line, tokenized for a byte-faithful edit (§4.1).
    pub fn line(&self, id: &Id) -> Result<ItemLine, CliError> {
        Ok(self.item(id)?.line().clone())
    }

    /// Replace the item's line with `line`'s text (§1.3).
    pub fn write_line(&self, id: &Id, line: &ItemLine) -> Result<(), CliError> {
        self.store.write_line(id, &line.to_string())?;
        Ok(())
    }

    /// `cfg.day.block_min`.
    pub fn block_min(&self) -> u32 {
        self.cfg.block_min()
    }

    /// The current location (§8.2 step 3's `runtime.loc`).
    pub fn loc(&self) -> Loc {
        self.state
            .loc
            .as_deref()
            .and_then(|s| Loc::parse(s).ok())
            .unwrap_or(Loc::Lounge)
    }

    /// Today's wake: `state.wake`, else the `wake` event of the day, else the
    /// fallback [`Model::wake_or_expected`] owns — the weekday's expected
    /// arrival (§8.4, §16 `[expected]`). This is the resolution `planner.rs`
    /// runs, in the same order and through the same fallback, so a plan and
    /// the verbs that cut their own slots read one wake.
    pub fn wake_time(&self) -> NaiveTime {
        self.model
            .wake_or_expected(self.logged_wake(), self.today.weekday(), &self.cfg)
    }

    /// The wake today actually has: `state.wake`, else the `wake` event of the
    /// day — what [`Ctx::wake_time`] falls back from, and what the capacity
    /// request sends as `wake` (the kernel applies the same fallback).
    pub fn logged_wake(&self) -> Option<NaiveTime> {
        self.state.wake.or_else(|| {
            self.replay
                .day(self.today)
                .and_then(|d| d.wake)
                .map(|t| t.with_timezone(&self.cfg.tz).time())
        })
    }

    /// Today's wake instant in `cfg.tz`.
    pub fn wake_dt(&self) -> DateTime<Tz> {
        capacity::local_dt(self.cfg.tz, self.today, self.wake_time())
    }

    /// Minutes slept last night, when `tm wake` recorded them.
    pub fn slept_min(&self) -> Option<u32> {
        self.replay.day(self.today).and_then(|d| d.slept_min)
    }

    /// A local time on today's date, in `cfg.tz`.
    pub fn at(&self, t: NaiveTime) -> DateTime<Tz> {
        capacity::local_dt(self.cfg.tz, self.today, t)
    }

    /// Today's walls: every open Interval item that overlaps the day, with
    /// its `buffer:` in front (§8.2 step 1).
    pub fn walls_today(&self) -> Vec<Wall> {
        self.walls_on(self.today)
    }

    /// The walls of one date.
    pub fn walls_on(&self, date: NaiveDate) -> Vec<Wall> {
        let mut out = Vec::new();
        for item in self.tree.iter() {
            if item.state.is_closed() {
                continue;
            }
            let id = Tree::key_of(item);
            let Shape::Interval { start, end } = self.tree.effective_shape(&id) else {
                continue;
            };
            let start = match item.buffer {
                Some(b) => start - chrono::Duration::minutes(i64::from(b.as_minutes())),
                None => start,
            };
            if start.date() > date || end.date() < date {
                continue;
            }
            out.push((self.instant(start), self.instant(end)));
        }
        out.sort_by_key(|(a, _)| *a);
        out
    }

    /// A naive local datetime as an instant in `cfg.tz` (DST-safe, §17.2).
    pub fn instant(&self, dt: NaiveDateTime) -> DateTime<Tz> {
        capacity::local_dt(self.cfg.tz, dt.date(), dt.time())
    }

    /// §8.1's working window and block budget: what `tm arrive` stored *for
    /// today*, else the formula from the arrival (or now). A window stored on
    /// an earlier day is ignored — its times belong to that day, not this one
    /// (see [`roll_day`], which normally clears it first).
    pub fn window(&self) -> (DateTime<Tz>, DateTime<Tz>, u32) {
        let today = self.state.date == Some(self.today);
        match (self.state.window, self.state.budget) {
            (Some((from, to)), Some(budget)) if today => (self.at(from), self.at(to), budget),
            _ => {
                let arrival = self
                    .state
                    .arrival
                    .filter(|_| today)
                    .map_or(self.now_tz, |t| self.at(t));
                let (end, budget) = capacity::window_and_budget(arrival, &self.walls_today(), &self.cfg);
                (arrival, end, budget)
            }
        }
    }

    /// Today's remaining slots with their predicted energy (§8.2 step 3).
    pub fn today_slots(&self, allow_home: bool) -> Vec<Slot> {
        let (start, end, _) = self.window();
        let from = start.max(self.now_tz);
        if end <= from {
            return Vec::new();
        }
        let walls = self.walls_today();
        let cut = capacity::cut_slots(from, end, &walls, &self.cfg);
        let obs: Vec<_> = self.replay.energy_on(self.today).cloned().collect();
        let posterior = Posterior::from_observations(&obs, self.cfg.tz, &self.cfg);
        let ectx = EnergyCtx::new(&self.model, &self.cfg, &posterior, self.wake_dt(), self.loc())
            .with_slept(self.slept_min())
            .with_blocks_done(self.replay.blocks_done(self.today))
            .with_allow_home(allow_home);
        capacity::energize(&cut.slots, &ectx)
    }

    /// §7: the candidates, their priorities and the first days of the capacity
    /// lookahead they were computed against — **the kernel's** since stage 5 D10
    /// L8 ([`kernel_capacity::rank`]: the exact mixture, step 3's EDF pass, the
    /// floor pass, §7.1–§7.4), in exact units. The candidates' facts are the
    /// host's (kernel/README.md gap 113). A configured value the kernel cannot
    /// read fails the verb by file and key (parity P26).
    pub fn priorities(&self, allow_home: bool) -> Result<(Vec<Candidate>, Vec<Prio>, Vec<UnitCapacity>), CliError> {
        let cands = priority::collect_candidates(
            &self.tree,
            &self.replay,
            &self.cfg,
            &self.model,
            self.today,
            self.now_tz,
        );
        let yesterday = self.hysteresis_input();
        let answer = kernel_capacity::rank(self, &cands, &yesterday, allow_home)?;
        Ok((cands, answer.prios, answer.days))
    }

    /// Yesterday's `p` per item (§7.4). `state.priorities_yesterday` holds it
    /// once the day has rolled; before the first plan of a new day the last
    /// stored plan is the previous day's, so its priorities are the ones to
    /// compare against.
    pub fn hysteresis_input(&self) -> BTreeMap<Id, u8> {
        let stored = self.last_plan().unwrap_or_default();
        match stored.date {
            Some(d) if d == self.today => self.state.priorities_yesterday.clone(),
            Some(_) => stored.priorities,
            None => self.state.priorities_yesterday.clone(),
        }
    }

    /// `.tm/last_plan.json`, if it is readable.
    pub fn last_plan(&self) -> Option<StoredPlan> {
        self.store.read_json::<StoredPlan>(LAST_PLAN_PATH).ok().flatten()
    }

    /// Write `.tm/last_plan.json`.
    pub fn save_last_plan(&self, plan: &StoredPlan) -> Result<(), CliError> {
        self.store.write_json(LAST_PLAN_PATH, plan)?;
        Ok(())
    }

    /// The number of `plan` events already logged today (§10.1
    /// `replans_today`).
    pub fn plans_today(&self) -> u32 {
        self.replay.day(self.today).map(|d| d.plans).unwrap_or(0)
    }

    /// §5.1: `[?]` items whose `on-event:` timeout has elapsed go back to
    /// `[ ]` with `est:` reset and `waiting:` removed. Returns what changed.
    ///
    /// **Only on a tree the kernel loads whole** (the owner's D6: a dangling
    /// or cyclic `@parent` refuses the whole tree). `refused` says the
    /// automatic close ahead of this was refused, which settles it without a
    /// second call; otherwise, when some timeout has elapsed, one kernel call
    /// with no commands ([`kernel_bridge::apply`], which writes nothing
    /// without a change) checks the tree first. A refusal skips every
    /// timeout, writes nothing and logs nothing, and is named on stderr — so a
    /// verb that then refuses the same tree has written nothing either
    /// (kernel/README.md "Stage 4 final, repair", defect 1: before this, a
    /// typo'd parent on the example tree's Monday rewrote `^a4` and created
    /// the log ahead of a refusal that said nothing was written). A kernel
    /// fault still fails the verb.
    fn resolve_timeouts(&mut self, refused: bool) -> Result<Vec<Id>, CliError> {
        let mut expired_ids = Vec::new();
        for id in self.tree.waiting_ids() {
            let Some(item) = self.tree.get(&id) else {
                continue;
            };
            if recur::waiting_state(item, &self.replay, self.today, &self.cfg).is_some_and(|w| w.expired) {
                expired_ids.push(id);
            }
        }
        if expired_ids.is_empty() || refused {
            return Ok(Vec::new());
        }
        match kernel_bridge::apply(self, &[]) {
            Ok(_) => {}
            Err(CliError::Kernel(issue)) if !issue.is_fault() => {
                if !kernel_bridge::capturing_kernel_stderr() {
                    eprintln!(
                        "tm: the waiting timeouts (§5.1) were not applied, so nothing was written; \
                         they run again on the next command. {}",
                        issue.message
                    );
                }
                return Ok(Vec::new());
            }
            Err(e) => return Err(e),
        }
        let mut changed = Vec::new();
        for id in expired_ids {
            let Some(item) = self.tree.get(&id) else {
                continue;
            };
            let mut line = item.line().clone();
            recur::on_event_arrived(item).apply(&mut line)?;
            self.store.write_line(&id, &line.to_string())?;
            self.append_event(Event::Edit {
                id: id.to_string(),
                field: "state".to_string(),
                from: State::Waiting.as_str().to_string(),
                to: State::Todo.as_str().to_string(),
            })?;
            changed.push(id);
        }
        Ok(changed)
    }

    /// Every id already used in the tree — the uniqueness set new ids are
    /// drawn against (§17.2).
    pub fn taken_ids(&self) -> HashSet<String> {
        self.files.ids()
    }
}

#[cfg(test)]
#[path = "../../tests/support/loggen.rs"]
#[allow(dead_code)]
mod loggen;

#[cfg(test)]
mod tests {
    use super::*;

    /// The body of an `insta` JSON snapshot: everything after its `---`
    /// header.
    fn snapshot_body(name: &str) -> serde_json::Value {
        let path = format!(
            "{}/tests/snapshots/log_ported_facts__{name}.snap",
            env!("CARGO_MANIFEST_DIR")
        );
        let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let body = text.splitn(3, "---\n").nth(2).unwrap_or_else(|| panic!("{path}: no header"));
        serde_json::from_str(body).unwrap_or_else(|e| panic!("{path}: {e}"))
    }

    /// **`tm log`'s two outputs cannot disagree about which lines they carry.**
    /// `Ctx::entries_at` is the second host-side read of `.tm/log.jsonl` in one
    /// `tm log` (the first is the replay's), and until the guard it enforces
    /// the doc comment's invariant it dropped a line it could not read back:
    /// `--json`'s `entries` lost it while `log_human` still printed its header
    /// from the row. A line the reader never accepted has no `ViewRow` and is
    /// never asked for, so this fires only on a log rewritten mid-command —
    /// and then it is named, not swallowed.
    #[test]
    fn a_line_that_does_not_read_back_is_named_not_dropped() {
        let dir = tempfile::TempDir::new().expect("tempdir");
        std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir");
        // Real lines, from the generator the other tests here use: a line the
        // reader refuses never becomes a `ViewRow` and so is never asked for,
        // which is the invariant this guard rests on.
        let gen = loggen::text(&loggen::log(loggen::Rate::SixtyOne, 1));
        let first: Vec<&str> = gen.lines().take(2).collect();
        assert_eq!(first.len(), 2, "the generator gives at least two lines");
        let text = format!("{}\n", first.join("\n"));
        std::fs::write(dir.path().join(LOG_PATH), &text).expect("write log");
        let store = FsStore::new(dir.path());
        let cfg = Config { tz: chrono_tz::America::Chicago, ..Config::default() };
        let today = NaiveDate::from_ymd_opt(2030, 1, 1).expect("date");

        // The lines the selection can actually make: both come back.
        let got = Ctx::entries_at(&store, &cfg, today, &[1, 2]).expect("both lines read back");
        assert_eq!(got.len(), 2);
        // Nothing asked for, nothing read.
        assert!(Ctx::entries_at(&store, &cfg, today, &[]).expect("no lines").is_empty());

        // A line the file does not hold — what a truncating writer leaves
        // behind between the replay's read and this one.
        let err = Ctx::entries_at(&store, &cfg, today, &[1, 5]).expect_err("line 5 cannot read back");
        let msg = err.to_string();
        assert!(msg.contains("line 5"), "the failure names the line: {msg}");
        assert!(msg.contains(LOG_PATH), "the failure names the file: {msg}");
    }

    /// D14 (step R11): the facts nothing reads reach every caller through the
    /// one door — **the kernel's, since S**. `Ctx::replay_with` over each log on
    /// disk gives the [`tm_core::log::PortedFacts`] that
    /// `tm/tests/log_ported_facts.rs` pins.
    ///
    /// **Its comparand is bytes on disk, not a second reader.** Until S this
    /// also compared the chokepoint against `Log::parse(text).replay(..)`;
    /// design §12 deleted that reader, and had this test kept only that arm it
    /// would now be comparing the kernel with itself (README gap 146). The
    /// pinned snapshot is what survives the deletion, and it is the arm that was
    /// always doing the work: the values were measured from the fork's own
    /// reader and committed.
    #[test]
    fn the_chokepoint_returns_the_ported_facts() {
        let corpus = |n: &str| {
            std::fs::read_to_string(format!("{}/../kernel/corpus/logs/{n}.jsonl", env!("CARGO_MANIFEST_DIR")))
                .expect("corpus log")
        };
        let logs = [
            ("three_days", corpus("three-days")),
            ("energy_14d", corpus("energy-14d")),
            ("review_14d", corpus("review-14d")),
            ("malformed", corpus("malformed")),
            ("loggen_1mo_40", loggen::text(&loggen::log(loggen::Rate::Forty, 30))),
            ("loggen_1mo_61", loggen::text(&loggen::log(loggen::Rate::SixtyOne, 30))),
        ];
        let cfg = Config { tz: chrono_tz::America::Chicago, ..Config::default() };
        let (now, today) = late_clock();
        for (name, text) in &logs {
            let dir = tempfile::TempDir::new().expect("tempdir");
            std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir");
            std::fs::write(dir.path().join(LOG_PATH), text).expect("write log");
            let store = FsStore::new(dir.path());
            let door = Ctx::replay_with(&store, &cfg, now, today, ReplayScope::All)
                .expect("replay_with")
                .replay;
            let json = serde_json::to_value(door.ported_facts()).expect("json");
            assert_eq!(json, snapshot_body(name), "{name}: the pinned values");
        }
    }

    /// An instant after every log these tests read, in both shapes the door
    /// wants: `now` is the undo stack's clock and `today` the day the kernel
    /// answers for. Later than every fixture, so no line is future-dated and
    /// every day of every log is a past day.
    fn late_clock() -> (DateTime<FixedOffset>, NaiveDate) {
        let now = DateTime::parse_from_rfc3339("2030-01-01T09:00:00-05:00").expect("instant");
        (now, now.date_naive())
    }

    /// W-3's repair: the recorder's tail read is the whole replay's rows from
    /// the same line, and its count the whole replay's, at every cut of logs
    /// with malformed, blank, CRLF and torn lines.
    #[test]
    fn the_recorders_tail_is_the_whole_replays() {
        let gen = loggen::text(&loggen::log(loggen::Rate::SixtyOne, 2));
        let mut lines: Vec<&str> = gen.lines().collect();
        lines.truncate(60);
        let good = lines.join("\n");
        let torn = &lines[3][..lines[3].len() / 2];
        let texts = [
            String::new(),
            "\n".to_string(),
            format!("{good}\n"),
            good.clone(),
            format!("{}\n\n{}\nnot json\n{}\r\n{}\n", lines[0], lines[1], lines[2], lines[4]),
            format!("{}\n{torn}", lines[0]),
            format!("{}\n{torn}{}\n{}\n", lines[0], lines[5], lines[6]),
            format!("{}\n\u{00e9}\u{0000}\n{}\n", lines[7], lines[8]),
        ];
        let cfg = Config { tz: chrono_tz::America::Chicago, ..Config::default() };
        let (now, today) = late_clock();
        for (k, text) in texts.iter().enumerate() {
            let dir = tempfile::TempDir::new().expect("tempdir");
            std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir");
            if k > 0 {
                std::fs::write(dir.path().join(LOG_PATH), text).expect("write log");
            }
            let store = FsStore::new(dir.path());
            let whole = Ctx::replay_with(&store, &cfg, now, today, ReplayScope::All)
                .expect("replay_with")
                .replay;
            let (count, none) = Ctx::log_tail_of(&store, &cfg, today, None).expect("count");
            assert_eq!((count, none.len()), (whole.line_count(), 0), "text {k}");
            for after in 0..=whole.line_count() + 2 {
                let (count, rows) = Ctx::log_tail_of(&store, &cfg, today, Some(after)).expect("tail");
                let want: Vec<LogHeader> = whole
                    .headers_from(after + 1)
                    .iter()
                    .map(|r| LogHeader { line: r.line, tag: r.tag.clone(), id: r.id.clone() })
                    .collect();
                assert_eq!(count, whole.line_count(), "text {k}");
                assert_eq!(rows, want, "text {k}, after {after}");
            }
        }
    }

    /// Step R13, **turned around at S** (README gap 140's sibling): before the
    /// switch every scope *was* the whole log, because `Ctx::replay_with`
    /// delegated to the one Rust reader and ignored the scope entirely. Since S
    /// each scope is the kernel's own (§11.1) and a narrow one **legitimately**
    /// carries fewer day records — so the old assertion would now be false, and
    /// asserting it would mean the switch had not happened.
    ///
    /// What replaces it is the claim the scopes exist to preserve, and it is
    /// the one that bites: **every scope answers, and every all-time fact is
    /// whole at every scope** (design §8.4's column **A**; gaps 135 and 136).
    /// Those are exactly the facts a narrowing could silently shrink — a
    /// `tm log` total that counted only the scope's rows, or a recurrence
    /// anchor that lost the dates below the horizon.
    ///
    /// The sharper per-scope claim — that each day record a narrow scope *does*
    /// carry is the whole log's — is made where it has a comparand that is not
    /// the kernel: `tm/tests/kernel_log_door.rs`.
    #[test]
    fn every_all_time_fact_is_whole_at_every_scope_after_the_switch() {
        let d = |s: &str| NaiveDate::parse_from_str(s, "%Y-%m-%d").expect("date");
        let text = loggen::text(&loggen::log(loggen::Rate::SixtyOne, 30));
        let cfg = Config { tz: chrono_tz::America::Chicago, ..Config::default() };
        let (now, today) = late_clock();
        let dir = tempfile::TempDir::new().expect("tempdir");
        std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir");
        std::fs::write(dir.path().join(LOG_PATH), &text).expect("write log");
        let store = FsStore::new(dir.path());
        let whole = Ctx::replay_with(&store, &cfg, now, today, ReplayScope::All)
            .expect("replay_with")
            .replay;
        // Not vacuous: the log really does hold the days and the completions
        // the loop below says survive every narrowing.
        assert_eq!(whole.line_count(), text.lines().count() as u64, "the All scope reads every line");
        assert!(whole.days.len() > 7, "the fixture must be wider than one scope: {}", whole.days.len());
        assert!(!whole.done_date_totals.is_empty(), "the fixture logs no completion");
        for scope in [
            ReplayScope::Hot,
            ReplayScope::Dates { from: d("2026-09-01"), to: d("2026-09-07") },
            ReplayScope::All,
        ] {
            let r = Ctx::replay_with(&store, &cfg, now, today, scope).expect("replay_with").replay;
            assert_eq!(r.entry_count(), whole.entry_count(), "{scope}: entryCount is all-time");
            assert_eq!(r.line_count(), whole.line_count(), "{scope}: the line count is the file's");
            assert_eq!(r.done_date_totals, whole.done_date_totals, "{scope}: the done-date totals");
            assert_eq!(r.done_items, whole.done_items, "{scope}: the done items");
            assert_eq!(r.last_done, whole.last_done, "{scope}: the last completion per item");
        }
    }
}
