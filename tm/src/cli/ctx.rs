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
//!   reader refused ([`LogRead`], asked for with the verb's [`ReplayScope`]
//!   through [`Ctx::replay_with`], over [`Ctx::replay_of`], the one reader of
//!   `.tm/log.jsonl`), the
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

use std::collections::{BTreeMap, HashSet};
use std::env;
use std::path::{Path, PathBuf};

use chrono::{DateTime, Datelike, FixedOffset, Local, NaiveDate, NaiveDateTime, NaiveTime};
use chrono_tz::Tz;
use serde::{Deserialize, Serialize};

use tm_core::capacity::{self, EnergyCtx, Slot, UnitCapacity, Wall};
use tm_core::config::Config;
use tm_core::energy::{Model, Posterior};
use tm_core::grammar::ItemLine;
use tm_core::horizon;
use tm_core::log::{Event, Log, LogEntry, LogWarning, Replay};
use tm_core::model::{Id, Item, Loc, Shape, State};
use tm_core::priority::{self, Candidate, Prio};
use tm_core::store::{
    self, FsStore, PlanFiles, RuntimeState, Store, StoreExt, LOG_PATH, MODEL_PATH,
};
use tm_core::tree::Tree;
use tm_core::recur;

use super::kernel_bridge;
use super::kernel_capacity;
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
    /// The lines the reader refused, in file order, each with its 1-based
    /// physical line number.
    pub warnings: Vec<LogWarning>,
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
    /// The lines of `.tm/log.jsonl` the reader refused, from the same call
    /// ([`LogRead::warnings`]). `tm check` names them (the owner's D18 (i));
    /// after the switch they are the kernel's `log.warnings` array
    /// (design §10.2).
    pub log_warnings: Vec<LogWarning>,
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
        Ctx::load_with(g, housekeeping, housekeeping, |_, _| ReplayScope::Hot)
    }

    /// [`Ctx::load`] with the replay asked for in the scope `scope` returns,
    /// given `.tm/state.json` as read and today's date (§11.1).
    pub fn load_scoped(
        g: &Globals,
        housekeeping: bool,
        scope: impl FnOnce(&RuntimeState, NaiveDate) -> ReplayScope,
    ) -> Result<Ctx, CliError> {
        Ctx::load_with(g, housekeeping, housekeeping, scope)
    }

    /// [`Ctx::load`] with housekeeping but without the automatic close — for
    /// `tm close`, whose own kernel call is the close: running the automatic
    /// one first would leave the verb reporting an empty close over a tree it
    /// had just rewritten.
    pub fn load_for_close(
        g: &Globals,
        scope: impl FnOnce(&RuntimeState, NaiveDate) -> ReplayScope,
    ) -> Result<Ctx, CliError> {
        Ctx::load_with(g, true, false, scope)
    }

    fn load_with(
        g: &Globals,
        housekeeping: bool,
        auto_close: bool,
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
        let read = Ctx::replay_with(&store, &cfg, scope)?;

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
            replay: read.replay,
            log_warnings: read.warnings,
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
        let read = Ctx::replay_with(&self.store, &self.cfg, self.scope)?;
        self.replay = read.replay;
        self.log_warnings = read.warnings;
        Ok(())
    }

    /// **The replay a verb family asks for** (design §11.1, step R13): the
    /// [`Replay`] holding every fact `scope` covers, and the lines the reader
    /// refused. Before the switch every scope is [`Ctx::replay_of`], the whole
    /// log; at the switch this body becomes the kernel's answer merged with
    /// the sealed records `scope` names, and no caller changes. With
    /// [`TRACE_SCOPE_ENV`] set it names the scope on stderr.
    pub fn replay_with(store: &FsStore, cfg: &Config, scope: ReplayScope) -> Result<LogRead, CliError> {
        if env::var_os(TRACE_SCOPE_ENV).is_some() {
            eprintln!("replay scope: {scope}");
        }
        Ctx::replay_of(store, cfg)
    }

    /// **The one door to the log** (design §14.3 row R8): the replay of the
    /// whole of `.tm/log.jsonl` as it is on disk now, in `cfg.tz`, and the
    /// lines it refused. A missing file is an empty log; **every** unreadable
    /// line — malformed JSON, an unknown field type, a bad timestamp, or bytes
    /// that are not UTF-8 — is one [`LogWarning`] and nothing else. Only an
    /// I/O failure is an error. Nothing else in `tm/src` or `tm-core/src`
    /// reads `LOG_PATH`: [`Ctx::append_entry`] and `horizon`'s close append to
    /// it. At the switch its body becomes the kernel's `log` call.
    ///
    /// **The file is read as bytes and split before any line is decoded**
    /// ([`tm_core::log::Log::parse_bytes`], `Store::read_bytes`). Reading it
    /// as one `String` made a single bad byte anywhere in the file fail every
    /// verb — `tm check` included, which is precisely the verb the owner's D18
    /// requires to keep working so the bad line can be found. This is design
    /// §17's parity P13 answered on the host side, with the same single
    /// reader: the kernel's column of that row, reached before the switch.
    pub fn replay_of(store: &FsStore, cfg: &Config) -> Result<LogRead, CliError> {
        let bytes = if store.exists(LOG_PATH) {
            store.read_bytes(LOG_PATH)?
        } else {
            Vec::new()
        };
        let log = Log::parse_bytes(&bytes);
        let warnings = log.warnings.clone();
        Ok(LogRead { replay: log.replay(None, cfg.tz), warnings })
    }

    /// **What the undo recorder reads, through the same door** (design §14.3
    /// rows R6 and R8): the log's physical line count on disk now and, when
    /// `after` is given, the entries on the physical lines after it, each with
    /// its line, in file order. The count is exactly
    /// `Ctx::replay_of(..).line_count()`, and the entries are exactly the `(line,
    /// entry)` of `Ctx::replay_of(..).headers_from(after + 1)` (unit test
    /// `the_recorders_tail_is_the_whole_replays`), without replaying the lines
    /// before `after`: a mutating verb used to replay the whole log twice more
    /// for its undo entry (W-3's audit: 4 replays a verb, ≈ 110 ms each on three
    /// years of log). A log with fewer lines than `after` (rewritten under the
    /// verb) falls back to the whole replay. At the switch this body becomes the
    /// kernel's `headersFrom`.
    pub fn log_tail_of(
        store: &FsStore,
        cfg: &Config,
        after: Option<u64>,
    ) -> Result<(u64, Vec<(u64, LogEntry)>), CliError> {
        let bytes = if store.exists(LOG_PATH) {
            store.read_bytes(LOG_PATH)?
        } else {
            Vec::new()
        };
        let count = tm_core::log::physical_line_count(&bytes);
        let Some(after) = after else {
            return Ok((count, Vec::new()));
        };
        let skip = usize::try_from(after).unwrap_or(usize::MAX);
        let start = if skip == 0 {
            Some(0)
        } else {
            bytes.iter().enumerate().filter(|(_, b)| **b == b'\n').nth(skip - 1).map(|(i, _)| i + 1)
        };
        let rows = match start {
            Some(at) => Log::parse_bytes(&bytes[at..])
                .replay(None, cfg.tz)
                .headers_from(1)
                .iter()
                .map(|r| (r.line + after, r.entry.clone()))
                .collect(),
            None => Log::parse_bytes(&bytes)
                .replay(None, cfg.tz)
                .headers_from(after + 1)
                .iter()
                .map(|r| (r.line, r.entry.clone()))
                .collect(),
        };
        Ok((count, rows))
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
            "{}/../tm-core/tests/snapshots/log_ported_facts__{name}.snap",
            env!("CARGO_MANIFEST_DIR")
        );
        let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let body = text.splitn(3, "---\n").nth(2).unwrap_or_else(|| panic!("{path}: no header"));
        serde_json::from_str(body).unwrap_or_else(|e| panic!("{path}: {e}"))
    }

    /// D14 (step R11): the facts nothing reads reach every caller through the
    /// one door. `Ctx::replay_of` over each log on disk gives the same
    /// [`tm_core::log::PortedFacts`] as the replay of the text, and both equal
    /// the values `tm-core/tests/log_ported_facts.rs` pins — so the kernel's
    /// port (T5, the sealed day records) is compared against what the
    /// chokepoint returns, not against a second reading.
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
        for (name, text) in &logs {
            let dir = tempfile::TempDir::new().expect("tempdir");
            std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir");
            std::fs::write(dir.path().join(LOG_PATH), text).expect("write log");
            let store = FsStore::new(dir.path());
            let door = Ctx::replay_of(&store, &cfg).expect("replay_of").replay;
            let direct = Log::parse(text).replay(None, cfg.tz);
            assert_eq!(door.ported_facts(), direct.ported_facts(), "{name}");
            let json = serde_json::to_value(door.ported_facts()).expect("json");
            assert_eq!(json, snapshot_body(name), "{name}: the pinned values");
        }
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
        for (k, text) in texts.iter().enumerate() {
            let dir = tempfile::TempDir::new().expect("tempdir");
            std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir");
            if k > 0 {
                std::fs::write(dir.path().join(LOG_PATH), text).expect("write log");
            }
            let store = FsStore::new(dir.path());
            let whole = Ctx::replay_of(&store, &cfg).expect("replay_of").replay;
            let (count, none) = Ctx::log_tail_of(&store, &cfg, None).expect("count");
            assert_eq!((count, none.len()), (whole.line_count(), 0), "text {k}");
            for after in 0..=whole.line_count() + 2 {
                let (count, rows) = Ctx::log_tail_of(&store, &cfg, Some(after)).expect("tail");
                let want: Vec<(u64, LogEntry)> =
                    whole.headers_from(after + 1).iter().map(|r| (r.line, r.entry.clone())).collect();
                assert_eq!(count, whole.line_count(), "text {k}");
                assert_eq!(rows, want, "text {k}, after {after}");
            }
        }
    }

    /// Step R13: before the switch every scope is the whole log, and each
    /// keeps the facts D14 ports (the switch changes only
    /// `Ctx::replay_with`'s body; §11.1's merge must keep them too).
    #[test]
    fn every_scope_is_the_whole_replay_before_the_switch() {
        let d = |s: &str| NaiveDate::parse_from_str(s, "%Y-%m-%d").expect("date");
        let text = loggen::text(&loggen::log(loggen::Rate::SixtyOne, 30));
        let cfg = Config { tz: chrono_tz::America::Chicago, ..Config::default() };
        let dir = tempfile::TempDir::new().expect("tempdir");
        std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir");
        std::fs::write(dir.path().join(LOG_PATH), &text).expect("write log");
        let store = FsStore::new(dir.path());
        let whole = Ctx::replay_of(&store, &cfg).expect("replay_of").replay;
        for scope in [
            ReplayScope::Hot,
            ReplayScope::Dates { from: d("2026-09-01"), to: d("2026-09-07") },
            ReplayScope::All,
        ] {
            let r = Ctx::replay_with(&store, &cfg, scope).expect("replay_with").replay;
            assert!(r == whole, "{scope}");
            assert_eq!(r.view(), whole.view(), "{scope}");
            assert_eq!(r.ported_facts(), whole.ported_facts(), "{scope}");
        }
    }
}
