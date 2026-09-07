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
//!   [`PlanFiles`] and their [`Tree`], the [`Log`] and its [`Replay`], the
//!   learned [`Model`] and `.tm/state.json` ([`RuntimeState`]), plus `now` in
//!   both `FixedOffset` (log timestamps) and `cfg.tz` (everything else).
//!   [`Ctx::load`] runs the housekeeping of §6.3 (auto-close of the last
//!   unclosed day/week/month) and §5.1 (waiting items whose timeout has
//!   elapsed) unless the verb opts out, and rolls the day-scoped fields of
//!   `state.json` when the date has moved on ([`roll_day`]).
//! * Helpers the verbs share: [`Ctx::append_event`] (§10.1),
//!   [`Ctx::save_state`] (§10.2), [`Ctx::item`] / [`Ctx::line`] /
//!   [`Ctx::write_line`] (byte-faithful edits through
//!   [`tm_core::grammar::ItemLine`]), [`Ctx::hz`] (a [`horizon::Ctx`]),
//!   [`Ctx::walls_today`] / [`Ctx::window`] / [`Ctx::today_slots`] (§8.1,
//!   §8.2 step 3) and [`Ctx::priorities`] (§7, the EDF pass over the §8.4
//!   lookahead).
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

use tm_core::capacity::{self, DayCapacity, EnergyCtx, Slot, Wall, WallsByDate};
use tm_core::config::Config;
use tm_core::energy::{Model, Posterior};
use tm_core::grammar::ItemLine;
use tm_core::horizon::{self, ClosedPeriod};
use tm_core::log::{Event, Log, LogEntry, Replay};
use tm_core::model::{Id, Item, Loc, Shape, State};
use tm_core::priority::{self, Candidate, Prio};
use tm_core::store::{
    self, FsStore, PlanFiles, RuntimeState, Store, StoreExt, LOG_PATH, MODEL_PATH,
};
use tm_core::tree::Tree;
use tm_core::recur;

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
    /// `.tm/log.jsonl` (§10.1).
    pub log: Log,
    /// The replay of the whole log.
    pub replay: Replay,
    /// `.tm/model.json` (§8.5).
    pub model: Model,
    /// What the §6.3 auto-close closed on the way in.
    pub closed: Vec<ClosedPeriod>,
    /// Items whose `on-event:` timeout elapsed and went back to `[ ]` (§5.1).
    pub timed_out: Vec<Id>,
}

impl Ctx {
    /// Load the plan directory named by `g`. `housekeeping` runs §6.3's
    /// auto-close and §5.1's waiting timeouts first (every verb but `init`,
    /// `check`, `log`, `undo` and `tui`).
    pub fn load(g: &Globals, housekeeping: bool) -> Result<Ctx, CliError> {
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
        let log = read_log(&store)?;
        let replay = log.replay(None, cfg.tz);

        let mut closed = Vec::new();
        if housekeeping {
            if roll_day(&mut state, today) {
                store.save_state(&state)?;
            }
            closed = horizon::auto_close(&store, &mut state, today, now, Some(&replay))?;
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
            log,
            replay,
            model,
            closed,
            timed_out: Vec::new(),
        };
        if housekeeping {
            cx.timed_out = cx.resolve_timeouts()?;
            if !cx.timed_out.is_empty() || !cx.closed.is_empty() {
                cx.reload()?;
            }
        }
        Ok(cx)
    }

    /// Re-read files, tree, log and replay after a write.
    pub fn reload(&mut self) -> Result<(), CliError> {
        self.files = self.store.read_tree()?;
        self.tree = self.files.tree();
        self.log = read_log(&self.store)?;
        self.replay = self.log.replay(None, self.cfg.tz);
        Ok(())
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
            .ok_or_else(|| CliError::msg(format!("no such item: {}", id.token())))
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

    /// Today's wake instant: `state.wake`, else the expected arrival for the
    /// weekday (§16 `[expected]`).
    pub fn wake_time(&self) -> NaiveTime {
        self.state
            .wake
            .unwrap_or_else(|| *self.cfg.expected.arrival.get(self.today.weekday()))
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

    /// Walls per date over `days` days from today (the §8.4 lookahead's
    /// input).
    pub fn walls_by_date(&self, days: u32) -> WallsByDate {
        let mut map: WallsByDate = BTreeMap::new();
        for i in 0..i64::from(days) {
            let Some(date) = self.today.checked_add_signed(chrono::Duration::days(i)) else {
                break;
            };
            let walls = self.walls_on(date);
            if !walls.is_empty() {
                map.insert(date, walls);
            }
        }
        map
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

    /// §7: the candidates, their priorities and the capacity lookahead they
    /// were computed against.
    pub fn priorities(&self, allow_home: bool) -> (Vec<Candidate>, Vec<Prio>, Vec<DayCapacity>) {
        let cands = priority::collect_candidates(
            &self.tree,
            &self.replay,
            &self.cfg,
            &self.model,
            self.today,
            self.now_tz,
        );
        let days = priority::lookahead_days(&cands, self.today);
        let walls = self.walls_by_date(days);
        let slots = self.today_slots(allow_home);
        let caps = capacity::lookahead(
            &walls,
            &self.cfg,
            &self.model,
            &slots,
            self.today,
            days,
            self.wake_time(),
        );
        let yesterday = self.hysteresis_input();
        let prios = priority::compute(&cands, &caps, &yesterday, &self.cfg, self.today);
        (cands, prios, caps)
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
    fn resolve_timeouts(&mut self) -> Result<Vec<Id>, CliError> {
        let mut changed = Vec::new();
        for id in self.tree.waiting_ids() {
            let Some(item) = self.tree.get(&id) else {
                continue;
            };
            let expired = recur::waiting_state(item, &self.replay, self.today, &self.cfg)
                .is_some_and(|w| w.expired);
            if !expired {
                continue;
            }
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

/// Read `.tm/log.jsonl`, treating a missing file as an empty log.
fn read_log(store: &FsStore) -> Result<Log, CliError> {
    if !store.exists(LOG_PATH) {
        return Ok(Log::new());
    }
    Ok(Log::parse(&store.read_text(LOG_PATH)?))
}
