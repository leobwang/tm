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
//!   [`Ctx::walls_today`] (§8.1) and [`Ctx::priorities`] (§7 and the §8.4
//!   lookahead, the kernel's since stage 5 D10 L8).  **`Ctx::window` and
//!   `Ctx::today_slots` are gone** (stage 6 step L9, gap 93): §8.1's window and
//!   §8.2 step 3's slots for **today** are the kernel's now, derived from its
//!   own replay, and a second definition here would be the bug AGENTS §5.3
//!   names.  The fork's versions live on as the parity harness's comparand
//!   (`tm/tests/kernel_lookahead_parity.rs`), as `Ctx::walls_on`'s copy does.
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

use tm_core::capacity::{self, UnitCapacity, Wall};
use tm_core::config::Config;
use tm_core::energy::{self, Model};
use tm_core::grammar::ItemLine;
use tm_core::horizon;
use tm_core::log::{DayReplay, Event, LogEntry, Replay};
use tm_core::model::{Id, Item, Loc, Shape, State};
use tm_core::priority::{self, Candidate, Prio};
use tm_core::store::{
    self, ActiveBlock, Closed, FsStore, InterruptState, PlanFiles, RuntimeState, Store, StoreExt,
    LOG_PATH, MODEL_PATH,
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

/// **The fields of `.tm/state.json` no replay of `.tm/log.jsonl` can supply**
/// (the owner's **D42**, README gap 993) — named here so the rebuild below can
/// say what it could not restore instead of regenerating it as `null`.
///
/// Each one is host-only for a reason the log module's own conventions state,
/// not for a reason this file decided:
///
/// * **`break`** — "`break.t` is when the break began; the entry is appended
///   when the break **ends**" (`tm_core::log`'s event conventions, and
///   `day::end_break` is the only caller that writes an `Event::Break`). A
///   break that is *running* has left no line in the log at all, so neither
///   its start, its planned length nor its `where` can be recovered. The
///   `active.paused` it set goes with it (`tm break` pauses the block without
///   an `Event::Pause`), which is why [`derived_state`] ORs the cache's own
///   running break back into the derived `paused`.
///
///   **And when the file is MISSING there is no cache to OR from, so the block
///   comes back RUNNING.** That is the one place a deletion moves an answer,
///   and it is named in the notice rather than left to be found: `tm --json
///   now`'s `active.paused` goes `true` -> `false` across the deletion, driven
///   at the W-21 repair step on `energy-14d`
///   (`deleting_the_runtime_state_while_a_break_runs_resumes_the_block`), where
///   it is the ONLY spelling of eleven that moves and `.tm/log.jsonl` stays at
///   162 lines. On a tree whose plan depends on the pause it reaches further —
///   a re-laid afternoon, a moved plan hash and a second `Event::Plan` — which
///   is a derivable cache's deletion writing to the authority; README gap 1085.
/// * **`active.est_min`** — `Event::Start` carries `pred`, `hsw`, `slept_min`,
///   `loc`, `blocks_done` and `since_break_min`, and **no estimate**; `tm
///   extend` then adds its minutes to the cached number, so two `extend`s and
///   a multiplier are not reconstructible from `Event::Extend{by_min}` either.
///   The rebuild puts [`Ctx::planned_block`] there — the same one function
///   `tm start` writes from, never a second copy of its arithmetic (AGENTS
///   §5.3) — which is the estimate the item carries **now**, not the one the
///   block was started with.
/// * **`priorities_yesterday`** — §7.4's hysteresis map. No event carries a
///   `p`; the host rolls it out of `.tm/last_plan.json`.
/// * **`closed`** — §6.3's stamps plus `closed.swept`, which is a fact about
///   whether a kernel `autoClose` has swept this tree and not about anything
///   that happened. Its absence is load-bearing in the safe direction (it
///   makes the automatic close sweep once), so the rebuild leaves it alone.
/// **This is the FIELD LIST, and it stopped being the notice at W-22.**
/// [`Ctx::rebuild_notice`] is the notice: two auditors drove the rebuild and
/// found the file byte-identical to the deleted one on all four of these, while
/// the sentence built out of this constant said they *"were NOT restored"*.
/// What is true of each field is what it is *derived from*, not that it is
/// lost, so the entries below say that and the notice computes the rest.
pub const HOST_ONLY_STATE: &[(&str, &str)] = &[
    ("`break`",
     "a running break is logged only when it ends, so one that was running left \
      no line to rebuild from"),
    ("`active.paused`",
     "restored when a `tm pause` set it, because `Event::Pause` is in the log, \
      and gone when a running `break` set it, because that writes nothing"),
    ("`active.est_min`",
     "recomputed by `Ctx::planned_block` from the item's line — no `start` event \
      carries an estimate — so a `tm extend` that ran before the file was \
      deleted is not in it"),
    ("`priorities_yesterday`",
     "§7.4's hysteresis map, and no event carries a `p`"),
    ("`closed`",
     "`swept` is a fact about a sweep, not an event, and its absence makes the \
      automatic close sweep run once more, which is the safe direction"),
];

/// Why one [`HOST_ONLY_STATE`] field is what it is — the notice's own text,
/// read out of the one table rather than written twice (AGENTS §5.3).
fn host_only(field: &str) -> &'static str {
    HOST_ONLY_STATE
        .iter()
        .find(|(name, _)| *name == field)
        .map(|(_, why)| *why)
        .unwrap_or("the log does not carry it")
}

/// **Which of §10.2's fields the log can answer for, and how.**
///
/// The owner's **D42** makes `.tm/state.json` a *derivable cache*, rebuilt
/// from the log when missing or stale exactly as `.tm/cache/replay` is under
/// D13. This is the derivation, and it reads **only today's** facts:
/// [`DayReplay`] for the day-scoped fields and the two whole-log "still open"
/// facts for the running block and the running interruption.
///
/// | §10.2 field | from |
/// |---|---|
/// | `date` | `today`, when the log has anything to say about it |
/// | `wake` | `DayReplay::wake` (`Event::Wake`) |
/// | `arrival` | [`last_arrival`] — the **last** `Event::Arrive` of the day, which is what `tm arrive` leaves in the cache (**D45**) |
/// | `loc` | the last of `DayReplay::loc_changes`, else `DayReplay::loc` |
/// | `window` | [`Ctx::arrival_window`] at that arrival — the one function `tm arrive` writes it from, never a second copy (**D45**, AGENTS §5.3) |
/// | `budget` | [`Ctx::arrival_window`] at that arrival, with `window` |
/// | `active` | `Replay::open_block` — id, `started`, `paused`; **not** `est_min` |
/// | `interrupt` | `Replay::open_interrupt` — `started`, `id` |
/// | `last_plan_hash` | `DayReplay::last_plan_hash` (`Event::Plan`) |
/// | `break` | **nothing** ([`HOST_ONLY_STATE`]) — and the `active.paused` a *break* set with it; a `tm pause`'s survives, because `Event::Pause` is in the log |
/// | `priorities_yesterday`, `closed` | **nothing** ([`HOST_ONLY_STATE`]); both come back empty, and `closed`'s emptiness is load-bearing in the safe direction |
///
/// **The one residue inside a derivable field, measured rather than waved at.**
/// `tm plan` appends its `Event::Plan` only when the hash *moved*, so a day
/// whose first plan reproduces a hash last logged on an earlier day logs
/// nothing and `last_plan_hash` derives as `None`. That is not a regression:
/// [`roll_day`] already nulls it at every day boundary, so the derived value is
/// never worse than the cached one, and the cost of the miss is one extra
/// `plan` line.
/// The most recent day on or before `today` that has an answer for `pick`.
///
/// `.tm/state.json`'s `wake` and `loc` are not day-scoped ([`roll_day`] keeps
/// them), so neither is their derivation; every other day field reads
/// `today`'s [`DayReplay`] alone.
fn latest<T>(replay: &Replay, today: NaiveDate, pick: impl Fn(&DayReplay) -> Option<T>) -> Option<T> {
    replay.days.range(..=today).rev().find_map(|(_, d)| pick(d))
}

/// **The day's arrival as `tm arrive` leaves it: the LAST one** (the owner's
/// **D45**, README gap **1202**).
///
/// `DayReplay::arrival` is the day's **first** `Event::Arrive`, and it stays
/// that way: it is the fork's own derivation, `Replay.lean`'s
/// `a_day_keeps_its_first_arrival_its_highest_replans_and_its_last_plan` proves
/// it, and T5 compares it key for key. The **cache** holds the last arrival,
/// because `tm arrive` overwrites `state.arrival` every time it runs. So on a
/// day with two arrivals the two readings disagreed, and deleting
/// `.tm/state.json` moved `arrival`, `window` and five of eleven `--json`
/// spellings with them. D45 makes the derivation follow the verb.
///
/// It reads the day's **headers** ([`Replay::view`]) rather than a fact,
/// because no fact carries the later arrivals: a header is a tag, an instant
/// and a mask bit, and that is exactly what "the last surviving `arrive` of
/// this day" needs. Rows are in **file order**, which is the order the cache
/// was written in — a retro `tm arrive --at 07:00` run after a 13:00 one wrote
/// 07:00 to the cache and appended its line last, and this returns 07:00.
///
/// **Its one blind spot, declared:** a day whose headers the replay's scope did
/// not carry answers `None` here. Every verb that reads the runtime asks about
/// **today**, which is an open day in every scope, so this has no reachable
/// caller — but rather than claim that, [`derived_state`] falls back to
/// `DayReplay::arrival`, which is never worse than the reading this replaces.
fn last_arrival(replay: &Replay, today: NaiveDate) -> Option<DateTime<FixedOffset>> {
    // The tag is asked of `Event` rather than spelled a second time here
    // (AGENTS §5.3). An empty `String` allocates nothing, so the probe costs a
    // stack value and no heap.
    let probe = Event::Arrive {
        loc: String::new(),
        window: [String::new(), String::new()],
        budget: 0,
    };
    let tag = probe.name();
    replay
        .view()
        .iter()
        .filter(|r| r.day == today && !r.cancelled && r.tag == tag)
        .next_back()
        .map(|r| r.t)
}

fn derived_state(replay: &Replay, tz: Tz, today: NaiveDate, running_break: bool) -> RuntimeState {
    let hhmm = |t: DateTime<FixedOffset>| t.with_timezone(&tz).time();
    let day = replay.day(today);
    let open = replay.open_block.as_ref();
    let interrupted = replay.open_interrupt.as_ref().filter(|i| i.end.is_none());
    RuntimeState {
        date: Some(today),
        // **`wake` and `loc` are the two fields [`roll_day`] deliberately does
        // NOT clear at a day boundary**, so the cache carries them across days
        // and the derivation has to as well: the most recent one on or before
        // today, not today's. A derivation that read today's `DayReplay` alone
        // answers `null` on any day with neither a `tm wake` nor a `tm arrive`
        // in it, which is WRONG and not merely narrower — measured on the T9
        // fixture, where it moved `tm now`, `tm plan`, `tm log` and two
        // reviews.
        wake: latest(replay, today, |d| d.wake).map(hhmm),
        // **The LAST `arrive` of the day, not `DayReplay::arrival`** — the
        // owner's D45, README gap 1202. `DayReplay`'s field is the day's
        // FIRST arrival, because that is what the fork derives and what
        // `Replay.lean`'s
        // `a_day_keeps_its_first_arrival_its_highest_replans_and_its_last_plan`
        // proves; the CACHE
        // holds whatever the last `tm arrive` wrote. Two readings of one day,
        // and the derivation is the one that moves (AGENTS §5.3).
        arrival: last_arrival(replay, today).or(day.and_then(|d| d.arrival)).map(hhmm),
        loc: latest(replay, today, |d| {
            d.loc_changes.last().map(|(_, l)| l.clone()).or_else(|| d.loc.clone())
        }),
        // Not the log's: `DayReplay::window` and `DayReplay::budget` are the
        // FIRST arrival's, and the arrival above is the LAST. The caller fills
        // these from `Ctx::arrival_window`, the one function `tm arrive`
        // writes them from — the same move `active.est_min` makes below.
        window: None,
        budget: None,
        active: open.map(|b| ActiveBlock {
            id: Id::new(&b.id),
            started: hhmm(b.started),
            // Not the log's: `Event::Start` carries no estimate. The caller
            // fills it from `Ctx::planned_block`, the one function
            // `tm start` writes it from.
            est_min: 0,
            // `tm break` and `tm interrupt` pause the block in the cache; only
            // `tm pause` logs an `Event::Pause`. So the derived pause is the
            // log's OR whatever the cache still knows is running.
            paused: b.paused || running_break || interrupted.is_some(),
        }),
        break_: None,
        interrupt: interrupted.map(|i| InterruptState {
            started: i.start.map(hhmm),
            id: i.id.as_deref().map(Id::new),
        }),
        last_plan_hash: day.and_then(|d| d.last_plan_hash.clone()),
        priorities_yesterday: BTreeMap::new(),
        closed: Closed::default(),
    }
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
    /// The checkpoint's ledger day after this call, or `None` when nothing is
    /// sealed ([`kernel_log::Read::ledger_day`]).
    pub ledger_day: Option<u64>,
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
pub(super) fn genesis_error(e: kernel_log::GenesisError) -> CliError {
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
    /// **The replay checkpoint's ledger day `L`** (§9.1), as of the call that
    /// loaded this `Ctx`; `None` when nothing is sealed.
    ///
    /// Days below `L` are final and their records went out once; days at or
    /// above it stay in the checkpoint as open days. A stall — a block or an
    /// interruption left open — holds `L` back, so the checkpoint keeps every
    /// day since as open (§9.4, §18.7). `tm check` is the one reader
    /// (README gap 119).
    pub ledger_day: Option<u64>,
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
        // **D42: `.tm/state.json` is a CACHE of the log** (README gap 993), so
        // whether the file was there at all is a fact the rebuild below needs.
        // `load_state` answers a missing file with `Default::default()`, which
        // is the null-for-every-field the owner drove.
        let cached = store.exists(store::STATE_PATH);
        let mut state = store.load_state()?;
        let scope = scope(&state, today);
        // Gap 145: `tm check` alone loads tolerantly, and only `reachTooFar` is
        // tolerated — see `Ctx::load_tolerant`.
        let (replay, replay_fault, ledger_day) = match Ctx::replay_with(&store, &cfg, now, today, scope) {
            Ok(read) => (read.replay, None, read.ledger_day),
            Err(CliError::Kernel(issue)) if tolerate && issue.name == REACH_TOO_FAR => {
                let line = issue
                    .detail
                    .get("line")
                    .and_then(Value::as_u64)
                    .and_then(|l| usize::try_from(l).ok())
                    .unwrap_or(1);
                let tz = Ctx::tz_wire(&store, &cfg);
                // No ledger day: the checkpoint is exactly what could not be
                // read, so `tm check` reports the fault and never a stall.
                (Ctx::empty_replay(&cfg, &tz, today)?, Some((line, issue.message)), None)
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
            ledger_day,
            scope,
            model,
            timed_out: Vec::new(),
        };
        // **D42**, before the automatic close and before any verb reads
        // `cx.state`: the cache is reconciled with the log it is a cache of.
        // IN MEMORY ONLY — see the function's last section.
        cx.reconcile_state(cached, housekeeping);
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

    /// **Reconcile `.tm/state.json` with the log it is a cache of** — the
    /// owner's **D42**, README **gap 993**.
    ///
    /// # The defect this closes, as the owner drove it
    ///
    /// With `^p1` running, `rm .tm/state.json` regenerated the file with
    /// `date`, `wake`, `arrival`, `loc`, `window`, `budget` and `active` **all
    /// null** while `.tm/log.jsonl` still held the `wake`, the `arrive` and the
    /// `start`. `tm plan` read the log and drew `^p1` with `▶`; `tm now` read
    /// the cache and said *"nothing running"*; `tm done` and `tm stop` said
    /// *"nothing is running"* and exited **1**; `tm check` said *"no
    /// problems"*. Two readers of one day, disagreeing — AGENTS §5.3, the
    /// defect class this rebuild is named after — and a recoverable session
    /// looked unrecoverable.
    ///
    /// # The root of it: a missing file and an empty one were one value
    ///
    /// `Store::load_state` is `read_json(..)?.unwrap_or_default()`, so **"there
    /// is no file"** and **"the file says nothing is running"** arrived as the
    /// same `RuntimeState`. They are not the same statement. A `null` `active`
    /// in a file that exists is a *positive* claim — every verb that ends a
    /// block writes it — and an absent file makes no claim at all. `load_with`
    /// now asks `store.exists` before `load_state` and hands the answer here.
    ///
    /// # What this does, in two halves, and why they are not symmetric
    ///
    /// **The file is absent — REBUILD.** Every field [`derived_state`] can
    /// answer for is taken from the log, exactly as `.tm/cache/replay` is
    /// rebuilt when it is not there (D13). What the log cannot answer for is
    /// named on stderr rather than left to read as "there was nothing there"
    /// ([`HOST_ONLY_STATE`]).
    ///
    /// **The file is present and says a different block is open — STALE, and
    /// the log wins.** This is the other half of D42's *"missing or stale"*,
    /// and it is not hypothetical: `tm undo`'s own compensating line, appended
    /// to the log by hand without its `.tm/undo.json` snapshot, reopens a block
    /// the cache has already closed. **Driven at `4ccf4ef`** on
    /// `corpus/plan-basic`: `start ^p1`, `done`, then one hand-appended
    /// `{"ev":"undo","of":"done","id":"p1"}` — and `tm plan` drew `^p1` with
    /// `▶` and *"60m so far"* while `tm now` said *"nothing running"* and `tm
    /// done` said *"nothing is running"*, **with `.tm/state.json` present**.
    /// That is gap 993's whole symptom set without deleting anything, and
    /// `cli_latency`'s three-year row builds exactly that tree.
    ///
    /// The comparison is on the running block's **identity** alone. What only
    /// the cache knows about that block stays the cache's: `est_min`, which
    /// `tm extend` adds to and no event carries, and `paused`, which `tm break`
    /// sets without an `Event::Pause`. Only when the log names a *different*
    /// block is the whole record replaced, and then `est_min` is rebuilt
    /// through [`Ctx::planned_block`] because the cache's belonged to another
    /// block.
    ///
    /// # Who is told
    ///
    /// `loud` is `housekeeping` — the verbs that **own** the day's runtime and
    /// are the ones that write it. A read verb (`tm log`, `tm check`, `tm
    /// undo`, the TUI's reloads) gets the reconciled runtime and says nothing
    /// about it: it did not rebuild anything, and `tm log`'s stdout **and
    /// stderr** are asserted byte-identical with the fork's over seven corpus
    /// trees, one of which (`logs/three-days`) ends with `^t8` still running
    /// and no `.tm/state.json` beside it. What `tm check` still cannot do is
    /// name the disagreement as a *problem* of its own — README gap 1032.
    ///
    /// **That gate is also what keeps these two lines off the TUI's screen**,
    /// and the ordering was checked rather than assumed: `tui::run` calls
    /// `tui::load` — `housekeeping`, so loud — at `tui/mod.rs:102`, **before**
    /// `tui::setup` enters the alternate screen at `:111`, and `tui::reload`
    /// loads with `housekeeping` false, so nothing writes to stderr while
    /// ratatui owns the terminal. AGENTS §4's own reason for the kernel being
    /// total is that `exit(1)` with no unwind leaves a ratatui terminal in raw
    /// mode; an `eprintln!` mid-frame is the smaller cousin of that.
    ///
    /// # It writes nothing, and that is not a shortcut
    ///
    /// The reconciled runtime lives in memory and reaches the disk only through
    /// the `save_state` the verb was going to run anyway — every one of which
    /// is **past `kernel_bridge::gate`**. Writing it here was tried and
    /// **measured**: `cli_write_gate`'s
    /// `every_write_verb_refuses_a_tree_the_kernel_cannot_load_and_writes_nothing`
    /// caught `tm wake` creating `.tm/state.json` on a tree the kernel refuses,
    /// which is precisely the D35 rule that test exists for — *"none of them
    /// writes a byte"* — and `a_now_before_the_ledger_is_answered_and_not_persisted`
    /// caught a read-only verb at an early `--now` persisting that instant's
    /// `arrival`, `window` and `budget`. A derived cache is not worth one byte
    /// written ahead of the gate.
    ///
    /// # What this is NOT
    ///
    /// It is not a second definition of any fact. `est_min` comes from
    /// [`Ctx::planned_block`], the one function `tm start` also writes it from;
    /// `wake` derives exactly as [`Ctx::logged_wake`] already fell back to the
    /// log; the day facts are `DayReplay`'s own fields and not a second read of
    /// `.tm/log.jsonl`.
    fn reconcile_state(&mut self, cached: bool, loud: bool) {
        let mut derived = derived_state(
            &self.replay,
            self.cfg.tz,
            self.today,
            self.state.break_.is_some(),
        );
        // **D45: the window and the budget are the arrival's**, computed by
        // the one function `tm arrive` writes them from. `derived_state` left
        // them `None` because it has no tree and no walls; this is the same
        // shape `active.est_min` takes two blocks below.
        if let Some(at) = derived.arrival {
            let (window, budget) = self.arrival_window(at);
            derived.window = Some(window);
            derived.budget = Some(budget);
        }

        if cached {
            // **The cache exists, so it is STALE only where the log contradicts
            // it about what is OPEN.** That is one comparison, on identity, and
            // the log wins it.
            let here = self.state.active.as_ref().map(|a| a.id.clone());
            let logged = derived.active.as_ref().map(|a| a.id.clone());
            if here != logged {
                if loud {
                    let say = |id: &Option<Id>| match id {
                        Some(i) => format!("{} is running", i.token()),
                        None => "nothing is running".to_string(),
                    };
                    eprintln!(
                        "tm: .tm/state.json said {} and .tm/log.jsonl says {} — \
                         the log decides (§10.2 is a cache of it, D42)",
                        say(&here),
                        say(&logged),
                    );
                }
                self.state.active = derived.active.clone().map(|mut a| {
                    a.est_min = self.planned_block(&a.id).0;
                    a
                });
            }
            let here = self.state.interrupt.as_ref().map(|i| i.id.clone());
            let logged = derived.interrupt.as_ref().map(|i| i.id.clone());
            if here != logged {
                self.state.interrupt = derived.interrupt.clone();
            }
            return;
        }

        let before = self.state.clone();
        self.state = RuntimeState {
            // Host-only: an absent file cannot have held them, so they are
            // `Default` — and the notice below says which they were.
            break_: None,
            priorities_yesterday: before.priorities_yesterday.clone(),
            closed: before.closed.clone(),
            active: derived.active.clone().map(|mut a| {
                a.est_min = self.planned_block(&a.id).0;
                a
            }),
            ..derived
        };
        if self.state == before {
            return;
        }

        // **LOUD, and only when something was STRANDED.** A plan directory
        // synced without `.tm/state.json` — `tm init` gitignores it, so that is
        // the ordinary case and not an incident — has lost nothing and is told
        // nothing. A rebuild that hands a RUNNING block or a RUNNING
        // interruption back is the case gap 993 was reported as, and there the
        // fields the log cannot carry have to be named.
        //
        // **AND A TREE THAT WAS BEING USED TODAY IS STRANDED TOO** (README gap
        // 1191, the W-22 repair step). `break` is the ONE field of §10.2 that
        // genuinely cannot be derived, and it was the one field whose loss was
        // silent: with a break running and nothing started, there was no block
        // to name, so the whole notice — including its second sentence, which
        // is about the log's limits and not about the block — was suppressed,
        // and `state.break` went from a running break to `null` with no `tm:`
        // line at all. D42's own words are that a field that cannot be derived
        // *fails LOUDLY rather than regenerating as null*, so the third
        // condition is the log having anything to say about today: a synced
        // directory nobody has driven today still says nothing, and a tree that
        // has been driven today and lost its cache always does.
        let used_today = self.replay.day(self.today).is_some();
        if loud && (self.state.active.is_some() || self.state.interrupt.is_some() || used_today) {
            eprintln!(
                "tm: .tm/state.json was missing; rebuilt from .tm/log.jsonl \
                 (§10.2 is a cache of the log — D42){}",
                self.state
                    .active
                    .as_ref()
                    .map(|a| format!(" — {} is running, started {}", a.id.token(), a.started.format("%H:%M")))
                    .unwrap_or_default()
            );
            for line in self.rebuild_notice() {
                eprintln!("tm: {line}");
            }
        }
    }

    /// **What the rebuild could not put back — computed, not listed** (README
    /// gap **1192**, the W-22 repair step).
    ///
    /// The notice used to print [`HOST_ONLY_STATE`], a constant naming four
    /// fields as *"NOT restored"*. Driven by two auditors independently: the
    /// rebuilt `.tm/state.json` was **byte-identical** to the deleted one on all
    /// four, `cmp` and all — `active.paused` came back `true`, `active.est_min`
    /// came back `120`, `priorities_yesterday` and `closed` came back with their
    /// contents — while `tm now` printed *"a paused block comes back RUNNING"*
    /// and the user read that four things were lost. A loud notice that names
    /// what it did in fact restore trains the reader to ignore it, which is what
    /// makes gap 1191 land.
    ///
    /// So each clause is now checked against the state this rebuild actually
    /// produced, and the three claims are kept apart because they are three
    /// different claims:
    ///
    /// * **Gone.** `break`. Nothing in the log says a break was running (the
    ///   entry is appended when it *ends*), so one that was is not recoverable —
    ///   the only field of §10.2 for which that is true. The pause it had set
    ///   goes with it, and whether that happened is **visible**: a block that
    ///   comes back running was either never paused or was paused by the break,
    ///   and a block that comes back paused was paused by an `Event::Pause`,
    ///   which the log does carry. The old parenthetical asserted the first case
    ///   unconditionally and was false in the second.
    /// * **Recomputed.** `active.est_min`, from [`Ctx::planned_block`] — the
    ///   item's estimate *now*, not the one the block was started with. That is
    ///   a different source, not an absence, and the number is printed so the
    ///   reader can tell whether it looks right.
    /// * **Reset.** `priorities_yesterday` (§7.4's hysteresis; no event carries
    ///   a `p`) and `closed` — and `closed`'s reset is *deliberate*, because an
    ///   absent stamp makes the automatic sweep run once more, which is the safe
    ///   direction. Calling either of those "not restored" was true of the field
    ///   and misleading about the consequence.
    fn rebuild_notice(&self) -> Vec<String> {
        let mut out = Vec::new();
        let pause_note = match self.state.active.as_ref() {
            Some(a) if a.paused => {
                " — this block's `active.paused` came back from the log's own \
                 `pause` event, so only the break itself is gone"
            }
            Some(_) => {
                " — and if one was running, the `active.paused` it had set is \
                 gone with it and the block is running again"
            }
            None => "",
        };
        out.push(format!(
            "GONE, and the log cannot answer for it: `break` — {}{pause_note}.",
            host_only("`break`")
        ));
        if let Some(a) = self.state.active.as_ref() {
            out.push(format!(
                "RECOMPUTED rather than restored: `active.est_min` is {}m — {}.",
                a.est_min,
                host_only("`active.est_min`")
            ));
        }
        out.push(format!(
            "RESET, both deliberately: `priorities_yesterday` ({}) and \
             `closed` ({}).",
            host_only("`priorities_yesterday`"),
            host_only("`closed`")
        ));
        out
    }

    /// **The planned minutes one block of `id` gets** (§8.5): the item's
    /// remaining estimate, or one block when it has none, through
    /// [`energy::duration_multiplier`].
    ///
    /// `tm start` writes this into `state.active.est_min` and **D42**'s rebuild
    /// puts the same number back when the cache is gone. It is one function
    /// because two would be AGENTS §5.3 — the defect this rebuild exists to
    /// stop having an instance of. It is also the one number in `active` that
    /// the log cannot return: `Event::Start` carries no estimate
    /// ([`HOST_ONLY_STATE`]), so after a rebuild this is the estimate the item
    /// carries **now**, and a `tm extend` that ran before the file was deleted
    /// is not in it.
    /// Returns the minutes **and** the multiplier they were computed with,
    /// because `tm start --json` prints the multiplier beside them
    /// (`StartOut::multiplier`) and reading it off a second call would be the
    /// same two-definitions mistake one step smaller.
    pub fn planned_block(&self, id: &Id) -> (u32, f64) {
        // `tm start` has already refused a missing line, so the `unwrap_or` is
        // reached only from the rebuild — a block the log holds whose line the
        // other writers have since removed (§1.3). `duration_multiplier` looks
        // its key up and falls through to the default tag, so `0` costs the
        // ci-specific multiplier and nothing else.
        let ci = self.tree.get(id).map(|i| i.ci).unwrap_or(0);
        let tags = self.tree.tags_effective(id);
        let multiplier = energy::duration_multiplier(&self.model, ci, &tags);
        let remaining = self
            .tree
            .remaining(id)
            .filter(|m| *m > 0)
            .unwrap_or_else(|| self.block_min());
        (energy::planned_minutes(remaining, multiplier), multiplier)
    }

    /// Re-read files, tree, log and replay after a write, in the same scope.
    pub fn reload(&mut self) -> Result<(), CliError> {
        self.files = self.store.read_tree()?;
        self.tree = self.files.tree();
        let read = Ctx::replay_with(&self.store, &self.cfg, self.now, self.today, self.scope)?;
        self.replay = read.replay;
        self.ledger_day = read.ledger_day;
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
        Ok(LogRead { replay: read.replay, ledger_day: read.ledger_day })
    }

    /// The log's bytes as they are on disk now; a missing file is an empty log.
    pub(super) fn log_bytes(store: &FsStore) -> Result<Vec<u8>, CliError> {
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
        horizon::Ctx::new(&self.store, &self.files, &self.tree, self.now)
            .with_replay(&self.replay)
            // D16: the id-less fallback paths (gap 5) write the kernel's bytes too, so every
            // line the *binary* appends has one definition of its format.
            .writing_lines_with(kernel_log::render_one)
    }

    /// Append one event to `.tm/log.jsonl` (§10.1).
    pub fn append_event(&self, ev: Event) -> Result<(), CliError> {
        self.append_entry(&LogEntry::new(self.now, ev))
    }

    /// Append one already-timestamped entry.
    ///
    /// **The kernel writes the line** (owner decision **D16**; design §22.1's step S2): the verb
    /// sends the event's values and appends the bytes the kernel hands back, so
    /// `LogEntry::to_json` is no longer the binary's writer and the log's format has **one**
    /// definition — the kernel's grammar, reached through the same `Log.renderLine` the reader
    /// reads through. The bytes do not move (`the_log_emits_what_it_reads`, and T2 over every
    /// writable event); what changes is who decides them.
    ///
    /// A refusal is an error and never a written line: an event whose values the reader would
    /// refuse is named rather than appended.
    pub fn append_entry(&self, entry: &LogEntry) -> Result<(), CliError> {
        let mut line = kernel_log::render_one(entry).map_err(|why| {
            CliError::msg(format!("the kernel could not write this log line: {why}"))
        })?;
        line.push('\n');
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
    ///
    /// **An ambiguous title is refused, never resolved** (W-16 repair, gap
    /// 578). D31 keys a box-less, id-less line by its title, so two lines with
    /// one title are two lines with one address — and `Tree`'s own index gives
    /// the key to the *first* of them and keys the second `file:line`. Every
    /// verb that addresses an item by name reaches this function, and until the
    /// repair `tm drop laundry` and `tm edit laundry ci=3` on a tree with two
    /// `laundry` routines wrote the first line, exited 0 and said nothing —
    /// disambiguate-by-occurrence, which is the option **D32 declined** for the
    /// kernel and AGENTS §5.6's "the loader never picks between two readings"
    /// for everyone else. The kernel refuses the whole tree for the same
    /// collision (`LErr.dupId`, naming both lines); this names both lines too,
    /// in the same path-then-line order, so the two refusals read alike.
    ///
    /// [`Tree::ambiguous_title`] is the one place that decides it; this only
    /// asks.
    pub fn item(&self, id: &Id) -> Result<&Item, CliError> {
        self.refuse_ambiguous_title(id)?;
        self.tree
            .get(id)
            .ok_or_else(|| CliError::NotFound(id.clone()))
    }

    /// **The refusal itself**, so the three verbs that look an argument up in
    /// `self.tree` directly rather than through [`Ctx::item`] — `tm done <id>`
    /// (which tolerates a missing line, §1.3), `tm skip` and `tm routine done`
    /// (both through `instance_of`) — say the same thing in the same words.
    /// [`Tree::ambiguous_title`] is the one place that *decides* it.
    ///
    /// The key is printed bare, in backticks, and not as `^title`: a title key
    /// is never written into a file, which is the fact the kernel's own `dupId`
    /// message spells out and the reason the two positions are what the user
    /// has to go on.
    pub fn refuse_ambiguous_title(&self, id: &Id) -> Result<(), CliError> {
        let Some(spots) = self.tree.ambiguous_title(id) else {
            return Ok(());
        };
        let where_ = spots
            .iter()
            .map(|(path, line)| format!("{path}:{line}"))
            .collect::<Vec<_>>()
            .join(" and ");
        Err(CliError::msg(format!(
            "`{}` names {} lines and nothing says which: {where_}. A line with no `^id` is \
             keyed by its title, so a repeated title is an ambiguous address — the kernel \
             refuses the whole tree for it (`dupId`, naming the same two lines) and this verb \
             will not pick one. Give one of the lines an `^id`, or change a title.",
            id.as_str(),
            spots.len(),
        )))
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

    /// **§8.1's working window and block budget from one arrival** — the ONE
    /// definition `tm arrive` writes into `.tm/state.json` and D42's rebuild
    /// derives back out of the log (the owner's **D45**, AGENTS §5.3).
    ///
    /// It is not a resurrection of the `Ctx::window` this module's header says
    /// is gone. That one answered "what is today's window?" beside the
    /// kernel's own answer, which is the two-definitions bug; this answers
    /// "what does `tm arrive` write at `at`?", it is the only wrapper around
    /// [`capacity::window_and_budget`] in `tm/src`, and its two callers are
    /// `tm arrive` and the rebuild — the writer and the derivation, agreeing
    /// by construction rather than by inspection.
    ///
    /// **What it reads that the log does not carry.** The walls and the config
    /// are **today's**, not the ones standing when the arrival was logged, so
    /// a calendar item added since moves the window this returns. That is the
    /// same fidelity [`Ctx::planned_block`] gives `active.est_min` — the
    /// estimate the item carries *now* — and it is the honest one: a derivable
    /// cache is a function of the tree it is derived from. The alternative,
    /// reading `Event::Arrive`'s own `window` back, can only answer for the
    /// **first** arrival of the day (`DayReplay::window`), which is the defect
    /// D45 exists to close.
    pub fn arrival_window(&self, at: NaiveTime) -> ((NaiveTime, NaiveTime), u32) {
        let (end, budget) = capacity::window_and_budget(self.at(at), &self.walls_today(), &self.cfg);
        ((at, end.time()), budget)
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

    // **`Ctx::window` and `Ctx::today_slots` were deleted at stage 6 step L9** (gap 93).
    // §8.1's window and §8.2 step 3's slots for today are the kernel's now: the capacity request
    // carries `at`, `state` and `allowHome`, the kernel reads last night's sleep and today's
    // energy reports off its own replay through D24's seam, and `Look.day0Hist` is the answer
    // (`Look.day_zero_is_the_spec_day_energised`).  Keeping a second definition here is exactly
    // the bug AGENTS §5.3 names; the fork's two functions live on as the comparand of
    // `tm/tests/kernel_lookahead_parity.rs`, the way `Ctx::walls_on` already does.

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
    /// second call; otherwise, when some timeout has elapsed, the one shared
    /// write gate ([`kernel_bridge::tree_refusal`], the owner's D35) asks the
    /// kernel whether the tree still loads. A refusal skips every timeout,
    /// writes nothing and logs nothing, and is named on stderr — so a verb
    /// that then refuses the same tree has written nothing either
    /// (kernel/README.md "Stage 4 final, repair", defect 1: before this, a
    /// typo'd parent on the example tree's Monday rewrote `^a4` and created
    /// the log ahead of a refusal that said nothing was written). A kernel
    /// fault still fails the verb.
    ///
    /// It asked `kernel_bridge::apply(self, &[])` until D35 — the same
    /// question through the machine that ends in a write step. `tree_refusal`
    /// goes to `kernel_bridge::call` directly and cannot write at all, so
    /// there is now exactly **one** definition of "does the kernel load this
    /// tree" in the binary (AGENTS §5.3).
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
        if let Some(issue) = kernel_bridge::tree_refusal(self)? {
            if !kernel_bridge::capturing_kernel_stderr() {
                eprintln!(
                    "tm: the waiting timeouts (§5.1) were not applied, so nothing was written; \
                     they run again on the next command. {}",
                    issue.message
                );
            }
            return Ok(Vec::new());
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

    /// **The field list and the notice do not drift apart** (README gap 1192).
    ///
    /// [`HOST_ONLY_STATE`] stopped being the sentence `tm` prints at the W-22
    /// repair step — it was a constant claiming four fields were lost while the
    /// rebuilt file came back byte-identical on all four — and stayed the
    /// *documentation* of which §10.2 fields the log cannot answer for.
    /// [`Ctx::rebuild_notice`] computes the sentence instead. This is what still
    /// ties the two together: five entries, each leading with the field it is
    /// about, in the spelling the notice uses.
    ///
    /// **What it cannot check**: that the notice still *prints* each of them.
    /// That needs a `Ctx`, and it is what the two T9 cases in
    /// `cli_switch_acceptance.rs` are for.
    #[test]
    fn every_host_only_field_leads_its_own_entry() {
        let fields = [
            "`break`",
            "`active.paused`",
            "`active.est_min`",
            "`priorities_yesterday`",
            "`closed`",
        ];
        assert_eq!(
            HOST_ONLY_STATE.len(),
            fields.len(),
            "HOST_ONLY_STATE has {} entries and this test knows {}",
            HOST_ONLY_STATE.len(),
            fields.len()
        );
        for ((name, why), field) in HOST_ONLY_STATE.iter().zip(fields) {
            assert_eq!(*name, field, "the table is not in the order this test knows");
            assert!(!why.is_empty(), "{field} has no reason beside it");
            assert_eq!(host_only(field), *why, "`host_only` cannot find {field}");
        }
    }

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
