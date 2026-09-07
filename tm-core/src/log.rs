//! Log — tm-spec-v1.md §10.1 `.tm/log.jsonl`: append-only JSONL events and
//! the replay that derives block, instance and monitor state (§5.1 instance
//! status, §6.4 `done_minutes`, §9 events, §11 monitor inputs, §13 `tm undo`).
//!
//! # API overview
//!
//! * [`Event`] — one variant per event kind with the §10.1 field names
//!   (`#[serde(tag = "ev")]`, lowercase names). Unknown event names
//!   deserialize into [`Event::Unknown`]`{ ev, rest }` and serialize back
//!   losslessly (`rest` keys come out sorted). [`Event::name`] is the `ev`
//!   tag, [`Event::primary_id`] the item/instance id an event is about,
//!   [`Event::is_state_change`] says whether `tm undo` may target it.
//! * [`LogEntry`]`{ t: DateTime<FixedOffset>, ev }` — one line; `t` is
//!   written RFC 3339 with the local offset (`2026-09-07T06:05:00-05:00`).
//!   [`LogEntry::to_json`] / [`LogEntry::parse`] convert one line.
//! * [`Log`] — the entries plus the [`LogWarning`]s for lines that did not
//!   parse. [`Log::read`]`(path)` (missing file → empty, malformed lines →
//!   warnings, never an error for content), [`Log::parse`]`(text)`,
//!   [`Log::append`]`(path, &entry)` / [`Log::append_all`] (create `.tm/`,
//!   one object per line), [`Log::to_jsonl`], [`Log::iter_day`]`(date, tz)`,
//!   [`Log::iter_range`]`(from, to, tz)`, [`Log::iter_item`]`(id)`.
//! * Undo (§10.1, §13): `undo{of, id?}` cancels the most recent
//!   not-yet-undone event of kind `of` (with that primary id when given).
//!   [`Log::undo_mask`] computes which entries are cancelled (the target and
//!   the undo itself; a dangling undo cancels only itself),
//!   [`Log::effective`] iterates the survivors, [`Log::undo_target`] /
//!   [`Log::compensating_undo`] pick what `tm undo` should cancel next.
//! * Days: [`DayIndex`] — a day runs from `wake` to the next `wake`; an
//!   entry belongs to the calendar date (in `tz`) of the last `wake` at or
//!   before it when that wake is less than 24 h earlier, else to its own
//!   calendar date. [`DayIndex::day_of`], [`DayIndex::bounds`],
//!   [`DayIndex::wake_of`]; [`Log::day_index`]`(tz)` builds one.
//!   [`hours_since_wake`]`(t, wake)` gives `hsw` rounded to 0.01.
//! * [`replay`]`(entries, range, tz) -> `[`Replay`] (also [`Log::replay`]):
//!   per-day [`DayReplay`] (wake/arrive, block minutes, blocks done, load,
//!   energy mix, lost, leak, idle, breaks, plans, starts, done ids, actual
//!   [`LogSegment`]s), per-item [`ItemReplay`] (minutes, blocks, by day,
//!   done times), [`InstanceRecord`]s per `(item, inst)`, [`EnergyObs`],
//!   [`DurationObs`], [`Interruption`]s, [`NamedEvent`]s, [`Demotion`]s
//!   with stamps, [`CloseRecord`]s, the longest leak, the still-open block.
//!   Helpers: `block_minutes(id)`, `blocks_done(date)`, `is_done(id)`,
//!   `last_done(id)`, `done_dates(id)`, `instance_status(item, inst)`,
//!   `stamps(id)`, `events_named(name)`.
//!
//! # Event conventions (what the writers log, what replay assumes)
//!
//! * `wake.t` is the wake time; `arrive.t` the arrival; `start.t` the block
//!   start. `done.actual_min` is authoritative for the block's minutes.
//! * `stop{id, remaining_min}` cuts an active block: it gets partial credit
//!   for its worked minutes — elapsed since `start` minus paused
//!   (`pause`…`unpause`) and interrupted (`interrupt`…`resume`) time. A
//!   `start` while another block is open cuts the open block the same way.
//!   A block still open at the end of the log gets no credit; it is
//!   reported as [`Replay::open_block`].
//! * `break.t` is when the break began; the entry is appended when the break
//!   ends with `actual_min` set (a missing `actual_min` counts as
//!   `planned_min`).
//! * `idle{attributed, min}` is appended when the idle prompt is answered:
//!   the gap `[t − min, t]` was `attributed` to `leak`, `work`, `break`,
//!   `routine` or `interrupt`; only `leak` feeds the leak ledger.
//! * `routine{item, inst, status, actual_min?}` sets the instance status
//!   (`done`, `skipped`, `missed`, `expired`, `pending`); `skip{item, inst}`
//!   marks it skipped. `inst` is the calendar date or the ordinal (`#3`).
//! * `resume{lost_min, dropped}` closes the interruption opened by the last
//!   `interrupt`; `lost_min` feeds the day's lost minutes.
//! * `plan{hash, replans_today, drift_min}`: `drift_min` is the drift of
//!   that replan; the day's drift is the sum.
//! * `done{partial: true}` finishes a block but not the item: it counts for
//!   minutes and blocks, not for `is_done` / `last_done`. A retro
//!   `tm done ^id` logs `actual_min: 0`: the item is done, no block or
//!   duration observation is recorded.
//! * `done.went` (1 fine, 2 hard, 3 collapsed) is attached to the energy
//!   observation of the block's `start`; `start` without `rep` yields no
//!   observation. `energy` events are observations too.
//! * `demote.from` is the horizon key the item left (`2026-W37`,
//!   `2026-09-07`); it becomes the stamp (`W37`, `D07`).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io::Write;
use std::ops::RangeInclusive;
use std::path::Path;

use chrono::{DateTime, Duration, FixedOffset, NaiveDate, SecondsFormat, TimeZone};
use chrono_tz::Tz;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use thiserror::Error;

use crate::model::{parse_date, InstanceStatus, IsoWeek, Stamp};

/// Errors from reading or writing the log file.
#[derive(Debug, Error)]
pub enum LogError {
    /// The file could not be read (other than not existing).
    #[error("cannot read {path}: {source}")]
    Read {
        /// Path attempted.
        path: String,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// The file (or its directory) could not be written.
    #[error("cannot write {path}: {source}")]
    Write {
        /// Path attempted.
        path: String,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// An entry could not be encoded as JSON.
    #[error("cannot encode log entry: {0}")]
    Json(#[from] serde_json::Error),
}

// ---------------------------------------------------------------------------
// Timestamps
// ---------------------------------------------------------------------------

/// Format a timestamp the way the log writes it: RFC 3339 with the offset
/// and whole seconds (`2026-09-07T06:05:00-05:00`).
pub fn fmt_timestamp(t: &DateTime<FixedOffset>) -> String {
    t.to_rfc3339_opts(SecondsFormat::Secs, false)
}

/// Parse a log timestamp: RFC 3339, or `YYYY-MM-DDTHH:MM±HH:MM` without
/// seconds.
pub fn parse_timestamp(s: &str) -> Result<DateTime<FixedOffset>, chrono::ParseError> {
    DateTime::parse_from_rfc3339(s).or_else(|_| DateTime::parse_from_str(s, "%Y-%m-%dT%H:%M%:z"))
}

mod ts {
    use super::{fmt_timestamp, parse_timestamp};
    use chrono::{DateTime, FixedOffset};
    use serde::{de, Deserialize, Deserializer, Serializer};

    pub fn serialize<S: Serializer>(t: &DateTime<FixedOffset>, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&fmt_timestamp(t))
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<DateTime<FixedOffset>, D::Error> {
        let s = String::deserialize(d)?;
        parse_timestamp(&s).map_err(|e| de::Error::custom(format!("invalid timestamp {s:?}: {e}")))
    }
}

fn is_false(b: &bool) -> bool {
    !*b
}

// ---------------------------------------------------------------------------
// Events
// ---------------------------------------------------------------------------

/// One log event (§10.1). Field names are the JSON keys; the variant name in
/// lowercase is the `ev` tag (`Named` is `event`).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "ev", rename_all = "lowercase")]
pub enum Event {
    /// `tm wake`: `t` is the wake time.
    Wake {
        /// Minutes slept.
        slept_min: u32,
        /// Minutes to fall asleep (`--onset`).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        onset_min: Option<u32>,
    },
    /// `tm arrive`: location, working window and block budget for the day.
    Arrive {
        /// Location name (`lounge`, `home`, …).
        loc: String,
        /// `[start, end]` as `HH:MM`.
        window: [String; 2],
        /// Block budget.
        budget: u32,
    },
    /// A block started.
    Start {
        /// Item id.
        id: String,
        /// Predicted slot energy.
        pred: u8,
        /// Reported energy, if asked.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        rep: Option<u8>,
        /// Hours since wake.
        #[serde(default)]
        hsw: f64,
        /// Minutes slept last night.
        #[serde(default)]
        slept_min: u32,
        /// Location.
        loc: String,
        /// Blocks done today before this one.
        #[serde(default)]
        blocks_done: u32,
        /// Minutes since the last break.
        #[serde(default)]
        since_break_min: u32,
    },
    /// A block (or, retro, an item) finished.
    Done {
        /// Item id.
        id: String,
        /// Estimated minutes for the block.
        est_min: u32,
        /// Actual minutes worked (0 for a retro `tm done ^id`).
        actual_min: u32,
        /// How it went: 1 fine, 2 hard, 3 collapsed.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        went: Option<u8>,
        /// The item's tags.
        #[serde(default)]
        tags: Vec<String>,
        /// The item's ci.
        ci: u8,
        /// True when the block is done but the item is not.
        #[serde(default, skip_serializing_if = "is_false")]
        partial: bool,
    },
    /// The block was extended.
    Extend {
        /// Item id.
        id: String,
        /// Minutes added.
        by_min: u32,
    },
    /// The block was stopped; the remainder re-competes.
    Stop {
        /// Item id.
        id: String,
        /// Remaining estimate in minutes.
        remaining_min: u32,
    },
    /// A break; `t` is its start.
    Break {
        /// Planned length.
        planned_min: u32,
        /// Actual length.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        actual_min: Option<u32>,
        /// Where (`walk`, `seat`, `bed`, `phone`).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        r#where: Option<String>,
    },
    /// An energy report outside a block start.
    Energy {
        /// Predicted energy.
        pred: u8,
        /// Reported energy.
        rep: u8,
        /// Hours since wake.
        #[serde(default)]
        hsw: f64,
        /// Location.
        loc: String,
    },
    /// An interruption began.
    Interrupt {
        /// The interrupted item, if a block was running.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
    },
    /// The interruption ended.
    Resume {
        /// Minutes lost.
        lost_min: u32,
        /// Items dropped from today's plan as a consequence.
        #[serde(default)]
        dropped: Vec<String>,
    },
    /// Timer paused.
    Pause {
        /// Item id.
        id: String,
    },
    /// Timer resumed.
    Unpause {
        /// Item id.
        id: String,
    },
    /// The idle prompt was answered: the gap `[t − min, t]` was attributed.
    Idle {
        /// `leak`, `work`, `break`, `routine` or `interrupt`.
        attributed: String,
        /// Length of the gap.
        min: u32,
    },
    /// A routine instance changed status.
    Routine {
        /// Routine name or id.
        item: String,
        /// Instance key: a date or an ordinal (`#3`).
        inst: String,
        /// `done`, `skipped`, `missed`, `expired`, `pending`.
        status: String,
        /// Minutes it took.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        actual_min: Option<u32>,
    },
    /// A routine instance was skipped.
    Skip {
        /// Routine name or id.
        item: String,
        /// Instance key.
        inst: String,
    },
    /// A plan was computed.
    Plan {
        /// Plan hash.
        hash: String,
        /// Replans so far today (running count).
        replans_today: u32,
        /// Minutes segments moved by this replan.
        drift_min: u32,
    },
    /// `tm event <name> [^id]`.
    #[serde(rename = "event")]
    Named {
        /// Event name.
        name: String,
        /// The item it resolves, if given.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
    },
    /// An item was demoted at a close.
    Demote {
        /// Item id.
        id: String,
        /// Horizon key it left (`2026-W37`, `2026-09-07`).
        from: String,
        /// Horizon key it went to (`2026-09`, `2026-W38`).
        to: String,
        /// Remaining estimate carried.
        est_min: u32,
    },
    /// `tm readopt`.
    Readopt {
        /// Item id.
        id: String,
    },
    /// `tm move`.
    Move {
        /// Item id.
        id: String,
        /// Source file / horizon.
        from: String,
        /// Destination file / horizon.
        to: String,
    },
    /// `tm drop`.
    Drop {
        /// Item id.
        id: String,
    },
    /// `tm edit`: one field changed.
    Edit {
        /// Item id.
        id: String,
        /// Field name.
        field: String,
        /// Old value (empty when it was unset).
        from: String,
        /// New value (empty when unset).
        to: String,
    },
    /// A free-text note.
    Note {
        /// The text.
        text: String,
    },
    /// Location changed.
    Loc {
        /// New location.
        loc: String,
    },
    /// `tm close <period>` ran.
    Close {
        /// `day`, `week` or `month`.
        period: String,
        /// The period key closed (`2026-09-07`, `2026-W37`, `2026-09`).
        key: String,
    },
    /// `tm undo`: cancels the most recent not-yet-undone event of kind `of`.
    Undo {
        /// Event kind to cancel.
        of: String,
        /// Restrict to events with this primary id.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
    },
    /// Any event kind this version does not know; kept verbatim.
    #[serde(untagged)]
    Unknown {
        /// The `ev` tag.
        ev: String,
        /// Every other field.
        #[serde(flatten)]
        rest: Map<String, Value>,
    },
}

/// The known `ev` tags, in §10.1 order.
pub const EVENT_NAMES: &[&str] = &[
    "wake", "arrive", "start", "done", "extend", "stop", "break", "energy", "interrupt", "resume",
    "pause", "unpause", "idle", "routine", "skip", "plan", "event", "demote", "readopt", "move",
    "drop", "edit", "note", "loc", "close", "undo",
];

impl Event {
    /// The `ev` tag.
    pub fn name(&self) -> &str {
        match self {
            Event::Wake { .. } => "wake",
            Event::Arrive { .. } => "arrive",
            Event::Start { .. } => "start",
            Event::Done { .. } => "done",
            Event::Extend { .. } => "extend",
            Event::Stop { .. } => "stop",
            Event::Break { .. } => "break",
            Event::Energy { .. } => "energy",
            Event::Interrupt { .. } => "interrupt",
            Event::Resume { .. } => "resume",
            Event::Pause { .. } => "pause",
            Event::Unpause { .. } => "unpause",
            Event::Idle { .. } => "idle",
            Event::Routine { .. } => "routine",
            Event::Skip { .. } => "skip",
            Event::Plan { .. } => "plan",
            Event::Named { .. } => "event",
            Event::Demote { .. } => "demote",
            Event::Readopt { .. } => "readopt",
            Event::Move { .. } => "move",
            Event::Drop { .. } => "drop",
            Event::Edit { .. } => "edit",
            Event::Note { .. } => "note",
            Event::Loc { .. } => "loc",
            Event::Close { .. } => "close",
            Event::Undo { .. } => "undo",
            Event::Unknown { ev, .. } => ev,
        }
    }

    /// The item id (or routine `item`) the event is about, if any. This is
    /// what `undo{id}` matches against.
    pub fn primary_id(&self) -> Option<&str> {
        match self {
            Event::Start { id, .. }
            | Event::Done { id, .. }
            | Event::Extend { id, .. }
            | Event::Stop { id, .. }
            | Event::Pause { id }
            | Event::Unpause { id }
            | Event::Demote { id, .. }
            | Event::Readopt { id }
            | Event::Move { id, .. }
            | Event::Drop { id }
            | Event::Edit { id, .. } => Some(id),
            Event::Routine { item, .. } | Event::Skip { item, .. } => Some(item),
            Event::Interrupt { id } | Event::Named { id, .. } | Event::Undo { id, .. } => {
                id.as_deref()
            }
            Event::Unknown { rest, .. } => rest.get("id").and_then(Value::as_str),
            _ => None,
        }
    }

    /// True for events `tm undo` may cancel: everything but `plan`, `note`,
    /// `undo` and unknown events.
    pub fn is_state_change(&self) -> bool {
        !matches!(
            self,
            Event::Plan { .. } | Event::Note { .. } | Event::Undo { .. } | Event::Unknown { .. }
        )
    }

    /// True for `idle` attributed to `leak`.
    pub fn is_leak(&self) -> bool {
        matches!(self, Event::Idle { attributed, .. } if attributed == "leak")
    }
}

/// One line of the log.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LogEntry {
    /// When it happened (local time with offset).
    #[serde(with = "ts")]
    pub t: DateTime<FixedOffset>,
    /// What happened.
    #[serde(flatten)]
    pub ev: Event,
}

impl LogEntry {
    /// Build an entry.
    pub fn new(t: DateTime<FixedOffset>, ev: Event) -> LogEntry {
        LogEntry { t, ev }
    }
    /// The entry as one JSON object (no trailing newline).
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
    /// Parse one line.
    pub fn parse(line: &str) -> Result<LogEntry, serde_json::Error> {
        serde_json::from_str(line)
    }
    /// The timestamp in `tz`.
    pub fn local(&self, tz: Tz) -> DateTime<Tz> {
        self.t.with_timezone(&tz)
    }
    /// The calendar date in `tz` (not wake-aware; see [`DayIndex`]).
    pub fn calendar_date(&self, tz: Tz) -> NaiveDate {
        self.local(tz).date_naive()
    }
}

/// A line that did not parse, kept so `tm check` / `tm log` can show it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LogWarning {
    /// 1-based line number.
    pub line: usize,
    /// The line text.
    pub text: String,
    /// Why it was rejected.
    pub error: String,
}

impl fmt::Display for LogWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {} ({:?})", self.line, self.error, self.text)
    }
}

/// Which entries an undo cancelled.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct UndoMask {
    /// `cancelled[i]` — entry `i` is skipped by replay (an undone event or an
    /// `undo` entry).
    pub cancelled: Vec<bool>,
    /// Indices of `undo` entries that matched nothing.
    pub dangling: Vec<usize>,
}

impl UndoMask {
    /// Number of `(undo, target)` pairs.
    pub fn pairs(&self) -> usize {
        (self.cancelled.iter().filter(|c| **c).count() - self.dangling.len()) / 2
    }
}

/// The whole log: entries in file order plus warnings for bad lines.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct Log {
    /// Entries in file order.
    pub entries: Vec<LogEntry>,
    /// Lines that did not parse.
    pub warnings: Vec<LogWarning>,
}

impl Log {
    /// An empty log.
    pub fn new() -> Log {
        Log::default()
    }

    /// A log from entries (no warnings).
    pub fn from_entries(entries: Vec<LogEntry>) -> Log {
        Log {
            entries,
            warnings: Vec::new(),
        }
    }

    /// Parse JSONL text. Blank lines are skipped; malformed lines become
    /// warnings.
    pub fn parse(text: &str) -> Log {
        let mut log = Log::new();
        for (i, raw) in text.lines().enumerate() {
            let line = raw.trim_end_matches('\r');
            if line.trim().is_empty() {
                continue;
            }
            match LogEntry::parse(line) {
                Ok(e) => log.entries.push(e),
                Err(e) => log.warnings.push(LogWarning {
                    line: i + 1,
                    text: line.to_string(),
                    error: e.to_string(),
                }),
            }
        }
        log
    }

    /// Read `path`. A missing file is an empty log; malformed lines are
    /// collected in `warnings`; only an I/O failure is an error.
    pub fn read(path: impl AsRef<Path>) -> Result<Log, LogError> {
        let path = path.as_ref();
        match std::fs::read_to_string(path) {
            Ok(text) => Ok(Log::parse(&text)),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(Log::new()),
            Err(source) => Err(LogError::Read {
                path: path.display().to_string(),
                source,
            }),
        }
    }

    /// Append one entry to `path` (created, with its directory, if needed).
    pub fn append(path: impl AsRef<Path>, entry: &LogEntry) -> Result<(), LogError> {
        Log::append_all(path, std::slice::from_ref(entry))
    }

    /// Append entries to `path`, one JSON object per line.
    pub fn append_all(path: impl AsRef<Path>, entries: &[LogEntry]) -> Result<(), LogError> {
        let path = path.as_ref();
        let write_err = |source: std::io::Error| LogError::Write {
            path: path.display().to_string(),
            source,
        };
        let mut buf = String::new();
        for e in entries {
            buf.push_str(&e.to_json()?);
            buf.push('\n');
        }
        if let Some(dir) = path.parent() {
            if !dir.as_os_str().is_empty() {
                std::fs::create_dir_all(dir).map_err(write_err)?;
            }
        }
        let mut f = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .map_err(write_err)?;
        f.write_all(buf.as_bytes()).map_err(write_err)?;
        Ok(())
    }

    /// Push an entry in memory.
    pub fn push(&mut self, entry: LogEntry) {
        self.entries.push(entry);
    }

    /// Number of entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// True when there are no entries.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The entries as JSONL text (one object per line, trailing newline).
    pub fn to_jsonl(&self) -> Result<String, serde_json::Error> {
        let mut out = String::new();
        for e in &self.entries {
            out.push_str(&e.to_json()?);
            out.push('\n');
        }
        Ok(out)
    }

    /// All entries in order.
    pub fn iter(&self) -> impl Iterator<Item = &LogEntry> {
        self.entries.iter()
    }

    /// Which entries are cancelled by `undo` entries (§10.1, §13). Each
    /// `undo{of, id?}` cancels the most recent earlier event of kind `of`
    /// (with primary id `id` when given) that is not already cancelled and is
    /// not itself an undo; the undo entry is always cancelled too. An undo
    /// that matches nothing is *dangling*.
    pub fn undo_mask(&self) -> UndoMask {
        let n = self.entries.len();
        let mut cancelled = vec![false; n];
        let mut dangling = Vec::new();
        for i in 0..n {
            let Event::Undo { of, id } = &self.entries[i].ev else {
                continue;
            };
            cancelled[i] = true;
            let target = (0..i).rev().find(|&j| {
                let ev = &self.entries[j].ev;
                !cancelled[j]
                    && !matches!(ev, Event::Undo { .. })
                    && ev.name() == of
                    && id.as_deref().is_none_or(|want| ev.primary_id() == Some(want))
            });
            match target {
                Some(j) => cancelled[j] = true,
                None => dangling.push(i),
            }
        }
        UndoMask {
            cancelled,
            dangling,
        }
    }

    /// Entries that survive undo cancellation, in order.
    pub fn effective(&self) -> impl Iterator<Item = &LogEntry> {
        let mask = self.undo_mask();
        self.entries
            .iter()
            .zip(mask.cancelled)
            .filter_map(|(e, c)| (!c).then_some(e))
    }

    /// The most recent surviving state-changing event — what `tm undo`
    /// would cancel next.
    pub fn undo_target(&self) -> Option<&LogEntry> {
        self.effective().filter(|e| e.ev.is_state_change()).last()
    }

    /// The `undo` event that cancels [`Log::undo_target`], if there is one.
    pub fn compensating_undo(&self) -> Option<Event> {
        self.undo_target().map(|e| Event::Undo {
            of: e.ev.name().to_string(),
            id: e.ev.primary_id().map(str::to_string),
        })
    }

    /// The wake-aware day index over the surviving `wake` entries.
    pub fn day_index(&self, tz: Tz) -> DayIndex {
        DayIndex::new(
            tz,
            self.effective()
                .filter(|e| matches!(e.ev, Event::Wake { .. }))
                .map(|e| e.t),
        )
    }

    /// Surviving entries belonging to `date` (wake to wake, see
    /// [`DayIndex`]).
    pub fn iter_day(&self, date: NaiveDate, tz: Tz) -> impl Iterator<Item = &LogEntry> {
        self.iter_range(date, date, tz)
    }

    /// Surviving entries whose day (see [`DayIndex`]) is in `from..=to`.
    pub fn iter_range(
        &self,
        from: NaiveDate,
        to: NaiveDate,
        tz: Tz,
    ) -> impl Iterator<Item = &LogEntry> {
        let days = self.day_index(tz);
        self.effective().filter(move |e| {
            let d = days.day_of(e.t);
            d >= from && d <= to
        })
    }

    /// Surviving entries whose primary id is `id`, in order.
    pub fn iter_item<'a>(&'a self, id: &'a str) -> impl Iterator<Item = &'a LogEntry> + 'a {
        self.effective().filter(move |e| e.ev.primary_id() == Some(id))
    }

    /// Derive state from the surviving entries; `None` = the whole log.
    pub fn replay(&self, range: Option<RangeInclusive<NaiveDate>>, tz: Tz) -> Replay {
        let entries: Vec<&LogEntry> = self.effective().collect();
        replay_refs(&entries, range, tz)
    }
}

// ---------------------------------------------------------------------------
// Days and hours since wake
// ---------------------------------------------------------------------------

/// Hours between `wake` and `t`, rounded to 0.01 (the `hsw` field).
pub fn hours_since_wake<A: TimeZone, B: TimeZone>(t: &DateTime<A>, wake: &DateTime<B>) -> f64 {
    let secs = t.signed_duration_since(wake).num_seconds() as f64;
    (secs / 36.0).round() / 100.0
}

/// Local midnight of `date` in `tz` (the first valid instant after it when
/// midnight falls in a DST gap).
pub fn local_midnight(date: NaiveDate, tz: Tz) -> DateTime<FixedOffset> {
    let naive = date.and_hms_opt(0, 0, 0).expect("midnight");
    for h in 0..4 {
        let cand = naive + Duration::hours(h);
        if let Some(dt) = tz.from_local_datetime(&cand).earliest() {
            return dt.fixed_offset();
        }
    }
    tz.from_utc_datetime(&naive).fixed_offset()
}

/// Wake-aware day attribution: a day runs from `wake` to the next `wake`.
///
/// An instant belongs to the calendar date (in `tz`) of the last `wake` at or
/// before it when that wake is less than 24 hours earlier; otherwise (no wake
/// logged, or the wake is stale) to its own calendar date.
#[derive(Clone, Debug, PartialEq)]
pub struct DayIndex {
    tz: Tz,
    wakes: Vec<DateTime<FixedOffset>>,
}

impl DayIndex {
    /// Build from wake times (sorted internally).
    pub fn new(tz: Tz, wakes: impl IntoIterator<Item = DateTime<FixedOffset>>) -> DayIndex {
        let mut wakes: Vec<_> = wakes.into_iter().collect();
        wakes.sort();
        DayIndex { tz, wakes }
    }

    /// The timezone.
    pub fn tz(&self) -> Tz {
        self.tz
    }

    /// The wake times, ascending.
    pub fn wakes(&self) -> &[DateTime<FixedOffset>] {
        &self.wakes
    }

    /// Calendar date of `t` in the timezone.
    pub fn calendar_date(&self, t: DateTime<FixedOffset>) -> NaiveDate {
        t.with_timezone(&self.tz).date_naive()
    }

    /// The last wake at or before `t`.
    pub fn last_wake_before(&self, t: DateTime<FixedOffset>) -> Option<DateTime<FixedOffset>> {
        let i = self.wakes.partition_point(|w| *w <= t);
        (i > 0).then(|| self.wakes[i - 1])
    }

    /// The day `t` belongs to.
    pub fn day_of(&self, t: DateTime<FixedOffset>) -> NaiveDate {
        match self.last_wake_before(t) {
            Some(w) if t.signed_duration_since(w) < Duration::hours(24) => self.calendar_date(w),
            _ => self.calendar_date(t),
        }
    }

    /// The first `wake` on `date` (calendar), if any.
    pub fn wake_of(&self, date: NaiveDate) -> Option<DateTime<FixedOffset>> {
        self.wakes
            .iter()
            .copied()
            .find(|w| self.calendar_date(*w) == date)
    }

    /// `[start, end)` of `date`: exactly the instants whose
    /// [`DayIndex::day_of`] is `date`. Without a wake on that date the day is
    /// the calendar day, shortened when the previous day's wake still claims
    /// its first hours.
    pub fn bounds(&self, date: NaiveDate) -> (DateTime<FixedOffset>, DateTime<FixedOffset>) {
        let mid = local_midnight(date, self.tz);
        let next_mid = local_midnight(date + Duration::days(1), self.tz);
        let mut cands = vec![mid, next_mid];
        for w in &self.wakes {
            let wd = self.calendar_date(*w);
            if wd >= date - Duration::days(1) && wd <= date + Duration::days(1) {
                cands.push(*w);
                cands.push(*w + Duration::hours(24));
            }
        }
        cands.sort();
        let start = cands
            .iter()
            .copied()
            .find(|c| self.day_of(*c) == date)
            .unwrap_or(mid);
        let end = cands
            .iter()
            .copied()
            .find(|c| *c > start && self.day_of(*c) != date)
            .unwrap_or(start + Duration::hours(24));
        (start, end)
    }
}

// ---------------------------------------------------------------------------
// Replay
// ---------------------------------------------------------------------------

/// What an actual (logged) time segment was.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SegmentKind {
    /// Working on an item.
    Block {
        /// Item id.
        id: String,
    },
    /// Timer paused.
    Pause {
        /// Item id.
        id: String,
    },
    /// An interruption.
    Interrupt {
        /// The interrupted item.
        id: Option<String>,
    },
    /// A break.
    Break {
        /// Where.
        r#where: Option<String>,
    },
    /// A routine instance being done.
    Routine {
        /// Routine name or id.
        item: String,
        /// Instance key.
        inst: String,
    },
    /// A gap attributed at the idle prompt.
    Idle {
        /// `leak`, `work`, …
        attributed: String,
    },
}

/// An actual time segment derived from the log (for the day bar and the
/// day review).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LogSegment {
    /// Start.
    pub start: DateTime<FixedOffset>,
    /// End.
    pub end: DateTime<FixedOffset>,
    /// What it was.
    pub kind: SegmentKind,
}

impl LogSegment {
    /// Length in whole minutes.
    pub fn minutes(&self) -> u32 {
        self.end
            .signed_duration_since(self.start)
            .num_minutes()
            .max(0) as u32
    }
}

/// An energy observation for the learned model (§8.5).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct EnergyObs {
    /// When.
    pub t: DateTime<FixedOffset>,
    /// The day it belongs to.
    pub day: NaiveDate,
    /// Predicted energy.
    pub pred: u8,
    /// Reported energy.
    pub rep: u8,
    /// Hours since wake.
    pub hsw: f64,
    /// Location.
    pub loc: String,
    /// Minutes slept (from the `start` event or the day's `wake`).
    pub slept_min: Option<u32>,
    /// How the block went (from the matching `done`), for weighting.
    pub went: Option<u8>,
    /// The item, for `start` observations.
    pub id: Option<String>,
    /// Whether it came from a `start` or an `energy` report.
    pub from_start: bool,
}

impl EnergyObs {
    /// `rep − pred`.
    pub fn delta(&self) -> i32 {
        self.rep as i32 - self.pred as i32
    }
    /// §8.5 weight: `went = 3` counts double, `went = 2` 1.5, else 1.
    pub fn weight(&self) -> f64 {
        match self.went {
            Some(3) => 2.0,
            Some(2) => 1.5,
            _ => 1.0,
        }
    }
}

/// A duration observation for the multipliers (§8.5): one per timed block.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct DurationObs {
    /// When the block ended.
    pub t: DateTime<FixedOffset>,
    /// The day it belongs to.
    pub day: NaiveDate,
    /// Item id.
    pub id: String,
    /// The item's ci.
    pub ci: u8,
    /// The item's tags.
    pub tags: Vec<String>,
    /// Estimated minutes.
    pub est_min: u32,
    /// Actual minutes.
    pub actual_min: u32,
    /// How it went.
    pub went: Option<u8>,
    /// Block done but item not finished.
    pub partial: bool,
}

impl DurationObs {
    /// `actual / est`, or `None` when there was no estimate.
    pub fn ratio(&self) -> Option<f64> {
        (self.est_min > 0).then(|| self.actual_min as f64 / self.est_min as f64)
    }
}

/// A break.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct BreakRecord {
    /// When it began.
    pub t: DateTime<FixedOffset>,
    /// The day it belongs to.
    pub day: NaiveDate,
    /// Planned minutes.
    pub planned_min: u32,
    /// Actual minutes, if logged.
    pub actual_min: Option<u32>,
    /// Where.
    pub r#where: Option<String>,
}

impl BreakRecord {
    /// Actual minutes, falling back to planned.
    pub fn actual_or_planned(&self) -> u32 {
        self.actual_min.unwrap_or(self.planned_min)
    }
}

/// An answered idle prompt.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct IdleRecord {
    /// When it was answered (the gap ends here).
    pub t: DateTime<FixedOffset>,
    /// The day it belongs to.
    pub day: NaiveDate,
    /// What the gap was attributed to.
    pub attributed: String,
    /// Length of the gap.
    pub min: u32,
}

/// An interruption (`interrupt` … `resume`).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Interruption {
    /// When it began (`None` for a `resume` without an `interrupt`).
    pub start: Option<DateTime<FixedOffset>>,
    /// When it ended (`None` while still open).
    pub end: Option<DateTime<FixedOffset>>,
    /// The day it belongs to.
    pub day: NaiveDate,
    /// The interrupted item.
    pub id: Option<String>,
    /// Minutes lost (from `resume`).
    pub lost_min: u32,
    /// Items dropped from the plan.
    pub dropped: Vec<String>,
}

/// A `tm event` occurrence.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct NamedEvent {
    /// When.
    pub t: DateTime<FixedOffset>,
    /// Event name.
    pub name: String,
    /// The item it was addressed to.
    pub id: Option<String>,
}

/// A demotion.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Demotion {
    /// When.
    pub t: DateTime<FixedOffset>,
    /// Item id.
    pub id: String,
    /// Horizon key left.
    pub from: String,
    /// Horizon key entered.
    pub to: String,
    /// Remaining estimate carried.
    pub est_min: u32,
    /// The stamp `from` implies (`W37` for `2026-W37`, `D07` for
    /// `2026-09-07`; none for a month key).
    pub stamp: Option<Stamp>,
}

/// A `close` event.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CloseRecord {
    /// When.
    pub t: DateTime<FixedOffset>,
    /// `day`, `week` or `month`.
    pub period: String,
    /// The period key.
    pub key: String,
}

/// The latest status of a routine instance.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct InstanceRecord {
    /// When it was set.
    pub t: DateTime<FixedOffset>,
    /// The status.
    pub status: InstanceStatus,
    /// The status string as logged.
    pub raw_status: String,
    /// Minutes it took, if logged.
    pub actual_min: Option<u32>,
}

/// A leak (for "longest single leak").
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LeakRecord {
    /// When it was attributed (the gap ends here).
    pub t: DateTime<FixedOffset>,
    /// The day.
    pub day: NaiveDate,
    /// Minutes.
    pub min: u32,
}

/// A block that was started and never closed.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct OpenBlock {
    /// Item id.
    pub id: String,
    /// When it started.
    pub started: DateTime<FixedOffset>,
    /// Worked minutes so far (closed sub-segments only).
    pub worked_min: u32,
    /// Running since (`None` while paused or interrupted).
    pub since: Option<DateTime<FixedOffset>>,
    /// Paused.
    pub paused: bool,
}

/// A `start` event (for adherence and start latency).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct StartRecord {
    /// When.
    pub t: DateTime<FixedOffset>,
    /// Item id.
    pub id: String,
    /// Predicted energy.
    pub pred: u8,
    /// Reported energy.
    pub rep: Option<u8>,
}

/// Per-day derived state.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct DayReplay {
    /// The day.
    pub date: NaiveDate,
    /// First `wake` of the day.
    pub wake: Option<DateTime<FixedOffset>>,
    /// Minutes slept (from `wake`).
    pub slept_min: Option<u32>,
    /// Sleep onset minutes (from `wake --onset`).
    pub onset_min: Option<u32>,
    /// First `arrive`.
    pub arrival: Option<DateTime<FixedOffset>>,
    /// Location at the first `arrive`.
    pub loc: Option<String>,
    /// Window from the first `arrive`.
    pub window: Option<[String; 2]>,
    /// Budget from the first `arrive`.
    pub budget: Option<u32>,
    /// Every location set today (`arrive` and `loc`), in order.
    pub loc_changes: Vec<(DateTime<FixedOffset>, String)>,
    /// First block start.
    pub first_start: Option<DateTime<FixedOffset>>,
    /// Every block start.
    pub starts: Vec<StartRecord>,
    /// Σ block minutes (done `actual_min` plus partial credit for cut blocks).
    pub block_min: u32,
    /// Blocks done (`done` events with `actual_min > 0`).
    pub blocks_done: u32,
    /// Σ `actual_min × ci / 5` over `done` events.
    pub load: f64,
    /// Minutes at each ci over `done` events (index = ci).
    pub minutes_by_ci: [u32; 6],
    /// Ids finished today (non-partial `done`), in order.
    pub done: Vec<String>,
    /// Σ `resume.lost_min`.
    pub lost_min: u32,
    /// Ids dropped by interruptions.
    pub dropped: Vec<String>,
    /// Σ `idle.min` attributed `leak`.
    pub leak_min: u32,
    /// Longest single leak.
    pub longest_leak: u32,
    /// Every answered idle prompt.
    pub idle: Vec<IdleRecord>,
    /// Breaks.
    pub breaks: Vec<BreakRecord>,
    /// Routine minutes (`routine … actual_min`).
    pub routine_min: u32,
    /// Number of `plan` events.
    pub plans: u32,
    /// Highest `replans_today` reported.
    pub replans_today: u32,
    /// Σ `plan.drift_min`.
    pub drift_min: u32,
    /// Hash of the last plan.
    pub last_plan_hash: Option<String>,
    /// Actual segments (blocks, pauses, interruptions, breaks, routines,
    /// idle gaps), by start time.
    pub segments: Vec<LogSegment>,
}

impl DayReplay {
    fn new(date: NaiveDate) -> DayReplay {
        DayReplay {
            date,
            wake: None,
            slept_min: None,
            onset_min: None,
            arrival: None,
            loc: None,
            window: None,
            budget: None,
            loc_changes: Vec::new(),
            first_start: None,
            starts: Vec::new(),
            block_min: 0,
            blocks_done: 0,
            load: 0.0,
            minutes_by_ci: [0; 6],
            done: Vec::new(),
            lost_min: 0,
            dropped: Vec::new(),
            leak_min: 0,
            longest_leak: 0,
            idle: Vec::new(),
            breaks: Vec::new(),
            routine_min: 0,
            plans: 0,
            replans_today: 0,
            drift_min: 0,
            last_plan_hash: None,
            segments: Vec::new(),
        }
    }

    /// Minutes from wake to arrival, if both are known.
    pub fn wake_to_arrive_min(&self) -> Option<i64> {
        Some(self.arrival?.signed_duration_since(self.wake?).num_minutes())
    }

    /// Minutes from arrival to the first block start, if both are known.
    pub fn arrive_to_start_min(&self) -> Option<i64> {
        Some(self.first_start?.signed_duration_since(self.arrival?).num_minutes())
    }

    /// Σ break minutes (actual or planned).
    pub fn break_min(&self) -> u32 {
        self.breaks.iter().map(BreakRecord::actual_or_planned).sum()
    }

    /// Block minutes with `ci ≥ 4` over `done` events.
    pub fn high_ci_min(&self) -> u32 {
        self.minutes_by_ci[4] + self.minutes_by_ci[5]
    }
}

/// Per-item derived state.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, Default)]
pub struct ItemReplay {
    /// Item id.
    pub id: String,
    /// Σ block minutes.
    pub minutes: u32,
    /// Blocks done (`done` events with `actual_min > 0`).
    pub blocks: u32,
    /// Block minutes per day.
    pub minutes_by_day: BTreeMap<NaiveDate, u32>,
    /// Non-partial `done` times.
    pub done_at: Vec<DateTime<FixedOffset>>,
    /// Partial `done` times.
    pub partial_done_at: Vec<DateTime<FixedOffset>>,
    /// Number of `stop` events.
    pub stops: u32,
    /// Σ `extend.by_min`.
    pub extended_min: u32,
}

/// Everything replay derives from the log.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Replay {
    /// Timezone used for day attribution.
    pub tz: Tz,
    /// The day range kept (`None` = everything).
    pub range: Option<RangeInclusive<NaiveDate>>,
    /// Per day.
    pub days: BTreeMap<NaiveDate, DayReplay>,
    /// Per item.
    pub items: BTreeMap<String, ItemReplay>,
    /// Routine instance statuses by `(item, inst)`.
    pub instances: BTreeMap<(String, String), InstanceRecord>,
    /// Energy observations in time order.
    pub energy: Vec<EnergyObs>,
    /// Duration observations in time order.
    pub durations: Vec<DurationObs>,
    /// Interruptions in time order.
    pub interrupts: Vec<Interruption>,
    /// `tm event` occurrences by name.
    pub events: BTreeMap<String, Vec<NamedEvent>>,
    /// Demotions by item id.
    pub demotions: BTreeMap<String, Vec<Demotion>>,
    /// `close` events.
    pub closes: Vec<CloseRecord>,
    /// Ids dropped (`drop`).
    pub dropped_items: BTreeSet<String>,
    /// Items with a non-partial `done`, or a routine instance done.
    pub done_items: BTreeSet<String>,
    /// Latest completion per item (non-partial `done`, or routine `done`).
    pub last_done: BTreeMap<String, DateTime<FixedOffset>>,
    /// Completion dates per item (routine `done` uses its `inst` when it is a
    /// date, else the day).
    pub done_dates: BTreeMap<String, BTreeSet<NaiveDate>>,
    /// The longest single leak.
    pub longest_leak: Option<LeakRecord>,
    /// A block started and not closed by the end of the log.
    pub open_block: Option<OpenBlock>,
    /// An interruption not yet resumed.
    pub open_interrupt: Option<Interruption>,
    /// Number of unknown events seen.
    pub unknown: u32,
    /// Inconsistencies noticed while replaying (a `done` for an item that was
    /// not started is fine; an unknown routine status is not).
    pub warnings: Vec<String>,
}

impl Replay {
    /// The day's record.
    pub fn day(&self, date: NaiveDate) -> Option<&DayReplay> {
        self.days.get(&date)
    }
    /// Σ block minutes for `id`.
    pub fn block_minutes(&self, id: &str) -> u32 {
        self.items.get(id).map_or(0, |i| i.minutes)
    }
    /// Block minutes for `id` on `date`.
    pub fn block_minutes_on(&self, id: &str, date: NaiveDate) -> u32 {
        self.items
            .get(id)
            .and_then(|i| i.minutes_by_day.get(&date).copied())
            .unwrap_or(0)
    }
    /// Blocks done on `date`.
    pub fn blocks_done(&self, date: NaiveDate) -> u32 {
        self.days.get(&date).map_or(0, |d| d.blocks_done)
    }
    /// Block minutes on `date`.
    pub fn block_minutes_on_day(&self, date: NaiveDate) -> u32 {
        self.days.get(&date).map_or(0, |d| d.block_min)
    }
    /// Leak minutes on `date`.
    pub fn leak_min(&self, date: NaiveDate) -> u32 {
        self.days.get(&date).map_or(0, |d| d.leak_min)
    }
    /// Lost minutes on `date`.
    pub fn lost_min(&self, date: NaiveDate) -> u32 {
        self.days.get(&date).map_or(0, |d| d.lost_min)
    }
    /// True when `id` has a non-partial `done` (or a routine instance done).
    pub fn is_done(&self, id: &str) -> bool {
        self.done_items.contains(id)
    }
    /// Latest completion of `id` (for after-done recurrence).
    pub fn last_done(&self, id: &str) -> Option<DateTime<FixedOffset>> {
        self.last_done.get(id).copied()
    }
    /// Completion dates of `id`, ascending (for calendar instances).
    pub fn done_dates(&self, id: &str) -> Vec<NaiveDate> {
        self.done_dates
            .get(id)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_default()
    }
    /// Status of a routine instance (`Pending` when nothing was logged).
    pub fn instance_status(&self, item: &str, inst: &str) -> InstanceStatus {
        self.instances
            .get(&(item.to_string(), inst.to_string()))
            .map_or(InstanceStatus::Pending, |r| r.status)
    }
    /// Occurrences of `tm event <name>`.
    pub fn events_named(&self, name: &str) -> &[NamedEvent] {
        self.events.get(name).map_or(&[], Vec::as_slice)
    }
    /// True when `name` was logged, optionally only after `since`, and
    /// optionally only when addressed to `id`.
    pub fn event_occurred(
        &self,
        name: &str,
        since: Option<DateTime<FixedOffset>>,
        id: Option<&str>,
    ) -> bool {
        self.events_named(name).iter().any(|e| {
            since.is_none_or(|s| e.t >= s) && id.is_none_or(|i| e.id.as_deref() == Some(i))
        })
    }
    /// Demotion stamps for `id`, in order.
    pub fn stamps(&self, id: &str) -> Vec<Stamp> {
        self.demotions
            .get(id)
            .map(|v| v.iter().filter_map(|d| d.stamp).collect())
            .unwrap_or_default()
    }
    /// Energy observations on `date`.
    pub fn energy_on(&self, date: NaiveDate) -> impl Iterator<Item = &EnergyObs> {
        self.energy.iter().filter(move |o| o.day == date)
    }
    /// Duration observations on `date`.
    pub fn durations_on(&self, date: NaiveDate) -> impl Iterator<Item = &DurationObs> {
        self.durations.iter().filter(move |o| o.day == date)
    }
    /// Σ block minutes over all days.
    pub fn total_block_min(&self) -> u32 {
        self.days.values().map(|d| d.block_min).sum()
    }
}

/// Parse a routine status string.
pub fn parse_instance_status(s: &str) -> Option<InstanceStatus> {
    match s {
        "done" => Some(InstanceStatus::Done),
        "pending" => Some(InstanceStatus::Pending),
        "missed" => Some(InstanceStatus::Missed),
        "expired" => Some(InstanceStatus::Expired),
        "skipped" | "skip" => Some(InstanceStatus::Skipped),
        _ => None,
    }
}

/// The stamp a `demote.from` key implies.
pub fn stamp_from_key(from: &str) -> Option<Stamp> {
    if let Ok(w) = IsoWeek::parse(from) {
        return Some(Stamp::Week(w.week));
    }
    if let Ok(d) = parse_date(from) {
        return Some(Stamp::Day(chrono::Datelike::day(&d)));
    }
    None
}

/// The block state machine.
struct Block {
    id: String,
    started: DateTime<FixedOffset>,
    since: Option<DateTime<FixedOffset>>,
    paused_at: Option<DateTime<FixedOffset>>,
    worked_min: u32,
    obs: Option<usize>,
}

struct Machine {
    days: DayIndex,
    range: Option<RangeInclusive<NaiveDate>>,
    out: Replay,
    block: Option<Block>,
    interrupt: Option<(DateTime<FixedOffset>, Option<String>)>,
}

impl Machine {
    fn in_range(&self, date: NaiveDate) -> bool {
        self.range.as_ref().is_none_or(|r| r.contains(&date))
    }

    fn day_mut(&mut self, date: NaiveDate) -> Option<&mut DayReplay> {
        if !self.in_range(date) {
            return None;
        }
        Some(
            self.out
                .days
                .entry(date)
                .or_insert_with(|| DayReplay::new(date)),
        )
    }

    fn item_mut(&mut self, id: &str) -> &mut ItemReplay {
        self.out.items.entry(id.to_string()).or_insert_with(|| ItemReplay {
            id: id.to_string(),
            ..ItemReplay::default()
        })
    }

    fn segment(&mut self, start: DateTime<FixedOffset>, end: DateTime<FixedOffset>, kind: SegmentKind) {
        let day = self.days.day_of(start);
        if let Some(d) = self.day_mut(day) {
            d.segments.push(LogSegment { start, end, kind });
        }
    }

    /// Close the running sub-segment of the open block at `t`.
    fn close_sub(&mut self, t: DateTime<FixedOffset>) {
        let Some(b) = self.block.as_mut() else {
            return;
        };
        let Some(since) = b.since.take() else {
            return;
        };
        let min = t.signed_duration_since(since).num_minutes().max(0) as u32;
        b.worked_min += min;
        let id = b.id.clone();
        if t > since {
            self.segment(since, t, SegmentKind::Block { id });
        }
    }

    fn credit(&mut self, id: &str, t: DateTime<FixedOffset>, min: u32) {
        let day = self.days.day_of(t);
        if !self.in_range(day) {
            return;
        }
        let it = self.item_mut(id);
        it.minutes += min;
        *it.minutes_by_day.entry(day).or_insert(0) += min;
        if let Some(d) = self.day_mut(day) {
            d.block_min += min;
        }
    }

    /// Cut the open block at `t` (stop, or a start of another block): its
    /// worked minutes are credited.
    fn cut(&mut self, t: DateTime<FixedOffset>) -> Option<Block> {
        self.close_sub(t);
        let b = self.block.take()?;
        self.credit(&b.id, t, b.worked_min);
        Some(b)
    }

    fn mark_done(&mut self, id: &str, t: DateTime<FixedOffset>, date: NaiveDate) {
        let day = self.days.day_of(t);
        if !self.in_range(day) {
            return;
        }
        self.out.done_items.insert(id.to_string());
        self.out.last_done.insert(id.to_string(), t);
        self.out
            .done_dates
            .entry(id.to_string())
            .or_default()
            .insert(date);
    }

    fn step(&mut self, e: &LogEntry) {
        let t = e.t;
        let day = self.days.day_of(t);
        match &e.ev {
            Event::Wake {
                slept_min,
                onset_min,
            } => {
                if let Some(d) = self.day_mut(day) {
                    if d.wake.is_none() {
                        d.wake = Some(t);
                        d.slept_min = Some(*slept_min);
                        d.onset_min = *onset_min;
                    }
                }
            }
            Event::Arrive {
                loc,
                window,
                budget,
            } => {
                if let Some(d) = self.day_mut(day) {
                    if d.arrival.is_none() {
                        d.arrival = Some(t);
                        d.loc = Some(loc.clone());
                        d.window = Some(window.clone());
                        d.budget = Some(*budget);
                    }
                    d.loc_changes.push((t, loc.clone()));
                }
            }
            Event::Loc { loc } => {
                if let Some(d) = self.day_mut(day) {
                    d.loc_changes.push((t, loc.clone()));
                }
            }
            Event::Start {
                id,
                pred,
                rep,
                hsw,
                slept_min,
                loc,
                ..
            } => {
                self.cut(t);
                let mut obs = None;
                if self.in_range(day) {
                    if let Some(rep) = rep {
                        obs = Some(self.out.energy.len());
                        self.out.energy.push(EnergyObs {
                            t,
                            day,
                            pred: *pred,
                            rep: *rep,
                            hsw: *hsw,
                            loc: loc.clone(),
                            slept_min: Some(*slept_min),
                            went: None,
                            id: Some(id.clone()),
                            from_start: true,
                        });
                    }
                    if let Some(d) = self.day_mut(day) {
                        if d.first_start.is_none() {
                            d.first_start = Some(t);
                        }
                        d.starts.push(StartRecord {
                            t,
                            id: id.clone(),
                            pred: *pred,
                            rep: *rep,
                        });
                    }
                }
                // A block started during an interruption runs from resume.
                let since = self.interrupt.is_none().then_some(t);
                self.block = Some(Block {
                    id: id.clone(),
                    started: t,
                    since,
                    paused_at: None,
                    worked_min: 0,
                    obs,
                });
            }
            Event::Pause { id } => {
                if self.block.as_ref().is_some_and(|b| &b.id == id) {
                    self.close_sub(t);
                    if let Some(b) = self.block.as_mut() {
                        if b.paused_at.is_none() {
                            b.paused_at = Some(t);
                        }
                    }
                }
            }
            Event::Unpause { id } => {
                if self.block.as_ref().is_some_and(|b| &b.id == id) {
                    let paused_at = self.block.as_mut().and_then(|b| b.paused_at.take());
                    if let Some(p) = paused_at {
                        self.segment(p, t, SegmentKind::Pause { id: id.clone() });
                    }
                    if self.interrupt.is_none() {
                        if let Some(b) = self.block.as_mut() {
                            b.since = Some(t);
                        }
                    }
                }
            }
            Event::Interrupt { id } => {
                self.close_sub(t);
                if self.interrupt.is_none() {
                    let who = id
                        .clone()
                        .or_else(|| self.block.as_ref().map(|b| b.id.clone()));
                    self.interrupt = Some((t, who));
                }
            }
            Event::Resume { lost_min, dropped } => {
                let open = self.interrupt.take();
                let (start, id) = match open {
                    Some((s, id)) => (Some(s), id),
                    None => (None, None),
                };
                if let Some(s) = start {
                    self.segment(s, t, SegmentKind::Interrupt { id: id.clone() });
                }
                let rec_day = start.map_or(day, |s| self.days.day_of(s));
                if self.in_range(rec_day) {
                    self.out.interrupts.push(Interruption {
                        start,
                        end: Some(t),
                        day: rec_day,
                        id,
                        lost_min: *lost_min,
                        dropped: dropped.clone(),
                    });
                }
                if let Some(d) = self.day_mut(rec_day) {
                    d.lost_min += lost_min;
                    d.dropped.extend(dropped.iter().cloned());
                }
                if let Some(b) = self.block.as_mut() {
                    if b.paused_at.is_none() && b.since.is_none() {
                        b.since = Some(t);
                    }
                }
            }
            Event::Done {
                id,
                est_min,
                actual_min,
                went,
                tags,
                ci,
                partial,
            } => {
                let matched = self.block.as_ref().is_some_and(|b| &b.id == id);
                if matched {
                    self.close_sub(t);
                    let b = self.block.take().expect("matched");
                    if let (Some(i), Some(w)) = (b.obs, went) {
                        if let Some(o) = self.out.energy.get_mut(i) {
                            o.went = Some(*w);
                        }
                    }
                }
                self.credit(id, t, *actual_min);
                if self.in_range(day) {
                    if *actual_min > 0 {
                        self.item_mut(id).blocks += 1;
                        let ci_idx = (*ci).min(5) as usize;
                        if let Some(d) = self.day_mut(day) {
                            d.blocks_done += 1;
                            d.load += *actual_min as f64 * *ci as f64 / 5.0;
                            d.minutes_by_ci[ci_idx] += actual_min;
                        }
                        self.out.durations.push(DurationObs {
                            t,
                            day,
                            id: id.clone(),
                            ci: *ci,
                            tags: tags.clone(),
                            est_min: *est_min,
                            actual_min: *actual_min,
                            went: *went,
                            partial: *partial,
                        });
                    }
                    if *partial {
                        self.item_mut(id).partial_done_at.push(t);
                    } else {
                        self.item_mut(id).done_at.push(t);
                        if let Some(d) = self.day_mut(day) {
                            d.done.push(id.clone());
                        }
                        self.mark_done(id, t, day);
                    }
                }
            }
            Event::Stop { id, .. } => {
                if self.block.as_ref().is_some_and(|b| &b.id == id) {
                    self.cut(t);
                    if self.in_range(day) {
                        self.item_mut(id).stops += 1;
                    }
                }
            }
            Event::Extend { id, by_min } => {
                if self.in_range(day) {
                    self.item_mut(id).extended_min += by_min;
                }
            }
            Event::Break {
                planned_min,
                actual_min,
                r#where,
            } => {
                let len = actual_min.unwrap_or(*planned_min);
                self.segment(
                    t,
                    t + Duration::minutes(len as i64),
                    SegmentKind::Break {
                        r#where: r#where.clone(),
                    },
                );
                if let Some(d) = self.day_mut(day) {
                    d.breaks.push(BreakRecord {
                        t,
                        day,
                        planned_min: *planned_min,
                        actual_min: *actual_min,
                        r#where: r#where.clone(),
                    });
                }
            }
            Event::Energy {
                pred,
                rep,
                hsw,
                loc,
            } => {
                if self.in_range(day) {
                    let slept = self.out.days.get(&day).and_then(|d| d.slept_min);
                    self.out.energy.push(EnergyObs {
                        t,
                        day,
                        pred: *pred,
                        rep: *rep,
                        hsw: *hsw,
                        loc: loc.clone(),
                        slept_min: slept,
                        went: None,
                        id: None,
                        from_start: false,
                    });
                }
            }
            Event::Idle { attributed, min } => {
                let start = t - Duration::minutes(*min as i64);
                let seg_day = self.days.day_of(start);
                if let Some(d) = self.day_mut(seg_day) {
                    d.segments.push(LogSegment {
                        start,
                        end: t,
                        kind: SegmentKind::Idle {
                            attributed: attributed.clone(),
                        },
                    });
                    d.idle.push(IdleRecord {
                        t,
                        day: seg_day,
                        attributed: attributed.clone(),
                        min: *min,
                    });
                    if attributed == "leak" {
                        d.leak_min += min;
                        d.longest_leak = d.longest_leak.max(*min);
                        if self.out.longest_leak.as_ref().is_none_or(|l| *min > l.min) {
                            self.out.longest_leak = Some(LeakRecord {
                                t,
                                day: seg_day,
                                min: *min,
                            });
                        }
                    }
                }
            }
            Event::Routine {
                item,
                inst,
                status,
                actual_min,
            } => {
                let parsed = parse_instance_status(status);
                if parsed.is_none() {
                    self.out
                        .warnings
                        .push(format!("{}: unknown routine status {status:?}", fmt_timestamp(&t)));
                }
                let st = parsed.unwrap_or(InstanceStatus::Pending);
                if self.in_range(day) {
                    self.out.instances.insert(
                        (item.clone(), inst.clone()),
                        InstanceRecord {
                            t,
                            status: st,
                            raw_status: status.clone(),
                            actual_min: *actual_min,
                        },
                    );
                }
                if st == InstanceStatus::Done {
                    let date = parse_date(inst).unwrap_or(day);
                    self.mark_done(item, t, date);
                    if let Some(min) = actual_min {
                        let start = t - Duration::minutes(*min as i64);
                        self.segment(
                            start,
                            t,
                            SegmentKind::Routine {
                                item: item.clone(),
                                inst: inst.clone(),
                            },
                        );
                        if let Some(d) = self.day_mut(day) {
                            d.routine_min += min;
                        }
                    }
                }
            }
            Event::Skip { item, inst } => {
                if self.in_range(day) {
                    self.out.instances.insert(
                        (item.clone(), inst.clone()),
                        InstanceRecord {
                            t,
                            status: InstanceStatus::Skipped,
                            raw_status: "skipped".to_string(),
                            actual_min: None,
                        },
                    );
                }
            }
            Event::Plan {
                hash,
                replans_today,
                drift_min,
            } => {
                if let Some(d) = self.day_mut(day) {
                    d.plans += 1;
                    d.replans_today = d.replans_today.max(*replans_today);
                    d.drift_min += drift_min;
                    d.last_plan_hash = Some(hash.clone());
                }
            }
            Event::Named { name, id } => {
                if self.in_range(day) {
                    self.out.events.entry(name.clone()).or_default().push(NamedEvent {
                        t,
                        name: name.clone(),
                        id: id.clone(),
                    });
                }
            }
            Event::Demote {
                id,
                from,
                to,
                est_min,
            } => {
                if self.in_range(day) {
                    self.out.demotions.entry(id.clone()).or_default().push(Demotion {
                        t,
                        id: id.clone(),
                        from: from.clone(),
                        to: to.clone(),
                        est_min: *est_min,
                        stamp: stamp_from_key(from),
                    });
                }
            }
            Event::Drop { id } => {
                if self.in_range(day) {
                    self.out.dropped_items.insert(id.clone());
                }
            }
            Event::Close { period, key } => {
                if self.in_range(day) {
                    self.out.closes.push(CloseRecord {
                        t,
                        period: period.clone(),
                        key: key.clone(),
                    });
                }
            }
            Event::Readopt { .. } | Event::Move { .. } | Event::Edit { .. } | Event::Note { .. } => {}
            Event::Undo { .. } => {
                // Undo entries are removed by the mask before replay; one
                // reaching here means the caller passed raw entries.
            }
            Event::Unknown { .. } => self.out.unknown += 1,
        }
    }

    fn finish(mut self) -> Replay {
        if let Some(b) = self.block.take() {
            self.out.open_block = Some(OpenBlock {
                id: b.id,
                started: b.started,
                worked_min: b.worked_min,
                since: b.since,
                paused: b.paused_at.is_some(),
            });
        }
        if let Some((s, id)) = self.interrupt.take() {
            self.out.open_interrupt = Some(Interruption {
                start: Some(s),
                end: None,
                day: self.days.day_of(s),
                id,
                lost_min: 0,
                dropped: Vec::new(),
            });
        }
        for d in self.out.days.values_mut() {
            d.segments.sort_by_key(|s| s.start);
        }
        self.out
    }
}

/// Derive state from `entries` (already undo-filtered; use [`Log::replay`]
/// for the mask). The block state machine runs over every entry; only
/// results dated inside `range` (wake-aware days, see [`DayIndex`]) are kept.
pub fn replay(entries: &[LogEntry], range: Option<RangeInclusive<NaiveDate>>, tz: Tz) -> Replay {
    let refs: Vec<&LogEntry> = entries.iter().collect();
    replay_refs(&refs, range, tz)
}

fn replay_refs(entries: &[&LogEntry], range: Option<RangeInclusive<NaiveDate>>, tz: Tz) -> Replay {
    let days = DayIndex::new(
        tz,
        entries
            .iter()
            .filter(|e| matches!(e.ev, Event::Wake { .. }))
            .map(|e| e.t),
    );
    let mut m = Machine {
        days,
        range: range.clone(),
        out: Replay {
            tz,
            range,
            days: BTreeMap::new(),
            items: BTreeMap::new(),
            instances: BTreeMap::new(),
            energy: Vec::new(),
            durations: Vec::new(),
            interrupts: Vec::new(),
            events: BTreeMap::new(),
            demotions: BTreeMap::new(),
            closes: Vec::new(),
            dropped_items: BTreeSet::new(),
            done_items: BTreeSet::new(),
            last_done: BTreeMap::new(),
            done_dates: BTreeMap::new(),
            longest_leak: None,
            open_block: None,
            open_interrupt: None,
            unknown: 0,
            warnings: Vec::new(),
        },
        block: None,
        interrupt: None,
    };
    for e in entries {
        m.step(e);
    }
    m.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(s: &str) -> DateTime<FixedOffset> {
        parse_timestamp(s).unwrap()
    }

    fn entry(s: &str, ev: Event) -> LogEntry {
        LogEntry::new(at(s), ev)
    }

    #[test]
    fn timestamp_round_trip() {
        let t = at("2026-09-07T06:05:00-05:00");
        assert_eq!(fmt_timestamp(&t), "2026-09-07T06:05:00-05:00");
        assert_eq!(at("2026-09-07T06:05-05:00"), t);
        assert!(parse_timestamp("2026-09-07T06:05").is_err());
        let e = entry("2026-09-07T06:05:00-05:00", Event::Wake { slept_min: 490, onset_min: None });
        let j = e.to_json().unwrap();
        assert_eq!(j, r#"{"t":"2026-09-07T06:05:00-05:00","ev":"wake","slept_min":490}"#);
        assert_eq!(LogEntry::parse(&j).unwrap(), e);
    }

    #[test]
    fn unknown_event_round_trips() {
        let line = r#"{"t":"2026-09-07T06:05:00-05:00","ev":"zorg","bar":"baz","foo":1}"#;
        let e = LogEntry::parse(line).unwrap();
        match &e.ev {
            Event::Unknown { ev, rest } => {
                assert_eq!(ev, "zorg");
                assert_eq!(rest.len(), 2);
                assert_eq!(rest["foo"], Value::from(1));
            }
            other => panic!("{other:?}"),
        }
        assert_eq!(e.ev.name(), "zorg");
        assert_eq!(e.to_json().unwrap(), line);
        // A known name with a bad payload is an error, not Unknown.
        assert!(LogEntry::parse(r#"{"t":"2026-09-07T06:05:00-05:00","ev":"wake"}"#).is_err());
        assert!(LogEntry::parse(r#"{"ev":"note","text":"x"}"#).is_err());
        assert!(LogEntry::parse(r#"{"t":"2026-09-07T06:05:00-05:00"}"#).is_err());
    }

    #[test]
    fn hsw_matches_spec() {
        let wake = at("2026-09-07T06:05:00-05:00");
        assert_eq!(hours_since_wake(&at("2026-09-07T07:02:00-05:00"), &wake), 0.95);
        assert_eq!(hours_since_wake(&at("2026-09-07T09:32:00-05:00"), &wake), 3.45);
        assert_eq!(hours_since_wake(&at("2026-09-07T06:05:00-05:00"), &wake), 0.0);
        // Different offsets compare by instant.
        assert_eq!(hours_since_wake(&at("2026-09-07T13:05:00+01:00"), &wake), 0.0);
    }

    #[test]
    fn day_index_wake_to_wake() {
        let tz = Tz::America__Chicago;
        let idx = DayIndex::new(
            tz,
            [at("2026-09-07T06:05:00-05:00"), at("2026-09-08T06:40:00-05:00")],
        );
        let d7 = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
        let d8 = NaiveDate::from_ymd_opt(2026, 9, 8).unwrap();
        let d9 = NaiveDate::from_ymd_opt(2026, 9, 9).unwrap();
        assert_eq!(idx.day_of(at("2026-09-07T06:05:00-05:00")), d7);
        assert_eq!(idx.day_of(at("2026-09-08T00:30:00-05:00")), d7, "after midnight, before the next wake");
        assert_eq!(idx.day_of(at("2026-09-08T06:20:00-05:00")), d8, "stale wake: calendar date");
        assert_eq!(idx.day_of(at("2026-09-08T06:40:00-05:00")), d8);
        assert_eq!(idx.day_of(at("2026-09-09T00:30:00-05:00")), d8);
        assert_eq!(idx.day_of(at("2026-09-09T07:00:00-05:00")), d9, "no wake on the 9th: calendar date");
        assert_eq!(idx.day_of(at("2026-09-07T05:00:00-05:00")), d7, "before the first wake: calendar date");
        assert_eq!(idx.wake_of(d7), Some(at("2026-09-07T06:05:00-05:00")));
        assert_eq!(idx.wake_of(d9), None);
        assert_eq!(
            idx.bounds(d7),
            (at("2026-09-07T00:00:00-05:00"), at("2026-09-08T06:05:00-05:00"))
        );
        assert_eq!(
            idx.bounds(d8),
            (at("2026-09-08T06:05:00-05:00"), at("2026-09-09T06:40:00-05:00"))
        );
        assert_eq!(
            idx.bounds(d9),
            (at("2026-09-09T06:40:00-05:00"), at("2026-09-10T00:00:00-05:00"))
        );
        // Every bound agrees with day_of.
        for d in [d7, d8, d9] {
            let (s, e) = idx.bounds(d);
            assert_eq!(idx.day_of(s), d);
            assert_ne!(idx.day_of(e), d);
            assert_eq!(idx.day_of(e - Duration::seconds(1)), d);
        }
        let empty = DayIndex::new(tz, []);
        assert_eq!(empty.day_of(at("2026-09-08T00:30:00-05:00")), d8);
        assert_eq!(
            empty.bounds(d8),
            (at("2026-09-08T00:00:00-05:00"), at("2026-09-09T00:00:00-05:00"))
        );
        // UTC-written entries are attributed in the configured zone.
        assert_eq!(empty.day_of(at("2026-09-08T03:00:00+00:00")), d7);
    }

    #[test]
    fn undo_mask_pairs_and_dangling() {
        let log = Log::from_entries(vec![
            entry("2026-09-07T08:00:00-05:00", Event::Done { id: "a".into(), est_min: 60, actual_min: 60, went: None, tags: vec![], ci: 3, partial: false }),
            entry("2026-09-07T08:01:00-05:00", Event::Done { id: "b".into(), est_min: 60, actual_min: 60, went: None, tags: vec![], ci: 3, partial: false }),
            entry("2026-09-07T08:02:00-05:00", Event::Undo { of: "done".into(), id: Some("a".into()) }),
            entry("2026-09-07T08:03:00-05:00", Event::Undo { of: "done".into(), id: None }),
            entry("2026-09-07T08:04:00-05:00", Event::Undo { of: "done".into(), id: None }),
            entry("2026-09-07T08:05:00-05:00", Event::Note { text: "n".into() }),
            entry("2026-09-07T08:06:00-05:00", Event::Undo { of: "undo".into(), id: None }),
        ]);
        let m = log.undo_mask();
        assert_eq!(m.cancelled, vec![true, true, true, true, true, false, true]);
        assert_eq!(m.dangling, vec![4, 6]);
        assert_eq!(m.pairs(), 2);
        assert_eq!(log.effective().count(), 1);
        assert!(log.undo_target().is_none(), "notes are not state changes");
        let log = Log::from_entries(vec![
            entry("2026-09-07T08:00:00-05:00", Event::Start { id: "a".into(), pred: 5, rep: None, hsw: 1.0, slept_min: 0, loc: "lounge".into(), blocks_done: 0, since_break_min: 0 }),
            entry("2026-09-07T08:05:00-05:00", Event::Plan { hash: "x".into(), replans_today: 1, drift_min: 0 }),
        ]);
        assert_eq!(
            log.compensating_undo(),
            Some(Event::Undo { of: "start".into(), id: Some("a".into()) })
        );
    }

    #[test]
    fn parse_tolerates_bad_lines() {
        let text = "\n{\"t\":\"2026-09-07T06:05:00-05:00\",\"ev\":\"wake\",\"slept_min\":490}\r\nnot json\n{\"ev\":\"note\"}\n";
        let log = Log::parse(text);
        assert_eq!(log.entries.len(), 1);
        assert_eq!(log.warnings.len(), 2);
        assert_eq!(log.warnings[0].line, 3);
        assert_eq!(log.warnings[0].text, "not json");
        assert_eq!(log.warnings[1].line, 4);
        assert!(log.warnings[1].to_string().contains("line 4"));
    }

    #[test]
    fn stamps_and_statuses() {
        assert_eq!(stamp_from_key("2026-W37"), Some(Stamp::Week(37)));
        assert_eq!(stamp_from_key("2026-09-07"), Some(Stamp::Day(7)));
        assert_eq!(stamp_from_key("2026-09"), None);
        assert_eq!(parse_instance_status("done"), Some(InstanceStatus::Done));
        assert_eq!(parse_instance_status("skip"), Some(InstanceStatus::Skipped));
        assert_eq!(parse_instance_status("nope"), None);
    }

    #[test]
    fn replay_credits_cut_blocks() {
        let tz = Tz::America__Chicago;
        let start = |s: &str, id: &str| {
            entry(s, Event::Start { id: id.into(), pred: 5, rep: Some(5), hsw: 1.0, slept_min: 480, loc: "lounge".into(), blocks_done: 0, since_break_min: 0 })
        };
        let log = Log::from_entries(vec![
            entry("2026-09-07T06:00:00-05:00", Event::Wake { slept_min: 480, onset_min: None }),
            start("2026-09-07T07:00:00-05:00", "a"),
            entry("2026-09-07T07:30:00-05:00", Event::Pause { id: "a".into() }),
            entry("2026-09-07T07:40:00-05:00", Event::Unpause { id: "a".into() }),
            entry("2026-09-07T08:00:00-05:00", Event::Interrupt { id: None }),
            entry("2026-09-07T08:20:00-05:00", Event::Resume { lost_min: 20, dropped: vec!["z".into()] }),
            entry("2026-09-07T09:00:00-05:00", Event::Stop { id: "a".into(), remaining_min: 30 }),
            start("2026-09-07T09:00:00-05:00", "b"),
            start("2026-09-07T09:45:00-05:00", "c"),
            entry("2026-09-07T10:45:00-05:00", Event::Done { id: "c".into(), est_min: 60, actual_min: 60, went: Some(3), tags: vec!["x".into()], ci: 4, partial: false }),
            start("2026-09-07T11:00:00-05:00", "d"),
        ]);
        let r = log.replay(None, tz);
        let d7 = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
        // a: 120 elapsed − 10 paused − 20 interrupted = 90.
        assert_eq!(r.block_minutes("a"), 90);
        assert_eq!(r.block_minutes("b"), 45, "cut by the next start");
        assert_eq!(r.block_minutes("c"), 60);
        assert_eq!(r.block_minutes("d"), 0, "still open");
        assert_eq!(r.open_block.as_ref().map(|b| b.id.as_str()), Some("d"));
        assert_eq!(r.blocks_done(d7), 1);
        assert_eq!(r.block_minutes_on_day(d7), 195);
        assert_eq!(r.lost_min(d7), 20);
        assert_eq!(r.day(d7).unwrap().dropped, vec!["z"]);
        assert_eq!(r.day(d7).unwrap().load, 48.0);
        assert_eq!(r.day(d7).unwrap().minutes_by_ci[4], 60);
        assert_eq!(r.energy.len(), 4);
        assert_eq!(r.energy[2].went, Some(3));
        assert_eq!(r.energy[2].weight(), 2.0);
        assert_eq!(r.energy[0].went, None);
        assert_eq!(r.interrupts.len(), 1);
        assert_eq!(r.interrupts[0].id.as_deref(), Some("a"));
        assert!(r.is_done("c") && !r.is_done("a"));
        let segs = &r.day(d7).unwrap().segments;
        let kinds: Vec<String> = segs
            .iter()
            .map(|s| format!("{}-{} {:?}", s.start.format("%H:%M"), s.end.format("%H:%M"), s.kind))
            .collect();
        assert_eq!(
            kinds,
            vec![
                "07:00-07:30 Block { id: \"a\" }",
                "07:30-07:40 Pause { id: \"a\" }",
                "07:40-08:00 Block { id: \"a\" }",
                "08:00-08:20 Interrupt { id: Some(\"a\") }",
                "08:20-09:00 Block { id: \"a\" }",
                "09:00-09:45 Block { id: \"b\" }",
                "09:45-10:45 Block { id: \"c\" }",
            ]
        );
        // A range outside the day keeps nothing.
        let d8 = NaiveDate::from_ymd_opt(2026, 9, 8).unwrap();
        let r = log.replay(Some(d8..=d8), tz);
        assert!(r.days.is_empty() && r.items.is_empty() && r.energy.is_empty());
        assert!(r.open_block.is_some(), "the machine still ran");
    }
}
