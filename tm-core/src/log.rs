//! Log — tm-spec-v1.md §10.1 `.tm/log.jsonl`: append-only JSONL events and
//! the replay that derives block, instance and monitor state (§5.1 instance
//! status, §6.4 `done_minutes`, §9 events, §11 monitor inputs, §13 `tm undo`).
//!
//! # API overview
//!
//! * [`Event`] — one variant per event kind with the §10.1 field names
//!   (`#[serde(tag = "ev")]`, lowercase names; [`EVENT_NAMES`] lists them).
//!   Unknown event names deserialize into [`Event::Unknown`]`{ ev, rest }`
//!   and serialize back with every key and value intact — `rest` is a
//!   `serde_json::Map`, so the keys come out **sorted**, which is
//!   value-lossless but not byte-identical for a line written with unsorted
//!   keys. Unknown *extra* keys on a **known** event are dropped on
//!   re-serialization; nothing rewrites `log.jsonl` (§10.1 is append-only),
//!   so this only affects [`Log::to_jsonl`]. A known name with a bad payload
//!   is a parse error naming the field, never an `Unknown`.
//!   [`Event::name`] is the `ev` tag, [`Event::primary_id`] the item/instance
//!   id an event is about, [`Event::is_state_change`] says whether `tm undo`
//!   may target it.
//! * [`LogEntry`]`{ t: DateTime<FixedOffset>, ev }` — one line; `t` is
//!   written RFC 3339 with the local offset (`2026-09-07T06:05:00-05:00`).
//!   [`LogEntry::to_json`] / [`LogEntry::parse`] convert one line.
//! * [`Log`] — the entries plus the [`LogWarning`]s for lines that did not
//!   parse. [`Log::read`]`(path)` (missing file → empty; malformed lines,
//!   invalid UTF-8 included, → warnings; never an error for content),
//!   [`Log::parse`]`(text)` / [`Log::parse_bytes`]`(bytes)`,
//!   [`Log::append`]`(path, &entry)` / [`Log::append_all`] (create `.tm/`,
//!   one object per line), [`Log::to_jsonl`], [`Log::iter_day`]`(date, tz)`,
//!   [`Log::iter_range`]`(from, to, tz)`, [`Log::iter_item`]`(id)`.
//! * Undo (§10.1, §13): `undo{of, id?}` cancels the most recent
//!   not-yet-undone event of kind `of` (with that primary id when given).
//!   [`undo_mask`] / [`Log::undo_mask`] compute which entries are cancelled
//!   (the target and the undo itself; a dangling undo cancels only itself),
//!   [`Log::effective`] iterates the survivors, [`Log::undo_target`] /
//!   [`Log::compensating_undo`] pick what `tm undo` should cancel next.
//!   Every replay and iterator below applies the mask first.
//! * Days: [`DayIndex`] — a day runs from `wake` to the next `wake`; an
//!   entry belongs to the calendar date (in `tz`) of the last `wake` at or
//!   before it when that wake is less than 24 h earlier, else to its own
//!   calendar date. Only the first `wake` of a date counts, so a day is
//!   never longer than 24 h. [`DayIndex::day_of`], [`DayIndex::bounds`],
//!   [`DayIndex::wake_of`]; [`Log::day_index`]`(tz)` builds one.
//!   [`hours_since_wake`]`(t, wake)` gives `hsw` rounded to 0.01.
//! * [`replay`]`(entries, range, tz) -> `[`Replay`] (also [`Log::replay`]):
//!   per-day [`DayReplay`] (wake/arrive, block minutes, blocks done, load,
//!   energy mix, lost, leak, idle, breaks, plans, starts, done ids, actual
//!   [`LogSegment`]s), per-item [`ItemReplay`] (minutes, blocks, by day,
//!   done times), [`InstanceRecord`]s as `item → inst → record`,
//!   [`EnergyObs`], [`DurationObs`], [`Interruption`]s, [`NamedRecord`]s (the
//!   latest `tm event` per `(name, id?)`, not the occurrence list),
//!   [`Demotion`]s with stamps, [`CloseRecord`]s, the longest leak, the
//!   still-open block. Helpers: `block_minutes(id)`, `blocks_done(date)`,
//!   `is_done(id)`, `last_done(id)`, `done_dates(id)`,
//!   `instance_status(item, inst)`, `instances_of(item)`, `stamps(id)`,
//!   `event_names()`, `latest_named(name, id, tz)`, `breaks()`,
//!   `done_minutes_map()` (§6.4, keyed by [`crate::model::Id`] for
//!   `tree::done_minutes`), [`DayReplay::gaps`] (unattributed gaps for
//!   the §11 leak ledger), and `seam(date)`, the [`DaySeam`] facts the
//!   CLI and TUI once walked the log for. [`Replay::view`] is every entry's
//!   **header** — physical line, tag, id, `t`, day and mask bit ([`ViewRow`],
//!   `tm log`'s rows; the line's payload comes from its own bytes, not from
//!   here), [`Replay::entry_count`] their number,
//!   [`Replay::headers_from`]`(line)` the rows from a physical line on
//!   (`tm undo`'s recorder). `Replay` is
//!   `Serialize`/`Deserialize` (JSON-safe: every map key is a string or a
//!   date) for `--json` output.
//!
//! # Event conventions (what the writers log, what replay assumes)
//!
//! * `wake.t` is the wake time; `arrive.t` the arrival; `start.t` the block
//!   start. `done.actual_min` is authoritative for the block's minutes: a
//!   `done` that closes a block already cut by `stop` (with no block started
//!   in between) *replaces* its partial credit instead of adding to it.
//! * `stop{id, remaining_min}` cuts an active block: it gets partial credit
//!   for its worked minutes — elapsed since `start` minus paused
//!   (`pause`…`unpause`) and interrupted (`interrupt`…`resume`) time. A
//!   `start` while another block is open cuts the open block the same way.
//!   A block still open at the end of the log gets no credit; it is
//!   reported as [`Replay::open_block`]. Neither `stop` nor `start` carries a
//!   `ci`, so a cut block's minutes land in [`DayReplay::ci_unknown`] rather
//!   than in `minutes_by_ci`/`load_fifths`; `Σ minutes_by_ci + ci_unknown_min() ==
//!   block_min` (§11 needs the tree to attribute the rest).
//! * `pause`/`unpause` bracket a `Pause` segment. §13 has `tm pause` but no
//!   `tm unpause`, so a block closed while still paused is ordinary: the
//!   pause is closed by the `done`/`stop`/next `start` (or by an interruption
//!   inside it, which splits it in two). An `unpause` with no `pause` open is
//!   a no-op.
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

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::io::{Read, Seek, SeekFrom, Write};
use std::ops::RangeInclusive;
use std::path::Path;

use chrono::{DateTime, Duration, FixedOffset, NaiveDate, SecondsFormat, TimeZone};
use chrono_tz::Tz;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use thiserror::Error;

use crate::model::{parse_date, Id, InstanceStatus, IsoWeek, Stamp};

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

/// Defines [`Event`] (the public enum, one variant per event kind plus
/// `Unknown`) and a private fallback-free mirror used for deserializing
/// known names, from one variant list. Each entry is
/// `Variant => "ev-tag" { fields }`.
macro_rules! define_events {
    (
        $(
            $(#[$vmeta:meta])*
            $variant:ident => $name:literal {
                $(
                    $(#[$fmeta:meta])*
                    $field:ident : $ty:ty
                ),* $(,)?
            }
        ),* $(,)?
    ) => {
        /// One log event (§10.1). Field names are the JSON keys; the `ev`
        /// tag is the lowercase variant name (`Named` is `event`).
        ///
        /// Deserializing: a known `ev` is decoded strictly (a missing or
        /// mistyped field is an error naming the event and the field); any
        /// other `ev` becomes [`Event::Unknown`] with every other key kept
        /// in `rest`, and serializes back losslessly.
        #[derive(Clone, Debug, PartialEq, Serialize)]
        #[serde(tag = "ev")]
        pub enum Event {
            $(
                $(#[$vmeta])*
                #[serde(rename = $name)]
                $variant {
                    $(
                        $(#[$fmeta])*
                        $field: $ty
                    ),*
                },
            )*
            /// Any event kind this version does not know; kept verbatim. A
            /// known `ev` with an invalid payload is a parse error, never an
            /// `Unknown`.
            #[serde(untagged)]
            Unknown {
                /// The `ev` tag (never one of [`EVENT_NAMES`]).
                ev: String,
                /// Every other field, in key order.
                #[serde(flatten)]
                rest: Map<String, Value>,
            },
        }

        /// The known variants only: derived, so a bad payload reports the
        /// offending field instead of falling through to `Unknown`.
        #[derive(Deserialize)]
        #[serde(tag = "ev")]
        enum Known {
            $(
                #[serde(rename = $name)]
                $variant {
                    $(
                        $(#[$fmeta])*
                        $field: $ty
                    ),*
                },
            )*
        }

        impl From<Known> for Event {
            fn from(k: Known) -> Event {
                match k {
                    $( Known::$variant { $($field),* } => Event::$variant { $($field),* }, )*
                }
            }
        }

        impl Known {
            /// The first field of event `ev` present in `map` whose value does
            /// not match its declared type, as `"<field>: <reason>"`. Used to
            /// turn serde's positional type error into one that names the
            /// field; `None` when every present field decodes (the failure was
            /// a missing field, which serde already names).
            fn field_error(ev: &str, map: &Map<String, Value>) -> Option<String> {
                match ev {
                    $(
                        $name => {
                            $(
                                let key = stringify!($field).trim_start_matches("r#");
                                if let Some(v) = map.get(key) {
                                    if let Err(e) = serde_json::from_value::<$ty>(v.clone()) {
                                        return Some(format!("{key}: {e}"));
                                    }
                                }
                            )*
                            None
                        }
                    )*
                    _ => None,
                }
            }
        }

        /// The known `ev` tags, in §10.1 order.
        pub const EVENT_NAMES: &[&str] = &[ $($name),* ];

        impl Event {
            /// The `ev` tag.
            pub fn name(&self) -> &str {
                match self {
                    $( Event::$variant { .. } => $name, )*
                    Event::Unknown { ev, .. } => ev,
                }
            }
        }
    };
}

define_events! {
    /// `tm wake`: `t` is the wake time.
    Wake => "wake" {
        /// Minutes slept.
        slept_min: u32,
        /// Minutes to fall asleep (`--onset`).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        onset_min: Option<u32>,
    },
    /// `tm arrive`: location, working window and block budget for the day.
    Arrive => "arrive" {
        /// Location name (`lounge`, `home`, …).
        loc: String,
        /// `[start, end]` as `HH:MM`.
        window: [String; 2],
        /// Block budget.
        budget: u32,
    },
    /// A block started.
    Start => "start" {
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
    Done => "done" {
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
    Extend => "extend" {
        /// Item id.
        id: String,
        /// Minutes added.
        by_min: u32,
    },
    /// The block was stopped; the remainder re-competes.
    Stop => "stop" {
        /// Item id.
        id: String,
        /// Remaining estimate in minutes.
        remaining_min: u32,
    },
    /// A break; `t` is its start.
    Break => "break" {
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
    Energy => "energy" {
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
    Interrupt => "interrupt" {
        /// The interrupted item, if a block was running.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
    },
    /// The interruption ended.
    Resume => "resume" {
        /// Minutes lost.
        lost_min: u32,
        /// Items dropped from today's plan as a consequence.
        #[serde(default)]
        dropped: Vec<String>,
    },
    /// Timer paused.
    Pause => "pause" {
        /// Item id.
        id: String,
    },
    /// Timer resumed.
    Unpause => "unpause" {
        /// Item id.
        id: String,
    },
    /// The idle prompt was answered: the gap `[t − min, t]` was attributed.
    Idle => "idle" {
        /// `leak`, `work`, `break`, `routine` or `interrupt`.
        attributed: String,
        /// Length of the gap.
        min: u32,
    },
    /// A routine instance changed status.
    Routine => "routine" {
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
    Skip => "skip" {
        /// Routine name or id.
        item: String,
        /// Instance key.
        inst: String,
    },
    /// A plan was computed.
    Plan => "plan" {
        /// Plan hash.
        hash: String,
        /// Replans so far today (running count).
        replans_today: u32,
        /// Minutes segments moved by this replan.
        drift_min: u32,
    },
    /// `tm event <name> [^id]` (the `ev` tag is `event`).
    Named => "event" {
        /// Event name.
        name: String,
        /// The item it resolves, if given.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
    },
    /// An item was demoted at a close.
    Demote => "demote" {
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
    Readopt => "readopt" {
        /// Item id.
        id: String,
    },
    /// `tm move`.
    Move => "move" {
        /// Item id.
        id: String,
        /// Source file / horizon.
        from: String,
        /// Destination file / horizon.
        to: String,
    },
    /// `tm drop`.
    Drop => "drop" {
        /// Item id.
        id: String,
    },
    /// `tm edit`: one field changed.
    Edit => "edit" {
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
    Note => "note" {
        /// The text.
        text: String,
    },
    /// Location changed.
    Loc => "loc" {
        /// New location.
        loc: String,
    },
    /// `tm close <period>` ran.
    Close => "close" {
        /// `day`, `week` or `month`.
        period: String,
        /// The period key closed (`2026-09-07`, `2026-W37`, `2026-09`).
        key: String,
    },
    /// `tm undo`: cancels the most recent not-yet-undone event of kind `of`.
    Undo => "undo" {
        /// Event kind to cancel.
        of: String,
        /// Restrict to events with this primary id.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
    },
}

impl<'de> Deserialize<'de> for Event {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Event, D::Error> {
        use serde::de::Error;
        let mut map = Map::<String, Value>::deserialize(d)?;
        let ev = match map.get("ev") {
            Some(Value::String(s)) => s.clone(),
            Some(_) => return Err(D::Error::custom("`ev` must be a string")),
            None => return Err(D::Error::missing_field("ev")),
        };
        if EVENT_NAMES.contains(&ev.as_str()) {
            let value = Value::Object(map);
            Known::deserialize(&value).map(Event::from).map_err(|e| {
                let detail = value
                    .as_object()
                    .and_then(|m| Known::field_error(&ev, m))
                    .unwrap_or_else(|| e.to_string());
                D::Error::custom(format!("event {ev:?}: {detail}"))
            })
        } else {
            map.remove("ev");
            Ok(Event::Unknown { ev, rest: map })
        }
    }
}

impl Event {
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
    /// The 1-based **physical** line of each entry (`lines[i]` is
    /// `entries[i]`'s): blank and malformed lines keep their numbers, so a
    /// line number names the same bytes whatever the lines around it hold.
    pub lines: Vec<u64>,
    /// How many physical lines the text has: the `\n`-separated segments,
    /// the empty segment after a final `\n` not counted (so a line appended
    /// after them is line `line_count + 1`).
    pub line_count: u64,
}

/// **The physical line count of log bytes** ([`Log::line_count`]): the
/// `\n`-separated segments, not counting the empty one after a final `\n`. An
/// entry appended next is on line `physical_line_count(bytes) + 1`.
pub fn physical_line_count(bytes: &[u8]) -> u64 {
    let newlines = bytes.iter().filter(|b| **b == b'\n').count();
    (newlines + usize::from(!bytes.is_empty() && !bytes.ends_with(b"\n"))) as u64
}

impl Log {
    /// An empty log.
    pub fn new() -> Log {
        Log::default()
    }

    /// A log from entries (no warnings).
    pub fn from_entries(entries: Vec<LogEntry>) -> Log {
        let n = entries.len() as u64;
        Log {
            entries,
            warnings: Vec::new(),
            lines: (1..=n).collect(),
            line_count: n,
        }
    }

    /// Parse JSONL text. Blank lines are skipped; malformed lines become
    /// warnings.
    pub fn parse(text: &str) -> Log {
        Log::parse_bytes(text.as_bytes())
    }

    /// Parse JSONL bytes: the file is split on `\n` and each line is decoded
    /// on its own, so one line of invalid UTF-8 (a torn write, a zero-padded
    /// block after a crash) is a [`LogWarning`] like any other malformed line
    /// instead of taking the whole log with it.
    pub fn parse_bytes(bytes: &[u8]) -> Log {
        let mut log = Log::new();
        log.line_count = physical_line_count(bytes);
        for (i, raw) in bytes.split(|b| *b == b'\n').enumerate() {
            let line = match std::str::from_utf8(raw) {
                Ok(s) => s.trim_end_matches('\r'),
                Err(err) => {
                    log.warnings.push(LogWarning {
                        line: i + 1,
                        text: String::from_utf8_lossy(raw).trim_end_matches('\r').to_string(),
                        error: format!("invalid UTF-8: {err}"),
                    });
                    continue;
                }
            };
            if line.trim().is_empty() {
                continue;
            }
            match LogEntry::parse(line) {
                Ok(e) => {
                    log.entries.push(e);
                    log.lines.push(i as u64 + 1);
                }
                Err(e) => log.warnings.push(LogWarning {
                    line: i + 1,
                    text: line.to_string(),
                    error: e.to_string(),
                }),
            }
        }
        log
    }

    /// Read `path`. A missing file is an empty log; malformed lines (invalid
    /// UTF-8 included) are collected in `warnings`; only an I/O failure is an
    /// error.
    pub fn read(path: impl AsRef<Path>) -> Result<Log, LogError> {
        let path = path.as_ref();
        match std::fs::read(path) {
            Ok(bytes) => Ok(Log::parse_bytes(&bytes)),
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

    /// Append entries to `path`, one JSON object per line. A file whose last
    /// line has no terminating newline (an append that failed part-way) gets
    /// one first, so the new event is never pasted onto the broken line.
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
            .read(true)
            .append(true)
            .open(path)
            .map_err(write_err)?;
        let len = f.metadata().map_err(write_err)?.len();
        if len > 0 {
            f.seek(SeekFrom::End(-1)).map_err(write_err)?;
            let mut last = [0u8; 1];
            f.read_exact(&mut last).map_err(write_err)?;
            if last[0] != b'\n' {
                f.write_all(b"\n").map_err(write_err)?;
            }
        }
        f.write_all(buf.as_bytes()).map_err(write_err)?;
        Ok(())
    }

    /// Push an entry in memory.
    pub fn push(&mut self, entry: LogEntry) {
        self.line_count += 1;
        self.lines.push(self.line_count);
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
    /// that matches nothing is *dangling*. See [`undo_mask`].
    pub fn undo_mask(&self) -> UndoMask {
        undo_mask(&self.entries)
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
        replay_lines(&self.entries, &self.lines, self.line_count, range, tz)
    }
}

/// Which entries of `entries` are cancelled by `undo` entries (§10.1, §13).
/// Each `undo{of, id?}` cancels the most recent earlier event of kind `of`
/// (with primary id `id` when given) that is not already cancelled and is
/// not itself an undo; the undo entry is always cancelled too. An undo that
/// matches nothing is *dangling* (only itself is cancelled). An undo of an
/// undo is therefore always dangling.
pub fn undo_mask(entries: &[LogEntry]) -> UndoMask {
    let n = entries.len();
    let mut cancelled = vec![false; n];
    let mut dangling = Vec::new();
    for i in 0..n {
        let Event::Undo { of, id } = &entries[i].ev else {
            continue;
        };
        cancelled[i] = true;
        let target = (0..i).rev().find(|&j| {
            let ev = &entries[j].ev;
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

// ---------------------------------------------------------------------------
// Days and hours since wake
// ---------------------------------------------------------------------------

/// Hours between `wake` and `t`, rounded to 0.01 (the `hsw` field). Negative
/// when `t` is before `wake`.
pub fn hours_since_wake<A: TimeZone, B: TimeZone>(t: &DateTime<A>, wake: &DateTime<B>) -> f64 {
    let secs = t.clone().signed_duration_since(wake.clone()).num_seconds() as f64;
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
/// logged, or the wake is stale) to its own calendar date. At most one wake
/// per calendar date is kept, so a day is never longer than 24 hours.
#[derive(Clone, Debug, PartialEq)]
pub struct DayIndex {
    tz: Tz,
    wakes: Vec<DateTime<FixedOffset>>,
}

impl DayIndex {
    /// Build from wake times (sorted internally). Only the **first** wake on
    /// each calendar date is kept: a second `tm wake` the same day (a nap, or
    /// a re-run of the verb) must not stretch that day past 24 hours and
    /// swallow the next morning (§12.1 "one row per 24h from wake to wake").
    /// This is the same wake [`DayIndex::wake_of`] and `DayReplay::wake`
    /// report.
    pub fn new(tz: Tz, wakes: impl IntoIterator<Item = DateTime<FixedOffset>>) -> DayIndex {
        let mut wakes: Vec<_> = wakes.into_iter().collect();
        wakes.sort();
        wakes.dedup_by(|later, kept| {
            later.with_timezone(&tz).date_naive() == kept.with_timezone(&tz).date_naive()
        });
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
///
/// `PartialEq` ignores [`EnergyObs::line`], as [`Replay`]'s ignores `rows`:
/// equal observations read from different lines are equal facts.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EnergyObs {
    /// The 1-based physical line of the entry it came from (a `start`'s
    /// observation carries the start's line, not its `done`'s). Line
    /// bookkeeping, not a fact: [`Replay::energy`] is sorted by it, which is
    /// file order (design §11.2); not serialised.
    #[serde(skip)]
    pub line: u64,
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

impl PartialEq for EnergyObs {
    fn eq(&self, other: &EnergyObs) -> bool {
        // Destructured so a new field is a compile error here.
        let EnergyObs {
            line: _,
            t,
            day,
            pred,
            rep,
            hsw,
            loc,
            slept_min,
            went,
            id,
            from_start,
        } = self;
        *t == other.t
            && *day == other.day
            && *pred == other.pred
            && *rep == other.rep
            && *hsw == other.hsw
            && *loc == other.loc
            && *slept_min == other.slept_min
            && *went == other.went
            && *id == other.id
            && *from_start == other.from_start
    }
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
///
/// `PartialEq` ignores [`DurationObs::line`], as [`EnergyObs`]'s does.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DurationObs {
    /// The 1-based physical line of the `done` it came from. Line bookkeeping,
    /// not a fact: [`Replay::durations`] is sorted by it (design §11.2); not
    /// serialised.
    #[serde(skip)]
    pub line: u64,
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

impl PartialEq for DurationObs {
    fn eq(&self, other: &DurationObs) -> bool {
        // Destructured so a new field is a compile error here.
        let DurationObs {
            line: _,
            t,
            day,
            id,
            ci,
            tags,
            est_min,
            actual_min,
            went,
            partial,
        } = self;
        *t == other.t
            && *day == other.day
            && *id == other.id
            && *ci == other.ci
            && *tags == other.tags
            && *est_min == other.est_min
            && *actual_min == other.actual_min
            && *went == other.went
            && *partial == other.partial
    }
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

/// **The latest `tm event <name>` of one `(name, id?)` key**, which is all the
/// kernel keeps of the occurrences (design §8.4's `events_named` row: "latest
/// instant per `(name, id?)`. Exact, because a `>= since` filter commutes with
/// max"), and all the two readers in the binary need —
/// [`crate::priority::collect_candidates`]'s `event_names()` and
/// `recur::arrival_of`'s [`Replay::latest_named`] (step R3's narrowing).
///
/// Two instants, because [`LatestNamed`] answers "the latest occurrence on or
/// after a local date" from them: `latest` by instant, `latest_dated` by
/// `(local date, instant)`. The lines are **bookkeeping, not facts** — they
/// break a tie between two occurrences of the same instant the way the fork's
/// file-order walk did, and, like [`EnergyObs::line`], they are neither
/// serialised nor compared.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct NamedLatest {
    /// The latest occurrence by instant (a tie goes to the later line).
    pub latest: DateTime<FixedOffset>,
    /// Its physical line. Bookkeeping; not serialised, not compared.
    #[serde(skip)]
    pub latest_line: u64,
    /// The latest occurrence by `(local date in the replay's tz, instant)` (a
    /// tie goes to the later line).
    pub latest_dated: DateTime<FixedOffset>,
    /// Its physical line. Bookkeeping; not serialised, not compared.
    #[serde(skip)]
    pub dated_line: u64,
}

impl PartialEq for NamedLatest {
    fn eq(&self, other: &NamedLatest) -> bool {
        // Destructured so a new field is a compile error here.
        let NamedLatest {
            latest,
            latest_line: _,
            latest_dated,
            dated_line: _,
        } = self;
        *latest == other.latest && *latest_dated == other.latest_dated
    }
}

impl NamedLatest {
    /// One occurrence, on `line`, as a record of its own.
    fn of(t: DateTime<FixedOffset>, line: u64) -> NamedLatest {
        NamedLatest {
            latest: t,
            latest_line: line,
            latest_dated: t,
            dated_line: line,
        }
    }

    /// Take the occurrence `(t, line)` into this record, in `tz`. The fork
    /// walked the occurrences in file order and kept `t >= latest` and
    /// `(date, t) >= (date, latest_dated)`, so a later line wins a tie; this
    /// is that walk, one occurrence at a time.
    fn absorb(&mut self, t: DateTime<FixedOffset>, line: u64, tz: Tz) {
        if (t, line) >= (self.latest, self.latest_line) {
            self.latest = t;
            self.latest_line = line;
        }
        let key = |x: DateTime<FixedOffset>, l: u64| (x.with_timezone(&tz).date_naive(), x, l);
        if key(t, line) >= key(self.latest_dated, self.dated_line) {
            self.latest_dated = t;
            self.dated_line = line;
        }
    }

    /// The record of the union of two keys' occurrences, in `tz`: a maximum
    /// over a union is the maximum of the maxima, which is why the narrowing
    /// loses nothing that [`Replay::latest_named`] reads.
    fn merged(self, other: NamedLatest, tz: Tz) -> NamedLatest {
        let mut out = self;
        out.absorb(other.latest, other.latest_line, tz);
        out.absorb(other.latest_dated, other.dated_line, tz);
        out
    }
}

/// **What one `tm event` name's occurrences narrow to** ([`NamedLatest`] per
/// `(name, id?)`): the latest addressed to nobody, and the latest addressed to
/// each id. Keyed by a `String` so [`Replay`] stays JSON-safe.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, Default)]
pub struct NamedRecord {
    /// The latest occurrence of this name addressed to nobody.
    pub unaddressed: Option<NamedLatest>,
    /// The latest occurrence of this name addressed to each id.
    pub by_id: BTreeMap<String, NamedLatest>,
}

impl NamedRecord {
    /// Take one occurrence in, in `tz`.
    fn absorb(&mut self, id: Option<&str>, t: DateTime<FixedOffset>, line: u64, tz: Tz) {
        let slot = match id {
            None => &mut self.unaddressed,
            Some(i) => {
                match self.by_id.get_mut(i) {
                    Some(rec) => rec.absorb(t, line, tz),
                    None => {
                        self.by_id.insert(i.to_string(), NamedLatest::of(t, line));
                    }
                }
                return;
            }
        };
        match slot {
            Some(rec) => rec.absorb(t, line, tz),
            None => *slot = Some(NamedLatest::of(t, line)),
        }
    }

    /// The record of every occurrence addressed to `id` **or to nobody** — the
    /// set the fork's `latest_named` filtered to.
    fn for_id(&self, id: &str, tz: Tz) -> Option<NamedLatest> {
        match (self.unaddressed, self.by_id.get(id).copied()) {
            (Some(a), Some(b)) => Some(a.merged(b, tz)),
            (a, b) => a.or(b),
        }
    }

    /// The latest occurrence of this name addressed to anyone or to nobody.
    fn any(&self, tz: Tz) -> Option<NamedLatest> {
        self.by_id
            .values()
            .copied()
            .chain(self.unaddressed)
            .reduce(|a, b| a.merged(b, tz))
    }
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

impl OpenBlock {
    /// Worked minutes as of `now`: the closed sub-segments plus the stretch
    /// running since [`OpenBlock::since`] (nothing accrues while the block is
    /// paused or interrupted). This is the elapsed time the overtime prompt
    /// (§9.1) compares against `est × r`.
    pub fn worked_min_at(&self, now: DateTime<FixedOffset>) -> u32 {
        let running = self
            .since
            .map_or(0, |s| now.signed_duration_since(s).num_minutes().max(0) as u32);
        self.worked_min + running
    }
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
    /// §11 load in exact fifths, `Σ block_min × min(ci, 5)`, over the block
    /// minutes whose ci the log records (i.e. every minute except
    /// [`DayReplay::ci_unknown`]). [`DayReplay::load`] divides it once, at
    /// display (design site R9, parity P21).
    pub load_fifths: u64,
    /// Minutes at each ci (index = ci), over the block minutes whose ci the
    /// log records.
    pub minutes_by_ci: [u32; 6],
    /// Block minutes whose ci the log does not record, by item id: a block cut
    /// by `stop` or by the next `start` is credited from the clock, and
    /// neither event carries a `ci`. `Σ minutes_by_ci + ci_unknown_min() ==
    /// block_min` always holds, so §11's load and energy mix can be completed
    /// by looking these items' `ci` up in the tree.
    pub ci_unknown: BTreeMap<String, u32>,
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
            load_fifths: 0,
            minutes_by_ci: [0; 6],
            ci_unknown: BTreeMap::new(),
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

    /// §11 load, `Σ block_min × ci / 5`: [`DayReplay::load_fifths`] divided
    /// once. A multiple of 0.2, so one decimal shows it exactly.
    pub fn load(&self) -> f64 {
        self.load_fifths as f64 / 5.0
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
        self.breaks
            .iter()
            .fold(0u32, |a, b| a.saturating_add(b.actual_or_planned()))
    }

    /// Block minutes with `ci ≥ 4` among the minutes whose ci is known. The
    /// §11 energy-mix share is this over `block_min − ci_unknown_min()`, or
    /// over `block_min` once the caller has attributed
    /// [`DayReplay::ci_unknown`] from the tree.
    pub fn high_ci_min(&self) -> u32 {
        self.minutes_by_ci[4].saturating_add(self.minutes_by_ci[5])
    }

    /// Σ [`DayReplay::ci_unknown`]: block minutes with no ci in the log.
    pub fn ci_unknown_min(&self) -> u32 {
        self.ci_unknown
            .values()
            .fold(0u32, |a, m| a.saturating_add(*m))
    }

    /// Stretches of at least `min_min` minutes between the day's first and
    /// last logged segment that nothing covers — the *unattributed gaps* of
    /// the leak ledger (§11), which `review.rs` adds to the `leak` minutes.
    /// Overlapping segments (a routine inside a block) are merged first, so a
    /// gap is time with nothing at all logged.
    pub fn gaps(&self, min_min: u32) -> Vec<(DateTime<FixedOffset>, DateTime<FixedOffset>)> {
        let mut spans: Vec<(DateTime<FixedOffset>, DateTime<FixedOffset>)> = self
            .segments
            .iter()
            .filter(|s| s.end > s.start)
            .map(|s| (s.start, s.end))
            .collect();
        spans.sort();
        let mut gaps = Vec::new();
        let mut cursor = match spans.first() {
            Some((_, end)) => *end,
            None => return gaps,
        };
        for (start, end) in spans {
            if start > cursor {
                let min = start.signed_duration_since(cursor).num_minutes();
                if min >= min_min as i64 {
                    gaps.push((cursor, start));
                }
            }
            cursor = cursor.max(end);
        }
        gaps
    }

    /// Σ minutes of [`DayReplay::gaps`].
    pub fn gap_min(&self, min_min: u32) -> u32 {
        self.gaps(min_min).iter().fold(0u32, |a, (s, e)| {
            a.saturating_add(e.signed_duration_since(*s).num_minutes().max(0) as u32)
        })
    }
}

/// A day's seam facts (stage 5 D9 Phase R, design §8.4's "since-break anchor,
/// idle marks" and `lastT` rows): what the CLI and TUI used to walk
/// `Log::iter_day` for, derived once by the replay instead.
///
/// Kept beside [`Replay::days`], not inside [`DayReplay`]: a `DayReplay`
/// exists only for a day some events create (a `wake`, `start`, `break`, …),
/// while these facts read **every** surviving entry whose wake-attributed day
/// is the date — a day holding only a `pause` or a `note` has a seam and no
/// `DayReplay`, and adding a `DayReplay` for it would change what
/// `Replay::day` and every `days` iteration see.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, Default)]
pub struct DaySeam {
    /// When the last `break` of the day ended (`t + actual_min`, a missing
    /// `actual_min` counting as 0), else the day's first `start`; `None` with
    /// neither. `day.rs`'s `since_break_min` measures from it.
    pub since_break: Option<DateTime<FixedOffset>>,
    /// The day's `pause`, `interrupt`, `unpause`, `resume` and `break` marks,
    /// in file order. `day.rs`'s `idle_min_since` pairs them into the minutes
    /// a running block was not worked.
    pub idle_marks: Vec<IdleMark>,
    /// The latest `t` (by instant) over the day's surviving entries of any
    /// kind, `plan`, `note` and unknown events included; the TUI's idle
    /// prompt measures the gap from it. Not file order: see
    /// [`Replay::last_effective_t`].
    pub last_t: Option<DateTime<FixedOffset>>,
}

/// One mark of [`DaySeam::idle_marks`]: the entry's kind and `t`, and a
/// break's `actual_min`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum IdleMark {
    /// A `pause` at `t`.
    Pause(DateTime<FixedOffset>),
    /// An `interrupt` at `t`.
    Interrupt(DateTime<FixedOffset>),
    /// An `unpause` at `t`.
    Unpause(DateTime<FixedOffset>),
    /// A `resume` at `t`.
    Resume(DateTime<FixedOffset>),
    /// A `break` that began at `t`, with the `actual_min` it was logged with.
    Break {
        /// When the break began.
        t: DateTime<FixedOffset>,
        /// Its logged length, if any.
        actual_min: Option<u32>,
    },
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

/// One row of [`Replay::view`]: **the kernel's line header**
/// `(line, tag, id?, day, cancelled, display)` (design §8.4, §11.4), and
/// nothing else. Every entry has one, cancelled entries and `undo`s included;
/// malformed and blank lines have none.
///
/// It does **not** hold the parsed [`LogEntry`]: the kernel supplies a header,
/// not an entry, and the line's own bytes come back from the `render` op
/// (§11.4 steps 3-4). `tm log`, the one verb that shows a line's payload,
/// reads those bytes for the lines it selected; everything else reads the
/// header. Until the switch `Ctx::entries_at` is that read (design §11.4 step
/// 3), and at the switch it becomes the kernel's `render`.
#[derive(Clone, Debug, PartialEq)]
pub struct ViewRow {
    /// The entry's 1-based physical line ([`Log::lines`]).
    pub line: u64,
    /// The entry's tag ([`Event::name`]).
    pub tag: String,
    /// Its primary id ([`Event::primary_id`]), when it has one.
    pub id: Option<String>,
    /// When it happened, as written (instant and offset).
    pub t: DateTime<FixedOffset>,
    /// Its wake-attributed day ([`DayIndex::day_of`] over the surviving
    /// wakes), whether or not it survives.
    pub day: NaiveDate,
    /// Cancelled by an `undo` (or itself an `undo`), per [`undo_mask`].
    pub cancelled: bool,
}

impl ViewRow {
    /// `t` as `tm log` prints it: `%Y-%m-%d %H:%M` in the written offset. A
    /// method, not a field: formatting it for every row of every replay cost
    /// about 20 ms a replay on three years of log, and only `tm log` and `tm
    /// check`'s far-future scan read it (W-3's latency repair; the clause used
    /// to say `tm log` alone, which `log_problems` has made false since D18 (ii)
    /// landed). The kernel's header carries the same string, and T5 compares the
    /// two, so the switch keeps one definition of the display and not two.
    pub fn display(&self) -> String {
        self.t.format("%Y-%m-%d %H:%M").to_string()
    }
}

/// Everything replay derives from the log.
///
/// Some of it has no reader in the binary and appears in no output (the
/// fields [`PortedFacts`] names). The owner's D14 keeps every one: the kernel
/// ports them, so nothing here may drop or stop deriving them before it does.
///
/// `PartialEq` compares the facts and ignores the line bookkeeping (`rows`,
/// `line_count`), as serialisation does: two logs with the same survivors
/// replay to equal facts whatever lines they were read from.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Replay {
    /// Timezone used for day attribution.
    pub tz: Tz,
    /// The day range kept (`None` = everything).
    pub range: Option<RangeInclusive<NaiveDate>>,
    /// Per day.
    pub days: BTreeMap<NaiveDate, DayReplay>,
    /// Per item.
    pub items: BTreeMap<String, ItemReplay>,
    /// Routine instance statuses: `item → inst → latest record`.
    pub instances: BTreeMap<String, BTreeMap<String, InstanceRecord>>,
    /// Energy observations in time order.
    pub energy: Vec<EnergyObs>,
    /// Duration observations in time order.
    pub durations: Vec<DurationObs>,
    /// Interruptions in time order.
    pub interrupts: Vec<Interruption>,
    /// `tm event` occurrences by name, narrowed to the latest per
    /// `(name, id?)` ([`NamedRecord`]): design §8.4's `events_named` row, and
    /// what the kernel's `named` facts carry. The occurrence **lists** are
    /// not kept: nothing in the binary reads one (step R3 narrowed
    /// `recur.rs` to [`Replay::latest_named`] and `priority.rs` to
    /// [`Replay::event_names`]), and a list is not a fact the kernel derives.
    pub named: BTreeMap<String, NamedRecord>,
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
    /// Per wake-attributed day inside the range: the seam facts of every
    /// surviving entry of that day ([`DaySeam`]).
    pub seams: BTreeMap<NaiveDate, DaySeam>,
    /// The `t` of the last surviving entry in **file order**, of any kind,
    /// whatever the range (`tm idle`'s default length reads it). Not the
    /// latest instant: a hand-appended or retro line can be dated earlier.
    pub last_effective_t: Option<DateTime<FixedOffset>>,
    /// Every entry in file order with its line, day, mask bit and display
    /// text ([`Replay::view`]), whatever the range. Line bookkeeping, not a
    /// fact: not serialised (the kernel's `factsView` omits it too).
    #[serde(skip)]
    pub rows: Vec<ViewRow>,
    /// The log's physical line count ([`Log::line_count`]). Line
    /// bookkeeping; not serialised.
    #[serde(skip)]
    pub line_count: u64,
}

impl PartialEq for Replay {
    fn eq(&self, other: &Replay) -> bool {
        // Destructured so a new field is a compile error here until it is
        // placed on one side or the other.
        let Replay {
            tz,
            range,
            days,
            items,
            instances,
            energy,
            durations,
            interrupts,
            named,
            demotions,
            closes,
            dropped_items,
            done_items,
            last_done,
            done_dates,
            longest_leak,
            open_block,
            open_interrupt,
            unknown,
            warnings,
            seams,
            last_effective_t,
            rows: _,
            line_count: _,
        } = self;
        *tz == other.tz
            && *range == other.range
            && *days == other.days
            && *items == other.items
            && *instances == other.instances
            && *energy == other.energy
            && *durations == other.durations
            && *interrupts == other.interrupts
            && *named == other.named
            && *demotions == other.demotions
            && *closes == other.closes
            && *dropped_items == other.dropped_items
            && *done_items == other.done_items
            && *last_done == other.last_done
            && *done_dates == other.done_dates
            && *longest_leak == other.longest_leak
            && *open_block == other.open_block
            && *open_interrupt == other.open_interrupt
            && *unknown == other.unknown
            && *warnings == other.warnings
            && *seams == other.seams
            && *last_effective_t == other.last_effective_t
    }
}

/// What [`Replay::latest_named`] keeps of the `tm event <name>` occurrences
/// addressed to one id or to nobody: two instants, enough to answer "the
/// latest occurrence on or after a local date" without the list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LatestNamed {
    /// The latest occurrence by instant (a tie goes to the later line).
    pub latest: DateTime<FixedOffset>,
    /// The latest occurrence by `(local date in tz, instant)` (a tie goes to
    /// the later line). It differs from `latest` only when the zone's clock
    /// went back across midnight between them.
    pub latest_dated: DateTime<FixedOffset>,
}

impl LatestNamed {
    /// The latest occurrence whose local date in `tz` is `since` or later
    /// (`None`: no bound), the value `recur::arrival_of` filtered and
    /// maximised the list for.
    ///
    /// Equal to that filter-then-maximum whenever the latest by instant is
    /// dated `since` or later (it is then the maximum), or no occurrence is
    /// (the latest-dated one is not either). In between, the answer is the
    /// latest-dated occurrence, and the two agree unless the local date went
    /// **backwards twice** across the occurrences in that interval — two
    /// backward offset changes of the zone within the sum of their sizes,
    /// which no zone of the tz database has.
    pub fn on_or_after(&self, since: Option<NaiveDate>, tz: Tz) -> Option<DateTime<FixedOffset>> {
        let Some(s) = since else {
            return Some(self.latest);
        };
        if self.latest.with_timezone(&tz).date_naive() >= s {
            Some(self.latest)
        } else if self.latest_dated.with_timezone(&tz).date_naive() >= s {
            Some(self.latest_dated)
        } else {
            None
        }
    }
}

/// The replay facts nothing in the binary reads and no output shows, kept by
/// the owner's **D14** (design §4 Q7, option (b); §22.1): the kernel ports
/// them into the sealed day records instead of the fork deleting them. This
/// view names every one in one place, borrowed from the [`Replay`] that
/// `Ctx::replay_of` (the chokepoint) returns, so the kernel's facts (T5) and
/// the sealed day records (W1) have one comparand, and
/// `tm-core/tests/log_ported_facts.rs` pins their values.
///
/// Every field here is also a plain field of [`Replay`], [`DayReplay`] or
/// [`ItemReplay`]; the view adds nothing and filters nothing.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct PortedFacts<'a> {
    /// [`Replay::closes`].
    pub closes: &'a [CloseRecord],
    /// [`Replay::dropped_items`].
    pub dropped_items: &'a BTreeSet<String>,
    /// [`Replay::open_interrupt`].
    pub open_interrupt: Option<&'a Interruption>,
    /// [`Replay::longest_leak`] (the global one).
    pub longest_leak: Option<&'a LeakRecord>,
    /// [`Replay::interrupts`]: every interruption, beyond the lost and
    /// dropped minutes each day sums.
    pub interrupts: &'a [Interruption],
    /// Per day, in date order.
    pub days: BTreeMap<NaiveDate, PortedDayFacts<'a>>,
    /// Per item, in id order.
    pub items: BTreeMap<&'a str, PortedItemFacts<'a>>,
}

/// [`PortedFacts`] of one [`DayReplay`].
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct PortedDayFacts<'a> {
    /// [`DayReplay::replans_today`].
    pub replans_today: u32,
    /// [`DayReplay::last_plan_hash`].
    pub last_plan_hash: Option<&'a str>,
    /// [`DayReplay::loc_changes`].
    pub loc_changes: &'a [(DateTime<FixedOffset>, String)],
    /// [`DayReplay::dropped`].
    pub dropped: &'a [String],
    /// [`DayReplay::longest_leak`] (the day's).
    pub longest_leak: u32,
    /// [`DayReplay::routine_min`] (W-3's audit: unread, and missing here).
    pub routine_min: u32,
    /// [`DayReplay::idle`] (unread outside `log.rs` too; found by the same grep).
    pub idle: &'a [IdleRecord],
}

/// [`PortedFacts`] of one [`ItemReplay`].
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct PortedItemFacts<'a> {
    /// [`ItemReplay::stops`].
    pub stops: u32,
    /// [`ItemReplay::extended_min`].
    pub extended_min: u32,
    /// [`ItemReplay::done_at`].
    pub done_at: &'a [DateTime<FixedOffset>],
    /// [`ItemReplay::partial_done_at`].
    pub partial_done_at: &'a [DateTime<FixedOffset>],
    /// [`ItemReplay::blocks`] (unread outside `log.rs`; found by W-3's repair grep).
    pub blocks: u32,
}

impl Replay {
    /// The facts D14 keeps though nothing reads them ([`PortedFacts`]),
    /// borrowed whole: every day and every item of this replay.
    pub fn ported_facts(&self) -> PortedFacts<'_> {
        PortedFacts {
            closes: &self.closes,
            dropped_items: &self.dropped_items,
            open_interrupt: self.open_interrupt.as_ref(),
            longest_leak: self.longest_leak.as_ref(),
            interrupts: &self.interrupts,
            days: self
                .days
                .iter()
                .map(|(d, day)| {
                    (
                        *d,
                        PortedDayFacts {
                            replans_today: day.replans_today,
                            last_plan_hash: day.last_plan_hash.as_deref(),
                            loc_changes: &day.loc_changes,
                            dropped: &day.dropped,
                            longest_leak: day.longest_leak,
                            routine_min: day.routine_min,
                            idle: &day.idle,
                        },
                    )
                })
                .collect(),
            items: self
                .items
                .iter()
                .map(|(id, it)| {
                    (
                        id.as_str(),
                        PortedItemFacts {
                            stops: it.stops,
                            extended_min: it.extended_min,
                            done_at: &it.done_at,
                            partial_done_at: &it.partial_done_at,
                            blocks: it.blocks,
                        },
                    )
                })
                .collect(),
        }
    }

    /// Every entry of the log in file order, cancelled ones included, with its
    /// physical line, wake-attributed day, mask bit and display text — what
    /// `tm log` selects from and prints.
    pub fn view(&self) -> &[ViewRow] {
        &self.rows
    }
    /// How many entries the log holds (malformed and blank lines not
    /// counted): `tm log`'s `total`.
    pub fn entry_count(&self) -> usize {
        self.rows.len()
    }
    /// The rows of the entries on physical line `line` or later, in file
    /// order: what a command appended after the log had `line - 1` lines
    /// (`tm undo`'s recorder; the kernel's `headersFrom`). Rows are in
    /// increasing line order, so this is a binary search.
    pub fn headers_from(&self, line: u64) -> &[ViewRow] {
        let i = self.rows.partition_point(|r| r.line < line);
        &self.rows[i..]
    }
    /// The log's physical line count ([`Log::line_count`]): an entry
    /// appended next is on line `line_count() + 1`.
    pub fn line_count(&self) -> u64 {
        self.line_count
    }
    /// The day's record.
    pub fn day(&self, date: NaiveDate) -> Option<&DayReplay> {
        self.days.get(&date)
    }
    /// The day's seam facts, when any surviving entry belongs to `date`.
    pub fn seam(&self, date: NaiveDate) -> Option<&DaySeam> {
        self.seams.get(&date)
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
    /// The first completion date of `id` (the `every:Nd` phase anchor).
    pub fn done_date_first(&self, id: &str) -> Option<NaiveDate> {
        self.done_dates.get(id).and_then(|s| s.first().copied())
    }
    /// How many distinct completion dates `id` has.
    pub fn done_date_count(&self, id: &str) -> usize {
        self.done_dates.get(id).map_or(0, BTreeSet::len)
    }
    /// Completion dates of `id`, ascending. Read by tests only; the library
    /// reads [`Replay::done_date_first`] and [`Replay::done_date_count`].
    pub fn done_dates(&self, id: &str) -> Vec<NaiveDate> {
        self.done_dates
            .get(id)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_default()
    }
    /// The latest record of a routine instance, if anything was logged.
    pub fn instance(&self, item: &str, inst: &str) -> Option<&InstanceRecord> {
        self.instances.get(item)?.get(inst)
    }
    /// Status of a routine instance (`Pending` when nothing was logged).
    pub fn instance_status(&self, item: &str, inst: &str) -> InstanceStatus {
        self.instance(item, inst)
            .map_or(InstanceStatus::Pending, |r| r.status)
    }
    /// Every logged instance of `item`: `(inst, record)` sorted by `inst`.
    pub fn instances_of(&self, item: &str) -> impl Iterator<Item = (&str, &InstanceRecord)> {
        self.instances
            .get(item)
            .into_iter()
            .flat_map(|m| m.iter().map(|(k, v)| (k.as_str(), v)))
    }
    /// What `tm event <name>` narrowed to ([`NamedRecord`]), or `None` when
    /// the name was never logged.
    pub fn named(&self, name: &str) -> Option<&NamedRecord> {
        self.named.get(name)
    }
    /// The names `tm event` was logged with (§5.5's `after:event:` deps).
    pub fn event_names(&self) -> impl Iterator<Item = &str> {
        self.named.keys().map(String::as_str)
    }
    /// The latest `tm event <name>` addressed to `id` or to nobody, with
    /// local dates in `tz` ([`LatestNamed`]); `None` when there is none.
    ///
    /// **`tz` must be the replay's own** ([`Replay::tz`]), which is the only
    /// tz any caller passes: `recur::arrival_of` passes `cfg.tz`, and
    /// `Ctx::replay_of` builds the replay with `cfg.tz`. `latest_dated` is a
    /// maximum by `(local date, instant)`, so it is chosen when the replay is
    /// built rather than when the query is asked, exactly as the kernel's
    /// `named` facts choose it.
    pub fn latest_named(&self, name: &str, id: &str, tz: Tz) -> Option<LatestNamed> {
        let rec = self.named.get(name)?.for_id(id, tz)?;
        Some(LatestNamed {
            latest: rec.latest,
            latest_dated: rec.latest_dated,
        })
    }
    /// Every break, in time order across days.
    pub fn breaks(&self) -> impl Iterator<Item = &BreakRecord> {
        self.days.values().flat_map(|d| d.breaks.iter())
    }
    /// Every interruption on `date`.
    pub fn interrupts_on(&self, date: NaiveDate) -> impl Iterator<Item = &Interruption> {
        self.interrupts.iter().filter(move |i| i.day == date)
    }
    /// True when `name` was logged, optionally only after `since`, and
    /// optionally only when addressed to `id`.
    ///
    /// "Some occurrence is at or after `since`" is "the latest occurrence is
    /// at or after `since`", which is why the narrowing answers it exactly
    /// (design §8.4: "a `>= since` filter commutes with max"). With `id`, the
    /// occurrences are that id's own — an unaddressed one is not addressed to
    /// it, as the fork's `e.id.as_deref() == Some(i)` said.
    pub fn event_occurred(
        &self,
        name: &str,
        since: Option<DateTime<FixedOffset>>,
        id: Option<&str>,
    ) -> bool {
        let Some(rec) = self.named.get(name) else {
            return false;
        };
        let latest = match id {
            Some(i) => rec.by_id.get(i).map(|r| r.latest),
            None => rec.any(self.tz).map(|r| r.latest),
        };
        latest.is_some_and(|t| since.is_none_or(|s| t >= s))
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
        self.days
            .values()
            .fold(0u32, |a, d| a.saturating_add(d.block_min))
    }

    /// Block minutes keyed by [`Id`] — the map `tree::done_minutes` (§6.4)
    /// takes to roll logged minutes up a subtree.
    pub fn done_minutes_map(&self) -> HashMap<Id, u32> {
        self.items
            .iter()
            .map(|(id, it)| (Id::new(id.clone()), it.minutes))
            .collect()
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
    /// Running since; `None` while paused or interrupted.
    since: Option<DateTime<FixedOffset>>,
    /// The timer is paused (`pause` seen, no `unpause` yet).
    paused: bool,
    /// Start of the open `Pause` segment; taken when the segment is emitted
    /// (an interruption inside a pause splits it in two, and `paused` stays
    /// true across it).
    paused_at: Option<DateTime<FixedOffset>>,
    worked_min: u32,
    obs: Option<usize>,
}

/// The last block cut by `stop` (or by the next `start`), with the minutes it
/// was credited: a `done` closing the same block replaces that credit instead
/// of adding to it.
struct Cut {
    id: String,
    t: DateTime<FixedOffset>,
    min: u32,
}

struct Machine {
    days: DayIndex,
    range: Option<RangeInclusive<NaiveDate>>,
    /// `slept_min` per day from the `wake` entries, built before the walk so
    /// an `energy` line logged before its `wake` still sees it.
    slept_by_day: HashMap<NaiveDate, u32>,
    out: Replay,
    block: Option<Block>,
    last_cut: Option<Cut>,
    interrupt: Option<(DateTime<FixedOffset>, Option<String>)>,
    /// The physical line of the entry being stepped.
    line: u64,
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
        b.worked_min = b.worked_min.saturating_add(min);
        let id = b.id.clone();
        if t > since {
            self.segment(since, t, SegmentKind::Block { id });
        }
    }

    /// Close the open `Pause` segment of the block at `t` (unpause, an
    /// interruption, or the block being closed while still paused). The
    /// `paused` flag is untouched: only `unpause` clears it.
    fn close_pause(&mut self, t: DateTime<FixedOffset>) {
        let Some(b) = self.block.as_mut() else {
            return;
        };
        let Some(p) = b.paused_at.take() else {
            return;
        };
        let id = b.id.clone();
        if t > p {
            self.segment(p, t, SegmentKind::Pause { id });
        }
    }

    /// Credit `min` block minutes to `id` at `t`. `ci` is the item's
    /// min-energy where the log carries it (a `done`); a block cut by `stop`
    /// or by the next `start` has none, and its minutes are recorded in
    /// [`DayReplay::ci_unknown`] instead of `minutes_by_ci`/`load_fifths`.
    fn credit(&mut self, id: &str, t: DateTime<FixedOffset>, min: u32, ci: Option<u8>) {
        let day = self.days.day_of(t);
        if !self.in_range(day) {
            return;
        }
        let it = self.item_mut(id);
        it.minutes = it.minutes.saturating_add(min);
        let by_day = it.minutes_by_day.entry(day).or_insert(0);
        *by_day = by_day.saturating_add(min);
        let id = id.to_string();
        if let Some(d) = self.day_mut(day) {
            d.block_min = d.block_min.saturating_add(min);
            match ci {
                Some(ci) => {
                    let ci = ci.min(5);
                    d.minutes_by_ci[ci as usize] =
                        d.minutes_by_ci[ci as usize].saturating_add(min);
                    d.load_fifths = d.load_fifths.saturating_add(u64::from(min) * u64::from(ci));
                }
                None if min > 0 => {
                    let unknown = d.ci_unknown.entry(id).or_insert(0);
                    *unknown = unknown.saturating_add(min);
                }
                None => {}
            }
        }
    }

    /// Undo a [`Machine::credit`] of ci-unknown minutes (a cut block whose
    /// `done` turned up right after).
    fn uncredit_cut(&mut self, cut: &Cut) {
        if cut.min == 0 {
            return;
        }
        let day = self.days.day_of(cut.t);
        if !self.in_range(day) {
            return;
        }
        if let Some(it) = self.out.items.get_mut(&cut.id) {
            it.minutes = it.minutes.saturating_sub(cut.min);
            if let Some(by_day) = it.minutes_by_day.get_mut(&day) {
                *by_day = by_day.saturating_sub(cut.min);
                if *by_day == 0 {
                    it.minutes_by_day.remove(&day);
                }
            }
        }
        if let Some(d) = self.out.days.get_mut(&day) {
            d.block_min = d.block_min.saturating_sub(cut.min);
            if let Some(unknown) = d.ci_unknown.get_mut(&cut.id) {
                *unknown = unknown.saturating_sub(cut.min);
                if *unknown == 0 {
                    d.ci_unknown.remove(&cut.id);
                }
            }
        }
    }

    /// Cut the open block at `t` (stop, or a start of another block): its
    /// worked minutes are credited, with no ci (neither event carries one).
    fn cut(&mut self, t: DateTime<FixedOffset>) -> Option<Block> {
        self.close_sub(t);
        self.close_pause(t);
        let b = self.block.take()?;
        self.credit(&b.id, t, b.worked_min, None);
        self.last_cut = Some(Cut {
            id: b.id.clone(),
            t,
            min: b.worked_min,
        });
        Some(b)
    }

    fn mark_done(&mut self, id: &str, t: DateTime<FixedOffset>, date: NaiveDate) {
        let day = self.days.day_of(t);
        if !self.in_range(day) {
            return;
        }
        self.out.done_items.insert(id.to_string());
        // Latest by timestamp, not by file position: an appended retro `done`
        // must not make an older completion look like the last one.
        let last = self.out.last_done.entry(id.to_string()).or_insert(t);
        if t > *last {
            *last = t;
        }
        self.out
            .done_dates
            .entry(id.to_string())
            .or_default()
            .insert(date);
    }

    fn step(&mut self, line: u64, e: &LogEntry) {
        self.line = line;
        let t = e.t;
        let day = self.days.day_of(t);
        self.out.last_effective_t = Some(t);
        if self.in_range(day) {
            let seam = self.out.seams.entry(day).or_default();
            if seam.last_t.is_none_or(|l| t >= l) {
                seam.last_t = Some(t);
            }
            match &e.ev {
                Event::Break { actual_min, .. } => {
                    seam.since_break = Some(t + Duration::minutes(i64::from(actual_min.unwrap_or(0))));
                    seam.idle_marks.push(IdleMark::Break {
                        t,
                        actual_min: *actual_min,
                    });
                }
                Event::Start { .. } if seam.since_break.is_none() => seam.since_break = Some(t),
                Event::Pause { .. } => seam.idle_marks.push(IdleMark::Pause(t)),
                Event::Interrupt { .. } => seam.idle_marks.push(IdleMark::Interrupt(t)),
                Event::Unpause { .. } => seam.idle_marks.push(IdleMark::Unpause(t)),
                Event::Resume { .. } => seam.idle_marks.push(IdleMark::Resume(t)),
                _ => {}
            }
        }
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
                            line: self.line,
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
                    paused: false,
                    paused_at: None,
                    worked_min: 0,
                    obs,
                });
                // A new block ends any claim the previous cut had on a later
                // `done`: those minutes belong to a block of their own.
                self.last_cut = None;
            }
            Event::Pause { id } => {
                if self.block.as_ref().is_some_and(|b| &b.id == id && !b.paused) {
                    self.close_sub(t);
                    if let Some(b) = self.block.as_mut() {
                        b.paused = true;
                        b.paused_at = Some(t);
                    }
                }
            }
            Event::Unpause { id } => {
                // A stray `unpause` (a duplicate keypress, or a `pause`
                // removed by `tm undo`) must not reset the block's clock.
                if self.block.as_ref().is_some_and(|b| &b.id == id && b.paused) {
                    self.close_pause(t);
                    if let Some(b) = self.block.as_mut() {
                        b.paused = false;
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
                self.close_pause(t);
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
                    d.lost_min = d.lost_min.saturating_add(*lost_min);
                    d.dropped.extend(dropped.iter().cloned());
                }
                if let Some(b) = self.block.as_mut() {
                    if b.paused {
                        // Still paused: the pause resumes where the
                        // interruption left off (a second `resume` without an
                        // `interrupt` must not restart it).
                        b.paused_at.get_or_insert(t);
                    } else if b.since.is_none() {
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
                    self.close_pause(t);
                    let b = self.block.take().expect("matched");
                    if let (Some(i), Some(w)) = (b.obs, went) {
                        if let Some(o) = self.out.energy.get_mut(i) {
                            o.went = Some(*w);
                        }
                    }
                    self.last_cut = None;
                }
                // `done.actual_min` is authoritative: when it closes a block
                // this same item was already given partial credit for (a
                // `stop` immediately followed by `d`, with no block in
                // between), it replaces that credit rather than adding to it.
                // A retro `done` (`actual_min: 0`) has nothing to replace it
                // with, so the worked minutes stand.
                if !matched
                    && *actual_min > 0
                    && self.block.is_none()
                    && self.last_cut.as_ref().is_some_and(|c| &c.id == id)
                {
                    let cut = self.last_cut.take().expect("checked just above");
                    self.uncredit_cut(&cut);
                }
                self.credit(id, t, *actual_min, Some(*ci));
                if self.in_range(day) {
                    if *actual_min > 0 {
                        let it = self.item_mut(id);
                        it.blocks = it.blocks.saturating_add(1);
                        if let Some(d) = self.day_mut(day) {
                            d.blocks_done = d.blocks_done.saturating_add(1);
                        }
                        self.out.durations.push(DurationObs {
                            line: self.line,
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
                        let it = self.item_mut(id);
                        it.stops = it.stops.saturating_add(1);
                    }
                }
            }
            Event::Extend { id, by_min } => {
                if self.in_range(day) {
                    let it = self.item_mut(id);
                    it.extended_min = it.extended_min.saturating_add(*by_min);
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
                    // From the day index, not from what has been replayed so
                    // far: `tm wake 06:05` typed after `tm energy 4` appends
                    // its line last.
                    let slept = self.slept_by_day.get(&day).copied();
                    self.out.energy.push(EnergyObs {
                        line: self.line,
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
                        d.leak_min = d.leak_min.saturating_add(*min);
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
                    self.out.instances.entry(item.clone()).or_default().insert(
                        inst.clone(),
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
                            d.routine_min = d.routine_min.saturating_add(*min);
                        }
                    }
                }
            }
            Event::Skip { item, inst } => {
                if self.in_range(day) {
                    self.out.instances.entry(item.clone()).or_default().insert(
                        inst.clone(),
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
                    d.plans = d.plans.saturating_add(1);
                    d.replans_today = d.replans_today.max(*replans_today);
                    d.drift_min = d.drift_min.saturating_add(*drift_min);
                    d.last_plan_hash = Some(hash.clone());
                }
            }
            Event::Named { name, id } => {
                if self.in_range(day) {
                    let (line, tz) = (self.line, self.out.tz);
                    self.out
                        .named
                        .entry(name.clone())
                        .or_default()
                        .absorb(id.as_deref(), t, line, tz);
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
            Event::Unknown { .. } => {
                if self.in_range(day) {
                    self.out.unknown += 1;
                }
            }
        }
    }

    fn finish(mut self) -> Replay {
        if let Some(b) = self.block.take() {
            self.out.open_block = Some(OpenBlock {
                id: b.id,
                started: b.started,
                worked_min: b.worked_min,
                since: b.since,
                paused: b.paused,
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
        // File order, as the kernel's observations are put back in order
        // after the switch (design §11.2). The walk is already in file order,
        // so this stable sort moves nothing here.
        self.out.energy.sort_by_key(|o| o.line);
        self.out.durations.sort_by_key(|o| o.line);
        self.out
    }
}

/// Derive state from `entries` in log order. Undo is applied first (see
/// [`undo_mask`]): an undone event and its `undo` entry are both skipped.
/// The block state machine then runs over every surviving entry (so a block
/// cut across a range edge is still accounted for); only results dated
/// inside `range` (wake-aware days, see [`DayIndex`]; `None` = everything)
/// are kept.
pub fn replay(entries: &[LogEntry], range: Option<RangeInclusive<NaiveDate>>, tz: Tz) -> Replay {
    let n = entries.len() as u64;
    let lines: Vec<u64> = (1..=n).collect();
    replay_lines(entries, &lines, n, range, tz)
}

/// [`replay`] with each entry's physical line (`lines[i]` is `entries[i]`'s)
/// and the text's line count, for [`Replay::view`]. An entry past the end of
/// `lines` (one pushed onto [`Log::entries`] directly) takes the line after
/// the previous entry's.
fn replay_lines(
    entries: &[LogEntry],
    lines: &[u64],
    line_count: u64,
    range: Option<RangeInclusive<NaiveDate>>,
    tz: Tz,
) -> Replay {
    let mask = undo_mask(entries);
    let mut prev = 0u64;
    let entry_lines: Vec<u64> = (0..entries.len())
        .map(|i| {
            let line = lines.get(i).copied().unwrap_or(prev + 1);
            prev = line;
            line
        })
        .collect();
    let refs: Vec<(u64, &LogEntry)> = entries
        .iter()
        .zip(&entry_lines)
        .zip(&mask.cancelled)
        .filter_map(|((e, line), c)| (!*c).then_some((*line, e)))
        .collect();
    let days = DayIndex::new(
        tz,
        refs.iter()
            .filter(|(_, e)| matches!(e.ev, Event::Wake { .. }))
            .map(|(_, e)| e.t),
    );
    let rows = entries
        .iter()
        .zip(&entry_lines)
        .zip(&mask.cancelled)
        .map(|((e, line), c)| {
            let line = *line;
            ViewRow {
                line,
                tag: e.ev.name().to_string(),
                id: e.ev.primary_id().map(str::to_string),
                t: e.t,
                day: days.day_of(e.t),
                cancelled: *c,
            }
        })
        .collect();
    let mut out = replay_refs(&refs, days, range, tz);
    out.rows = rows;
    out.line_count = line_count.max(prev);
    out
}

fn replay_refs(
    entries: &[(u64, &LogEntry)],
    days: DayIndex,
    range: Option<RangeInclusive<NaiveDate>>,
    tz: Tz,
) -> Replay {
    // The day's sleep, indexed before the walk: `tm wake 06:05` may be typed
    // (and appended) after events it precedes. The first `wake` of a day wins,
    // as it does for `DayReplay::wake`.
    let mut slept_by_day: HashMap<NaiveDate, u32> = HashMap::new();
    for (_, e) in entries {
        if let Event::Wake { slept_min, .. } = &e.ev {
            slept_by_day.entry(days.day_of(e.t)).or_insert(*slept_min);
        }
    }
    let mut m = Machine {
        days,
        range: range.clone(),
        slept_by_day,
        out: Replay {
            tz,
            range,
            days: BTreeMap::new(),
            items: BTreeMap::new(),
            instances: BTreeMap::new(),
            energy: Vec::new(),
            durations: Vec::new(),
            interrupts: Vec::new(),
            named: BTreeMap::new(),
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
            seams: BTreeMap::new(),
            last_effective_t: None,
            rows: Vec::new(),
            line_count: 0,
        },
        block: None,
        last_cut: None,
        interrupt: None,
        line: 0,
    };
    for (line, e) in entries {
        m.step(*line, e);
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
        let err = LogEntry::parse(r#"{"t":"2026-09-07T06:05:00-05:00","ev":"wake"}"#).unwrap_err();
        eprintln!("bad payload error: {err}");
        assert!(err.to_string().contains("wake"), "{err}");
        assert!(LogEntry::parse(r#"{"ev":"note","text":"x"}"#).is_err());
        assert!(LogEntry::parse(r#"{"t":"2026-09-07T06:05:00-05:00"}"#).is_err());
    }

    #[test]
    fn hsw_matches_spec() {
        let wake = at("2026-09-07T06:05:00-05:00");
        assert_eq!(hours_since_wake(&at("2026-09-07T07:02:00-05:00"), &wake), 0.95);
        assert_eq!(hours_since_wake(&at("2026-09-07T09:32:00-05:00"), &wake), 3.45);
        assert_eq!(hours_since_wake(&at("2026-09-07T06:05:00-05:00"), &wake), 0.0);
        // Different offsets compare by instant (06:05−05:00 is 11:05Z).
        assert_eq!(hours_since_wake(&at("2026-09-07T12:05:00+01:00"), &wake), 0.0);
        assert_eq!(hours_since_wake(&at("2026-09-07T13:05:00+01:00"), &wake), 1.0);
        assert_eq!(hours_since_wake(&at("2026-09-07T05:35:00-05:00"), &wake), -0.5);
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
        let open = r.open_block.as_ref().unwrap();
        assert_eq!(open.worked_min_at(at("2026-09-07T11:40:00-05:00")), 40);
        assert_eq!(open.worked_min_at(at("2026-09-07T10:00:00-05:00")), 0, "before the start");
        assert_eq!(r.blocks_done(d7), 1);
        assert_eq!(r.block_minutes_on_day(d7), 195);
        assert_eq!(r.lost_min(d7), 20);
        assert_eq!(r.day(d7).unwrap().dropped, vec!["z"]);
        assert_eq!(r.day(d7).unwrap().load(), 48.0, "only c's minutes carry a ci");
        assert_eq!(r.day(d7).unwrap().minutes_by_ci[4], 60);
        // a (90) and b (45) were cut by `stop` / the next `start`, which carry
        // no ci; every block minute is still accounted for.
        assert_eq!(r.day(d7).unwrap().ci_unknown_min(), 135);
        let day = r.day(d7).unwrap();
        assert_eq!(
            day.minutes_by_ci.iter().sum::<u32>() + day.ci_unknown_min(),
            day.block_min
        );
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

/// The tests of this reader's own internals that `tests/` held until step R12
/// (the undo mask, the day index, the ranged replay, the byte-identical
/// fixture round trip). Every consumer test reads a log through the test
/// chokepoint (`tm/tests/support/replay.rs`) instead; these test what the
/// switch deletes, so they stay beside it and go with it. Moved verbatim from
/// `tests/log_replay.rs` and `tests/log_serde.rs`.
#[cfg(test)]
mod reader_tests {
    use std::collections::BTreeSet;
    use std::path::{Path, PathBuf};

    use chrono::{DateTime, Duration, FixedOffset, NaiveDate};
    use chrono_tz::Tz;

    use super::{hours_since_wake, replay, Event, Log, LogEntry, Replay, EVENT_NAMES};
    use crate::model::InstanceStatus;

    const TZ: Tz = Tz::America__Chicago;

    fn fixture() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/logs/three-days.jsonl")
    }

    fn load() -> Log {
        let log = Log::read(fixture()).unwrap();
        assert!(log.warnings.is_empty());
        log
    }

    fn at(s: &str) -> DateTime<FixedOffset> {
        DateTime::parse_from_rfc3339(s).unwrap()
    }

    fn d(s: &str) -> NaiveDate {
        NaiveDate::parse_from_str(s, "%Y-%m-%d").unwrap()
    }

    #[test]
    fn undo_cancels_targets_and_itself() {
        let log = load();
        let mask = log.undo_mask();
        let cancelled: Vec<usize> = (0..log.len()).filter(|&i| mask.cancelled[i]).map(|i| i + 1).collect();
        // 1-based fixture lines: (39 done t6, 40), (44 skip laundry, 45),
        // (46 stop t7, 47), (58 drop a5, 59), (61 event visa, 62), (67 note, 68).
        assert_eq!(cancelled, vec![39, 40, 44, 45, 46, 47, 58, 59, 61, 62, 67, 68]);
        assert!(mask.dangling.is_empty());
        assert_eq!(mask.pairs(), 6);
        assert_eq!(log.effective().count(), 62);
        // What `tm undo` would cancel next: the last surviving state change.
        assert_eq!(
            log.compensating_undo(),
            Some(Event::Undo { of: "pause".into(), id: Some("t8".into()) })
        );
        // The free function applies the mask itself, so raw entries are safe:
        // replaying the raw log gives what replaying the already-masked entries
        // gives — and the masked list really is 12 entries shorter, so this is
        // not two spellings of the same call.
        let effective: Vec<LogEntry> = log.effective().cloned().collect();
        assert_eq!(effective.len(), log.len() - 12);
        assert!(!effective.iter().any(|e| matches!(e.ev, Event::Undo { .. })));
        assert_eq!(replay(&log.entries, None, TZ), replay(&effective, None, TZ));
        // …and it is not vacuous: the undone events do change the result.
        assert_ne!(replay(&log.entries, None, TZ), replay_raw(&log));
    }

    /// Replay as if `undo` did nothing: every entry except the `undo` lines
    /// themselves. Only used to prove the undo mask has an effect.
    fn replay_raw(log: &Log) -> Replay {
        let kept: Vec<LogEntry> = log
            .iter()
            .filter(|e| !matches!(e.ev, Event::Undo { .. }))
            .cloned()
            .collect();
        replay(&kept, None, TZ)
    }

    #[test]
    fn days_run_wake_to_wake() {
        let log = load();
        let idx = log.day_index(TZ);
        assert_eq!(idx.wakes().len(), 2);
        // 21:30 CDT written as UTC belongs to the 7th; the close at 00:10 on the
        // 9th belongs to the 8th (its wake is < 24 h earlier); the 9th has no
        // wake and falls back to the calendar date.
        assert_eq!(idx.day_of(at("2026-09-08T02:30:00+00:00")), d("2026-09-07"));
        assert_eq!(idx.day_of(at("2026-09-09T00:10:00-05:00")), d("2026-09-08"));
        assert_eq!(idx.day_of(at("2026-09-09T09:00:00-05:00")), d("2026-09-09"));
        assert_eq!(idx.wake_of(d("2026-09-09")), None);
        // 06:20 on the 8th is 24h15m after the 7th's wake: that wake is stale, so
        // the entry falls back to its calendar date. The 8th therefore begins
        // when the 7th's wake goes stale (06:05 + 24 h), not at its own 06:40
        // wake, and the days still tile exactly (`bounds` agrees with `day_of`).
        assert_eq!(idx.day_of(at("2026-09-08T06:20:00-05:00")), d("2026-09-08"));
        assert_eq!(
            idx.bounds(d("2026-09-07")),
            (at("2026-09-07T00:00:00-05:00"), at("2026-09-08T06:05:00-05:00"))
        );
        assert_eq!(
            idx.bounds(d("2026-09-08")),
            (at("2026-09-08T06:05:00-05:00"), at("2026-09-09T06:40:00-05:00"))
        );
        assert_eq!(log.iter_day(d("2026-09-07"), TZ).count(), 31);
        assert_eq!(log.iter_day(d("2026-09-08"), TZ).count(), 24, "34 entries minus 10 cancelled");
        assert_eq!(log.iter_day(d("2026-09-09"), TZ).count(), 7);
        assert_eq!(log.iter_range(d("2026-09-07"), d("2026-09-08"), TZ).count(), 55);
        assert_eq!(log.iter_range(d("2026-09-01"), d("2026-09-06"), TZ).count(), 0);
        assert_eq!(log.iter_item("t3").count(), 5, "start, extend, done, start, done");
        // The logged `hsw` values agree with the helper wherever a wake exists.
        for e in log.effective() {
            if let Event::Start { hsw, .. } = &e.ev {
                if let Some(w) = idx.wake_of(idx.day_of(e.t)) {
                    assert_eq!(*hsw, hours_since_wake(&e.t, &w), "{}", e.to_json().unwrap());
                }
            }
        }
    }

    #[test]
    fn range_keeps_only_the_requested_days() {
        let log = load();
        let d8 = d("2026-09-08");
        let r = log.replay(Some(d8..=d8), TZ);
        assert_eq!(r.days.keys().copied().collect::<Vec<_>>(), vec![d8]);
        assert_eq!(r.block_minutes("t3"), 65, "only day-2 minutes");
        assert_eq!(r.block_minutes("t1"), 0);
        assert!(!r.items.contains_key("t1"));
        assert_eq!(r.energy.len(), 3);
        assert_eq!(r.durations.len(), 3);
        assert!(r.named("reply").is_none());
        assert_eq!(r.instance_status("lunch", "2026-09-07"), InstanceStatus::Pending);
        assert_eq!(r.done_dates("t3"), vec![d8]);
        assert!(r.last_done("lunch").is_none());
        assert_eq!(r.closes.len(), 1);
        assert_eq!(r.unknown, 1);
        assert!(r.open_block.is_some(), "the machine still runs to the end");
        assert_eq!(r.range, Some(d8..=d8));
        // A range starting mid-log still credits a block cut inside it.
        let d9 = d("2026-09-09");
        let r = log.replay(Some(d9..=d9 + Duration::days(1)), TZ);
        assert_eq!(r.block_minutes("t8"), 60);
        assert_eq!(r.lost_min(d9), 15);
        assert!(r.longest_leak.is_none());
    }

    #[test]
    fn fixture_log_serializes_back_byte_identically_and_is_snapshotted() {
        let path = fixture();
        let text = std::fs::read_to_string(&path).unwrap();
        let log = Log::read(&path).unwrap();
        assert!(log.warnings.is_empty(), "{:?}", log.warnings);
        assert_eq!(log.len(), 74);
        let back = log.to_jsonl().unwrap();
        assert_eq!(back, text, "the fixture is written in canonical form");
        assert_eq!(Log::parse(&back), log);
        insta::assert_snapshot!("three_days_jsonl", back);
        // Every kind appears in the fixture (plus one unknown), so the snapshot
        // shows the field names of each.
        let mut kinds: BTreeSet<&str> = log.entries.iter().map(|e| e.ev.name()).collect();
        assert!(kinds.remove("mood"));
        let all: BTreeSet<&str> = EVENT_NAMES.iter().copied().collect();
        assert_eq!(kinds, all);
    }
}
