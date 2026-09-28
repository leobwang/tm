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
//!   so this only affects Log::to_jsonl, which went at S. A known name with a bad payload
//!   is a parse error naming the field, never an `Unknown`.
//!   [`Event::name`] is the `ev` tag, [`Event::primary_id`] the item/instance
//!   id an event is about, [`Event::is_state_change`] says whether `tm undo`
//!   may target it.
//! * [`LogEntry`]`{ t: DateTime<FixedOffset>, ev }` — one line; `t` is
//!   written RFC 3339 with the local offset (`2026-09-07T06:05:00-05:00`).
//!   [`LogEntry::to_json`] writes one line.
//!
//! # What is here, and what left at the switch (S, design §12)
//!
//! **This module is the log's *writer* and its *decoded view*, and nothing
//! else.** The reader — `Log` and all its iterators, `LogEntry::parse`,
//! `parse_timestamp`, `impl Deserialize for Event`, `undo_mask`/`UndoMask`,
//! `DayIndex`, `local_midnight`, the replay machine and `replay` itself,
//! about 1,700 lines — was deleted at S, when [`Replay`] began to come from
//! the Lean kernel instead (the owner's **D9**: one reader of the log, and it
//! is the proved one). `tm/src/cli/kernel_log.rs` is that reader's host side,
//! `Ctx::replay_with` is the one door, and `tm/src/cli/ctx.rs` is where the
//! body swap lives.
//!
//! What that means for anyone reading this file expecting a parser: the facts
//! below are **decoded from the kernel's answer** (`kernel_log::decode_facts`,
//! design §11.1), not derived here. The accessors are unchanged, and so are
//! their signatures (D9-20, CRIT 4) — that is what made the switch a body swap
//! rather than a rewrite of every consumer.
//!
//! Undo (§10.1, §13) still works the same way and is still what `tm undo`
//! reads — `undo{of, id?}` cancels the most recent not-yet-undone event of
//! kind `of` (with that primary id when given), the target and the undo itself
//! — but the mask is computed by the kernel and arrives in [`ViewRow::cancelled`].
//! Day attribution (a day runs from `wake` to the next `wake`) is likewise the
//! kernel's; [`hours_since_wake`]`(t, wake)` stays, because the *writer* needs
//! it to stamp `hsw` on a line it is appending.
//!
//! * [`Replay`] — what one read of the log yields:
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

// The file-handling imports (`std::io`'s traits, `std::path::Path`) went at S
// with `Log::read`/`Log::append`: this module no longer opens a file. The
// binary appends through `FsStore::append_text` (G9, parity P19) and the kernel
// reads.
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::ops::RangeInclusive;

use chrono::{DateTime, FixedOffset, NaiveDate, SecondsFormat, TimeZone};
use chrono_tz::Tz;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use thiserror::Error;

use crate::model::{Id, InstanceStatus, Stamp};

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

mod ts {
    use super::fmt_timestamp;
    use chrono::{DateTime, FixedOffset};
    use serde::Serializer;

    // `deserialize` went with `parse_timestamp` at S (design §12, CRIT 20):
    // Rust no longer parses a timestamp anywhere. The kernel reads every `t`
    // in the log, and this half writes the ones the binary appends.
    pub fn serialize<S: Serializer>(t: &DateTime<FixedOffset>, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&fmt_timestamp(t))
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

        // The private `Known` mirror, its `From<Known> for Event` and its
        // `field_error` went at S with `impl Deserialize for Event` (design
        // §12): they existed only to make a *parse* name the offending event
        // and field, and nothing in either crate parses a log line any more.
        // The kernel reads them, and names its own refusals (§17's P15).

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

}

/// One line of the log.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct LogEntry {
    /// When it happened (local time with offset).
    #[serde(serialize_with = "ts::serialize")]
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
    ///
    /// **The writer, which S keeps** (design §12; D16's S2 is where it moves
    /// into the kernel). `parse`, `local` and calendar_date were the reading
    /// half and went at S with the rest of the reader.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
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

/// **The physical line count of log bytes** ([`Log::line_count`]): the
/// `\n`-separated segments, not counting the empty one after a final `\n`. An
/// entry appended next is on line `physical_line_count(bytes) + 1`.
pub fn physical_line_count(bytes: &[u8]) -> u64 {
    let newlines = bytes.iter().filter(|b| **b == b'\n').count();
    (newlines + usize::from(!bytes.is_empty() && !bytes.ends_with(b"\n"))) as u64
}

/// Hours between `wake` and `t`, rounded to 0.01 (the `hsw` field). Negative
/// when `t` is before `wake`.
pub fn hours_since_wake<A: TimeZone, B: TimeZone>(t: &DateTime<A>, wake: &DateTime<B>) -> f64 {
    let secs = t.clone().signed_duration_since(wake.clone()).num_seconds() as f64;
    (secs / 36.0).round() / 100.0
}

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

/// **The idle spans of a block begun at `started`**, out of a day's
/// [`DaySeam::idle_marks`] in file order: each `(from, until)`, `until` `None`
/// while it is still open (a pause or interruption not yet lifted, the running
/// break `running_break`). The ONE pairing of pause/unpause, interrupt/resume
/// and break entries: [`Replay::idle_min_since`] sums it and `tm`'s D61 wall
/// pause asks whether an instant lies in it (W-36 repair, README gap 3134 —
/// `day.rs` carried a second copy of these arms, and the W-36 run had to add
/// the `Pause(t) if t < started` arm to both).
///
/// **A pause stamped before `started` was ANOTHER block's** (W-36 track T,
/// README gap 2920). `tm done` and `tm stop` on a paused block log no
/// `unpause`, and D61's wall pause is left open by a block that ends inside
/// the meeting, so such a pause stayed "open" and swallowed the NEXT block
/// whole: DRIVEN on `dd8b95b` — `pause` 09:10, `done` 09:20, `start ^t1` 09:30,
/// and at 10:00 `tm now` read `elapsed_min: 0` and `tm done` logged
/// `actual_min: 0` (fork `day::worked_min` did the same). The replay's machine
/// never had it: a `start` opens a fresh, running block. An INTERRUPTION is not
/// a block's — one still running when a block starts holds it until the
/// resume, as the machine does (`since` stays `none`) — so it still opens.
/// A `break` entry is written when the break ends, stamped at its start, so
/// the pair is one entry; one logged without `actual_min` is no span.
pub fn idle_spans(
    marks: &[IdleMark],
    started: DateTime<FixedOffset>,
    running_break: Option<DateTime<FixedOffset>>,
) -> Vec<(DateTime<FixedOffset>, Option<DateTime<FixedOffset>>)> {
    let mut out = Vec::new();
    let mut open: Option<DateTime<FixedOffset>> = None;
    for mark in marks {
        match *mark {
            IdleMark::Pause(t) if t < started => {}
            IdleMark::Pause(t) | IdleMark::Interrupt(t) => {
                if open.is_none() {
                    open = Some(t);
                }
            }
            IdleMark::Unpause(t) | IdleMark::Resume(t) => {
                if let Some(a) = open.take() {
                    out.push((a, Some(t)));
                }
            }
            IdleMark::Break {
                t,
                actual_min: Some(m),
            } => out.push((t, Some(t + chrono::Duration::minutes(i64::from(m))))),
            IdleMark::Break { actual_min: None, .. } => {}
        }
    }
    if let Some(a) = open {
        out.push((a, None));
    }
    if let Some(s) = running_break {
        out.push((s, None));
    }
    out
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
/// `PartialEq` compares the facts and ignores the **four** derived fields
/// (`rows`, `line_count`, `entry_count`, `done_date_totals`), as serialisation
/// does: two logs with the same survivors replay to equal facts whatever lines
/// they were read from, and `replay(raw) == replay(masked)` holds although one
/// entry list is twelve entries shorter than the other — which is exactly what
/// `entry_count` counts.
///
/// The last two are derived all-time facts that the fork's `Replay` has no key
/// for. Keeping them off the wire is what lets the stage-5 oracle compare the
/// two shapes key for key, and it is why they cannot be compared here: a JSON
/// round trip could not restore them. They are asserted **by name** instead,
/// in `tm/tests/kernel_log_door.rs`, which is the stronger statement — it
/// names the scope each one must survive.
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
    /// **How many entries the log holds, all-time** (design §8.4's
    /// `entryCount`, column **A**; §11.4 step 5's `tm log` `total`).
    ///
    /// Not `rows.len()`. The two agree for a whole-log replay and part
    /// company under a narrowed scope, where `rows` carries the scope's days
    /// and this stays the count of every entry the log has ever held — which
    /// is what `total` means. The kernel derives it in the checkpoint, so it
    /// survives folding; the reader fills it from the entries it read.
    ///
    /// Neither serialised nor compared by [`PartialEq`] (see the type's own
    /// doc): the fork's `Replay` has no such key, and the count is of the
    /// entry list a replay was given, not of the facts it derived.
    #[serde(skip)]
    pub entry_count: usize,
    /// **Per id, all-time: the first done date and the count of distinct done
    /// dates** (design §8.4's `done_dates` row, column **A**).
    ///
    /// [`Replay::done_date_first`] and [`Replay::done_date_count`] read this,
    /// never [`Replay::done_dates`], because those two questions are all-time
    /// and the date **set** is a window fact: under a narrowed scope the set
    /// holds only the dates at or above the horizon, so `.first()` would move
    /// and `.len()` would shrink. `first` is `None` only for an id with no
    /// done date, which is not given an entry here at all.
    ///
    /// The kernel carries both numbers in each item's all-time record
    /// (`Seal.ItemAgg.doneFirst`/`doneCount`, "over **every** date, a date
    /// below the horizon included"); the reader derives them from its own
    /// whole set. Neither serialised nor compared, for the reason
    /// `entry_count` gives; `kernel_log_door.rs` asserts it by name and by
    /// scope.
    #[serde(skip)]
    pub done_date_totals: BTreeMap<String, (Option<NaiveDate>, u32)>,
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
            entry_count: _,
            done_date_totals: _,
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
    /// **Minutes the running block has been WORKED as of `now`** — the ONE
    /// reading every host surface prints and logs (README gaps 2741 and 2920,
    /// W-35 repair): `tm now`'s header and `--json`'s `active.elapsed_min`, the
    /// TUI's timer and §9.1's overtime prompt, and the `actual_min` `tm done`
    /// and `tm stop` write to the log.
    ///
    /// The wall clock since `started`, net of [`Replay::idle_min_since`]: the
    /// pauses, interruptions and BREAKS that fell inside the block, the running
    /// break (`running_break`, `state.json`'s — its `break` entry is written
    /// only when it ends) included. This is fork `day::worked_min`, the rule
    /// fork `tm done` logged, moved here unchanged so the header can call it.
    ///
    /// **It is not the log's open block** ([`OpenBlock::worked_min_at`]),
    /// which W-35 track E made the header's reading: the replay's open block is
    /// fork `Machine::step`'s and never sees a `break`, so after a five-minute
    /// break `tm now` said `30m of 30m` while `tm done` logged 25 (the W-35
    /// audit's drive). The planner's `▶` row still reads the open block, the
    /// fork's `active_run` until R3 and the kernel's `openWorkedMin` after it —
    /// README gap 2920 is that residue, by name.
    pub fn active_worked_min(
        &self,
        day: NaiveDate,
        started: DateTime<FixedOffset>,
        now: DateTime<FixedOffset>,
        running_break: Option<DateTime<FixedOffset>>,
    ) -> u32 {
        let elapsed = now.signed_duration_since(started).num_minutes().max(0) as u32;
        elapsed.saturating_sub(self.idle_min_since(day, started, now, running_break))
    }

    /// The minutes of the running block that were *not* worked: §9 pauses
    /// (`pause`…`unpause`), interruptions (`interrupt`…`resume`) and breaks
    /// (`break`…) that fell inside it, out of `day`'s [`DaySeam::idle_marks`],
    /// plus the running break since `running_break`. log.rs's own convention
    /// for a block's worked minutes is "elapsed since `start` minus paused and
    /// interrupted time"; §8.5's duration multiplier and §11's ledgers both
    /// double-count without it (the same minutes are already `resume{lost_min}`).
    /// Fork `day::idle_min_since`, moved (W-35 repair).
    pub fn idle_min_since(
        &self,
        day: NaiveDate,
        started: DateTime<FixedOffset>,
        now: DateTime<FixedOffset>,
        running_break: Option<DateTime<FixedOffset>>,
    ) -> u32 {
        let marks = self.seam(day).map_or(&[][..], |s| s.idle_marks.as_slice());
        let mut total = 0i64;
        for (a, b) in idle_spans(marks, started, running_break) {
            let a = a.max(started);
            let b = b.unwrap_or(now).min(now);
            if b > a {
                total += (b - a).num_minutes();
            }
        }
        total.clamp(0, 24 * 60) as u32
    }

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
    /// How many entries the log holds, **all-time** (malformed and blank lines
    /// not counted): `tm log`'s `total` (design §11.4 step 5).
    ///
    /// [`Replay::entry_count`], never `rows.len()`: the rows are the scope's,
    /// the count is the log's. They agree for a whole-log replay.
    pub fn entry_count(&self) -> usize {
        self.entry_count
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
    ///
    /// All-time, from [`Replay::done_date_totals`] and **not** from the date
    /// set, which is a window fact: see that field.
    pub fn done_date_first(&self, id: &str) -> Option<NaiveDate> {
        self.done_date_totals.get(id).and_then(|(first, _)| *first)
    }
    /// How many distinct completion dates `id` has, all-time
    /// ([`Replay::done_date_totals`]).
    pub fn done_date_count(&self, id: &str) -> usize {
        self.done_date_totals.get(id).map_or(0, |(_, n)| *n as usize)
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
