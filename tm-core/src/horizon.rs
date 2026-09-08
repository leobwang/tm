//! Horizon lifecycle — tm-spec-v1.md §0 principle 6 ("demotion, not
//! deletion"), §2 ("horizon is the file"), §6.1, §6.3 (close day / week /
//! month, demote, readopt, move), §10.1 (the `demote`, `readopt`, `move`,
//! `drop` and `close` events), §10.2 (`state.closed`), §13
//! (`tm move|rank|demote|readopt|drop|close`).
//!
//! # API overview
//!
//! Everything here is a *write* against a [`Store`], computed from a
//! snapshot of the tree taken before the first write. Clocks are injected:
//! every entry point takes `now` (through [`Ctx`]) and the period or date it
//! acts on, so nothing in this module reads a clock.
//!
//! * [`Ctx`]`::new(store, files, tree, now)` — the store to write through,
//!   the parsed tree to reason about ([`PlanFiles`] carries `config`), and
//!   the instant that timestamps the log events.
//!   [`Ctx::with_replay`] adds the [`Replay`] that [`close_day`] subtracts
//!   today's logged minutes from.
//! * **Single-item verbs** (§13): [`move_item`]`(cx, id, to, section)` moves
//!   the exact line between horizon files (creating the target with its
//!   front matter, into `section` or the target's default section) and logs
//!   `move`; [`demote`]`(cx, id)` marks a week item
//!   `[-]` and copies it into `month/<current>#Demoted` with `est:` and a
//!   `demoted:W<nn>` stamp; [`readopt`]`(cx, id, to)` moves that copy back
//!   into a week (`[-]` → `[ ]`, stamps kept), refusing an id with no
//!   demoted line and absorbing the copy — its stamps *and* its `est:` —
//!   into the live line when the id still has one; [`drop_item`]`(cx, id)` sets
//!   `[~]`; [`rank`]`(cx, id, n)` moves a line to position `n` (1-based)
//!   within its section.
//! * **Closes** (§6.3): [`close_day`]`(cx, date)`, [`close_week`]`(cx,
//!   week)`, [`close_month`]`(cx, month, drops)` — each returns a
//!   [`CloseReport`] (`Serialize`, for `--json` and `/plan-month`) and
//!   appends one `close` event plus one `demote` / `move` / `drop` event per
//!   item it touched.
//! * [`auto_close`]`(store, state, today, now, replay)` — the "auto-run when
//!   overdue" of §13: compares [`RuntimeState::closed`] with the periods
//!   that have ended before `today`, runs the missing closes (day, then
//!   week, then month, so demotions cascade upward), records them in
//!   `state.closed`, saves `.tm/state.json` and returns what ran as
//!   [`ClosedPeriod`]s. Idempotent: running it twice in a day does nothing
//!   the second time.
//!
//! # What each close does (§6.3)
//!
//! * **day**: every `[>]` in `week/<week of date>` and in the day file's
//!   `# Pinned` section becomes `[ ]` with `est:` = remaining (the §6.4
//!   rollup), floored at [`MIN_REMAINING_MIN`]. Pinned items still open then
//!   move to `week/<week of date>` with `demoted:D<dd>` appended. Nothing
//!   else moves. An existing day file gets its `<!-- tm:review start -->`
//!   placeholder at the end (`review.rs` fills it later) — unless the block
//!   is already there with a review in it, which is left untouched; a day
//!   that was never planned gets no file.
//!
//!   A line that already carries an `est:` keeps it: §9.1's `tm stop` and
//!   partial `tm done` write `est:` = remaining *after* the block they
//!   close, so subtracting the day's logged minutes from it again would
//!   count them twice. Only an estimate no tool has touched (`est:` absent,
//!   so the remaining is still the leading estimate) has the minutes the
//!   replay records for the item on that date subtracted from it.
//! * **week**: every unfinished (`[ ]`/`[>]`) line of the week file becomes
//!   `[-]` *in place* — the week file is an archive from then on, and its
//!   front matter gets `closed: <date>` — and is **copied** to
//!   `month/<current>#Demoted` with `est:` = remaining and a `demoted:W<nn>`
//!   stamp appended (stamps accumulate across the *archive copy* too:
//!   `W36,W37`). Unfinished children — items in the week file whose nearest
//!   ancestor in the same file is a demoted item, at any depth — are removed
//!   from the week file instead, and their remaining is folded into that
//!   ancestor's `est:` (see "Folding children" below). Dated items past due
//!   with `on_miss = persist` move to `backlog.md#Overdue` instead of being
//!   demoted, exactly as written; dated intervals that are *not* past due —
//!   the walls of §7.2: exams, meetings — are never demoted either (§6.3,
//!   §5.3) and move, with their prep children, into the live planning week
//!   (today's, or the week after the one being closed when that close is
//!   running inside its own week).
//!   Recurring items are never touched (§5.3), and neither are `[x] [-] [~]
//!   [?]` lines.
//! * **month**: unfinished outcomes and everything under `# Demoted` move to
//!   the next month file, each into the section it came from (outcomes keep
//!   their `!k`, demoted items keep their stamps); ids listed in `drops`
//!   become `[~]` and stay. A line whose id the next month's file already
//!   carries is folded into the line that is there (stamps unioned) instead
//!   of being written twice — §4.1's ids are global. Items with ≥ 2 stamps
//!   are called out in [`CloseReport::notes`] for `/plan-month`.
//!
//! Every line this module writes keeps its bytes apart from the tokens it
//! must change: edits go through [`ItemLine`], moves through
//! [`Store::move_line_from`], so a line that crosses a horizon crosses it
//! byte for byte.
//!
//! # Choices the spec leaves open
//!
//! * **`est:` units** — whole blocks when the minutes divide evenly (`3b`),
//!   else the compact `Nm` / `NhMm` form; the floor is
//!   [`MIN_REMAINING_MIN`].
//! * **Folding children** — a demoted parent carries
//!   `max(remaining(parent), Σ own remaining of the children dropped with
//!   it)`. A subtask is normally a *decomposition* of its parent, so the
//!   §6.4 rollup (a milestone written as `6b` with three 1b subtasks has
//!   `remaining = 6b`) already covers it and the `max` changes nothing; when
//!   the dropped lines add up to more than the parent's own estimate, that
//!   estimate is stale and the larger number is carried, so a week close
//!   never removes work from the tree (§0 principle 6). Each dropped line is
//!   counted once, by its own `est:`/leading estimate; lines that stay (an
//!   overdue child filed in the backlog, a child living in another file) are
//!   never folded in.
//! * **What a week close never touches** — recurring lines (§5.3) and
//!   anything not `[ ]`/`[>]`. A dated interval (`at:`) is a wall (§7.2:
//!   "calendar, exams, meetings"), and §6.3 exempts walls from demotion:
//!   one that is past due goes to `backlog.md#Overdue` like any other
//!   past-due `persist` item, and one still in the future stays `[ ]` as
//!   §5.3 requires. Because the week file becomes an archive, staying `[ ]`
//!   in it would take the wall out of the planner's sight (§6.2 reads
//!   `week/<this week>`), so the wall and its prep children (§6.4) are moved
//!   into the current week instead — the one horizon that is still live.
//!   Closing a week from inside itself leaves them where they are, and so
//!   does a wall that is already over: nothing is carried from an instance
//!   that expired (§5.3), and it is still not demoted.
//! * **A parent cycle** (`@a` on `^b` and `@b` on `^a`, a `tm check` error
//!   under §5.5) never deletes a line: a cycle member is demoted as a root
//!   rather than dropped as somebody's child, and the report notes it.
//! * **Where a section-less move lands** — §13's `tm move ^id <horizon>`
//!   has no section argument, and three section names change what a line
//!   *means* (§4.2): `# Demoted` (§6.3), `# Pinned` (§6.2 — the only day
//!   section the planner reads) and `## series:<name>` (§5.4 — only the head
//!   is active), to which a day file's append-only `## Log` and free-text
//!   `## Notes` are added. So a move with no section appends to the last
//!   section of the target file that means nothing in particular; a move
//!   into a day always goes to `# Pinned`; a file whose sections are all
//!   loaded gets the horizon's canonical one (`Untied`, `Outcomes`,
//!   `Tasks`), created by [`Store::insert_line`]; a file with no sections at
//!   all (a freshly created week) takes the line at the end.
//! * **A second demotion of the same item** rewrites the one copy under
//!   `# Demoted` (accumulating stamps) instead of adding a second line, so
//!   the id never becomes a `tm check` duplicate; a stamp already on the
//!   line is not repeated. The copy is looked for in every month file, not
//!   only in the `month/<current>` this demotion writes into: a close
//!   catching up after the month turned over would otherwise leave the old
//!   record where it was and write a second one, and the next month close —
//!   carrying the older copy forward — would put both in one file. So the
//!   record *moves* (stamps merged into the new copy, the old line deleted),
//!   and one id keeps one archive copy however many periods a sweep catches
//!   up over.
//! * **A `--drop` that is already done.** §6.3's closes are idempotent, so a
//!   `--drop ^id` naming an item that is neither in the month being closed
//!   nor in the next month's file, and is already `[~]`, is the state the
//!   flag asked for: it is reported as dropped and nothing is written or
//!   logged. Only an id that is unknown, or live somewhere this close cannot
//!   act on, is an error.
//! * **The review block** is appended at the end of the day file (below
//!   `## Notes`) rather than at [`Store::replace_generated`]'s default
//!   insertion point, which is above the generated plan.
//! * **Log events** are appended through the store (`.tm/log.jsonl`) rather
//!   than a separately injected path, so a [`crate::store::MemStore`] test
//!   sees them too.

use std::collections::{HashMap, HashSet};

use chrono::{DateTime, Datelike, FixedOffset, NaiveDate, NaiveDateTime};
use chrono_tz::Tz;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::config::Config;
use crate::grammar::{EditError, ItemLine, ParsedFile};
use crate::log::{Event, LogEntry, Replay};
use crate::model::{
    Dur, Horizon, Id, IsoWeek, Item, OnMiss, Period, Recur, Shape, Stamp, State, YearMonth,
};
use crate::store::{edit, PlanFiles, RuntimeState, Store, StoreError, LOG_PATH};
use crate::tree::{self, Tree};

/// The floor a computed `est:` is clamped to. An item that was worked on for
/// at least as long as its estimate is not finished — only a `done` event
/// finishes it — so the remainder it carries into the next horizon is small
/// but never zero (§6.3, §9.1 "stop, demote rest").
pub const MIN_REMAINING_MIN: u32 = 5;

/// The section demoted copies live in, inside a month file (§4.2, §6.3).
pub const DEMOTED_SECTION: &str = "Demoted";
/// The section day-horizon items live in, inside a day file (§4.2, §6.2).
pub const PINNED_SECTION: &str = "Pinned";
/// The section overdue-persist items are moved to, in `backlog.md` (§6.3).
pub const OVERDUE_SECTION: &str = "Overdue";
/// Name of the generated block a close writes into the day file; `review.rs`
/// replaces its body later.
pub const REVIEW_BLOCK: &str = "review";
/// The one-line body [`close_day`] leaves in the review block when it has no
/// review in it yet. A block that already holds one is never overwritten.
pub const REVIEW_PLACEHOLDER: &str = "review pending";

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from a lifecycle operation.
#[derive(Debug, Error)]
pub enum HorizonError {
    /// The store could not read or write a file.
    #[error(transparent)]
    Store(#[from] StoreError),
    /// No line with that id (or title key) in the tree.
    #[error("^{0} is not in the plan")]
    NotFound(Id),
    /// The file the operation acts on does not exist.
    #[error("{0} does not exist")]
    MissingFile(String),
    /// The line cannot be rewritten the way the operation needs (a grammar
    /// edit was refused, so the line is unchanged).
    #[error("^{id}: {message}")]
    Edit {
        /// The item.
        id: Id,
        /// What the grammar refused.
        message: String,
    },
    /// The operation does not apply to this item's horizon.
    #[error("^{id} is in {horizon}: {message}")]
    Horizon {
        /// The item.
        id: Id,
        /// Where it lives.
        horizon: String,
        /// Why that is a problem.
        message: String,
    },
    /// A log event could not be encoded.
    #[error("cannot encode a log event: {0}")]
    Log(#[from] serde_json::Error),
}

// ---------------------------------------------------------------------------
// Periods
// ---------------------------------------------------------------------------

/// The period name §10.1 writes into a `close` event (`day`, `week`,
/// `month`) — [`Period::as_str`] is the one-letter budget form (`d`).
pub fn period_name(p: Period) -> &'static str {
    match p {
        Period::Day => "day",
        Period::Week => "week",
        Period::Month => "month",
    }
}

/// `Period` as the log spells it, for `serde(with = ...)`.
mod period_str {
    use super::*;
    use serde::{Deserializer, Serializer};

    pub fn serialize<S: Serializer>(p: &Period, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(period_name(*p))
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Period, D::Error> {
        let s = String::deserialize(d)?;
        Period::parse(&s).map_err(serde::de::Error::custom)
    }
}

/// `Option<Period>` as the log spells it, for `serde(with = ...)`.
mod opt_period_str {
    use super::*;
    use serde::{Deserializer, Serializer};

    pub fn serialize<S: Serializer>(p: &Option<Period>, s: S) -> Result<S::Ok, S::Error> {
        match p {
            Some(p) => s.serialize_some(period_name(*p)),
            None => s.serialize_none(),
        }
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Option<Period>, D::Error> {
        let s = Option::<String>::deserialize(d)?;
        s.map(|s| Period::parse(&s).map_err(serde::de::Error::custom))
            .transpose()
    }
}

// ---------------------------------------------------------------------------
// Reports
// ---------------------------------------------------------------------------

/// A line that changed file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Moved {
    /// The item.
    pub id: Id,
    /// Path it left.
    pub from: String,
    /// Path it landed in.
    pub to: String,
}

/// `Vec<Stamp>` in the notation §4.1 writes and reads (`["W36","W37"]`)
/// rather than serde's default enum shape (`[{"Week":36}]`), for
/// `serde(with = ...)`: `W37` is the only spelling of a stamp the rest of
/// the system — the line token, [`Stamp::parse`], `/plan-month` reading
/// `tm close --json` — speaks.
mod stamp_list {
    use super::*;
    use serde::ser::SerializeSeq;
    use serde::{Deserializer, Serializer};

    pub fn serialize<S: Serializer>(v: &[Stamp], s: S) -> Result<S::Ok, S::Error> {
        let mut seq = s.serialize_seq(Some(v.len()))?;
        for stamp in v {
            seq.serialize_element(&stamp.to_string())?;
        }
        seq.end()
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<Stamp>, D::Error> {
        Vec::<String>::deserialize(d)?
            .iter()
            .map(|s| Stamp::parse(s).map_err(serde::de::Error::custom))
            .collect()
    }
}

/// An item that was demoted (or stamped and moved down a horizon).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Demoted {
    /// The item.
    pub id: Id,
    /// The remaining estimate written as `est:` (0 when the item has none).
    pub est_min: u32,
    /// Its stamps after the close, in the `demoted:` notation
    /// (`["W36","W37"]`).
    #[serde(with = "stamp_list")]
    pub stamps: Vec<Stamp>,
}

/// An item whose `[>]` was reset to `[ ]` with a fresh `est:` (day close).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Reopened {
    /// The item.
    pub id: Id,
    /// The remaining estimate written as `est:` (0 when the item has none).
    pub est_min: u32,
}

/// What one close did (§6.3). `Serialize` for `tm close --json` and for the
/// `/plan-month` conversation.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CloseReport {
    /// Which period was closed.
    #[serde(with = "opt_period_str")]
    pub period: Option<Period>,
    /// Its key (`2026-09-07`, `2026-W37`, `2026-09`).
    pub key: String,
    /// Lines that changed file (pinned → week, overdue → backlog, month
    /// carry-over).
    pub moved: Vec<Moved>,
    /// Items demoted or stamped, with the estimate they carry.
    pub demoted: Vec<Demoted>,
    /// `[>]` → `[ ]` rewrites with a fresh `est:` (day close).
    pub reopened: Vec<Reopened>,
    /// Children removed from the week file because their parent was demoted
    /// (their remaining folded into that parent's `est:`).
    pub dropped_children: Vec<Id>,
    /// Walls — dated intervals (§7.2) — and their prep children, which a
    /// week close never demotes (§6.3): they stay `[ ]` and move into the
    /// live planning week.
    pub carried: Vec<Id>,
    /// Items dropped by `tm close month --drop ^id`.
    pub dropped: Vec<Id>,
    /// Dated persist items moved to `backlog.md#Overdue`.
    pub overdue_to_backlog: Vec<Id>,
    /// Human-readable remarks (duplicate ids, cut proposals, skipped items).
    pub notes: Vec<String>,
}

impl CloseReport {
    fn new(period: Period, key: String) -> CloseReport {
        CloseReport {
            period: Some(period),
            key,
            ..CloseReport::default()
        }
    }
    /// Fold `earlier` in front of this report.
    ///
    /// §6.3's closes are idempotent, which means the *second* run of one
    /// reports nothing. `Ctx::load` runs the §6.3 auto-close on the way in,
    /// so an explicit `tm close week` for a period that has already ended
    /// finds the work done and would otherwise print an all-empty report.
    /// Absorbing what the auto-close did makes `tm close` say what the close
    /// actually did, whichever run performed it.
    ///
    /// A `--drop` this run honoured undoes the carry `earlier` reported for
    /// the same id ([`close_month`] brings the line back), so those entries
    /// are folded out: the counts describe the tree the two runs together
    /// left behind, not the intermediate state.
    pub fn absorb(&mut self, mut earlier: CloseReport) {
        fn prepend<T>(mine: &mut Vec<T>, mut theirs: Vec<T>) {
            theirs.append(mine);
            *mine = theirs;
        }
        if !self.dropped.is_empty() {
            let dropped: HashSet<&Id> = self.dropped.iter().collect();
            earlier.moved.retain(|m| !dropped.contains(&m.id));
            earlier.demoted.retain(|d| !dropped.contains(&d.id));
        }
        prepend(&mut self.moved, earlier.moved);
        prepend(&mut self.demoted, earlier.demoted);
        prepend(&mut self.reopened, earlier.reopened);
        prepend(&mut self.dropped_children, earlier.dropped_children);
        prepend(&mut self.carried, earlier.carried);
        prepend(&mut self.dropped, earlier.dropped);
        prepend(&mut self.overdue_to_backlog, earlier.overdue_to_backlog);
        prepend(&mut self.notes, earlier.notes);
    }

    /// True when nothing at all was written apart from the `close` event.
    pub fn is_empty(&self) -> bool {
        self.moved.is_empty()
            && self.demoted.is_empty()
            && self.reopened.is_empty()
            && self.dropped_children.is_empty()
            && self.carried.is_empty()
            && self.dropped.is_empty()
            && self.overdue_to_backlog.is_empty()
    }
}

/// One close that [`auto_close`] ran.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClosedPeriod {
    /// Which period.
    #[serde(with = "period_str")]
    pub period: Period,
    /// Its key (`2026-09-07`, `2026-W37`, `2026-09`).
    pub key: String,
    /// What it did.
    pub report: CloseReport,
}

// ---------------------------------------------------------------------------
// Context
// ---------------------------------------------------------------------------

/// Everything a lifecycle operation needs: where to write, what the tree
/// looks like right now, and the instant to stamp the log with.
///
/// The `files` / `tree` snapshot is read once by the caller
/// ([`Store::read_tree`] + [`PlanFiles::tree`]); each operation computes
/// every decision from it *before* its first write, so a stale snapshot can
/// never be half-applied. After an operation the snapshot is out of date —
/// re-read it before running another one (that is exactly what
/// [`auto_close`] does between closes).
pub struct Ctx<'a> {
    /// Where lines are written.
    pub store: &'a dyn Store,
    /// The parsed tree (and `config`).
    pub files: &'a PlanFiles,
    /// The index over `files`.
    pub tree: &'a Tree,
    /// Log replay. [`close_day`] subtracts the minutes it records for a date
    /// from the estimate of a line that carries no `est:` of its own — see
    /// [`close_day`]; a line whose `est:` §9.1 already rewrote is left alone.
    pub replay: Option<&'a Replay>,
    /// The instant the operation happens at; timestamps every log event.
    pub now: DateTime<FixedOffset>,
}

impl<'a> Ctx<'a> {
    /// Build a context without a replay.
    pub fn new(
        store: &'a dyn Store,
        files: &'a PlanFiles,
        tree: &'a Tree,
        now: DateTime<FixedOffset>,
    ) -> Ctx<'a> {
        Ctx {
            store,
            files,
            tree,
            replay: None,
            now,
        }
    }

    /// Attach the log replay [`close_day`] reads today's minutes from.
    pub fn with_replay(mut self, replay: &'a Replay) -> Ctx<'a> {
        self.replay = Some(replay);
        self
    }

    /// The configuration read with the tree.
    pub fn cfg(&self) -> &Config {
        &self.files.config
    }

    /// `config.day.block_min`.
    pub fn block_min(&self) -> u32 {
        self.cfg().block_min()
    }

    /// `now` in the configured timezone (§17.2: work in `DateTime<Tz>`,
    /// convert at the edges).
    pub fn local(&self) -> DateTime<Tz> {
        self.now.with_timezone(&self.cfg().tz)
    }

    /// The local date of `now`.
    pub fn today(&self) -> NaiveDate {
        self.local().date_naive()
    }

    /// The local wall clock of `now` (what the files' naive times mean).
    pub fn now_naive(&self) -> NaiveDateTime {
        self.local().naive_local()
    }

    fn log(&self, ev: Event) -> Result<(), HorizonError> {
        let mut line = LogEntry::new(self.now, ev).to_json()?;
        line.push('\n');
        self.store.append_text(LOG_PATH, &line)?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

/// The key an item is addressed by, and the file it is in.
fn locate<'a>(cx: &Ctx<'a>, id: &Id) -> Result<(String, &'a Item), HorizonError> {
    let tree: &'a Tree = cx.tree;
    let node = tree.node(id).ok_or_else(|| HorizonError::NotFound(id.clone()))?;
    let path = tree
        .files()
        .get(node.file)
        .map(|f| f.path.clone())
        .ok_or_else(|| HorizonError::NotFound(id.clone()))?;
    // The node's `item` has its `ci` resolved; the *written* line is the one
    // in the file, so take that (it is what every edit here rewrites).
    let item = cx
        .files
        .file(&path)
        .and_then(|f| item_of(f, id))
        .unwrap_or(&node.item);
    Ok((path, item))
}

/// The item addressed by `key` inside one parsed file.
fn item_of<'f>(file: &'f ParsedFile, key: &Id) -> Option<&'f Item> {
    file.items().find(|i| Tree::key_of(i) == *key)
}

/// Apply a grammar edit to a copy of the item's line and return the text.
fn rewrite(
    item: &Item,
    key: &Id,
    f: impl FnOnce(&mut ItemLine) -> Result<(), EditError>,
) -> Result<String, HorizonError> {
    let mut line = item.line().clone();
    f(&mut line).map_err(|e| HorizonError::Edit {
        id: key.clone(),
        message: e.to_string(),
    })?;
    Ok(line.to_string())
}

/// `est:` as a `Dur`: whole blocks when the minutes divide evenly (`3b`),
/// else the most compact of `Nm` / `Nh` / `NhMm` (§4.1 value formats).
fn est_dur(minutes: u32, block_min: u32) -> Dur {
    if block_min > 0 && minutes > 0 && minutes.is_multiple_of(block_min) {
        Dur::blocks(minutes / block_min, block_min)
    } else {
        Dur::canonical(minutes)
    }
}

/// The item's stamps with `add` appended (once — a second close in the same
/// period does not write `W37,W37`).
fn stamps_with(item: &Item, add: Stamp) -> Vec<Stamp> {
    merge_stamps(&[], &item.stamps.demoted, add)
}

/// The stamps a demoted copy carries after this demotion: the history
/// already on the archive copy (`prior`), then anything the live line adds,
/// then `add` — each stamp once, in that order (§6.3 "stamps accumulate:
/// `W36,W37`"; §11 counts them for the cut proposal). The order is where
/// each stamp was found, not when it was written: a [`Stamp`] is `W37` or
/// `D07` with no year, so two of them cannot be put in age order at all.
fn merge_stamps(prior: &[Stamp], own: &[Stamp], add: Stamp) -> Vec<Stamp> {
    union_stamps(&union_stamps(prior, own), &[add])
}

/// The `demoted:` history of two lines carrying one id, each stamp once and
/// `a`'s order first, then whatever `b` adds (§6.3 "stamps accumulate:
/// `W36,W37`"). Callers pass the line whose history came first as `a`; the
/// stamps themselves cannot be sorted (see [`merge_stamps`]).
fn union_stamps(a: &[Stamp], b: &[Stamp]) -> Vec<Stamp> {
    let mut v: Vec<Stamp> = Vec::new();
    for s in a.iter().chain(b) {
        if !v.contains(s) {
            v.push(*s);
        }
    }
    v
}

/// What an archive copy records about a demotion that already happened: the
/// `demoted:` stamps it accumulated, and the `est:` that close measured as
/// the remaining (`None` when the copy carries no explicit `est:`).
///
/// Both go away when [`demote_one`] supersedes the copy, so both have to be
/// read off it first: the stamps accumulate (§6.3 "`W36,W37`") and the
/// remaining is §0 principle 6's whole point.
#[derive(Debug, Default)]
struct ArchivedRecord {
    /// The copy's `demoted:` stamps, in the order it carries them.
    stamps: Vec<Stamp>,
    /// The copy's explicit `est:` in minutes — the remaining the close that
    /// wrote it measured, dropped children folded in.
    est_min: Option<u32>,
}

/// Read [`ArchivedRecord`] off the `# Demoted` copy of `key` in `month_path`,
/// from the store (that copy may have been written by an earlier close, long
/// after the snapshot in [`Ctx::files`] was taken). Empty when there is none.
fn archived_record(cx: &Ctx, month_path: &str, key: &Id) -> Result<ArchivedRecord, HorizonError> {
    if !cx.store.exists(month_path) {
        return Ok(ArchivedRecord::default());
    }
    let parsed = cx.store.read_file(month_path)?;
    let rec = parsed
        .items()
        .find(|i| Tree::key_of(i) == *key && in_section(i, DEMOTED_SECTION))
        .map(|i| ArchivedRecord {
            stamps: i.stamps.demoted.clone(),
            est_min: i.est.map(|d| d.as_minutes()),
        })
        .unwrap_or_default();
    Ok(rec)
}

/// The `# Demoted` archive copy of `key` left in a month file *other* than
/// the one this demotion writes into, with what it records.
///
/// §6.3 gives an id one archive copy ("the line is **copied** to
/// `month/<current>#Demoted`"), and `tree.rs` models exactly one; but
/// `<current>` is today's month, so a close that catches up on an old week
/// writes into a later month than the one holding the record — and a month
/// close carrying the older copy forward would then put two lines with one
/// id in a single file, which is a `tm check` `dup-id` (§4.1, §17.2).
/// [`demote_one`] merges this copy's stamps into the one it writes and
/// deletes it, so the record moves rather than multiplying.
fn stale_archive_copy<'a>(
    cx: &Ctx<'a>,
    month_path: &str,
    key: &Id,
) -> Option<(String, ArchivedRecord)> {
    let files: &'a PlanFiles = cx.files;
    files.files.iter().find_map(|f| {
        if f.path == month_path || !matches!(f.horizon, Horizon::Month(_)) {
            return None;
        }
        let item = item_of(f, key)?;
        in_section(item, DEMOTED_SECTION).then(|| {
            (
                f.path.clone(),
                ArchivedRecord {
                    stamps: item.stamps.demoted.clone(),
                    est_min: item.est.map(|d| d.as_minutes()),
                },
            )
        })
    })
}

/// `demoted:` value as written (`W36,W37`).
fn stamp_value(stamps: &[Stamp]) -> String {
    stamps
        .iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>()
        .join(",")
}

/// True when the item sits in a section with this heading text.
fn in_section(item: &Item, name: &str) -> bool {
    item.src.section.as_deref() == Some(name)
}

/// Is this dated item past due with `on_miss = persist` (§5.3)? Uses the
/// *effective* shape, so a prep child is overdue once its interval started.
fn overdue_at(cx: &Ctx, key: &Id, item: &Item, now: NaiveDateTime) -> bool {
    if item.on_miss != OnMiss::Persist || item.recur != Recur::None {
        return false;
    }
    let shape = if cx.tree.contains(key) {
        cx.tree.effective_shape(key)
    } else {
        item.shape.clone()
    };
    match shape {
        Shape::Point { due } => due.end_of_day() < now,
        Shape::Interval { end, .. } => end < now,
        _ => false,
    }
}

/// The remaining minutes an `est:` should carry for `key` (§6.4 rollup:
/// `est` → `est_original` → `dur` → Σ children), floored at
/// [`MIN_REMAINING_MIN`]; `None` when neither the item nor any descendant
/// has an estimate, in which case no `est:` is written.
fn remaining_est(cx: &Ctx, key: &Id, item: &Item) -> Option<u32> {
    let own = item.own_remaining().map(|d| d.as_minutes());
    let rolled = cx.tree.remaining(key);
    own.or(rolled).map(|m| m.max(MIN_REMAINING_MIN))
}

/// The `est:` a demoted item carries: the largest of the §6.4 rollup,
/// `folded` — the remaining of the children this close dropped with it
/// (§6.3 "their remaining is folded into the parent's `est:`") — and
/// `recorded`, the remaining an earlier demotion already measured onto the
/// archive copy this one supersedes. `None` only when there is nothing to
/// write at all.
///
/// All three are floors rather than one of them winning outright, because
/// each knows something the others cannot (§0 principle 6, "demotion, not
/// deletion" — no work leaves the tree):
///
/// * the rollup is the only one that sees the line as it stands now, so an
///   estimate raised since the last demotion (`tm edit est=`, a child added)
///   is not thrown away;
/// * `folded` is the only one that sees the lines this close is about to
///   delete from the week file;
/// * `recorded` is the only one that still knows what an *earlier* close
///   measured — its own dropped children included — because §6.3 writes
///   `est:` = remaining onto the archive copy and never onto the line it
///   archives, no verb ever writes that copy ([`tree::record_rank`] ranks
///   every live line above every archive copy, so it is what `tm edit` and
///   `tm stop` reach), and this demotion is about to overwrite or delete it.
fn demote_est(cx: &Ctx, key: &Id, item: &Item, folded: u32, recorded: Option<u32>) -> Option<u32> {
    let floor = folded.max(recorded.unwrap_or(0));
    match (remaining_est(cx, key, item), floor) {
        (Some(base), f) => Some(base.max(f)),
        (None, 0) => None,
        (None, f) => Some(f.max(MIN_REMAINING_MIN)),
    }
}

/// What one line is worth on its own (`est:` → leading estimate → `dur:`),
/// used to fold a dropped child into its parent: each dropped line counts
/// once, and a line that has no estimate of its own contributes nothing.
fn own_minutes(item: &Item) -> u32 {
    item.own_remaining().map_or(0, |d| d.as_minutes())
}

// -- where a section-less move lands ----------------------------------------

/// Sections whose *name* changes what a line means, so a move that was not
/// asked for one must not land in them: `# Demoted` (§6.3), `# Pinned`
/// (§6.2), `## series:<name>` (§5.4), and a day file's append-only `## Log`
/// and free-text `## Notes` (§4.3).
fn is_reserved_section(name: &str) -> bool {
    matches!(
        name,
        DEMOTED_SECTION | PINNED_SECTION | OVERDUE_SECTION | "Log" | "Notes"
    ) || name.starts_with("series:")
}

/// The section a horizon file keeps its ordinary work in, created on demand
/// when every section the file has is reserved.
fn canonical_section(to: &Horizon) -> Option<&'static str> {
    match to {
        Horizon::Day(_) => Some(PINNED_SECTION),
        Horizon::Backlog => Some("Untied"),
        Horizon::Month(_) => Some("Outcomes"),
        Horizon::Week(_) => Some("Tasks"),
        _ => None,
    }
}

/// The section [`move_item`] appends to when §13's `tm move ^id <horizon>`
/// names none: `# Pinned` in a day file (§6.2: nothing else there is a
/// planning candidate), otherwise the last section of the target that is not
/// reserved — the end of the file, when it has no sections at all.
fn default_section(cx: &Ctx, to: &Horizon) -> Result<Option<String>, HorizonError> {
    if matches!(to, Horizon::Day(_)) {
        return Ok(Some(PINNED_SECTION.to_string()));
    }
    let path = to.path();
    if !cx.store.exists(&path) {
        return Ok(None);
    }
    let parsed = cx.store.read_file(&path)?;
    let headings = edit::headings(&parsed);
    match headings.last() {
        // No sections, or a last section that means nothing in particular:
        // appending at the end of the file is safe.
        None => Ok(None),
        Some(h) if !is_reserved_section(&h.text) => Ok(None),
        Some(_) => Ok(headings
            .iter()
            .rev()
            .find(|h| !is_reserved_section(&h.text))
            .map(|h| h.text.clone())
            .or_else(|| canonical_section(to).map(str::to_string))),
    }
}

/// Move the line carrying `key` from `from` into the horizon file for `to`
/// — created with its front matter when missing — appending it to `section`
/// or to [`default_section`]. Returns the destination path. Writes no log
/// event: the caller decides whether this was a `move`, a `readopt` or part
/// of a close.
fn move_to(
    cx: &Ctx,
    from: &str,
    key: &Id,
    to: &Horizon,
    section: Option<&str>,
) -> Result<String, HorizonError> {
    let to_path = to.path();
    let section = match section {
        Some(s) => Some(s.to_string()),
        None => default_section(cx, to)?,
    };
    cx.store.ensure_horizon_file(to)?;
    cx.store
        .move_line_from(Some(from), key, &to_path, section.as_deref())?;
    Ok(to_path)
}

// -- raw line/front-matter transforms ---------------------------------------

fn text_lines(parsed: &ParsedFile) -> Vec<(String, String)> {
    parsed
        .lines
        .iter()
        .map(|l| (l.text(), l.eol.clone()))
        .collect()
}

fn default_eol(lines: &[(String, String)]) -> String {
    lines
        .iter()
        .map(|(_, e)| e)
        .find(|e| !e.is_empty())
        .cloned()
        .unwrap_or_else(|| "\n".to_string())
}

/// Join `(text, eol)` lines back into a file, giving every line but the last
/// an ending (a file that ended without a newline keeps that shape).
fn join_lines(mut lines: Vec<(String, String)>) -> String {
    let eol = default_eol(&lines);
    let n = lines.len();
    for (i, l) in lines.iter_mut().enumerate() {
        if l.1.is_empty() && i + 1 < n {
            l.1 = eol.clone();
        }
    }
    let mut out = String::new();
    for (text, eol) in lines {
        out.push_str(&text);
        out.push_str(&eol);
    }
    out
}

/// The file text with `key: value` set in the front matter (replacing the
/// key if it is already there, else added just above the closing `---`; a
/// file without front matter gets one).
fn with_front_matter(parsed: &ParsedFile, key: &str, value: &str) -> String {
    let mut lines = text_lines(parsed);
    let eol = default_eol(&lines);
    let entry = format!("{key}: {value}");
    let front = edit::front_matter_len(parsed);
    if front == 0 {
        let mut head = vec![
            ("---".to_string(), eol.clone()),
            (entry, eol.clone()),
            ("---".to_string(), eol),
        ];
        head.extend(lines);
        return join_lines(head);
    }
    let prefix = format!("{key}:");
    match lines[1..front - 1]
        .iter()
        .position(|(t, _)| t.trim_start().starts_with(&prefix))
    {
        Some(i) => lines[1 + i].0 = entry,
        None => lines.insert(front - 1, (entry, eol)),
    }
    join_lines(lines)
}

/// The file text with a `<!-- tm:review start -->…<!-- tm:review end -->`
/// block holding `body` appended at the end (after a blank separator).
fn with_block_at_end(parsed: &ParsedFile, name: &str, body: &str) -> String {
    let mut lines = text_lines(parsed);
    let eol = default_eol(&lines);
    if lines.last().is_some_and(|(t, _)| !t.trim().is_empty()) {
        lines.push((String::new(), eol.clone()));
    }
    lines.push((edit::start_marker(name, None), eol.clone()));
    for l in body.split('\n') {
        lines.push((l.to_string(), eol.clone()));
    }
    lines.push((edit::end_marker(name), eol));
    join_lines(lines)
}

// ---------------------------------------------------------------------------
// Single-item verbs (§13)
// ---------------------------------------------------------------------------

/// `tm move ^id <backlog|month|week|day>` (§13): move the exact line into
/// the horizon file for `to` — created with its front matter when missing —
/// appending it to `section` (`Some("Tasks")`, `Some("# Demoted")`) or to
/// the end of the file. Logs `move`.
///
/// A `[-]` line moved into a week is a readopt: it becomes `[ ]` and keeps
/// its `demoted:` stamps (§6.3). Use [`readopt`] to take the copy out of
/// `month/…# Demoted` by name and log it as such.
pub fn move_item(
    cx: &Ctx,
    id: &Id,
    to: &Horizon,
    section: Option<&str>,
) -> Result<Moved, HorizonError> {
    let (from, item) = locate(cx, id)?;
    move_line(cx, &from, id, item, to, section, false)
}

/// The shared body of [`move_item`] and [`readopt`]. `as_readopt` picks the
/// log event; the `[-]` → `[ ]` rewrite happens for both (a demoted line
/// that lands in a week is live again either way).
fn move_line(
    cx: &Ctx,
    from: &str,
    key: &Id,
    item: &Item,
    to: &Horizon,
    section: Option<&str>,
    as_readopt: bool,
) -> Result<Moved, HorizonError> {
    // Re-open a demoted line that is moving back into a planning horizon.
    let reopen = item.state == State::Demoted && matches!(to, Horizon::Week(_) | Horizon::Day(_));
    if reopen {
        let text = rewrite(item, key, |l| l.set_state(State::Todo))?;
        cx.store.write_line_in(Some(from), key, &text)?;
    }
    let to_path = move_to(cx, from, key, to, section)?;
    let ev = if as_readopt {
        Event::Readopt {
            id: key.to_string(),
        }
    } else {
        Event::Move {
            id: key.to_string(),
            from: from.to_string(),
            to: to_path.clone(),
        }
    };
    cx.log(ev)?;
    Ok(Moved {
        id: key.clone(),
        from: from.to_string(),
        to: to_path,
    })
}

/// `tm demote ^id` (§6.3, §13): mark a week item `[-]` in its week file and
/// copy the line into `month/<current>#Demoted` with `est:` = remaining and
/// `demoted:W<nn>` appended. Logs `demote`.
///
/// Only week items are demoted this way — a day-pinned item is *moved* into
/// the week by [`close_day`], and a month outcome has no enclosing horizon
/// to fall into.
pub fn demote(cx: &Ctx, id: &Id) -> Result<Demoted, HorizonError> {
    let (from, item) = locate(cx, id)?;
    let Horizon::Week(week) = item.horizon else {
        return Err(HorizonError::Horizon {
            id: id.clone(),
            horizon: item.horizon.to_string(),
            message: "only week items are demoted (use `tm move`)".to_string(),
        });
    };
    let month = YearMonth::from_date(cx.today());
    // A note here would only ever say that the month file has a live line
    // with the same id, which is a `tm check` duplicate-id problem of its own.
    let mut notes = Vec::new();
    demote_one(cx, &from, id, item, week, month, 0, &mut notes)
}

/// Demote one week line: `[-]` in place, a stamped copy under the month's
/// `# Demoted`, one `demote` event. `folded` is the remaining of the
/// children dropped with it (§6.3), 0 for a bare `tm demote`.
#[allow(clippy::too_many_arguments)]
fn demote_one(
    cx: &Ctx,
    from: &str,
    key: &Id,
    item: &Item,
    week: IsoWeek,
    month: YearMonth,
    folded: u32,
    notes: &mut Vec<String>,
) -> Result<Demoted, HorizonError> {
    let block_min = cx.block_min();
    let month_path = Horizon::Month(month).path();
    // The archive copy is where the history lives: the live week line only
    // knows the stamps written on it, so the copy's stamps come first — and
    // the copy may be sitting in an *earlier* month than the one this
    // demotion writes into (a catch-up close: §6.3's `month/<current>` is
    // today's month, the record was left in the month the last close ran in).
    // Its stamps come first of all, and its line goes away below, so the id
    // keeps the one copy §6.3 sanctions.
    let stale = stale_archive_copy(cx, &month_path, key);
    let here = archived_record(cx, &month_path, key)?;
    let mut prior: Vec<Stamp> = stale.as_ref().map(|(_, r)| r.stamps.clone()).unwrap_or_default();
    prior.extend(here.stamps.iter().copied());
    // …and so does the remaining: §6.3 writes `est:` = remaining onto the
    // copy and never onto the line it archives, so whatever an earlier close
    // measured — the children it dropped from the week file folded in —
    // exists only on the copy this demotion is about to overwrite or delete.
    // It goes into the new copy's `est:` as a floor, so the record moves
    // rather than restarting from the estimate the line has carried since
    // before its first demotion (§0 principle 6).
    let recorded = here.est_min.max(stale.as_ref().and_then(|(_, r)| r.est_min));
    let est = demote_est(cx, key, item, folded, recorded);
    let stamps = merge_stamps(&prior, &item.stamps.demoted, Stamp::Week(week.week));
    let value = stamp_value(&stamps);
    let copy = rewrite(item, key, |l| {
        l.set_state(State::Demoted)?;
        if let Some(m) = est {
            l.set_token("est", &est_dur(m, block_min).to_string());
        }
        l.set_token("demoted", &value);
        Ok(())
    })?;
    let archived = rewrite(item, key, |l| l.set_state(State::Demoted))?;
    notes.extend(write_demoted_copy(cx, &month_path, key, &copy)?);
    // The record this demotion just rewrote in `month_path` replaces the one
    // an earlier close left behind: two archive copies of one id are a
    // `tm check` `dup-id` the moment a month close carries them into the
    // same file (§4.1, §17.2 "ids are global").
    if let Some((path, _)) = &stale {
        cx.store.remove_line_in(Some(path), key)?;
    }
    cx.store.write_line_in(Some(from), key, &archived)?;
    cx.log(Event::Demote {
        id: key.to_string(),
        from: week.to_string(),
        to: month.to_string(),
        est_min: est.unwrap_or(0),
    })?;
    Ok(Demoted {
        id: key.clone(),
        est_min: est.unwrap_or(0),
        stamps,
    })
}

/// Write the archive copy of a demoted line into `month/…# Demoted`:
/// replacing the copy that is already there (a second demotion of the same
/// item accumulates stamps on one line, §6.3), else appending it.
/// Returns a note when the month file also has a *live* line with that id.
fn write_demoted_copy(
    cx: &Ctx,
    month_path: &str,
    key: &Id,
    text: &str,
) -> Result<Option<String>, HorizonError> {
    if cx.store.exists(month_path) {
        let parsed = cx.store.read_file(month_path)?;
        match edit::find_line(&parsed, key) {
            Some(i) if edit::is_demoted(&parsed, i) => {
                cx.store.write_line_in(Some(month_path), key, text)?;
                return Ok(None);
            }
            Some(_) => {
                cx.store
                    .insert_line(month_path, Some(DEMOTED_SECTION), text)?;
                return Ok(Some(format!(
                    "^{key} is also a live line in {month_path}; the demoted copy was added anyway"
                )));
            }
            None => {}
        }
    }
    cx.store
        .insert_line(month_path, Some(DEMOTED_SECTION), text)?;
    Ok(None)
}

/// `tm readopt ^id [--to week]` (§6.3, §13): take the demoted copy of `id`
/// (the one under `month/…# Demoted`, else wherever the line is) into `to`
/// — the current week by default — turning `[-]` back into `[ ]` and keeping
/// its stamps. Logs `readopt`.
///
/// Readopt is the demoted line's verb: an id with no demoted line anywhere is
/// refused (`tm move` is the verb for moving a live line between horizons),
/// so a `readopt` event in the log always records a real demotion undone
/// (§10.1, §11's demotion churn).
///
/// When the tree still holds a **live** line with that id — the shape §4.3's
/// own example tree ships, a `[ ]` week milestone beside its `[-]` archive
/// copy under `month/…# Demoted` — moving the copy in would put the id on two
/// live lines (§4.1: ids are global) and break `tm check`. The item is
/// already in the plan, so the archive copy is *absorbed* instead: its
/// `demoted:` stamps join the live line, the copy is removed, and the live
/// line itself is what moves into `to`.
pub fn readopt(cx: &Ctx, id: &Id, to: Option<&Horizon>) -> Result<Moved, HorizonError> {
    let current = Horizon::Week(IsoWeek::from_date(cx.today()));
    let to = to.unwrap_or(&current);
    let (from, item) = demoted_copy(cx, id)?;
    if let Some(moved) = absorb_into_live(cx, &from, to, id, item)? {
        return Ok(moved);
    }
    move_line(cx, &from, id, item, to, None, true)
}

/// Fold the archive copy of `key` into the live line the tree still has for
/// it, if there is one: the copy's stamps and its `est:` are merged onto that
/// line, the copy is deleted, and the line moves into `to` (it is the item;
/// the copy was only the record). `None` when the id has no live line, which
/// is the ordinary readopt.
///
/// The copy owns the *remaining* estimate — §6.3's week close writes `est:`
/// = remaining onto it (the children it dropped from the week file folded
/// in) and never onto the line it archives, and that number is the whole
/// point of demoting rather than deleting (§0 principle 6) — while the live
/// line still carries whatever it was estimated at before the demotion.
///
/// Nothing has changed that copy since, and nothing ever will:
/// [`tree::record_rank`] ranks *every* live line above *every* archive copy
/// (`is_archive_copy` is its first key, and `false` sorts first — the stamp
/// count only breaks ties between two archive copies), so `Tree::get` and
/// `store::choose` both resolve the id to the live line, and that is the
/// line `tm edit`, `tm stop` and `tm done --partial` read and rewrite. The
/// copy is a dead end holding a number that exists nowhere else, and this
/// absorb deletes it — so the surviving line takes its remaining with it. A
/// copy that carries no estimate at all leaves the live line's own alone.
fn absorb_into_live(
    cx: &Ctx,
    from: &str,
    to: &Horizon,
    key: &Id,
    copy: &Item,
) -> Result<Option<Moved>, HorizonError> {
    let Some((live_path, live)) = live_line(cx, key, from) else {
        return Ok(None);
    };
    let stamps = union_stamps(&copy.stamps.demoted, &live.stamps.demoted);
    let est = copy
        .own_remaining()
        .filter(|d| live.own_remaining().map(|l| l.as_minutes()) != Some(d.as_minutes()));
    let write_stamps = !stamps.is_empty() && stamps != live.stamps.demoted;
    if write_stamps || est.is_some() {
        let value = stamp_value(&stamps);
        let text = rewrite(live, key, |l| {
            // `est:` first, so a line that has neither token ends up in
            // §4.3's order (`est: demoted: ^id`): both are inserted before
            // the `^id`, in the order they are written.
            if let Some(d) = est {
                l.set_token("est", &d.to_string());
            }
            if write_stamps {
                l.set_token("demoted", &value);
            }
            Ok(())
        })?;
        cx.store.write_line_in(Some(&live_path), key, &text)?;
    }
    cx.store.remove_line_in(Some(from), key)?;
    let to_path = to.path();
    if live_path != to_path {
        move_to(cx, &live_path, key, to, None)?;
    }
    cx.log(Event::Readopt {
        id: key.to_string(),
    })?;
    Ok(Some(Moved {
        id: key.clone(),
        from: from.to_string(),
        to: to_path,
    }))
}

/// The live line carrying `key` — one that is not a §6.3 archive copy, the
/// same test `tm check` counts duplicates by ([`tree::is_archive_copy`]) — in
/// a file other than `skip` (the archive copy being readopted). `None` when
/// the id is only archive copies, which is the ordinary readopt.
fn live_line<'a>(cx: &Ctx<'a>, key: &Id, skip: &str) -> Option<(String, &'a Item)> {
    let files: &'a PlanFiles = cx.files;
    files.files.iter().find_map(|f| {
        if f.path == skip {
            return None;
        }
        let item = item_of(f, key)?;
        (!tree::is_archive_copy(item)).then(|| (f.path.clone(), item))
    })
}

/// The copy of `id` to readopt: a `# Demoted` line in a month file if there
/// is one (that is where a week close leaves it), else any other demoted
/// line. Readopt only ever moves a demoted line (§6.3), so an id with none is
/// refused rather than moved like `tm move`.
fn demoted_copy<'a>(cx: &Ctx<'a>, id: &Id) -> Result<(String, &'a Item), HorizonError> {
    let files: &'a PlanFiles = cx.files;
    let mut fallback: Option<(String, &Item)> = None;
    for f in &files.files {
        let Some(item) = item_of(f, id) else { continue };
        let demoted_here = in_section(item, DEMOTED_SECTION) || item.state == State::Demoted;
        if matches!(f.horizon, Horizon::Month(_)) && demoted_here {
            return Ok((f.path.clone(), item));
        }
        if demoted_here && fallback.is_none() {
            fallback = Some((f.path.clone(), item));
        }
    }
    match fallback {
        Some(x) => Ok(x),
        None => {
            let (_, item) = locate(cx, id)?;
            Err(HorizonError::Horizon {
                id: id.clone(),
                horizon: item.horizon.to_string(),
                message: "not demoted, so there is nothing to readopt (use `tm move`)".to_string(),
            })
        }
    }
}

/// `tm drop ^id` (§13): set the state to `[~]` where the line lives. Logs
/// `drop`.
pub fn drop_item(cx: &Ctx, id: &Id) -> Result<String, HorizonError> {
    let (from, item) = locate(cx, id)?;
    let text = rewrite(item, id, |l| l.set_state(State::Dropped))?;
    cx.store.write_line_in(Some(from.as_str()), id, &text)?;
    cx.log(Event::Drop {
        id: id.to_string(),
    })?;
    Ok(text)
}

/// `tm rank ^id <n>` (§13, §7.4): move the line to position `n` (1-based)
/// among the item lines of its own section — rank *is* line order. Returns
/// whether the line moved (`n` is clamped to the section).
pub fn rank(cx: &Ctx, id: &Id, n: usize) -> Result<bool, HorizonError> {
    let (path, _) = locate(cx, id)?;
    let parsed = cx.store.read_file(&path)?;
    let idx = edit::find_line(&parsed, id).ok_or_else(|| HorizonError::NotFound(id.clone()))?;
    let (start, end) = edit::section_range(&parsed, idx);
    let items: Vec<usize> = (start..end)
        .filter(|&i| parsed.lines[i].item().is_some())
        .collect();
    let pos = items
        .iter()
        .position(|&i| i == idx)
        .ok_or_else(|| HorizonError::NotFound(id.clone()))?;
    let target = n.max(1).min(items.len()) - 1;
    let delta = target as i64 - pos as i64;
    if delta == 0 {
        return Ok(false);
    }
    Ok(cx.store.reorder_line(id, delta as i32)?)
}

// ---------------------------------------------------------------------------
// Close: day (§6.3)
// ---------------------------------------------------------------------------

/// `tm close day` for `date` (§6.3).
///
/// Every `[>]` in `week/<week of date>` and in the day file's `# Pinned`
/// section becomes `[ ]` with `est:` = remaining (the §6.4 rollup, with the
/// replay's minutes for `date` taken off only when
/// the line carries no tool-written `est:` yet, floored at
/// [`MIN_REMAINING_MIN`]); pinned items still open then move to the week
/// file with `demoted:D<dd>` (recurring lines stay put, §5.3); nothing else
/// moves. An existing day file receives its review placeholder, unless its
/// review block already holds a review (§13's `tm review day --write`), which
/// a close never overwrites. Appends one `demote` per moved pinned item and a
/// `close{period:"day"}`.
pub fn close_day(cx: &Ctx, date: NaiveDate) -> Result<CloseReport, HorizonError> {
    let week = IsoWeek::from_date(date);
    let week_path = Horizon::Week(week).path();
    let day_path = Horizon::Day(date).path();
    let block_min = cx.block_min();
    let mut report = CloseReport::new(Period::Day, date.format("%Y-%m-%d").to_string());

    // 1. Active items in the week file: `[>]` -> `[ ]` with a fresh `est:`.
    let week_active: Vec<(Id, &Item)> = cx
        .files
        .file(&week_path)
        .map(|f| {
            f.items()
                .filter(|i| i.state == State::Active)
                .map(|i| (Tree::key_of(i), i))
                .collect()
        })
        .unwrap_or_default();
    for (key, item) in &week_active {
        let est = day_remaining(cx, key, item, date);
        let text = rewrite(item, key, |l| {
            l.set_state(State::Todo)?;
            if let Some(m) = est {
                l.set_token("est", &est_dur(m, block_min).to_string());
            }
            Ok(())
        })?;
        cx.store.write_line_in(Some(week_path.as_str()), key, &text)?;
        report.reopened.push(Reopened {
            id: key.clone(),
            est_min: est.unwrap_or(0),
        });
    }

    // 2. The day file's `# Pinned` section: the same reset, then a move into
    //    the week with a `demoted:D<dd>` stamp for everything still open.
    let pinned: Vec<(Id, &Item)> = cx
        .files
        .file(&day_path)
        .map(|f| {
            f.items()
                .filter(|i| in_section(i, PINNED_SECTION))
                .map(|i| (Tree::key_of(i), i))
                .collect()
        })
        .unwrap_or_default();
    let stamp = Stamp::Day(date.day());
    for (key, item) in &pinned {
        // A recurring line is never demoted — its instances expire or persist
        // per §5.3 — and a finished one has nowhere to go.
        if !item.state.is_open() || item.recur != Recur::None {
            continue;
        }
        let was_active = item.state == State::Active;
        let est = if was_active {
            day_remaining(cx, key, item, date)
        } else {
            None
        };
        let stamps = stamps_with(item, stamp);
        let value = stamp_value(&stamps);
        let text = rewrite(item, key, |l| {
            if was_active {
                l.set_state(State::Todo)?;
                if let Some(m) = est {
                    l.set_token("est", &est_dur(m, block_min).to_string());
                }
            }
            l.set_token("demoted", &value);
            Ok(())
        })?;
        cx.store.write_line_in(Some(day_path.as_str()), key, &text)?;
        if was_active {
            report.reopened.push(Reopened {
                id: key.clone(),
                est_min: est.unwrap_or(0),
            });
        }
        move_to(cx, &day_path, key, &Horizon::Week(week), None)?;
        let est_min = est.or_else(|| remaining_est(cx, key, item)).unwrap_or(0);
        cx.log(Event::Demote {
            id: key.to_string(),
            from: date.format("%Y-%m-%d").to_string(),
            to: week.to_string(),
            est_min,
        })?;
        report.moved.push(Moved {
            id: key.clone(),
            from: day_path.clone(),
            to: week_path.clone(),
        });
        report.demoted.push(Demoted {
            id: key.clone(),
            est_min,
            stamps,
        });
    }

    // 3. The review placeholder `review.rs` fills in later.
    if !write_review_placeholder(cx, &day_path)? {
        report
            .notes
            .push(format!("{day_path} does not exist; no review section written"));
    }

    cx.log(Event::Close {
        period: period_name(Period::Day).to_string(),
        key: date.format("%Y-%m-%d").to_string(),
    })?;
    Ok(report)
}

/// Remaining minutes for a day close (§6.3 "`est:` = remaining"): the §6.4
/// rollup as the line has it, floored at [`MIN_REMAINING_MIN`]. `None` when
/// there is no estimate anywhere to write.
///
/// The day's logged minutes are subtracted **only** from a line that carries
/// no `est:` of its own. `est:` is tool-written (§9.1: `tm stop` and
/// `tm done --partial` set it to what is left *after* the block they close),
/// so subtracting the same minutes again at midnight would count them twice
/// and walk the estimate down to the floor. A line with no `est:` still
/// carries the estimate it was written with, and the minutes the replay
/// recorded against it on `date` are genuinely not in it yet.
fn day_remaining(cx: &Ctx, key: &Id, item: &Item, date: NaiveDate) -> Option<u32> {
    let base = remaining_est(cx, key, item)?;
    if item.est.is_some() {
        return Some(base);
    }
    let done = cx
        .replay
        .map_or(0, |r| r.block_minutes_on(key.as_str(), date));
    Some(base.saturating_sub(done).max(MIN_REMAINING_MIN))
}

/// True when the review block of a day file already holds a review: a line
/// between its markers that is neither blank nor [`REVIEW_PLACEHOLDER`].
///
/// An **unterminated** block has no body at all (§1.3 and
/// [`edit::replace_generated`]: with the end marker lost, everything below is
/// ordinary text), so it counts as empty and the close writes the placeholder
/// between fresh markers, leaving that text verbatim underneath.
fn has_written_review(parsed: &ParsedFile) -> bool {
    let Some(g) = parsed.generated(REVIEW_BLOCK) else {
        return false;
    };
    let Some(end) = g.end_line else {
        return false;
    };
    parsed
        .lines
        .get(g.start_line..end - 1)
        .unwrap_or_default()
        .iter()
        .any(|l| {
            let t = l.text();
            !t.trim().is_empty() && t.trim() != REVIEW_PLACEHOLDER
        })
}

/// Put the `<!-- tm:review … -->` block in the day file: appending it at the
/// end (below `## Notes`), which is where a review belongs —
/// [`Store::replace_generated`] would otherwise create it above the generated
/// plan.
///
/// §6.3 gives the day file its review *section*; §13's `tm review day
/// --write` gives it the review *text*, and the two run in either order —
/// the close of §13 fires automatically on the first command after the day
/// ends, which is easily after the review was written by hand. So a block
/// that already holds a review is **left exactly as it is**: overwriting it
/// would delete the one copy of that text. Only an absent, empty or
/// still-placeholder block is (re)written, which is also what keeps a second
/// close a no-op.
fn write_review_placeholder(cx: &Ctx, day_path: &str) -> Result<bool, HorizonError> {
    // A day that was never planned has no file; closing it does not create
    // one (`tm close day` after a day off would otherwise leave an empty
    // day file behind).
    if !cx.store.exists(day_path) {
        return Ok(false);
    }
    cx.store.modify_file(day_path, &mut |parsed: &ParsedFile| {
        if parsed.generated(REVIEW_BLOCK).is_some() {
            if has_written_review(parsed) {
                return Ok(None);
            }
            return Ok(Some(edit::replace_generated(
                parsed,
                REVIEW_BLOCK,
                None,
                REVIEW_PLACEHOLDER,
            )));
        }
        Ok(Some(with_block_at_end(
            parsed,
            REVIEW_BLOCK,
            REVIEW_PLACEHOLDER,
        )))
    })?;
    Ok(true)
}

// ---------------------------------------------------------------------------
// Close: week (§6.3)
// ---------------------------------------------------------------------------

/// `tm close week` for `week` (§6.3).
///
/// Unfinished lines become `[-]` in the week file and are copied to
/// `month/<current>#Demoted` with `est:` = remaining and `demoted:W<nn>`
/// (accumulating the stamps the archive copy already carries); unfinished
/// children of a demoted item are removed from the week file, their
/// remaining folded into that item's `est:`; dated persist items past due
/// move to `backlog.md#Overdue` instead; walls — dated intervals that are
/// not past due (§7.2) — and their prep children are never demoted (§6.3)
/// and move into the current week; recurring items and closed lines are
/// untouched. The week file's front matter gets `closed: <date>`.
pub fn close_week(cx: &Ctx, week: IsoWeek) -> Result<CloseReport, HorizonError> {
    let week_path = Horizon::Week(week).path();
    let file = cx
        .files
        .file(&week_path)
        .ok_or_else(|| HorizonError::MissingFile(week_path.clone()))?;
    let month = YearMonth::from_date(cx.today());
    let now = cx.now_naive();
    let mut report = CloseReport::new(Period::Week, week.to_string());

    // Classify first, from the snapshot: nothing below re-reads the tree.
    let open: Vec<(Id, &Item)> = file
        .items()
        .filter(|i| i.state.is_open() && i.recur == Recur::None)
        .map(|i| (Tree::key_of(i), i))
        .collect();
    let overdue: HashSet<Id> = open
        .iter()
        .filter(|(k, i)| overdue_at(cx, k, i, now))
        .map(|(k, _)| k.clone())
        .collect();
    // Walls and their prep are never demoted (§6.3); everything else that is
    // still open and not past due is.
    let carried = carried_walls(cx, &open, &overdue, |i| {
        matches!(i.shape, Shape::Interval { .. })
    });
    // Of those, the ones still ahead of us move into the live week; a wall
    // that is over stays in the archive it was planned in.
    let carry_forward = carried_walls(cx, &open, &overdue, |i| {
        matches!(i.shape, Shape::Interval { end, .. } if end >= now)
    });
    let candidates: HashSet<Id> = open
        .iter()
        .map(|(k, _)| k.clone())
        .filter(|k| !overdue.contains(k) && !carried.contains(k))
        .collect();
    let cycles: HashSet<Id> = cx.tree.parent_cycles().into_iter().flatten().collect();
    let mut roots: Vec<(Id, &Item)> = Vec::new();
    let mut children: Vec<(Id, &Item, Id)> = Vec::new();
    for (key, item) in &open {
        if !candidates.contains(key) {
            continue;
        }
        match demoted_ancestor(cx.tree, &candidates, &cycles, key) {
            Some(root) => children.push((key.clone(), item, root)),
            None => {
                if cycles.contains(key) {
                    report.notes.push(format!(
                        "^{key} is in a parent cycle (a `tm check` error); it was demoted as a \
                         root rather than dropped as somebody's child"
                    ));
                }
                roots.push((key.clone(), item));
            }
        }
    }
    // Each dropped line is worth its own estimate, once, to the item it
    // folds into (§6.3 "their remaining is folded into the parent's `est:`").
    let mut folded: HashMap<Id, u32> = HashMap::new();
    for (_, item, root) in &children {
        *folded.entry(root.clone()).or_default() += own_minutes(item);
    }

    // 1. Demote the roots: `[-]` in place, a stamped copy in the month file.
    for (key, item) in &roots {
        let fold = folded.get(key).copied().unwrap_or(0);
        let demoted = demote_one(cx, &week_path, key, item, week, month, fold, &mut report.notes)?;
        report.demoted.push(demoted);
    }
    // 2. Drop the children's lines; their remaining went into that est:.
    for (key, _, _) in &children {
        cx.store.remove_line_in(Some(week_path.as_str()), key)?;
        report.dropped_children.push(key.clone());
    }
    // 3. Walls stay `[ ]` (§5.3) and move into the live planning week — the
    //    horizon the planner still reads (§6.2). Closing *this* week (the
    //    verb's documented default: `tm close week` on the Sunday) still
    //    archives this file, so the walls go to the following week rather
    //    than staying behind in an archive nothing plans from.
    let today_week = IsoWeek::from_date(cx.today());
    let live = if today_week.monday() > week.monday() {
        today_week
    } else {
        week.next()
    };
    for (key, _) in open.iter().filter(|(k, _)| carried.contains(k)) {
        report.carried.push(key.clone());
        if !carry_forward.contains(key) {
            continue;
        }
        let to_path = move_to(cx, &week_path, key, &Horizon::Week(live), None)?;
        cx.log(Event::Move {
            id: key.to_string(),
            from: week_path.clone(),
            to: to_path.clone(),
        })?;
        report.moved.push(Moved {
            id: key.clone(),
            from: week_path.clone(),
            to: to_path,
        });
    }
    // 4. Dated persist items past due go to `backlog.md#Overdue` instead.
    for (key, _) in open.iter().filter(|(k, _)| overdue.contains(k)) {
        let to_path = move_to(cx, &week_path, key, &Horizon::Backlog, Some(OVERDUE_SECTION))?;
        cx.log(Event::Move {
            id: key.to_string(),
            from: week_path.clone(),
            to: to_path.clone(),
        })?;
        report.moved.push(Moved {
            id: key.clone(),
            from: week_path.clone(),
            to: to_path,
        });
        report.overdue_to_backlog.push(key.clone());
    }
    // 5. The week file is an archive from now on.
    let closed_on = cx.today().format("%Y-%m-%d").to_string();
    cx.store.modify_file(&week_path, &mut |parsed: &ParsedFile| {
        Ok(Some(with_front_matter(parsed, "closed", &closed_on)))
    })?;

    for d in &report.demoted {
        if d.stamps.len() >= 2 {
            report.notes.push(cut_note(&d.id, d.stamps.len()));
        }
    }
    cx.log(Event::Close {
        period: period_name(Period::Week).to_string(),
        key: week.to_string(),
    })?;
    Ok(report)
}

/// The open lines a week close leaves live instead of demoting: dated
/// intervals that are not past due — the walls of §7.2 (calendar, exams,
/// meetings), which §6.3 exempts — and everything below them that is still
/// in this file (§6.4 prep children, at any depth).
///
/// `wall` picks which intervals seed the set: every one of them for "never
/// demote this", only the ones that have not ended for "move this into the
/// live week" (a wall that is over carries nothing forward — its instance
/// expired, §5.3 — and a past-due `persist` one is in `overdue` already).
fn carried_walls(
    cx: &Ctx,
    open: &[(Id, &Item)],
    overdue: &HashSet<Id>,
    wall: impl Fn(&Item) -> bool,
) -> HashSet<Id> {
    let mut carried: HashSet<Id> = open
        .iter()
        .filter(|(k, i)| !overdue.contains(k) && wall(i))
        .map(|(k, _)| k.clone())
        .collect();
    // Walk down one generation at a time; `carried` only grows, so this ends.
    loop {
        let mut grew = false;
        for (key, _) in open {
            if carried.contains(key) || overdue.contains(key) {
                continue;
            }
            if cx.tree.parent(key).is_some_and(|p| carried.contains(p)) {
                carried.insert(key.clone());
                grew = true;
            }
        }
        if !grew {
            return carried;
        }
    }
}

/// Is this line the top of its demoted subtree — is nothing above it in the
/// same file being demoted too? A member of a parent cycle counts as one: a
/// cycle has no top, and every line in it would otherwise be dropped as
/// somebody's child and vanish (§0 principle 6, §5.5).
fn is_demotion_root(
    tree: &Tree,
    candidates: &HashSet<Id>,
    cycles: &HashSet<Id>,
    key: &Id,
) -> bool {
    cycles.contains(key) || tree.parent(key).is_none_or(|p| !candidates.contains(p))
}

/// The nearest ancestor of `key` that this close demotes as a root, reached
/// through a chain of lines it also demotes; `None` when `key` is itself
/// such a root (or when the chain runs out without finding one, in which
/// case the caller demotes the line rather than dropping it).
fn demoted_ancestor(
    tree: &Tree,
    candidates: &HashSet<Id>,
    cycles: &HashSet<Id>,
    key: &Id,
) -> Option<Id> {
    if is_demotion_root(tree, candidates, cycles, key) {
        return None;
    }
    let mut seen: HashSet<Id> = HashSet::new();
    seen.insert(key.clone());
    let mut cur = key.clone();
    while let Some(parent) = tree.parent(&cur) {
        if !candidates.contains(parent) || !seen.insert(parent.clone()) {
            return None;
        }
        if is_demotion_root(tree, candidates, cycles, parent) {
            return Some(parent.clone());
        }
        cur = parent.clone();
    }
    None
}

/// The §6.3 / §11 "demotion churn" remark: two stamps means re-scope or cut.
fn cut_note(id: &Id, stamps: usize) -> String {
    format!("^{id} has {stamps} demotion stamps — /plan-month proposes a cut or a re-scope")
}

// ---------------------------------------------------------------------------
// Close: month (§6.3)
// ---------------------------------------------------------------------------

/// `tm close month [--drop ^id …]` for `month` (§6.3).
///
/// Unfinished outcomes and everything under `# Demoted` move to the next
/// month file, each into the section it came from (outcomes keep their `!k`,
/// demoted items keep their stamps); ids in `drops` become `[~]` and stay
/// behind. The report lists what carried over with its stamp count, which is
/// what `/plan-month` proposes cuts from.
///
/// A `--drop` is never silently discarded. The close auto-runs with an empty
/// drop list on the first command after the month ends ([`auto_close`]), so
/// by the time a user types `tm close month --drop ^id` the carry has usually
/// already happened and the line is in the *next* month's file. Such an id is
/// brought back and dropped, which is exactly where the same command run
/// before the auto-close would have left it — the close is idempotent under a
/// growing drop list. An id in neither file cannot be honoured and is an
/// error.
pub fn close_month(
    cx: &Ctx,
    month: YearMonth,
    drops: &[Id],
) -> Result<CloseReport, HorizonError> {
    let from = Horizon::Month(month).path();
    let file = cx
        .files
        .file(&from)
        .ok_or_else(|| HorizonError::MissingFile(from.clone()))?;
    let next = month.next();
    let to = Horizon::Month(next).path();
    let wanted: HashSet<&Id> = drops.iter().collect();
    let mut report = CloseReport::new(Period::Month, month.to_string());

    struct Carry<'a> {
        key: Id,
        item: &'a Item,
        section: Option<String>,
        demoted: bool,
    }
    let mut carry: Vec<Carry> = Vec::new();
    let mut to_drop: Vec<(Id, &Item)> = Vec::new();
    let mut resolved: HashSet<Id> = HashSet::new();
    for item in file.items() {
        let key = Tree::key_of(item);
        if wanted.contains(&key) {
            resolved.insert(key.clone());
            to_drop.push((key, item));
            continue;
        }
        let demoted = in_section(item, DEMOTED_SECTION);
        // `[x]` and `[~]` outcomes stay in the month they belong to; anything
        // still open — `[ ]`, `[>]`, and a `[?]` waiting on someone — carries.
        if !demoted && item.state.is_closed() {
            continue;
        }
        carry.push(Carry {
            key,
            item,
            section: item.src.section.clone(),
            demoted,
        });
    }

    // Drops whose line this close already carried into `to` (an earlier run
    // of the very same close — usually the auto-close): `(id, line, section
    // to put it back in)`. `resolved` holds the ids the loop above matched,
    // so this one sees only the leftovers, each exactly once. Like every
    // other decision here it is made before the first write, so a `--drop`
    // that cannot be honoured leaves the tree untouched rather than
    // half-closed.
    let mut pull_back: Vec<(Id, &Item, Option<String>)> = Vec::new();
    // Drops this close has nothing left to do about: the line is already
    // `[~]` wherever it ended up. Reported as dropped, written again nowhere.
    let mut already: Vec<Id> = Vec::new();
    for id in drops {
        if !resolved.insert(id.clone()) {
            continue;
        }
        match cx.files.file(&to).and_then(|f| item_of(f, id)) {
            Some(item) => pull_back.push((id.clone(), item, item.src.section.clone())),
            None => {
                let found = locate(cx, id);
                // §6.3 "idempotent": the second run of a close that already
                // honoured this `--drop` asks for a state the item is in, so
                // it is done, not wrong. (The line can be anywhere by then —
                // `tm close month --drop ^id` leaves it in the month it was
                // dropped from, which the next month's close does not carry.)
                if let Ok((_, item)) = &found {
                    if item.state == State::Dropped {
                        already.push(id.clone());
                        continue;
                    }
                }
                return Err(match found {
                    Ok((path, _)) => HorizonError::Horizon {
                        id: id.clone(),
                        horizon: path,
                        message: format!(
                            "--drop only names items of {from} (or ones this close already \
                             carried into {to}); drop it where it lives with `tm drop`"
                        ),
                    },
                    Err(e) => e,
                })
            }
        }
    }

    for (key, item) in &to_drop {
        let text = rewrite(item, key, |l| l.set_state(State::Dropped))?;
        cx.store.write_line_in(Some(from.as_str()), key, &text)?;
        cx.log(Event::Drop {
            id: key.to_string(),
        })?;
        report.dropped.push(key.clone());
    }

    for (key, item, section) in &pull_back {
        let text = rewrite(item, key, |l| l.set_state(State::Dropped))?;
        cx.store.write_line_in(Some(to.as_str()), key, &text)?;
        cx.store
            .move_line_from(Some(to.as_str()), key, &from, section.as_deref())?;
        cx.log(Event::Move {
            id: key.to_string(),
            from: to.clone(),
            to: from.clone(),
        })?;
        cx.log(Event::Drop {
            id: key.to_string(),
        })?;
        report.dropped.push(key.clone());
    }
    // A drop that was already honoured writes nothing and logs nothing (§10.1
    // records what happened, and nothing did), but it is still part of what
    // this close was asked for, so the report says so.
    report.dropped.extend(already);

    if !carry.is_empty() {
        cx.store.ensure_horizon_file(&Horizon::Month(next))?;
    }
    // What the next month's file already holds, so the carry never writes an
    // id it has (§4.1, §17.2: ids are global; two lines with one id in a
    // single file is a `tm check` `dup-id`). A record that meets a line for
    // its own id there is folded into it — one line, accumulated stamps
    // (§6.3) — which is also how a tree that arrived with two `# Demoted`
    // copies of one item stops carrying both forward every month.
    let mut in_to: HashMap<Id, &Item> = cx
        .files
        .file(&to)
        .map(|f| f.items().map(|i| (Tree::key_of(i), i)).collect())
        .unwrap_or_default();
    for c in &carry {
        if let Some(there) = in_to.get(&c.key).copied() {
            // The carried copy's stamps first, then the ones the line in
            // `to` adds — the order the two lines are read in, not an age
            // order, which `Stamp` (`W37`, `D07`, no year) cannot express.
            let stamps = union_stamps(&c.item.stamps.demoted, &there.stamps.demoted);
            if stamps != there.stamps.demoted {
                let text = rewrite(there, &c.key, |l| {
                    l.set_token("demoted", &stamp_value(&stamps));
                    Ok(())
                })?;
                cx.store.write_line_in(Some(to.as_str()), &c.key, &text)?;
            }
            cx.store.remove_line_in(Some(from.as_str()), &c.key)?;
            // §6.3's month close "moves them to the next month file", and
            // this id's record did move: it has no line in `from` any more
            // and the line in `to` is now it. The fold is only the carry
            // arriving where a line for the id already sits, so it logs the
            // carry's event (§10.1 records every state change, and `tm log
            // --item ^id` is how §13 asks what became of one) — the note
            // below says the two records became one, which no event does.
            cx.log(Event::Move {
                id: c.key.to_string(),
                from: from.clone(),
                to: to.clone(),
            })?;
            report.notes.push(format!(
                "^{} was already a line of {to}; the copy carried from {from} was merged \
                 into it (§4.1: one line per id)",
                c.key
            ));
            continue;
        }
        cx.store
            .move_line_from(Some(from.as_str()), &c.key, &to, c.section.as_deref())?;
        in_to.insert(c.key.clone(), c.item);
        cx.log(Event::Move {
            id: c.key.to_string(),
            from: from.clone(),
            to: to.clone(),
        })?;
        report.moved.push(Moved {
            id: c.key.clone(),
            from: from.clone(),
            to: to.clone(),
        });
        if c.demoted {
            let stamps = c.item.stamps.demoted.clone();
            if stamps.len() >= 2 {
                report.notes.push(cut_note(&c.key, stamps.len()));
            }
            report.demoted.push(Demoted {
                id: c.key.clone(),
                est_min: remaining_est(cx, &c.key, c.item).unwrap_or(0),
                stamps,
            });
        }
    }

    cx.log(Event::Close {
        period: period_name(Period::Month).to_string(),
        key: month.to_string(),
    })?;
    Ok(report)
}

// ---------------------------------------------------------------------------
// auto_close (§13 "auto-run when overdue", §10.2 `state.closed`)
// ---------------------------------------------------------------------------

/// How many periods of one kind a single [`auto_close`] sweep will catch up
/// on. A tree that has not been opened for a year should not spend the first
/// command closing 365 days one at a time; the sweep closes the most recent
/// [`AUTO_CLOSE_CATCHUP`] periods that still have a file and stamps the rest
/// as closed. Sixteen of each kind is a fortnight and a bit of days, a
/// quarter of weeks and well over a year of months — wide enough for a
/// holiday, and the same bound whether or not the tree has close history,
/// because a fresh tree (no `state.json` yet) is the *commonest* way to
/// arrive with several unclosed periods behind you.
pub const AUTO_CLOSE_CATCHUP: usize = 16;

/// Run the closes that are due and have not run yet (§6.3: "runs
/// automatically on the first command after the period ends; idempotent;
/// recorded in `state.json`").
///
/// Every unclosed period of each kind is closed, oldest first — skip a week
/// and its unfinished milestones are still demoted into the month, which is
/// §0's "demotion, not deletion"; stamping a period closed without running
/// it would strand them in a file the planner no longer reads. A period
/// whose file does not exist is recorded as closed without running.
///
/// A tree with no close history at all (`state.closed` empty, which is every
/// tree between `tm init` and its first command) is caught up the same way,
/// over the last [`AUTO_CLOSE_CATCHUP`] periods of each kind: `tm init`
/// writes week and day files but no `state.json`, so treating "no history"
/// as "nothing to catch up on" would stamp the very periods the tree was
/// created in as closed without running them, and their items — never
/// demoted, never in a diagnostic, invisible to `tm plan` — could then only
/// be recovered with an explicit `tm close`. The catch-up is capped at
/// [`AUTO_CLOSE_CATCHUP`] periods per kind either way; older periods are
/// stamped, not run.
///
/// The kinds run finest-first (day, week, month) so a pinned item that lands
/// in the week can still be demoted to the month in the same sweep; the tree
/// is re-read before every close.
///
/// `state.closed` is updated and `.tm/state.json` saved whenever anything
/// ran, which is what makes the next command a no-op.
pub fn auto_close(
    store: &dyn Store,
    state: &mut RuntimeState,
    today: NaiveDate,
    now: DateTime<FixedOffset>,
    replay: Option<&Replay>,
) -> Result<Vec<ClosedPeriod>, HorizonError> {
    let mut ran: Vec<ClosedPeriod> = Vec::new();
    let mut dirty = false;

    // -- day: every unclosed day up to yesterday -----------------------------
    if let Some(last_day) = today.pred_opt() {
        let due = catch_up(state.closed.day, last_day, |d| d.pred_opt());
        for day in due {
            let week_path = Horizon::Week(IsoWeek::from_date(day)).path();
            let day_path = Horizon::Day(day).path();
            if store.exists(&day_path) || store.exists(&week_path) {
                let files = store.read_tree()?;
                let tree = files.tree();
                let mut cx = Ctx::new(store, &files, &tree, now);
                cx.replay = replay;
                let report = close_day(&cx, day)?;
                ran.push(ClosedPeriod {
                    period: Period::Day,
                    key: day.format("%Y-%m-%d").to_string(),
                    report,
                });
            }
            state.closed.day = Some(day);
            dirty = true;
        }
    }

    // -- week: every unclosed week up to the one before this ------------------
    let last_week = IsoWeek::from_date(today).prev();
    for week in catch_up(state.closed.week, last_week, |w| Some(w.prev())) {
        if store.exists(&Horizon::Week(week).path()) {
            let files = store.read_tree()?;
            let tree = files.tree();
            let cx = Ctx::new(store, &files, &tree, now);
            let report = close_week(&cx, week)?;
            ran.push(ClosedPeriod {
                period: Period::Week,
                key: week.to_string(),
                report,
            });
        }
        state.closed.week = Some(week);
        dirty = true;
    }

    // -- month: every unclosed month up to the one before this ----------------
    let last_month = YearMonth::from_date(today).prev();
    for month in catch_up(state.closed.month, last_month, |m| Some(m.prev())) {
        if store.exists(&Horizon::Month(month).path()) {
            let files = store.read_tree()?;
            let tree = files.tree();
            let cx = Ctx::new(store, &files, &tree, now);
            let report = close_month(&cx, month, &[])?;
            ran.push(ClosedPeriod {
                period: Period::Month,
                key: month.to_string(),
                report,
            });
        }
        state.closed.month = Some(month);
        dirty = true;
    }

    if dirty {
        store.save_state(state)?;
    }
    Ok(ran)
}

/// The periods still to close, oldest first: everything after `closed` up to
/// and including `last`, capped at the most recent [`AUTO_CLOSE_CATCHUP`].
///
/// `None` in `closed` is a tree with no close history — the same bounded
/// window applies, because a period that ended before a tree's first command
/// is still a period `tm` never closed (§6.3), and the file it left behind is
/// the only place its unfinished items live.
///
/// The walk runs backwards from `last` so that a `closed` in the distant past
/// costs [`AUTO_CLOSE_CATCHUP`] steps, not one per period since. Periods
/// older than the window are not returned: they are stamped closed by the
/// caller's loop as it passes the ones it does run, because `state.closed`
/// only ever moves forward. An empty result means nothing is overdue.
fn catch_up<T: Copy + Ord>(closed: Option<T>, last: T, prev: impl Fn(T) -> Option<T>) -> Vec<T> {
    if closed.is_some_and(|c| c >= last) {
        return Vec::new();
    }
    let mut out = vec![last];
    while out.len() < AUTO_CLOSE_CATCHUP {
        let Some(p) = prev(out[out.len() - 1]) else {
            break;
        };
        if closed.is_some_and(|c| c >= p) {
            break;
        }
        out.push(p);
    }
    out.reverse();
    out
}

/// The periods [`auto_close`] would close right now, without writing
/// anything — what `tm status` shows and what the CLI prints before running
/// a close.
///
/// The same catch-up window and the same "has a file" gate as [`auto_close`],
/// so a sweep that will close three skipped weeks says so instead of naming
/// only the last one.
pub fn pending_closes(store: &dyn Store, state: &RuntimeState, today: NaiveDate) -> Vec<(Period, String)> {
    let mut out = Vec::new();
    if let Some(last_day) = today.pred_opt() {
        for day in catch_up(state.closed.day, last_day, |d| d.pred_opt()) {
            if store.exists(&Horizon::Day(day).path())
                || store.exists(&Horizon::Week(IsoWeek::from_date(day)).path())
            {
                out.push((Period::Day, day.format("%Y-%m-%d").to_string()));
            }
        }
    }
    let last_week = IsoWeek::from_date(today).prev();
    for week in catch_up(state.closed.week, last_week, |w| Some(w.prev())) {
        if store.exists(&Horizon::Week(week).path()) {
            out.push((Period::Week, week.to_string()));
        }
    }
    let last_month = YearMonth::from_date(today).prev();
    for month in catch_up(state.closed.month, last_month, |m| Some(m.prev())) {
        if store.exists(&Horizon::Month(month).path()) {
            out.push((Period::Month, month.to_string()));
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Diagnostics
// ---------------------------------------------------------------------------

/// Items with at least `min` demotion stamps anywhere in the tree, most
/// stamped first — the §11 "demotion churn" monitor and the cut list
/// `/plan-month` proposes.
pub fn churn(tree: &Tree, min: usize) -> Vec<(Id, Vec<Stamp>)> {
    let mut seen: HashMap<Id, Vec<Stamp>> = HashMap::new();
    for node in tree.nodes() {
        let stamps = node.item.stamps.demoted.clone();
        if stamps.is_empty() || stamps.len() < min {
            continue;
        }
        let e = seen.entry(node.key.clone()).or_default();
        if stamps.len() > e.len() {
            *e = stamps;
        }
    }
    let mut out: Vec<(Id, Vec<Stamp>)> = seen.into_iter().collect();
    out.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then_with(|| a.0.cmp(&b.0)));
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::parse_file;

    fn cfg() -> Config {
        Config::default()
    }

    #[test]
    fn est_units_are_blocks_when_they_divide() {
        assert_eq!(est_dur(180, 60).to_string(), "3b");
        assert_eq!(est_dur(45, 60).to_string(), "45m");
        assert_eq!(est_dur(90, 60).to_string(), "1h30m");
        assert_eq!(est_dur(5, 60).to_string(), "5m");
    }

    #[test]
    fn stamps_accumulate_without_repeating() {
        let f = parse_file(
            "week/2026-W37.md",
            "- [ ] 4 6b Rollback demoted:W36 ^m2\n",
            &cfg(),
        );
        let it = f.items().next().unwrap();
        assert_eq!(
            stamp_value(&stamps_with(it, Stamp::Week(37))),
            "W36,W37".to_string()
        );
        assert_eq!(
            stamp_value(&stamps_with(it, Stamp::Week(36))),
            "W36".to_string()
        );
    }

    #[test]
    fn stamps_of_the_archive_copy_come_first_and_survive() {
        // §6.3: the copy under `# Demoted` is the history; the live line adds
        // whatever its own `demoted:` says, then this close's stamp.
        assert_eq!(
            stamp_value(&merge_stamps(
                &[Stamp::Week(35), Stamp::Week(36)],
                &[],
                Stamp::Week(37)
            )),
            "W35,W36,W37"
        );
        assert_eq!(
            stamp_value(&merge_stamps(
                &[Stamp::Week(35)],
                &[Stamp::Week(36)],
                Stamp::Week(37)
            )),
            "W35,W36,W37"
        );
        // Closing the same week twice does not write `W37,W37`.
        assert_eq!(
            stamp_value(&merge_stamps(&[Stamp::Week(37)], &[], Stamp::Week(37))),
            "W37"
        );
    }

    #[test]
    fn a_section_that_means_something_is_never_a_default_target() {
        for loaded in [
            DEMOTED_SECTION,
            PINNED_SECTION,
            OVERDUE_SECTION,
            "Log",
            "Notes",
            "series:cell-bio",
        ] {
            assert!(is_reserved_section(loaded), "{loaded}");
        }
        for neutral in ["Outcomes", "Milestones", "Tasks", "Untied", "Dated, far out"] {
            assert!(!is_reserved_section(neutral), "{neutral}");
        }
    }

    #[test]
    fn front_matter_is_added_and_replaced() {
        let text = "---\nweek: 2026-W37\nbudget: 25\n---\n# Milestones\n";
        let f = parse_file("week/2026-W37.md", text, &cfg());
        let out = with_front_matter(&f, "closed", "2026-09-14");
        assert_eq!(
            out,
            "---\nweek: 2026-W37\nbudget: 25\nclosed: 2026-09-14\n---\n# Milestones\n"
        );
        let f2 = parse_file("week/2026-W37.md", &out, &cfg());
        let out2 = with_front_matter(&f2, "closed", "2026-09-21");
        assert_eq!(
            out2,
            "---\nweek: 2026-W37\nbudget: 25\nclosed: 2026-09-21\n---\n# Milestones\n"
        );
    }

    #[test]
    fn front_matter_is_created_when_missing() {
        let f = parse_file("backlog.md", "# Untied\n- [ ] 2 30m Bike ^a1\n", &cfg());
        assert_eq!(
            with_front_matter(&f, "closed", "2026-09-14"),
            "---\nclosed: 2026-09-14\n---\n# Untied\n- [ ] 2 30m Bike ^a1\n"
        );
    }

    #[test]
    fn a_block_is_appended_below_the_last_line() {
        let f = parse_file("day/2026-09-07.md", "---\ndate: 2026-09-07\n---\n## Notes\n", &cfg());
        assert_eq!(
            with_block_at_end(&f, "review", "review pending"),
            "---\ndate: 2026-09-07\n---\n## Notes\n\n<!-- tm:review start -->\nreview pending\n<!-- tm:review end -->\n"
        );
    }

    #[test]
    fn crlf_files_keep_their_line_endings() {
        let f = parse_file("week/2026-W37.md", "---\r\nweek: 2026-W37\r\n---\r\n", &cfg());
        assert_eq!(
            with_front_matter(&f, "closed", "2026-09-14"),
            "---\r\nweek: 2026-W37\r\nclosed: 2026-09-14\r\n---\r\n"
        );
    }
}
