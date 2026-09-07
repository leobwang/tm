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
//!   front matter) and logs `move`; [`demote`]`(cx, id)` marks a week item
//!   `[-]` and copies it into `month/<current>#Demoted` with `est:` and a
//!   `demoted:W<nn>` stamp; [`readopt`]`(cx, id, to)` moves that copy back
//!   into a week (`[-]` → `[ ]`, stamps kept); [`drop_item`]`(cx, id)` sets
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
//!   `# Pinned` section becomes `[ ]` with `est:` = remaining, where
//!   remaining = the item's own estimate − the minutes the replay records
//!   for it *on that date*, floored at [`MIN_REMAINING_MIN`] (a partially
//!   done item never reads as finished). Pinned items still open then move
//!   to `week/<week of date>` with `demoted:D<dd>` appended. Nothing else
//!   moves. An existing day file gets its `<!-- tm:review start -->`
//!   placeholder at the end (`review.rs` fills it later); a day that was
//!   never planned gets no file.
//!
//!   Only the minutes logged *on that date* are subtracted, because `est:`
//!   is what earlier days already left behind: `tm stop` and a partial
//!   `tm done` write it and set the state back to `[ ]`, so a line that is
//!   still `[>]` at midnight is one whose `est:` predates today's block.
//! * **week**: every unfinished (`[ ]`/`[>]`) line of the week file becomes
//!   `[-]` *in place* — the week file is an archive from then on, and its
//!   front matter gets `closed: <date>` — and is **copied** to
//!   `month/<current>#Demoted` with `est:` = remaining and a `demoted:W<nn>`
//!   stamp appended (stamps accumulate: `W36,W37`). Unfinished children —
//!   items in the week file whose parent is also an unfinished item in the
//!   *same* week file, at any depth — are removed from the week file
//!   instead; their remaining is folded into the parent's `est:` by the §6.4
//!   rollup ([`Tree::remaining`]: a parent with its own estimate already
//!   covers its children, one without inherits their sum). Dated items past
//!   due with `on_miss = persist` move to `backlog.md#Overdue` instead of
//!   being demoted, exactly as written. Recurring items are never touched
//!   (§5.3), and neither are `[x] [-] [~] [?]` lines.
//! * **month**: unfinished outcomes and everything under `# Demoted` move to
//!   the next month file, each into the section it came from (outcomes keep
//!   their `!k`, demoted items keep their stamps); ids listed in `drops`
//!   become `[~]` and stay. Items with ≥ 2 stamps are called out in
//!   [`CloseReport::notes`] for `/plan-month`.
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
//! * **Folding children** — "their remaining is folded into the parent's
//!   `est:`" is the §6.4 rollup, not a sum on top of the parent's own
//!   estimate: a milestone written as `6b` with three 1b subtasks carries
//!   `est:6b`, because §6.4 defines its remaining that way. Only a parent
//!   with *no* estimate of its own inherits the children's sum.
//! * **What a week close never touches** — recurring lines (§5.3) and
//!   anything not `[ ]`/`[>]`. A dated interval written in a *week* file (an
//!   exam, a meeting) is demoted like any other line: the "calendar
//!   intervals" §6.3 exempts are the synced `calendar/` walls, which live in
//!   their own files and are never in a week file.
//! * **A second demotion of the same item** rewrites the one copy under
//!   `# Demoted` (accumulating stamps) instead of adding a second line, so
//!   the id never becomes a `tm check` duplicate; a stamp already on the
//!   line is not repeated.
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
use crate::tree::Tree;

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
/// The one-line body [`close_day`] leaves in the review block.
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

/// An item that was demoted (or stamped and moved down a horizon).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Demoted {
    /// The item.
    pub id: Id,
    /// The remaining estimate written as `est:` (0 when the item has none).
    pub est_min: u32,
    /// Its stamps after the close (`[W36, W37]`).
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
    /// Children removed from the week file because their parent was demoted.
    pub dropped_children: Vec<Id>,
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
    /// True when nothing at all was written apart from the `close` event.
    pub fn is_empty(&self) -> bool {
        self.moved.is_empty()
            && self.demoted.is_empty()
            && self.reopened.is_empty()
            && self.dropped_children.is_empty()
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
    /// Log replay, for the minutes [`close_day`] subtracts.
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
    let mut v = item.stamps.demoted.clone();
    if !v.contains(&add) {
        v.push(add);
    }
    v
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
    let to_path = to.path();
    // Re-open a demoted line that is moving back into a planning horizon.
    let reopen = item.state == State::Demoted && matches!(to, Horizon::Week(_) | Horizon::Day(_));
    if reopen {
        let text = rewrite(item, key, |l| l.set_state(State::Todo))?;
        cx.store.write_line_in(Some(from), key, &text)?;
    }
    cx.store.ensure_horizon_file(to)?;
    cx.store.move_line_from(Some(from), key, &to_path, section)?;
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
    demote_one(cx, &from, id, item, week, month, &mut notes)
}

/// Demote one week line: `[-]` in place, a stamped copy under the month's
/// `# Demoted`, one `demote` event.
fn demote_one(
    cx: &Ctx,
    from: &str,
    key: &Id,
    item: &Item,
    week: IsoWeek,
    month: YearMonth,
    notes: &mut Vec<String>,
) -> Result<Demoted, HorizonError> {
    let block_min = cx.block_min();
    let est = remaining_est(cx, key, item);
    let stamps = stamps_with(item, Stamp::Week(week.week));
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
    let month_path = Horizon::Month(month).path();
    notes.extend(write_demoted_copy(cx, &month_path, key, &copy)?);
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
pub fn readopt(cx: &Ctx, id: &Id, to: Option<&Horizon>) -> Result<Moved, HorizonError> {
    let current = Horizon::Week(IsoWeek::from_date(cx.today()));
    let to = to.unwrap_or(&current);
    let (from, item) = demoted_copy(cx, id)?;
    move_line(cx, &from, id, item, to, None, true)
}

/// The copy of `id` to readopt: a `# Demoted` line in a month file if there
/// is one (that is where a week close leaves it), else the line the tree
/// resolves the id to.
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
        None => locate(cx, id),
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
/// section becomes `[ ]` with `est:` = own remaining − the minutes the
/// replay records for it on `date` (floored at [`MIN_REMAINING_MIN`]);
/// pinned items still open then move to the week file with `demoted:D<dd>`
/// (recurring lines stay put, §5.3); nothing else moves. An existing day file
/// receives its review placeholder. Appends one `demote` per moved pinned
/// item and a `close{period:"day"}`.
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
        cx.store.ensure_horizon_file(&Horizon::Week(week))?;
        cx.store
            .move_line_from(Some(day_path.as_str()), key, &week_path, None)?;
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

/// Remaining minutes for a day close: the item's own estimate minus the
/// minutes logged against it *on that date*, floored at
/// [`MIN_REMAINING_MIN`]. `None` when there is no estimate to shrink.
fn day_remaining(cx: &Ctx, key: &Id, item: &Item, date: NaiveDate) -> Option<u32> {
    let base = item
        .own_remaining()
        .map(|d| d.as_minutes())
        .or_else(|| cx.tree.remaining(key))?;
    let done = cx
        .replay
        .map_or(0, |r| r.block_minutes_on(key.as_str(), date));
    Some(base.saturating_sub(done).max(MIN_REMAINING_MIN))
}

/// Put the `<!-- tm:review … -->` block in the day file: replacing its body
/// when the block is there, else appending the block at the end (below
/// `## Notes`), which is where a review belongs — [`Store::replace_generated`]
/// would otherwise create it above the generated plan.
fn write_review_placeholder(cx: &Ctx, day_path: &str) -> Result<bool, HorizonError> {
    // A day that was never planned has no file; closing it does not create
    // one (`tm close day` after a day off would otherwise leave an empty
    // day file behind).
    if !cx.store.exists(day_path) {
        return Ok(false);
    }
    cx.store.modify_file(day_path, &mut |parsed: &ParsedFile| {
        if parsed.generated(REVIEW_BLOCK).is_some() {
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
/// `month/<current>#Demoted` with `est:` = remaining and `demoted:W<nn>`;
/// unfinished children of a demoted item are removed from the week file
/// (their remaining is already in the parent's rollup); dated persist items
/// past due move to `backlog.md#Overdue` instead; recurring items and closed
/// lines are untouched. The week file's front matter gets `closed: <date>`.
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
    let open_keys: HashSet<&Id> = open.iter().map(|(k, _)| k).collect();
    let overdue: HashSet<Id> = open
        .iter()
        .filter(|(k, i)| overdue_at(cx, k, i, now))
        .map(|(k, _)| k.clone())
        .collect();
    let mut roots: Vec<(Id, &Item)> = Vec::new();
    let mut children: Vec<(Id, &Item)> = Vec::new();
    for (key, item) in &open {
        if overdue.contains(key) {
            continue;
        }
        let under_demoted_parent = cx
            .tree
            .parent(key)
            .is_some_and(|p| open_keys.contains(p) && !overdue.contains(p));
        if under_demoted_parent {
            children.push((key.clone(), item));
        } else {
            roots.push((key.clone(), item));
        }
    }

    // 1. Demote the roots: `[-]` in place, a stamped copy in the month file.
    for (key, item) in &roots {
        let demoted = demote_one(cx, &week_path, key, item, week, month, &mut report.notes)?;
        report.demoted.push(demoted);
    }
    // 2. Drop the children's lines; their remaining is in the parent's est:.
    for (key, _) in &children {
        cx.store.remove_line_in(Some(week_path.as_str()), key)?;
        report.dropped_children.push(key.clone());
    }
    // 3. Dated persist items past due go to `backlog.md#Overdue` instead.
    for (key, _) in open.iter().filter(|(k, _)| overdue.contains(k)) {
        cx.store.move_line_from(
            Some(week_path.as_str()),
            key,
            &Horizon::Backlog.path(),
            Some(OVERDUE_SECTION),
        )?;
        cx.log(Event::Move {
            id: key.to_string(),
            from: week_path.clone(),
            to: Horizon::Backlog.path(),
        })?;
        report.moved.push(Moved {
            id: key.clone(),
            from: week_path.clone(),
            to: Horizon::Backlog.path(),
        });
        report.overdue_to_backlog.push(key.clone());
    }
    // 4. The week file is an archive from now on.
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
    let drops: HashSet<&Id> = drops.iter().collect();
    let mut report = CloseReport::new(Period::Month, month.to_string());

    struct Carry<'a> {
        key: Id,
        item: &'a Item,
        section: Option<String>,
        demoted: bool,
    }
    let mut carry: Vec<Carry> = Vec::new();
    let mut to_drop: Vec<(Id, &Item)> = Vec::new();
    for item in file.items() {
        let key = Tree::key_of(item);
        if drops.contains(&key) {
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

    for (key, item) in &to_drop {
        let text = rewrite(item, key, |l| l.set_state(State::Dropped))?;
        cx.store.write_line_in(Some(from.as_str()), key, &text)?;
        cx.log(Event::Drop {
            id: key.to_string(),
        })?;
        report.dropped.push(key.clone());
    }

    if !carry.is_empty() {
        cx.store.ensure_horizon_file(&Horizon::Month(next))?;
    }
    for c in &carry {
        cx.store
            .move_line_from(Some(from.as_str()), &c.key, &to, c.section.as_deref())?;
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

/// Run the closes that are due and have not run yet (§6.3: "runs
/// automatically on the first command after the period ends; idempotent;
/// recorded in `state.json`").
///
/// Only the **last** unclosed period of each kind is closed — yesterday, the
/// week before this one, the month before this one — never a backlog of
/// them: closing a two-week-old week after this week's has been planned
/// would demote lines that were readopted long ago, and the file it would
/// write into is not the current one any more. A period whose file does not
/// exist is recorded as closed without running. The three run finest-first
/// (day, week, month) so a pinned item that lands in the week can still be
/// demoted to the month in the same sweep; the tree is re-read between them.
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

    // -- day: yesterday ------------------------------------------------------
    if let Some(day) = today.pred_opt() {
        if state.closed.day.is_none_or(|d| d < day) {
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

    // -- week: the week before this one --------------------------------------
    let last_week = IsoWeek::from_date(today).prev();
    if state.closed.week.is_none_or(|w| w < last_week) {
        if store.exists(&Horizon::Week(last_week).path()) {
            let files = store.read_tree()?;
            let tree = files.tree();
            let cx = Ctx::new(store, &files, &tree, now);
            let report = close_week(&cx, last_week)?;
            ran.push(ClosedPeriod {
                period: Period::Week,
                key: last_week.to_string(),
                report,
            });
        }
        state.closed.week = Some(last_week);
        dirty = true;
    }

    // -- month: the month before this one ------------------------------------
    let last_month = YearMonth::from_date(today).prev();
    if state.closed.month.is_none_or(|m| m < last_month) {
        if store.exists(&Horizon::Month(last_month).path()) {
            let files = store.read_tree()?;
            let tree = files.tree();
            let cx = Ctx::new(store, &files, &tree, now);
            let report = close_month(&cx, last_month, &[])?;
            ran.push(ClosedPeriod {
                period: Period::Month,
                key: last_month.to_string(),
                report,
            });
        }
        state.closed.month = Some(last_month);
        dirty = true;
    }

    if dirty {
        store.save_state(state)?;
    }
    Ok(ran)
}

/// The periods [`auto_close`] would close right now, without writing
/// anything — what `tm status` shows and what the CLI prints before running
/// a close.
pub fn pending_closes(store: &dyn Store, state: &RuntimeState, today: NaiveDate) -> Vec<(Period, String)> {
    let mut out = Vec::new();
    if let Some(day) = today.pred_opt() {
        if state.closed.day.is_none_or(|d| d < day)
            && (store.exists(&Horizon::Day(day).path())
                || store.exists(&Horizon::Week(IsoWeek::from_date(day)).path()))
        {
            out.push((Period::Day, day.format("%Y-%m-%d").to_string()));
        }
    }
    let last_week = IsoWeek::from_date(today).prev();
    if state.closed.week.is_none_or(|w| w < last_week)
        && store.exists(&Horizon::Week(last_week).path())
    {
        out.push((Period::Week, last_week.to_string()));
    }
    let last_month = YearMonth::from_date(today).prev();
    if state.closed.month.is_none_or(|m| m < last_month)
        && store.exists(&Horizon::Month(last_month).path())
    {
        out.push((Period::Month, last_month.to_string()));
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
