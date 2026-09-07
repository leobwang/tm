//! Recurrence — instances of recurring items over a date range (§5).
//!
//! # API overview
//!
//! Everything here is pure: `today`, `now` and the log [`Replay`] are
//! injected, nothing reads a clock and nothing does I/O.
//!
//! * [`instances`] — the occurrences of one item inside an inclusive date
//!   range, with their window, due point and [`InstanceStatus`]. It covers all
//!   four recurrence kinds plus one-off `win:` items:
//!   * `every:` ([`Recur::Calendar`]) → one instance per matching date,
//!     keyed [`InstanceKey::Date`];
//!   * `after-done:` ([`Recur::AfterDone`]) → the logged completions plus
//!     exactly one pending instance, keyed [`InstanceKey::Nth`];
//!   * `on-event:` ([`Recur::OnEvent`]) → the logged completions plus one
//!     pending instance while the item is not `[?]` waiting;
//!   * [`Recur::None`] with an absolute `win:`+`dur:` → the single instance
//!     that window describes (this is what makes "Pick up package" a
//!     mandatory window instance on its last day, §5.2).
//! * [`instances_with_info`], [`instance_info`], [`InstanceInfo`] — the
//!   planner-facing flags (mandatory, last chance, overdue, carried,
//!   deferred, not yet open, minutes to place). [`Instance`] itself is
//!   `model.rs`'s and gains nothing.
//! * [`is_mandatory`] — §5.2's "placed before any task" test.
//! * [`today_instances`] / [`week_instances`] — the day planner's step 2 input
//!   and the Necessities grid.
//! * [`after_done_state`] / [`AfterDoneState`] — last completion, due,
//!   validity end and whether the last chance was missed.
//! * [`waiting_state`] / [`WaitingState`], [`event_resolves`] — the `[?]`
//!   ledger for the Necessities screen and `tm event <name>`.
//! * [`on_done_waiting`], [`on_event_arrived`], [`Edits`], [`Edit`] — the line
//!   edits the CLI applies through [`ItemLine`] when a wait starts or ends.
//! * [`skip_instance`], [`done_instance`] — the [`LogEntry`] to append for
//!   `tm skip <routine>` / `tm routine done <name>`; no I/O happens here.
//!
//! ## Conventions this module fixes
//!
//! * **Instance identity.** Items without a `^id` (routines, optional) are
//!   keyed by their title, exactly as [`Tree::key_of`] does, so a log line
//!   `{"ev":"routine","item":"lunch","inst":"2026-09-07"}` matches. The `inst`
//!   string is [`InstanceKey`]'s `Display`: `2026-09-07` for a calendar
//!   instance, `#6` for the sixth after-done/on-event occurrence.
//! * **Status.** A logged status always wins (`done`, `skipped`, `missed`,
//!   `expired`). Otherwise an instance is `Pending` while its window has not
//!   closed (`close.date() >= today`, so an overnight window is still pending
//!   on the morning it ends), and once it has closed §5.3 applies: `expire` →
//!   `Expired`, `persist` → `Pending` (carried, overdue), `next` → `Skipped`.
//!   [`InstanceStatus::Missed`] therefore only ever comes from the log.
//! * **Span.** An instance's `window` is the whole stretch it may be placed
//!   in: a daily window on its date (an overnight `win:22:00-08:00` runs into
//!   the next morning), the absolute window as written, the whole week for
//!   `every:week`, and `due..valid_until` for `after-done:2d~1d`. `due` is the
//!   end of the *on-time* chance: the window end on the instance's own date.
//! * **Anchors.** `every:Nd` is anchored at the item's earliest known
//!   completion (from the log) and falls back to the range start; the phase
//!   extends in both directions from the anchor. `every:Nw:<wd>` is anchored
//!   on ISO week number: a week counts when `(iso_week − 1) % N == 0`, so
//!   `every:2w:Sun` is the Sunday of every odd ISO week. `every:month:D`
//!   clamps `D` to the length of the month. `every:week` / `every:Nw` (no
//!   weekday) yields one instance per qualifying ISO week, keyed by its
//!   Monday and placeable on any day of that week.
//! * **Ordinals.** `Nth(n)` counts distinct completion *dates* in the log, so
//!   the next after-done instance after five showers is `#6`.
//! * **Time.** Instance windows and dues are wall-clock `Naive*` values in
//!   `cfg.tz`, exactly as the line writes them. The only instants are log
//!   timestamps: they are converted with `cfg.tz` into `DateTime<Tz>` before
//!   any date arithmetic, and a whole-day offset advances calendar days, so a
//!   DST change never moves a due date.
//! * **Closed items.** A `[x]`/`[-]` item has no pending ordinal instance
//!   (its logged ones still show), and [`today_instances`] /
//!   [`week_instances`] skip it entirely.
//! * **Mandatory** (§5.2, exact rule): the instance is still actionable, the
//!   item is a `win:` item, and its span closes today or earlier
//!   (`close.date() <= today`) — that covers a persisted instance carried
//!   from a previous day, which §5.3 also calls mandatory. With
//!   `on_miss = expire` the chance is gone once `now` passes the close, so a
//!   closed expire window is no longer mandatory. Only `expire` gets that
//!   veto: §5.2 says "on_miss ≠ expire" for the first arm, so an
//!   `on-miss:next` instance is mandatory on its closing day too.
//!
//! ## Deviations from the scope
//!
//! 1. `instances`, `after_done_state` and `waiting_state` take `today` (and
//!    `cfg`, for `cfg.tz`) as parameters: statuses are relative to today and
//!    log timestamps are `DateTime<FixedOffset>` that only `cfg.tz` can turn
//!    into local dates. `today_instances`/`week_instances`/`is_mandatory` also
//!    take `now` for the expire veto above.
//! 2. `after_done_state` returns `Option` (`None` when the item is not an
//!    `after-done:` item) instead of an unconditional value.
//! 3. The extra-flags struct is called [`InstanceInfo`] (the name the planner
//!    scope uses) rather than `InstanceExt`.
//! 4. [`WaitingState`] carries a fifth field, `arrived`: the `tm event` that
//!    already resolved the wait, if the log has one. The Necessities screen
//!    needs to tell "still waiting" from "arrived, flip the line".
//! 5. [`done_instance`] is added next to [`skip_instance`]; `tm routine done`
//!    needs the symmetric constructor and it is three lines.

use chrono::{DateTime, Datelike, Duration, FixedOffset, NaiveDate, NaiveDateTime, NaiveTime};
use serde::{Deserialize, Serialize};

use crate::config::Config;
use crate::grammar::{EditError, ItemLine};
use crate::log::{Event, LogEntry, Replay};
use crate::model::{
    Dep, Dur, Id, Instance, InstanceKey, InstanceStatus, IsoWeek, Item, Moment, OnMiss, Recur,
    Rule, Shape, State, WindowRange,
};
use crate::tree::Tree;

/// An inclusive date range, `(from, to)`.
pub type DateRange = (NaiveDate, NaiveDate);

/// How far back [`today_instances`] looks for a `persist` instance that is
/// still pending. Older misses are noise, not work.
pub const CARRY_LOOKBACK_DAYS: i64 = 60;

// ---------------------------------------------------------------------------
// Extra per-instance information
// ---------------------------------------------------------------------------

/// The planner-facing flags of one [`Instance`] (§5.2, §5.3, §8.2 step 2).
///
/// [`Instance`] is `model.rs`'s type and stays as the spec defines it; this
/// travels beside it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct InstanceInfo {
    /// §5.2: place it before any task.
    pub mandatory: bool,
    /// Today is the last day it can be done at all.
    pub last_chance: bool,
    /// Its due point is already past (it was carried into today).
    pub overdue: bool,
    /// The date it was originally due, when `overdue`.
    pub carried_from: Option<NaiveDate>,
    /// Its window opened before today and it is still pending.
    pub deferred_from_yesterday: bool,
    /// Its window has not opened yet at `now`.
    pub not_yet: bool,
    /// Minutes to place (`dur:`), when the item says.
    pub dur_min: Option<u32>,
}

/// State of an `after-done:` item (§5.1, §5.3).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AfterDoneState {
    /// The last completion, as logged.
    pub last_done: Option<DateTime<FixedOffset>>,
    /// The last completion's local date (`cfg.tz`).
    pub last_done_date: Option<NaiveDate>,
    /// Completions so far (distinct completion dates in the log).
    pub count: u32,
    /// The date the next instance is due.
    pub due: NaiveDate,
    /// The moment the on-time chance ends (window close on `due`).
    pub due_at: NaiveDateTime,
    /// The last date it is still valid (`~window`), when there is one.
    pub valid_until: Option<NaiveDate>,
    /// The moment validity ends.
    pub valid_until_at: Option<NaiveDateTime>,
    /// The previous chance was missed (`today > valid_until`), so this
    /// instance is due immediately (§5.3).
    pub missed: bool,
}

/// State of a `[?]` waiting item (§5.1, §11 "Waiting").
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaitingState {
    /// `waiting:<date>` as written.
    pub since: Option<NaiveDate>,
    /// Days waited so far (0 when `since` is missing or in the future).
    pub days_waiting: i64,
    /// The date the `on-event:` timeout elapses, when there is one.
    pub timeout_at: Option<NaiveDate>,
    /// `today` is past `timeout_at`: the wait ends by timeout (§5.1).
    pub expired: bool,
    /// The `tm event` that already resolved this wait, if the log has one.
    pub arrived: Option<DateTime<FixedOffset>>,
}

// ---------------------------------------------------------------------------
// Instances
// ---------------------------------------------------------------------------

/// The occurrences of `item` whose span intersects `range` (inclusive), with
/// their status at `today` (§5.1).
///
/// Non-recurring items yield nothing, except an absolute `win:`+`dur:` item,
/// which yields the single instance its window describes. See the module docs
/// for the anchor, span and status rules.
///
/// The single pending `after-done:` / `on-event:` instance is included
/// whenever its due date is not after the range end (it stays pending, so a
/// range that starts after it was due still sees it).
pub fn instances(
    item: &Item,
    range: DateRange,
    today: NaiveDate,
    replay: &Replay,
    cfg: &Config,
) -> Vec<Instance> {
    if range.1 < range.0 {
        return Vec::new();
    }
    let key = Tree::key_of(item);
    match &item.recur {
        Recur::Calendar(rule) => calendar_instances(item, &key, rule, range, today, replay),
        Recur::AfterDone { .. } => after_done_instances(item, &key, range, today, replay, cfg),
        Recur::OnEvent { .. } => on_event_instances(item, &key, range, today, replay, cfg),
        Recur::None => one_off_instances(item, &key, range, today, replay),
    }
}

/// [`instances`] with each instance's [`InstanceInfo`].
pub fn instances_with_info(
    item: &Item,
    range: DateRange,
    today: NaiveDate,
    now: NaiveDateTime,
    replay: &Replay,
    cfg: &Config,
) -> Vec<(Instance, InstanceInfo)> {
    instances(item, range, today, replay, cfg)
        .into_iter()
        .map(|i| {
            let info = instance_info(item, &i, today, now);
            (i, info)
        })
        .collect()
}

/// The flags of one instance (§5.2, §5.3).
pub fn instance_info(
    item: &Item,
    inst: &Instance,
    today: NaiveDate,
    now: NaiveDateTime,
) -> InstanceInfo {
    let actionable = is_actionable(inst.status);
    let close = close_of(inst);
    let start = start_of(inst);
    let due = inst.due.or(close);
    let overdue = actionable && due.is_some_and(|d| d.date() < today);
    InstanceInfo {
        mandatory: is_mandatory(item, inst, today, now),
        last_chance: actionable
            && item.on_miss != OnMiss::Persist
            && has_closing_deadline(item)
            && close.is_some_and(|c| c.date() == today),
        overdue,
        carried_from: if overdue { due.map(|d| d.date()) } else { None },
        deferred_from_yesterday: actionable && start.is_some_and(|s| s.date() < today),
        not_yet: start.is_some_and(|s| s > now),
        dur_min: place_minutes(item),
    }
}

/// §5.2: is this window instance placed before any task?
///
/// True when the instance is still actionable, the item is a `win:` item and
/// its span closes today or earlier (`close.date() <= today`), with two
/// qualifications:
///
/// * under `on-miss:persist` a closed span is *still* mandatory — that is the
///   carried laundry of §5.3;
/// * otherwise the chance has to be left: an `expire` or `next` instance whose
///   window `now` has already passed is over, not mandatory, and an
///   `after-done:` item with no `~validity` has no closing deadline at all, so
///   it is never a last chance.
pub fn is_mandatory(item: &Item, inst: &Instance, today: NaiveDate, now: NaiveDateTime) -> bool {
    if !is_actionable(inst.status) || !matches!(item.shape, Shape::Window { .. }) {
        return false;
    }
    let Some(close) = close_of(inst) else {
        return false;
    };
    if close.date() > today {
        return false;
    }
    if item.on_miss == OnMiss::Persist {
        return true;
    }
    has_closing_deadline(item) && now < close
}

/// Every instance of `items` that can be worked on today, with its flags —
/// the planner's step 2 input (§8.2).
///
/// An instance qualifies when it is still actionable, its window has opened
/// by the end of today, and there is still a chance left: a window that `now`
/// has already passed only stays under `on-miss:persist`. Instances carried
/// from an earlier day are collapsed to the most recent one per item; a wholly
/// future occurrence is left out. Items in a closed state are skipped.
pub fn today_instances<'a, I>(
    items: I,
    today: NaiveDate,
    now: NaiveDateTime,
    replay: &Replay,
    cfg: &Config,
) -> Vec<(Instance, InstanceInfo)>
where
    I: IntoIterator<Item = &'a Item>,
{
    let from = today
        .checked_sub_signed(Duration::days(CARRY_LOOKBACK_DAYS))
        .unwrap_or(today);
    let mut out = Vec::new();
    for item in items {
        if item.state.is_closed() {
            continue;
        }
        let mine: Vec<(Instance, InstanceInfo)> =
            instances_with_info(item, (from, today), today, now, replay, cfg)
                .into_iter()
                .filter(|(i, _)| {
                    is_actionable(i.status)
                        && start_of(i).is_none_or(|s| s.date() <= today)
                        && (item.on_miss == OnMiss::Persist
                            || close_of(i).is_none_or(|c| c >= now))
                })
                .collect();
        let (carried, current): (Vec<_>, Vec<_>) = mine
            .into_iter()
            .partition(|(i, _)| close_of(i).is_some_and(|c| c.date() < today));
        out.extend(carried.into_iter().max_by_key(|(i, _)| close_of(i)));
        out.extend(current);
    }
    out
}

/// Every instance of `items` inside one ISO week, with its flags — the
/// Necessities screen's 7-column grid (§12.3).
pub fn week_instances<'a, I>(
    items: I,
    week: IsoWeek,
    today: NaiveDate,
    now: NaiveDateTime,
    replay: &Replay,
    cfg: &Config,
) -> Vec<(Instance, InstanceInfo)>
where
    I: IntoIterator<Item = &'a Item>,
{
    let range = week.range();
    items
        .into_iter()
        .filter(|i| !i.state.is_closed())
        .flat_map(|item| instances_with_info(item, range, today, now, replay, cfg))
        .collect()
}

// ---------------------------------------------------------------------------
// After-done
// ---------------------------------------------------------------------------

/// Where an `after-done:` item stands (§5.1, §5.3), or `None` when the item
/// does not recur on completion.
///
/// Before the first completion the instance is due today. After a miss
/// (`today > valid_until`) with `on_miss ≠ persist` the next instance is due
/// immediately — today — and keeps the same ordinal; under `persist` the
/// original due point stands and the instance simply runs overdue.
pub fn after_done_state(
    item: &Item,
    replay: &Replay,
    today: NaiveDate,
    cfg: &Config,
) -> Option<AfterDoneState> {
    let Recur::AfterDone { offset, window } = &item.recur else {
        return None;
    };
    let key = Tree::key_of(item);
    let last = replay.last_done(key.as_str());
    let last_local = last.map(|t| t.with_timezone(&cfg.tz));
    let last_done_date = last_local.map(|t| t.date_naive());
    let count = replay.done_dates(key.as_str()).len() as u32;

    let base_due = match last_local {
        Some(t) => {
            let min = i64::from(offset.as_minutes());
            if min % 1440 == 0 {
                add_days(t.date_naive(), min / 1440)
            } else {
                (t + Duration::minutes(min)).date_naive()
            }
        }
        None => today,
    };
    let base_valid = window.map(|w| add_days(base_due, whole_days(w)));
    let missed = base_valid.is_some_and(|v| today > v);
    let (due, valid_until) = if missed && item.on_miss != OnMiss::Persist {
        (today, window.map(|w| add_days(today, whole_days(w))))
    } else {
        (base_due, base_valid)
    };
    Some(AfterDoneState {
        last_done: last,
        last_done_date,
        count,
        due,
        due_at: close_on(item, due),
        valid_until,
        valid_until_at: valid_until.map(|d| close_on(item, d)),
        missed,
    })
}

// ---------------------------------------------------------------------------
// On-event and waiting
// ---------------------------------------------------------------------------

/// Where a `[?]` waiting item stands, or `None` when it is not waiting.
///
/// `expired` is the §5.1 timeout: it becomes true the day *after* the timeout
/// date (`waiting:2026-09-05` + `7d` → expired from 2026-09-13).
pub fn waiting_state(
    item: &Item,
    replay: &Replay,
    today: NaiveDate,
    cfg: &Config,
) -> Option<WaitingState> {
    if item.state != State::Waiting {
        return None;
    }
    let since = item.stamps.waiting_since;
    let timeout = match &item.recur {
        Recur::OnEvent { timeout, .. } => *timeout,
        _ => None,
    };
    let timeout_at = match (since, timeout) {
        (Some(s), Some(t)) => Some(add_days(s, whole_days(t))),
        _ => None,
    };
    Some(WaitingState {
        since,
        days_waiting: since.map_or(0, |s| (today - s).num_days().max(0)),
        timeout_at,
        expired: timeout_at.is_some_and(|t| today > t),
        arrived: arrival_of(item, replay, cfg),
    })
}

/// True when `tm event <name>` resolves this item: it recurs on that event
/// (§5.1) or depends on it (`after:event:<name>`, §5.5).
pub fn event_resolves(item: &Item, name: &str) -> bool {
    matches!(&item.recur, Recur::OnEvent { name: n, .. } if n == name)
        || item
            .after
            .iter()
            .any(|d| matches!(d, Dep::Event(n) if n == name))
}

// ---------------------------------------------------------------------------
// Line edits (applied by the CLI through `ItemLine`)
// ---------------------------------------------------------------------------

/// One change to an item line.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Edit {
    /// Set the checkbox state.
    State(State),
    /// Set `key:value` (replacing the token in place when it exists).
    Set {
        /// Token key.
        key: String,
        /// Token value.
        value: String,
    },
    /// Remove `key:` if present.
    Unset {
        /// Token key.
        key: String,
    },
}

/// A small ordered list of [`Edit`]s: what the CLI writes back through
/// [`ItemLine`] (byte-faithfully) for a state transition.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Edits {
    /// The edits, in the order they must be applied.
    pub edits: Vec<Edit>,
}

impl Edits {
    /// No edit needed.
    pub fn is_empty(&self) -> bool {
        self.edits.is_empty()
    }
    /// How many edits.
    pub fn len(&self) -> usize {
        self.edits.len()
    }
    /// Iterate the edits.
    pub fn iter(&self) -> impl Iterator<Item = &Edit> {
        self.edits.iter()
    }
    /// Apply them to a parsed line. The line keeps every other token exactly
    /// as written.
    pub fn apply(&self, line: &mut ItemLine) -> Result<(), EditError> {
        for e in &self.edits {
            match e {
                Edit::State(s) => line.set_state(*s)?,
                Edit::Set { key, value } => line.set_token(key, value),
                Edit::Unset { key } => {
                    line.remove_token(key)?;
                }
            }
        }
        Ok(())
    }
}

/// §5.1: an `on-event:` item was done, so the wait starts — state `[?]` plus
/// `waiting:<today>`. Empty for an item that does not wait on an event.
pub fn on_done_waiting(item: &Item, today: NaiveDate) -> Edits {
    if !matches!(item.recur, Recur::OnEvent { .. }) {
        return Edits::default();
    }
    Edits {
        edits: vec![
            Edit::State(State::Waiting),
            Edit::Set {
                key: "waiting".to_string(),
                value: today.format("%Y-%m-%d").to_string(),
            },
        ],
    }
}

/// §5.1: the event arrived (or the timeout elapsed) — state `[ ]`, the
/// remaining estimate reset to the estimate as written, `waiting:` removed.
pub fn on_event_arrived(item: &Item) -> Edits {
    let mut edits = vec![Edit::State(State::Todo)];
    if item.est.is_some() {
        edits.push(Edit::Unset {
            key: "est".to_string(),
        });
    }
    if item.stamps.waiting_since.is_some() {
        edits.push(Edit::Unset {
            key: "waiting".to_string(),
        });
    }
    Edits { edits }
}

// ---------------------------------------------------------------------------
// Log entries
// ---------------------------------------------------------------------------

/// The `skip` entry `tm skip <routine>` appends for this instance (§10.1).
/// Appending it is the caller's job.
pub fn skip_instance(item: &Item, inst: &Instance, now: DateTime<FixedOffset>) -> LogEntry {
    LogEntry::new(
        now,
        Event::Skip {
            item: Tree::key_of(item).to_string(),
            inst: inst.key.to_string(),
        },
    )
}

/// The `routine … status:"done"` entry `tm routine done <name>` appends.
pub fn done_instance(
    item: &Item,
    inst: &Instance,
    now: DateTime<FixedOffset>,
    actual_min: Option<u32>,
) -> LogEntry {
    LogEntry::new(
        now,
        Event::Routine {
            item: Tree::key_of(item).to_string(),
            inst: inst.key.to_string(),
            status: "done".to_string(),
            actual_min,
        },
    )
}

// ---------------------------------------------------------------------------
// Instance construction, per recurrence kind
// ---------------------------------------------------------------------------

fn calendar_instances(
    item: &Item,
    key: &Id,
    rule: &Rule,
    range: DateRange,
    today: NaiveDate,
    replay: &Replay,
) -> Vec<Instance> {
    let anchor = replay
        .done_dates(key.as_str())
        .first()
        .copied()
        .unwrap_or(range.0);
    rule_occurrences(rule, range, anchor)
        .into_iter()
        .map(|(first, last)| {
            let (window, due) = span(item, first, last);
            let k = InstanceKey::Date(first);
            let close = window.map_or(due, |w| w.1);
            let status = status_of(item, key, &k, close, today, replay);
            Instance {
                item: key.clone(),
                key: k,
                due: Some(due),
                window,
                status,
            }
        })
        .collect()
}

fn after_done_instances(
    item: &Item,
    key: &Id,
    range: DateRange,
    today: NaiveDate,
    replay: &Replay,
    cfg: &Config,
) -> Vec<Instance> {
    let Some(st) = after_done_state(item, replay, today, cfg) else {
        return Vec::new();
    };
    let pending = InstanceKey::Nth(st.count + 1);
    let mut out = logged_instances(key, range, replay, cfg, Some(pending));
    if st.due <= range.1 && !item.state.is_closed() {
        // With a `~validity` the span ends there; without one the instance
        // never expires, so its span keeps stretching to today's window —
        // which is where the planner can still place it.
        let end = st.valid_until.unwrap_or_else(|| st.due.max(today));
        let window = match &item.shape {
            Shape::Window { range: wr, .. } => {
                Some((window_on(wr, st.due).0, window_on(wr, end).1))
            }
            _ => None,
        };
        out.push(Instance {
            item: key.clone(),
            key: pending,
            due: Some(st.due_at),
            window,
            status: logged_status(key, &pending, replay).unwrap_or(InstanceStatus::Pending),
        });
    }
    out
}

fn on_event_instances(
    item: &Item,
    key: &Id,
    range: DateRange,
    today: NaiveDate,
    replay: &Replay,
    cfg: &Config,
) -> Vec<Instance> {
    let mut out = Vec::new();
    let count = replay.done_dates(key.as_str()).len() as u32;
    let pending = InstanceKey::Nth(count + 1);
    out.extend(logged_instances(key, range, replay, cfg, Some(pending)));
    // While the item waits, no instance is pending: the wait ends when the
    // event arrives or the timeout elapses (§5.1).
    let waiting = waiting_state(item, replay, today, cfg);
    let blocked = waiting.is_some_and(|w| !w.expired && w.arrived.is_none());
    if !blocked && today <= range.1 && !item.state.is_closed() {
        let (window, due) = span(item, today, today);
        out.push(Instance {
            item: key.clone(),
            key: pending,
            due: match item.shape {
                Shape::None => None,
                _ => Some(due),
            },
            window,
            status: logged_status(key, &pending, replay).unwrap_or(InstanceStatus::Pending),
        });
    }
    out
}

fn one_off_instances(
    item: &Item,
    key: &Id,
    range: DateRange,
    today: NaiveDate,
    replay: &Replay,
) -> Vec<Instance> {
    let Shape::Window {
        range: WindowRange::Absolute { from, to },
        ..
    } = &item.shape
    else {
        return Vec::new();
    };
    if to.date() < range.0 || from.date() > range.1 {
        return Vec::new();
    }
    let k = InstanceKey::Date(from.date());
    let mut status = status_of(item, key, &k, *to, today, replay);
    if status == InstanceStatus::Pending {
        if item.state == State::Done || replay.is_done(key.as_str()) {
            status = InstanceStatus::Done;
        } else if item.state == State::Dropped {
            status = InstanceStatus::Skipped;
        }
    }
    vec![Instance {
        item: key.clone(),
        key: k,
        due: Some(*to),
        window: Some((*from, *to)),
        status,
    }]
}

/// The instances the log knows about, for the ordinal-keyed recurrences.
/// Their window is not reconstructed — only the log says they happened.
fn logged_instances(
    key: &Id,
    range: DateRange,
    replay: &Replay,
    cfg: &Config,
    skip: Option<InstanceKey>,
) -> Vec<Instance> {
    let mut out: Vec<Instance> = replay
        .instances_of(key.as_str())
        .filter_map(|(inst, rec)| {
            let k = parse_instance_key(inst)?;
            if Some(k) == skip {
                return None;
            }
            let date = match k {
                InstanceKey::Date(d) => d,
                InstanceKey::Nth(_) => rec.t.with_timezone(&cfg.tz).date_naive(),
            };
            (date >= range.0 && date <= range.1).then(|| Instance {
                item: key.clone(),
                key: k,
                due: None,
                window: None,
                status: rec.status,
            })
        })
        .collect();
    out.sort_by_key(|i| i.key);
    out
}

// ---------------------------------------------------------------------------
// Calendar rules
// ---------------------------------------------------------------------------

/// The occurrences of `rule` whose span intersects `range`, as
/// `(first day, last day)` — the two differ only for `every:week` /
/// `every:Nw`, which spans a whole ISO week.
fn rule_occurrences(rule: &Rule, range: DateRange, anchor: NaiveDate) -> Vec<(NaiveDate, NaiveDate)> {
    let (from, to) = range;
    let mut out = Vec::new();
    match rule {
        Rule::Daily => each_day(range, &mut out, |_| true),
        Rule::Weekdays => each_day(range, &mut out, |d| {
            d.weekday().num_days_from_monday() < 5
        }),
        Rule::Weekly(days) => each_day(range, &mut out, |d| days.contains(&d.weekday())),
        Rule::EveryNDays(n) => {
            let n = i64::from((*n).max(1));
            each_day(range, &mut out, |d| (d - anchor).num_days().rem_euclid(n) == 0);
        }
        Rule::EveryNWeeks(n, wd) => {
            let n = (*n).max(1);
            each_day(range, &mut out, |d| {
                d.weekday() == *wd && (d.iso_week().week() - 1).is_multiple_of(n)
            });
        }
        Rule::Monthly(day) => {
            let (mut y, mut m) = (from.year(), from.month());
            loop {
                let dom = u32::from(*day).clamp(1, month_len(y, m));
                if let Some(d) = NaiveDate::from_ymd_opt(y, m, dom) {
                    if d >= from && d <= to {
                        out.push((d, d));
                    }
                }
                if (y, m) >= (to.year(), to.month()) {
                    break;
                }
                if m == 12 {
                    y += 1;
                    m = 1;
                } else {
                    m += 1;
                }
            }
        }
        Rule::Weeks(n) => {
            let n = (*n).max(1);
            let mut monday = add_days(from, -i64::from(from.weekday().num_days_from_monday()));
            while monday <= to {
                let sunday = add_days(monday, 6);
                if sunday >= from && (monday.iso_week().week() - 1).is_multiple_of(n) {
                    out.push((monday, sunday));
                }
                let next = add_days(monday, 7);
                if next == monday {
                    break;
                }
                monday = next;
            }
        }
    }
    out
}

fn each_day(range: DateRange, out: &mut Vec<(NaiveDate, NaiveDate)>, mut f: impl FnMut(NaiveDate) -> bool) {
    let mut d = range.0;
    while d <= range.1 {
        if f(d) {
            out.push((d, d));
        }
        match d.checked_add_signed(Duration::days(1)) {
            Some(next) => d = next,
            None => break,
        }
    }
}

fn month_len(year: i32, month: u32) -> u32 {
    let (ny, nm) = if month == 12 {
        (year + 1, 1)
    } else {
        (year, month + 1)
    };
    match (
        NaiveDate::from_ymd_opt(year, month, 1),
        NaiveDate::from_ymd_opt(ny, nm, 1),
    ) {
        (Some(a), Some(b)) => u32::try_from(b.signed_duration_since(a).num_days()).unwrap_or(28),
        _ => 28,
    }
}

// ---------------------------------------------------------------------------
// Windows, spans and statuses
// ---------------------------------------------------------------------------

/// The window on one date. An overnight daily window (`22:00-08:00`) runs
/// into the next day.
fn window_on(range: &WindowRange, date: NaiveDate) -> (NaiveDateTime, NaiveDateTime) {
    match range {
        WindowRange::Daily { from, to } => {
            let start = date.and_time(*from);
            let end = if to <= from {
                add_days(date, 1).and_time(*to)
            } else {
                date.and_time(*to)
            };
            (start, end)
        }
        WindowRange::Absolute { from, to } => (*from, *to),
    }
}

/// The `(window, due)` of an occurrence running from `first` to `last`
/// (the same date for every rule but `every:week`).
fn span(item: &Item, first: NaiveDate, last: NaiveDate) -> (Option<(NaiveDateTime, NaiveDateTime)>, NaiveDateTime) {
    match &item.shape {
        Shape::Window { range, .. } => {
            let start = window_on(range, first).0;
            let end = window_on(range, last).1;
            (Some((start, end)), end)
        }
        Shape::Interval { start, end } => {
            let s = first.and_time(start.time());
            let e = s + (*end - *start);
            (Some((s, e)), e)
        }
        Shape::Point { .. } | Shape::None => (None, close_on(item, last)),
    }
}

/// When the chance to do this item on `date` ends.
fn close_on(item: &Item, date: NaiveDate) -> NaiveDateTime {
    match &item.shape {
        Shape::Window { range, .. } => window_on(range, date).1,
        Shape::Point {
            due: Moment::DateTime(dt),
        } => date.and_time(dt.time()),
        Shape::Interval { start, end } => date.and_time(start.time()) + (*end - *start),
        _ => end_of_day(date),
    }
}

/// The logged status of an instance, if the log has one that is not the
/// default `pending`.
fn logged_status(key: &Id, k: &InstanceKey, replay: &Replay) -> Option<InstanceStatus> {
    replay
        .instance(key.as_str(), &k.to_string())
        .map(|r| r.status)
        .filter(|s| *s != InstanceStatus::Pending)
}

/// The log's status, else §5.3's derivation from `close` and `on_miss`.
fn status_of(
    item: &Item,
    key: &Id,
    k: &InstanceKey,
    close: NaiveDateTime,
    today: NaiveDate,
    replay: &Replay,
) -> InstanceStatus {
    if let Some(s) = logged_status(key, k, replay) {
        return s;
    }
    if close.date() >= today {
        return InstanceStatus::Pending;
    }
    match item.on_miss {
        OnMiss::Expire => InstanceStatus::Expired,
        OnMiss::Persist => InstanceStatus::Pending,
        OnMiss::Next => InstanceStatus::Skipped,
    }
}

/// False only for an `after-done:` item with no `~validity`: its instance
/// stays pending for ever, so no day is its last chance.
fn has_closing_deadline(item: &Item) -> bool {
    !matches!(item.recur, Recur::AfterDone { window: None, .. })
}

fn is_actionable(status: InstanceStatus) -> bool {
    matches!(status, InstanceStatus::Pending | InstanceStatus::Missed)
}

fn close_of(inst: &Instance) -> Option<NaiveDateTime> {
    inst.window.map(|w| w.1).or(inst.due)
}

fn start_of(inst: &Instance) -> Option<NaiveDateTime> {
    inst.window.map(|w| w.0).or(inst.due)
}

/// The minutes an instance takes: `dur:` inside the window, else the line's
/// own `dur:`.
fn place_minutes(item: &Item) -> Option<u32> {
    match &item.shape {
        Shape::Window { dur, .. } => Some(dur.as_minutes()),
        _ => item.dur.map(|d| d.as_minutes()),
    }
}

/// The `tm event` that resolved this item's wait, if any: the latest event of
/// the item's `on-event:` name, addressed to it or to nobody, on or after the
/// day the wait started.
fn arrival_of(item: &Item, replay: &Replay, cfg: &Config) -> Option<DateTime<FixedOffset>> {
    let Recur::OnEvent { name, .. } = &item.recur else {
        return None;
    };
    let key = Tree::key_of(item);
    let since = item.stamps.waiting_since;
    replay
        .events_named(name)
        .iter()
        .filter(|e| e.id.is_none() || e.id.as_deref() == Some(key.as_str()))
        .filter(|e| since.is_none_or(|s| e.t.with_timezone(&cfg.tz).date_naive() >= s))
        .map(|e| e.t)
        .max()
}

fn parse_instance_key(inst: &str) -> Option<InstanceKey> {
    if let Some(n) = inst.strip_prefix('#') {
        return n.parse().ok().map(InstanceKey::Nth);
    }
    crate::model::parse_date(inst).ok().map(InstanceKey::Date)
}

/// Whole days in a duration (a sub-day duration is 0 days: valid until later
/// the same day).
fn whole_days(d: Dur) -> i64 {
    i64::from(d.as_minutes()) / 1440
}

fn add_days(date: NaiveDate, days: i64) -> NaiveDate {
    date.checked_add_signed(Duration::days(days)).unwrap_or(date)
}

fn end_of_day(date: NaiveDate) -> NaiveDateTime {
    date.and_hms_opt(23, 59, 0)
        .unwrap_or_else(|| date.and_time(NaiveTime::MIN))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::{parse_line, ParseCtx};
    use crate::log::Log;

    fn cfg() -> Config {
        Config::default()
    }

    fn item(text: &str) -> Item {
        let ctx = ParseCtx::new("routines.md", cfg().block_min());
        parse_line(text, &ctx).expect("fixture line parses")
    }

    fn backlog_item(text: &str) -> Item {
        let ctx = ParseCtx::new("backlog.md", cfg().block_min());
        parse_line(text, &ctx).expect("fixture line parses")
    }

    fn replay_of(jsonl: &str) -> Replay {
        Log::parse(jsonl).replay(None, cfg().tz)
    }

    fn date(s: &str) -> NaiveDate {
        crate::model::parse_date(s).expect("date")
    }

    fn dt(s: &str) -> NaiveDateTime {
        crate::model::parse_datetime(s).expect("datetime")
    }

    #[test]
    fn daily_window_expands_over_the_range() {
        let it = item("- lunch win:11:30-13:30 dur:30m every:day");
        let r = replay_of("");
        let v = instances(
            &it,
            (date("2026-09-07"), date("2026-09-09")),
            date("2026-09-07"),
            &r,
            &cfg(),
        );
        assert_eq!(v.len(), 3);
        assert_eq!(v[0].key, InstanceKey::Date(date("2026-09-07")));
        assert_eq!(v[0].window, Some((dt("2026-09-07T11:30"), dt("2026-09-07T13:30"))));
        assert_eq!(v[0].due, Some(dt("2026-09-07T13:30")));
        assert!(v.iter().all(|i| i.status == InstanceStatus::Pending));
    }

    #[test]
    fn overnight_window_runs_into_the_next_morning() {
        let it = item("- sleep win:22:00-08:00 dur:8h30m every:day ci:0");
        let r = replay_of("");
        let v = instances(
            &it,
            (date("2026-09-07"), date("2026-09-07")),
            date("2026-09-07"),
            &r,
            &cfg(),
        );
        assert_eq!(
            v[0].window,
            Some((dt("2026-09-07T22:00"), dt("2026-09-08T08:00")))
        );
    }

    #[test]
    fn monthly_clamps_to_the_month_length() {
        let it = item("- bins win:07:00-09:00 dur:10m every:month:31");
        let r = replay_of("");
        let v = instances(
            &it,
            (date("2026-02-01"), date("2026-03-31")),
            date("2026-02-01"),
            &r,
            &cfg(),
        );
        let keys: Vec<InstanceKey> = v.iter().map(|i| i.key).collect();
        assert_eq!(
            keys,
            vec![
                InstanceKey::Date(date("2026-02-28")),
                InstanceKey::Date(date("2026-03-31")),
            ]
        );
    }

    #[test]
    fn a_recurring_item_without_a_window_is_due_at_the_end_of_its_day() {
        let it = backlog_item("- [ ] 2 30m Pay the water bill  every:month:1 ^w1");
        let r = replay_of("");
        let v = instances(
            &it,
            (date("2026-09-01"), date("2026-10-31")),
            date("2026-09-07"),
            &r,
            &cfg(),
        );
        assert_eq!(v.len(), 2);
        assert_eq!(v[0].due, Some(dt("2026-09-01T23:59")));
        assert_eq!(v[0].window, None);
        assert_eq!(v[0].status, InstanceStatus::Pending, "on-miss:persist");
        // No window, so it is never a "placed before any task" instance.
        assert!(!is_mandatory(
            &it,
            &v[0],
            date("2026-09-07"),
            dt("2026-09-07T10:42")
        ));
    }

    #[test]
    fn missing_expire_window_expires_and_persist_carries() {
        let expire = item("- lunch win:11:30-13:30 dur:30m every:day");
        let persist = item("- laundry win:09:00-21:00 dur:30m every:day on-miss:persist");
        let next = item("- stretch win:07:00-09:00 dur:15m every:day on-miss:next");
        let r = replay_of("");
        let range = (date("2026-09-05"), date("2026-09-05"));
        let today = date("2026-09-07");
        assert_eq!(
            instances(&expire, range, today, &r, &cfg())[0].status,
            InstanceStatus::Expired
        );
        assert_eq!(
            instances(&persist, range, today, &r, &cfg())[0].status,
            InstanceStatus::Pending
        );
        assert_eq!(
            instances(&next, range, today, &r, &cfg())[0].status,
            InstanceStatus::Skipped
        );
    }

    #[test]
    fn waiting_item_has_no_pending_instance_until_the_timeout() {
        let it = backlog_item("- [?] 2 15m Ask about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4");
        let r = replay_of("");
        let range = (date("2026-09-07"), date("2026-09-07"));
        assert!(instances(&it, range, date("2026-09-07"), &r, &cfg()).is_empty());
        let later = (date("2026-09-13"), date("2026-09-13"));
        assert_eq!(
            instances(&it, later, date("2026-09-13"), &r, &cfg()).len(),
            1
        );
    }

    #[test]
    fn edits_for_the_waiting_transitions() {
        let it = backlog_item("- [ ] 2 15m Ask about the reading group  on-event:reply/7d est:5m ^a4");
        let mut line = it.line().clone();
        on_done_waiting(&it, date("2026-09-07"))
            .apply(&mut line)
            .expect("apply");
        assert_eq!(
            line.to_string(),
            "- [?] 2 15m Ask about the reading group  on-event:reply/7d est:5m waiting:2026-09-07 ^a4"
        );
        let waiting = backlog_item(&line.to_string());
        let mut line = waiting.line().clone();
        on_event_arrived(&waiting).apply(&mut line).expect("apply");
        assert_eq!(
            line.to_string(),
            "- [ ] 2 15m Ask about the reading group  on-event:reply/7d ^a4"
        );
    }
}
