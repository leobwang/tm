//! Review — the monitors of tm-spec-v1.md §11, the day/week/month reviews
//! behind `tm review <day|week|month> [--write] [--json]` (§13), the §12.1
//! status line and the §12.4 Review screen, plus the writer that puts a day
//! review into the day file's `<!-- tm:review -->` block (§6.3).
//!
//! Everything here is a pure computation over a [`Replay`] of the log
//! (§10.1), the [`Tree`], the [`Config`] and the learned [`Model`]. Nothing
//! reads a clock: the day, week or month under review is a parameter, and
//! the monitors that need the *plan* (adherence, the underused-slot count,
//! tomorrow's candidates, the optional quota, deadline health) take that
//! data as parameters too, so `review.rs` never depends on `planner.rs`.
//!
//! # API overview
//!
//! * [`StatusLine`] + [`status_line`] — the always-visible §11 status line
//!   (blocks done / budget, leak, adherence, window end, lost, rest debt,
//!   load). [`render_status`] renders its tail (`● 5/6 · leak 14m · …`) and
//!   [`render_status_full`] the whole §12.1 first line, given a
//!   [`StatusHead`] with the parts that are not monitors (date, clock,
//!   location, wake, the current energy pair).
//! * [`DayReview`] + [`day_review`] + [`render_day`] — §12.4's seven rows:
//!   blocks and load, the leak ledger, adherence, start latency, replans and
//!   drift, break integrity, rest debt, energy mix, energy calibration
//!   ([`EnergyReview`], including the hour after which the bias flips),
//!   estimate calibration, sleep, the done and demoted lists, tomorrow's
//!   first candidates and the optional quota. [`DayExtras`] carries the
//!   plan-dependent parameters.
//! * [`WeekReview`] + [`week_review`] + [`render_week`] — milestones hit and
//!   demoted, blocks per day, the [`DayHeat`] grid (7 days × 24 hours ×
//!   [`HEAT_STYLES`] styles) the TUI draws, the [`LoungeRate`], calibration
//!   trends, the prior-vs-learned [`CurveOverlay`], plan honesty, deadline
//!   health, demotion churn and carry-over, plus the week surfaces of the
//!   day monitors §11 asks for a week trend of: the energy mix, the break
//!   histogram, start latency and the [`SleepRow`] panel.
//! * [`MonthReview`] + [`month_review`] + [`render_month`] — outcomes done
//!   and not, demotion churn, carry-over week over week and the proposed cut
//!   list (anything with ≥ [`CUT_STAMPS`] stamps).
//! * [`WaitingRow`] + [`waiting`] + [`render_waiting`] — §11's "Waiting" row
//!   (items in `[?]` with days waiting and timeout), whose surface is §12.3's
//!   Necessities screen rather than a review.
//! * [`write_day_review`] — puts rendered text into the day file's
//!   `<!-- tm:review start --> … <!-- tm:review end -->` block, the one
//!   [`horizon::close_day`] leaves behind as a
//!   placeholder ([`crate::horizon::REVIEW_BLOCK`]).
//!
//! Every review type is `Serialize` for `tm review … --json` (§14: the
//! `/review-day` and `/review-week` skills consume it), `Clone`, `Debug` and
//! `PartialEq`.
//!
//! # Choices the spec leaves open (deviations)
//!
//! 1. **`load`** is §11's formula exactly — `Σ block_min × ci / 5`, i.e.
//!    ci-weighted *minutes*, which is what [`log::DayReplay::load`] already
//!    computes. §12.4's printed `load 18.4` is not reproducible from its own
//!    row (five blocks) under any reading of the formula, so the number
//!    here is the formula's, not the example's. [`DayReview::load_blocks`]
//!    gives the same quantity in blocks for readers who want a small number.
//!    Blocks the log cannot attribute a `ci` to (a block cut by `stop`, see
//!    [`log::DayReplay::ci_unknown`]) are attributed from the tree here, so
//!    the day review's load and energy mix cover every logged minute. An
//!    item the tree no longer holds is attributed `ci 0`: it adds nothing to
//!    the load, but its minutes stay in [`EnergyMix::total_min`].
//! 2. **Leak ledger** = `idle{attributed:"leak"}` minutes **plus**
//!    unattributed gaps *longer than* `cfg.day.idle_min` (§11's strict
//!    inequality; [`log::DayReplay::gaps`] keeps gaps of at least its
//!    argument, so it is asked for `idle_min + 1`). "Longest single leak" is
//!    the longest of either kind.
//! 3. **Adherence** needs the plan as it stood at arrival, which is not in
//!    the log; it is the `plan_at_arrival` parameter (§12.1's ghost row).
//!    A planned block counts as started when a `start` for its id happened
//!    within [`ADHERENCE_TOLERANCE_MIN`] of its planned start (each start is
//!    matched to at most one planned block, closest first), and as completed
//!    when its id has a non-partial `done` that day.
//! 4. **Rest debt** (§11 "planned breaks skipped or cut, cumulative today")
//!    is `expected − actual`, floored at 0, where `expected` is
//!    `⌊blocks_done / break_after_blocks⌋ × break_min` (the breaks the day
//!    owed) and `actual` is the sum of the breaks taken. A break that was
//!    cut short and a break that was skipped therefore cost the same debt.
//! 5. **Energy calibration** is scored on the *logged* `pred` (what the day
//!    was actually planned against, which is what §12.4's row shows), via
//!    [`energy::calibration`]. [`EnergyReview::mae_prior`] and
//!    [`EnergyReview::mae_learned`] additionally re-score the config prior
//!    and the learned model with [`energy::compare`]. The bias flip hour is
//!    the first hour whose bias sign is opposite to the first non-zero hour's
//!    and after which that first sign never returns. Both the hourly rows
//!    and §12.4's `pred … rep …` cells run in the day's own order, forwards
//!    from the first observation to the last: a day runs wake to wake
//!    (§10.1), so an observation after midnight is the *end* of the day, not
//!    its beginning, and the row never reaches back to hours the day never
//!    lived through.
//! 6. **Estimate calibration** is computed over the *whole* replay's
//!    duration observations, not only the day's: §12.4's `lean ×1.6 (n=9)`
//!    is a running multiplier, and a single day never has nine.
//! 7. **The day of an event** is its wake-to-wake day for everything the
//!    replay already bucketed ([`log::DayIndex`]); demotions, which the
//!    replay keeps globally, are attributed by their calendar date in `tz`.
//! 8. **Plan honesty** (§11 "planned blocks / realistic budget", day and
//!    week). For the *week* the realistic budget is
//!    `budget × cfg.week.plan_ratio` (§16's own comment: "warn if planned >
//!    0.8 × budget"); the week's budget is not in the tree — it is the week
//!    file's `budget:` front matter — so it is a parameter
//!    ([`WeekExtras::budget_blocks`]), and planned blocks default to Σ
//!    `remaining` over the week's top-level items. For the *day* the block
//!    budget has already been through `budget_ratio` (§8.1), so it *is* the
//!    realistic budget and the ratio is `plan_at_arrival.len() / budget`.
//! 9. **Signatures.** [`status_line`] takes `cfg` as well as the replay, the
//!    runtime and the plan: the leak ledger needs `idle_min`, rest debt
//!    needs `break_min`/`break_after_blocks` and the budget falls back to
//!    §8.1's formula when the day has no `arrive`. The three review
//!    functions take their `*Extras` by reference. Everything else is the
//!    shape §11 and §13 name.
//! 10. **Minutes are printed** as `8h10m` / `45m` and estimates as blocks
//!    (`0.5b`, `2.6b`, `20m`) — [`fmt_hm`] and [`fmt_blocks_min`], the
//!    latter differing from [`crate::priority::fmt_blocks`] only in that it
//!    prints a half block as `0.5b` rather than `30m`, which is what §12.4's
//!    `t5 (0.5b → week)` shows.
//! 11. **Energy mix** is §11's share *of budget*: [`EnergyMix::high_share`]
//!    is `high_min / budget_min`, where `budget_min` is the block budget
//!    (§8.1) in minutes — the day's own budget, and for a week the sum of
//!    the budgets of the days the log knows. A day that works half its
//!    budget at `ci 5` therefore reads 50%, not 100%, and a day that
//!    overshoots its budget can read over 100%. The minutes actually worked
//!    stay in [`EnergyMix::total_min`].
//! 12. **Break integrity** counts a break as over-run at *more* than
//!    [`BREAK_OVERRUN_FACTOR`]× its planned length (§11's "share > 2×"), so
//!    a break of exactly twice its plan does not count.
//! 13. **What is not here.** §11's "Waiting" row has no review surface — it
//!    is the Necessities screen (§12.3) — but its data is [`waiting`]. The
//!    day bar and the week's stacked bars are drawings; this module supplies
//!    their numbers ([`DayHeat`], [`EnergyMix`]) and leaves the drawing to
//!    the TUI.

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;

use chrono::{DateTime, Duration, FixedOffset, NaiveDate, NaiveTime, Timelike};
use chrono_tz::Tz;
use serde::Serialize;
use thiserror::Error;

use crate::config::Config;
use crate::energy::{self, Calibration, Model, TagStats};
use crate::grammar::ParsedFile;
use crate::horizon::{self, REVIEW_BLOCK};
use crate::log::{self, BreakRecord, DayReplay, Replay, SegmentKind};
use crate::model::{parse_time, Horizon, Id, IsoWeek, Stamp, State, YearMonth};
use crate::priority::DeadlineHealth;
use crate::store::{edit, RuntimeState, Store, StoreError};
use crate::tree::Tree;

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// §11 adherence: a planned block counts as started on time when the `start`
/// is within this many minutes of the planned start.
pub const ADHERENCE_TOLERANCE_MIN: i64 = 10;

/// §11 rest debt: the status line warns above this many minutes.
pub const REST_DEBT_WARN_MIN: u32 = 40;

/// §11 break integrity: a break longer than this multiple of its planned
/// length counts in the "share > 2×" column.
pub const BREAK_OVERRUN_FACTOR: u32 = 2;

/// §6.3 / §12.4: the number of demotion stamps that puts an item on the
/// month review's proposed cut list.
pub const CUT_STAMPS: usize = 2;

/// Hours in a heat-grid day row.
pub const HEAT_HOURS: usize = 24;

/// Styles counted per heat-grid cell (see [`Style`]).
pub const HEAT_STYLES: usize = 7;

/// The most cells §12.4's `energy pred … rep …` row can hold. A day runs
/// wake to wake, so a long one still fits inside a day and a bit; the cap is
/// only there to bound a log whose timestamps run away.
const MAX_ENERGY_HOURS: usize = 48;

/// Errors from writing a review into the day file.
#[derive(Debug, Error)]
pub enum ReviewError {
    /// The day file could not be read or written.
    #[error(transparent)]
    Store(#[from] StoreError),
}

// ---------------------------------------------------------------------------
// Formatting helpers
// ---------------------------------------------------------------------------

/// `490 → "8h10m"`, `45 → "45m"`, `120 → "2h"`, `0 → "0m"`.
pub fn fmt_hm(minutes: u32) -> String {
    let (h, m) = (minutes / 60, minutes % 60);
    match (h, m) {
        (0, m) => format!("{m}m"),
        (h, 0) => format!("{h}h"),
        (h, m) => format!("{h}h{m}m"),
    }
}

/// Minutes as blocks the way §12.4 writes them: `360 → "6b"`,
/// `30 → "0.5b"`, `155 → "2.6b"`, `20 → "20m"`.
pub fn fmt_blocks_min(minutes: u32, block_min: u32) -> String {
    if block_min == 0 {
        return format!("{minutes}m");
    }
    if minutes % block_min == 0 {
        return format!("{}b", minutes / block_min);
    }
    if minutes * 2 >= block_min {
        return format!("{:.1}b", minutes as f64 / block_min as f64);
    }
    format!("{minutes}m")
}

/// §12.1 writes a zero as a bare `0` and anything else with its unit.
fn fmt_lost(minutes: u32) -> String {
    if minutes == 0 {
        "0".to_string()
    } else {
        format!("{minutes}m")
    }
}

/// One decimal, with the typographic minus §12.4 uses (`−0.3`).
fn fmt_signed(x: f64) -> String {
    if x < 0.0 {
        format!("−{:.1}", -x)
    } else {
        format!("{x:.1}")
    }
}

/// A percentage, or `-` when there is nothing to divide by.
fn fmt_pct(p: Option<u8>) -> String {
    p.map_or_else(|| "-".to_string(), |p| format!("{p}%"))
}

fn pct(part: usize, whole: usize) -> Option<u8> {
    (whole > 0).then(|| (part as f64 / whole as f64 * 100.0).round() as u8)
}

fn round1(x: f64) -> f64 {
    (x * 10.0).round() / 10.0
}

fn round2(x: f64) -> f64 {
    (x * 100.0).round() / 100.0
}

/// Join with `sep`, or `none` when empty.
fn join_or(items: &[String], sep: &str, none: &str) -> String {
    if items.is_empty() {
        none.to_string()
    } else {
        items.join(sep)
    }
}

// ---------------------------------------------------------------------------
// Status line (§11, §12.1)
// ---------------------------------------------------------------------------

/// One block of the plan as it stood at arrival — the ghost row of §12.1 and
/// the denominator of the §11 adherence monitor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PlannedBlock {
    /// The item the block was for.
    pub id: Id,
    /// When the block was planned to start.
    pub start: DateTime<Tz>,
}

impl PlannedBlock {
    /// Build one.
    pub fn new(id: Id, start: DateTime<Tz>) -> PlannedBlock {
        PlannedBlock { id, start }
    }
}

/// The always-visible §11 status line: blocks done / budget · leak ·
/// adherence, plus the window end, lost minutes, rest debt and load §12.1
/// also shows.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct StatusLine {
    /// Blocks finished today.
    pub blocks_done: u32,
    /// Today's block budget (§8.1).
    pub budget: u32,
    /// Leak ledger total: attributed leak plus unattributed gaps.
    pub leak_min: u32,
    /// Share of planned blocks started within
    /// [`ADHERENCE_TOLERANCE_MIN`]; `None` when nothing was planned.
    pub adherence_pct: Option<u8>,
    /// End of today's window.
    pub window_end: Option<NaiveTime>,
    /// Minutes lost to interruptions (`resume.lost_min`).
    pub lost_min: u32,
    /// Rest debt so far today (§11).
    pub rest_debt_min: u32,
    /// §11 load: `Σ block_min × ci / 5`.
    pub load: f64,
}

/// The parts of §12.1's first line that are not monitors.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct StatusHead {
    /// The day.
    pub date: NaiveDate,
    /// The clock.
    pub now: NaiveTime,
    /// Current location.
    pub loc: Option<String>,
    /// Wake time.
    pub wake: Option<NaiveTime>,
    /// Minutes slept.
    pub slept_min: Option<u32>,
    /// Currently predicted energy.
    pub pred: Option<u8>,
    /// Last reported energy.
    pub rep: Option<u8>,
}

/// The §11 status line for the day `runtime.date` names (falling back to the
/// last day in `replay`).
///
/// `plan_at_arrival` is the plan the day started with (§12.1's ghost row);
/// pass an empty slice before the first plan, and `adherence_pct` is `None`.
/// `load` is [`log::DayReplay::load`] as the log records it — [`day_review`]
/// additionally attributes blocks the log has no `ci` for from the tree.
pub fn status_line(
    replay: &Replay,
    cfg: &Config,
    runtime: &RuntimeState,
    plan_at_arrival: &[PlannedBlock],
) -> StatusLine {
    let date = runtime
        .date
        .or_else(|| replay.days.keys().next_back().copied());
    let day = date.and_then(|d| replay.day(d));
    let adherence = adherence(day, plan_at_arrival);
    StatusLine {
        blocks_done: day.map_or(0, |d| d.blocks_done),
        budget: budget_of(day, runtime, cfg),
        leak_min: leak(day, cfg).total_min,
        adherence_pct: adherence.started_pct,
        window_end: runtime
            .window
            .map(|(_, end)| end)
            .or_else(|| day.and_then(window_of).map(|(_, end)| end)),
        lost_min: day.map_or(0, |d| d.lost_min),
        rest_debt_min: rest_debt(day, cfg),
        load: day.map_or(0.0, |d| round1(d.load)),
    }
}

/// The monitor tail of §12.1's first line:
/// `● 3/6 · leak 14m · adherence 83% · window → 16:00 · lost 0`, with the
/// §11 rest-debt warning appended above [`REST_DEBT_WARN_MIN`].
pub fn render_status(s: &StatusLine) -> String {
    let mut out = format!("● {}/{}", s.blocks_done, s.budget);
    let _ = write!(out, " · leak {}m", s.leak_min);
    let _ = write!(out, " · adherence {}", fmt_pct(s.adherence_pct));
    if let Some(end) = s.window_end {
        let _ = write!(out, " · window → {}", end.format("%H:%M"));
    }
    let _ = write!(out, " · lost {}", fmt_lost(s.lost_min));
    if s.rest_debt_min > REST_DEBT_WARN_MIN {
        let _ = write!(out, " · rest debt {}m", s.rest_debt_min);
    }
    out
}

/// The whole of §12.1's first line:
/// `tm · Mon 2026-09-07 · 10:42 · lounge · wake 06:05 (8h10m) · pred 4 rep 4 ·  ● 3/6 · …`.
pub fn render_status_full(head: &StatusHead, s: &StatusLine) -> String {
    let mut out = format!(
        "tm · {} {} · {}",
        head.date.format("%a"),
        head.date,
        head.now.format("%H:%M")
    );
    if let Some(loc) = &head.loc {
        let _ = write!(out, " · {loc}");
    }
    if let Some(wake) = head.wake {
        let _ = write!(out, " · wake {}", wake.format("%H:%M"));
        if let Some(slept) = head.slept_min {
            let _ = write!(out, " ({})", fmt_hm(slept));
        }
    }
    match (head.pred, head.rep) {
        (Some(p), Some(r)) => {
            let _ = write!(out, " · pred {p} rep {r}");
        }
        (Some(p), None) => {
            let _ = write!(out, " · pred {p}");
        }
        _ => {}
    }
    let _ = write!(out, " ·  {}", render_status(s));
    out
}

// ---------------------------------------------------------------------------
// Shared day monitors
// ---------------------------------------------------------------------------

/// The §11 leak ledger: attributed leak, unattributed gaps and the longest
/// single leak.
#[derive(Clone, Copy, Debug, Default, PartialEq, Serialize)]
pub struct LeakLedger {
    /// Σ `idle{attributed:"leak"}` minutes.
    pub attributed_min: u32,
    /// Σ unattributed gaps longer than `cfg.day.idle_min` (§11's strict
    /// `> idle_min`).
    pub gap_min: u32,
    /// The two above.
    pub total_min: u32,
    /// The longest single leak of either kind.
    pub longest_min: u32,
}

fn leak(day: Option<&DayReplay>, cfg: &Config) -> LeakLedger {
    let Some(day) = day else {
        return LeakLedger::default();
    };
    // §11 counts gaps *longer* than `idle_min`; `DayReplay::gaps` keeps gaps
    // of at least its argument, so ask it for one minute more.
    let gaps = day.gaps(cfg.day.idle_min.saturating_add(1));
    let gap_min = gaps.iter().fold(0u32, |a, (s, e)| {
        a.saturating_add(e.signed_duration_since(*s).num_minutes().max(0) as u32)
    });
    let longest_gap = gaps.iter().fold(0u32, |a, (s, e)| {
        a.max(e.signed_duration_since(*s).num_minutes().max(0) as u32)
    });
    LeakLedger {
        attributed_min: day.leak_min,
        gap_min,
        total_min: day.leak_min.saturating_add(gap_min),
        longest_min: day.longest_leak.max(longest_gap),
    }
}

/// The §11 adherence monitor over the plan as it stood at arrival.
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
pub struct Adherence {
    /// Blocks in the plan at arrival.
    pub planned: usize,
    /// Of those, started within [`ADHERENCE_TOLERANCE_MIN`] of plan.
    pub started_on_time: usize,
    /// Of those, whose item was finished today.
    pub completed: usize,
    /// `started_on_time / planned`.
    pub started_pct: Option<u8>,
    /// `completed / planned`.
    pub completed_pct: Option<u8>,
    /// Planned blocks that were not started on time, in plan order.
    pub missed: Vec<Id>,
}

fn adherence(day: Option<&DayReplay>, plan: &[PlannedBlock]) -> Adherence {
    let mut used = vec![false; day.map_or(0, |d| d.starts.len())];
    let (mut on_time, mut completed) = (0usize, 0usize);
    let mut missed = Vec::new();
    for block in plan {
        let mut best: Option<(i64, usize)> = None;
        if let Some(day) = day {
            for (i, start) in day.starts.iter().enumerate() {
                if used[i] || start.id != block.id.as_str() {
                    continue;
                }
                let delta = start.t.signed_duration_since(block.start).num_minutes().abs();
                if best.is_none_or(|(d, _)| delta < d) {
                    best = Some((delta, i));
                }
            }
        }
        match best {
            Some((delta, i)) if delta <= ADHERENCE_TOLERANCE_MIN => {
                used[i] = true;
                on_time += 1;
            }
            _ => missed.push(block.id.clone()),
        }
        if day.is_some_and(|d| d.done.iter().any(|id| id == block.id.as_str())) {
            completed += 1;
        }
    }
    Adherence {
        planned: plan.len(),
        started_on_time: on_time,
        completed,
        started_pct: pct(on_time, plan.len()),
        completed_pct: pct(completed, plan.len()),
        missed,
    }
}

fn rest_debt(day: Option<&DayReplay>, cfg: &Config) -> u32 {
    let Some(day) = day else { return 0 };
    let per = cfg.day.break_after_blocks.max(1);
    let owed = (day.blocks_done / per).saturating_mul(cfg.day.break_min);
    owed.saturating_sub(day.break_min())
}

fn budget_of(day: Option<&DayReplay>, runtime: &RuntimeState, cfg: &Config) -> u32 {
    runtime
        .budget
        .or_else(|| day.and_then(|d| d.budget))
        .unwrap_or_else(|| crate::capacity::budget_blocks(cfg))
}

fn window_of(day: &DayReplay) -> Option<(NaiveTime, NaiveTime)> {
    let w = day.window.as_ref()?;
    Some((parse_time(&w[0]).ok()?, parse_time(&w[1]).ok()?))
}

// ---------------------------------------------------------------------------
// Waiting (§11, §12.3)
// ---------------------------------------------------------------------------

/// One `[?]` item of §11's "Waiting" monitor: how long it has waited and when
/// the wait times out. §12.3 draws it as `? a4 Prof. Lee reply 2d / 7d`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct WaitingRow {
    /// The item.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// The event it waits for (`on-event:reply/7d` → `reply`).
    pub event: Option<String>,
    /// `waiting:<date>` as written.
    pub since: Option<NaiveDate>,
    /// Days waited so far (0 without a `waiting:` stamp).
    pub days_waiting: i64,
    /// Whole days the timeout allows (`7d` → 7), when there is one.
    pub timeout_days: Option<i64>,
    /// The date the timeout elapses, when both the stamp and the timeout are
    /// there.
    pub timeout_at: Option<NaiveDate>,
    /// `today` is past `timeout_at` (§5.1: the day *after* the timeout date),
    /// so the wait ends by timeout.
    pub expired: bool,
    /// The `tm event` that already resolved the wait, if the log has one.
    pub arrived: Option<DateTime<FixedOffset>>,
}

/// §11's "Waiting" row: every item in state `[?]`, with the days it has
/// waited and its timeout (§12.3's Necessities screen).
///
/// The data is the tree's — [`Tree::waiting_ids`] and
/// [`crate::recur::waiting_state`] — plus, from the log, the `tm event` that
/// has already resolved the wait. Rows keep the tree's order.
pub fn waiting(tree: &Tree, replay: &Replay, today: NaiveDate, cfg: &Config) -> Vec<WaitingRow> {
    tree.waiting_ids()
        .into_iter()
        .filter_map(|id| {
            let item = tree.get(&id)?;
            let state = crate::recur::waiting_state(item, replay, today, cfg)?;
            let (event, timeout_days) = match &item.recur {
                crate::model::Recur::OnEvent { name, timeout } => (
                    Some(name.clone()),
                    timeout.map(|t| i64::from(t.as_minutes()) / 1440),
                ),
                _ => (None, None),
            };
            Some(WaitingRow {
                id,
                title: item.title.clone(),
                event,
                since: state.since,
                days_waiting: state.days_waiting,
                timeout_days,
                timeout_at: state.timeout_at,
                expired: state.expired,
                arrived: state.arrived,
            })
        })
        .collect()
}

/// §12.3's Waiting panel, one line per row: `? a4 reply 2d / 7d`.
pub fn render_waiting(rows: &[WaitingRow]) -> String {
    let mut out = String::new();
    for r in rows {
        let mut line = format!(" ? {} {}", r.id, r.title);
        if let Some(event) = &r.event {
            let _ = write!(line, " · {event}");
        }
        let _ = write!(line, " · {}d", r.days_waiting);
        if let Some(days) = r.timeout_days {
            let _ = write!(line, " / {days}d");
        }
        if r.expired {
            line.push_str(" · timed out");
        } else if r.arrived.is_some() {
            line.push_str(" · arrived");
        }
        let _ = writeln!(out, "{line}");
    }
    out
}

// ---------------------------------------------------------------------------
// Day review (§12.4)
// ---------------------------------------------------------------------------

/// One break, as the §11 break-integrity monitor sees it.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct BreakRow {
    /// Planned length.
    pub planned_min: u32,
    /// Actual length (the planned one when the log has no actual).
    pub actual_min: u32,
    /// `walk`, `seat`, `bed`, `phone`, …
    pub place: Option<String>,
    /// `actual > 2 × planned` (§11's strict `> 2×`).
    pub over: bool,
}

/// §11 break integrity: planned versus actual, the share over
/// [`BREAK_OVERRUN_FACTOR`]×, and the histogram by `where`.
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
pub struct BreakIntegrity {
    /// Every break of the day, in order.
    pub breaks: Vec<BreakRow>,
    /// Σ planned minutes.
    pub planned_min: u32,
    /// Σ actual minutes.
    pub actual_min: u32,
    /// Breaks longer than [`BREAK_OVERRUN_FACTOR`]× their planned length.
    pub over_count: usize,
    /// `over_count / breaks.len()`.
    pub over_share: Option<u8>,
    /// `where → (count, minutes)`.
    pub by_where: BTreeMap<String, (usize, u32)>,
}

fn break_integrity(breaks: &[BreakRecord]) -> BreakIntegrity {
    let mut out = BreakIntegrity::default();
    for b in breaks {
        let actual = b.actual_or_planned();
        // §11: "share > 2×" — a break of exactly twice its plan is not over.
        let over = actual > b.planned_min.saturating_mul(BREAK_OVERRUN_FACTOR) && b.planned_min > 0;
        out.planned_min = out.planned_min.saturating_add(b.planned_min);
        out.actual_min = out.actual_min.saturating_add(actual);
        if over {
            out.over_count += 1;
        }
        let key = b.r#where.clone().unwrap_or_else(|| "-".to_string());
        let e = out.by_where.entry(key).or_insert((0, 0));
        e.0 += 1;
        e.1 = e.1.saturating_add(actual);
        out.breaks.push(BreakRow {
            planned_min: b.planned_min,
            actual_min: actual,
            place: b.r#where.clone(),
            over,
        });
    }
    out.over_share = pct(out.over_count, out.breaks.len());
    out
}

/// §11 energy mix: minutes at each `ci`, the share **of the budget** at
/// `ci ≥ 4`, and the count of under-used slots the planner reported.
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
pub struct EnergyMix {
    /// Block minutes at each `ci` (index = ci).
    pub minutes_by_ci: [u32; 6],
    /// Σ of the above: the minutes actually worked.
    pub total_min: u32,
    /// Minutes at `ci ≥ 4`.
    pub high_min: u32,
    /// The budget those minutes are measured against, in minutes: the block
    /// budget (§8.1) × `block_min`, summed over the days covered.
    pub budget_min: u32,
    /// §11's "share of budget with `ci ≥ 4`": `high_min / budget_min`, so a
    /// day that works half its budget at `ci 5` reads 50%, not 100%. `None`
    /// when there is no budget to divide by. It can exceed 100 on a day that
    /// overshoots its budget.
    pub high_share: Option<u8>,
    /// Slots the planner flagged `↓` (gap ≥ 2) — a parameter.
    pub underused: usize,
}

/// One hour of §12.4's `energy pred … rep …` row. The cells run forwards in
/// time, so a wake-to-wake day that crosses midnight ends on a smaller clock
/// hour than it started on.
#[derive(Clone, Copy, Debug, PartialEq, Serialize)]
pub struct EnergyHour {
    /// Clock hour.
    pub hour: u32,
    /// Predicted energy: the mean of the hour's logged predictions, or the
    /// model's prediction for the hour when nothing was logged in it.
    pub pred: u8,
    /// Reported energy: the mean of the hour's reports, `None` when the hour
    /// was never asked (§12.1's `·`).
    pub rep: Option<u8>,
}

/// §11 energy calibration.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct EnergyReview {
    /// Observations scored.
    pub n: usize,
    /// MAE of the logged prediction.
    pub mae: f64,
    /// Mean signed error `rep − pred` of the logged prediction.
    pub bias: f64,
    /// `(hour, n, mae, bias)`, in the order the day met them: a day runs
    /// wake to wake (§10.1), so an hour after midnight comes last, not
    /// first.
    pub by_hour: Vec<(u32, usize, f64, f64)>,
    /// The hour after which the bias sign flips, when it flips once.
    pub flip_hour: Option<u32>,
    /// MAE the config prior would have scored.
    pub mae_prior: f64,
    /// MAE the learned model would have scored.
    pub mae_learned: f64,
    /// The hourly `pred` / `rep` series §12.4 prints.
    pub hours: Vec<EnergyHour>,
}

/// One item demoted during the day.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct DemotedRow {
    /// The item.
    pub id: Id,
    /// Remaining estimate carried.
    pub est_min: u32,
    /// The horizon it went to (`2026-W37`).
    pub to: String,
}

/// One of tomorrow's first candidates — a parameter, since it comes from the
/// planner and the EDF pass, not from the log.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TomorrowCandidate {
    /// The item.
    pub id: Id,
    /// What to say about it (`after t4`, `p1 u=0.6`, `done`).
    pub note: Option<String>,
}

impl TomorrowCandidate {
    /// Build one.
    pub fn new(id: Id, note: Option<&str>) -> TomorrowCandidate {
        TomorrowCandidate {
            id,
            note: note.map(str::to_string),
        }
    }
}

/// §11 optional quota: minutes spent on `optional.md` items against their
/// `max:`, and how many of those minutes were not in a Rest slot. Both come
/// from the plan, so both are parameters.
#[derive(Clone, Copy, Debug, Default, PartialEq, Serialize)]
pub struct OptionalQuota {
    /// Minutes spent on optionals.
    pub minutes: u32,
    /// The `max:` for the period, when there is one.
    pub cap_min: Option<u32>,
    /// Of `minutes`, those outside a Rest slot.
    pub outside_rest_min: u32,
}

/// The plan-dependent parameters of [`day_review`].
#[derive(Clone, Debug, Default, PartialEq)]
pub struct DayExtras {
    /// The plan as it stood at arrival (§12.1's ghost row) — the adherence
    /// denominator.
    pub plan_at_arrival: Vec<PlannedBlock>,
    /// `diagnostics.underused` (§8.2 step 8).
    pub underused: usize,
    /// Tomorrow's first candidates, in order.
    pub tomorrow_first: Vec<TomorrowCandidate>,
    /// The optional quota, when the day had optionals.
    pub optional: Option<OptionalQuota>,
    /// What the day was lost to (`call`), for §12.4's `lost 55m (call)`.
    pub lost_note: Option<String>,
    /// The block budget, when the day has no `arrive` event.
    pub budget: Option<u32>,
}

/// Everything the §12.4 Review screen shows for one day.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct DayReview {
    /// The day.
    pub date: NaiveDate,
    /// Where the day was spent.
    pub loc: Option<String>,
    /// Blocks finished.
    pub blocks_done: u32,
    /// Block budget (§8.1).
    pub budget: u32,
    /// §11 load, `Σ block_min × ci / 5`.
    pub load: f64,
    /// The same in blocks (`load / block_len_min`).
    pub load_blocks: f64,
    /// `cfg.day.block_min`: the length of one block, so a renderer can turn
    /// the minutes below into blocks without the config.
    pub block_len_min: u32,
    /// §11 plan honesty for the day: blocks in the plan at arrival over the
    /// block budget (§8.1 has already applied `budget_ratio`, so the budget
    /// *is* the realistic one). `None` when nothing was planned.
    pub plan_honesty: Option<f64>,
    /// Σ block minutes.
    pub block_min: u32,
    /// The working window.
    pub window: Option<(NaiveTime, NaiveTime)>,
    /// Minutes lost to interruptions.
    pub lost_min: u32,
    /// What they were lost to.
    pub lost_note: Option<String>,
    /// The leak ledger.
    pub leak: LeakLedger,
    /// Adherence.
    pub adherence: Adherence,
    /// Wake → arrive, in minutes.
    pub wake_to_arrive_min: Option<i64>,
    /// Arrive → first `start`, in minutes.
    pub arrive_to_start_min: Option<i64>,
    /// `plan` events today.
    pub replans: u32,
    /// Σ drift over those replans.
    pub drift_min: u32,
    /// Break integrity.
    pub breaks: BreakIntegrity,
    /// Rest debt.
    pub rest_debt_min: u32,
    /// Energy mix.
    pub mix: EnergyMix,
    /// Energy calibration.
    pub energy: EnergyReview,
    /// Estimate calibration, per tag.
    pub estimates: Vec<TagStats>,
    /// Minutes slept.
    pub slept_min: Option<u32>,
    /// Sleep onset.
    pub onset_min: Option<u32>,
    /// Items finished today.
    pub done: Vec<Id>,
    /// Items demoted today.
    pub demoted: Vec<DemotedRow>,
    /// Tomorrow's first candidates.
    pub tomorrow: Vec<TomorrowCandidate>,
    /// The optional quota.
    pub optional: Option<OptionalQuota>,
}

/// The §12.4 day review: every §11 monitor that has a day surface, computed
/// from the log replay, the tree, the config and the learned model.
///
/// `date` picks the (wake-to-wake) day out of `replay`; `tz` is the zone the
/// clock hours are read in (normally `cfg.tz`); `extras` carries the
/// plan-dependent parameters.
pub fn day_review(
    tree: &Tree,
    replay: &Replay,
    cfg: &Config,
    model: &Model,
    date: NaiveDate,
    tz: Tz,
    extras: &DayExtras,
) -> DayReview {
    let day = replay.day(date);
    let block_min = cfg.block_min().max(1);
    let budget = extras
        .budget
        .or_else(|| day.and_then(|d| d.budget))
        .unwrap_or_else(|| crate::capacity::budget_blocks(cfg));

    // Load and energy mix: start from what the log knows, then attribute the
    // blocks it has no `ci` for (cut blocks) from the tree.
    let (minutes_by_ci, load) = mix_and_load(day.into_iter(), tree);
    let mix = energy_mix(
        minutes_by_ci,
        budget.saturating_mul(block_min),
        extras.underused,
    );

    let obs: Vec<log::EnergyObs> = day
        .map(|d| {
            replay
                .energy
                .iter()
                .filter(|o| o.day == d.date)
                .cloned()
                .collect()
        })
        .unwrap_or_default();
    let calib = energy::calibration(cfg, &obs);
    let comparison = energy::compare(cfg, &Model::from_config(cfg), model, &obs);
    let by_hour = by_hour_in_day_order(&calib, &obs, cfg.tz);
    let flip = flip_hour(&by_hour);
    let energy_review = EnergyReview {
        n: calib.n,
        mae: calib.mae,
        bias: calib.bias,
        by_hour,
        flip_hour: flip,
        mae_prior: comparison.mae_a,
        mae_learned: comparison.mae_b,
        hours: energy_hours(&obs, day, cfg, model, tz),
    };

    let demoted: Vec<DemotedRow> = replay
        .demotions
        .values()
        .flatten()
        .filter(|d| d.t.with_timezone(&tz).date_naive() == date)
        .map(|d| DemotedRow {
            id: Id::new(d.id.clone()),
            est_min: d.est_min,
            to: d.to.clone(),
        })
        .collect();

    DayReview {
        date,
        loc: day.and_then(|d| d.loc.clone()),
        blocks_done: day.map_or(0, |d| d.blocks_done),
        budget,
        load: round1(load),
        load_blocks: round2(load / block_min as f64),
        block_len_min: block_min,
        plan_honesty: (!extras.plan_at_arrival.is_empty() && budget > 0)
            .then(|| round2(extras.plan_at_arrival.len() as f64 / budget as f64)),
        block_min: day.map_or(0, |d| d.block_min),
        window: day.and_then(window_of),
        lost_min: day.map_or(0, |d| d.lost_min),
        lost_note: extras.lost_note.clone(),
        leak: leak(day, cfg),
        adherence: adherence(day, &extras.plan_at_arrival),
        wake_to_arrive_min: day.and_then(|d| d.wake_to_arrive_min()),
        arrive_to_start_min: day.and_then(|d| d.arrive_to_start_min()),
        replans: day.map_or(0, |d| d.plans),
        drift_min: day.map_or(0, |d| d.drift_min),
        breaks: break_integrity(day.map_or(&[], |d| d.breaks.as_slice())),
        rest_debt_min: rest_debt(day, cfg),
        mix,
        energy: energy_review,
        estimates: energy::estimate_calibration(cfg, &replay.durations, date),
        slept_min: day.and_then(|d| d.slept_min),
        onset_min: day.and_then(|d| d.onset_min),
        done: day
            .map(|d| d.done.iter().map(|i| Id::new(i.clone())).collect())
            .unwrap_or_default(),
        demoted,
        tomorrow: extras.tomorrow_first.clone(),
        optional: extras.optional,
    }
}

/// §11's load and energy mix over any set of days: the log's own totals plus
/// the block minutes it has no `ci` for, attributed from the tree.
///
/// An item the tree no longer holds (dropped, or cut out of the plan by a
/// close) is counted at `ci 0`: it adds nothing to the load, but its minutes
/// stay in the mix, so `Σ minutes_by_ci == Σ block_min` always holds.
fn mix_and_load<'a>(
    days: impl Iterator<Item = &'a DayReplay>,
    tree: &Tree,
) -> ([u32; 6], f64) {
    let mut minutes_by_ci = [0u32; 6];
    let mut load = 0.0f64;
    for day in days {
        for (ci, min) in day.minutes_by_ci.iter().enumerate() {
            minutes_by_ci[ci] = minutes_by_ci[ci].saturating_add(*min);
        }
        load += day.load;
        for (id, min) in &day.ci_unknown {
            let ci = tree
                .get(&Id::new(id.clone()))
                .map_or(0, |item| item.ci.min(5) as usize);
            minutes_by_ci[ci] = minutes_by_ci[ci].saturating_add(*min);
            load += *min as f64 * ci as f64 / 5.0;
        }
    }
    (minutes_by_ci, load)
}

fn energy_mix(minutes_by_ci: [u32; 6], budget_min: u32, underused: usize) -> EnergyMix {
    let total: u32 = minutes_by_ci.iter().fold(0u32, |a, m| a.saturating_add(*m));
    let high = minutes_by_ci[4].saturating_add(minutes_by_ci[5]);
    EnergyMix {
        minutes_by_ci,
        total_min: total,
        high_min: high,
        budget_min,
        // §11: "share of budget with ci ≥ 4", not share of what was worked.
        high_share: pct(high as usize, budget_min as usize),
        underused,
    }
}

/// [`energy::calibration`]'s hourly rows in the order the day met them.
///
/// The rows are keyed by clock hour, but a day runs wake to wake (§10.1), so
/// an observation after midnight belongs at the end of the day and not at
/// its front. Rows are ordered by the first observation in each hour; `tz`
/// must be the zone `calibration` bucketed them in (`cfg.tz`).
fn by_hour_in_day_order(
    calib: &Calibration,
    obs: &[log::EnergyObs],
    tz: Tz,
) -> Vec<(u32, usize, f64, f64)> {
    let mut first_seen: HashMap<u32, DateTime<FixedOffset>> = HashMap::new();
    for o in obs {
        let hour = o.t.with_timezone(&tz).hour();
        first_seen
            .entry(hour)
            .and_modify(|t| {
                if o.t < *t {
                    *t = o.t;
                }
            })
            .or_insert(o.t);
    }
    let mut rows = calib.by_hour.clone();
    rows.sort_by(|a, b| {
        first_seen
            .get(&a.0)
            .cmp(&first_seen.get(&b.0))
            .then(a.0.cmp(&b.0))
    });
    rows
}

/// The hour after which the bias sign flips: the first hour whose bias has
/// the opposite sign to the first non-zero hour's, provided the original
/// sign never comes back. `None` when the bias never changes sign.
///
/// `rows` must be in the day's own order (see [`by_hour_in_day_order`]):
/// across midnight the clock hour no longer sorts the day.
fn flip_hour(rows: &[(u32, usize, f64, f64)]) -> Option<u32> {
    let sign = |x: f64| {
        if x > 0.0 {
            1i8
        } else if x < 0.0 {
            -1i8
        } else {
            0
        }
    };
    let first = rows.iter().position(|(_, _, _, b)| sign(*b) != 0)?;
    let s0 = sign(rows[first].3);
    let flip = rows.iter().position(|(_, _, _, b)| sign(*b) == -s0)?;
    let returns = rows
        .iter()
        .skip(flip + 1)
        .any(|(_, _, _, b)| sign(*b) == s0);
    (!returns).then(|| rows[flip].0)
}

/// §12.4's `pred … rep …` row: one cell per clock hour from the first
/// observation of the day to the last, walking **forwards in time** — the
/// day runs wake to wake (§10.1), so the row may cross midnight and end on a
/// smaller clock hour than it began on. An hour with no observation keeps
/// the model's prediction for that hour and reports `None` (§12.1's `·`).
fn energy_hours(
    obs: &[log::EnergyObs],
    day: Option<&DayReplay>,
    cfg: &Config,
    model: &Model,
    tz: Tz,
) -> Vec<EnergyHour> {
    // Keyed by the instant the hour starts, so the order is chronological.
    let mut buckets: BTreeMap<DateTime<Tz>, (Vec<f64>, Vec<f64>)> = BTreeMap::new();
    for o in obs {
        let e = buckets
            .entry(hour_start(o.t.with_timezone(&tz)))
            .or_default();
        e.0.push(o.pred as f64);
        e.1.push(o.rep as f64);
    }
    let (Some(first), Some(last)) = (
        buckets.keys().next().copied(),
        buckets.keys().next_back().copied(),
    ) else {
        return Vec::new();
    };
    let mean = |xs: &[f64]| xs.iter().sum::<f64>() / xs.len() as f64;
    let mut out = Vec::new();
    let mut cursor = first;
    while cursor <= last && out.len() < MAX_ENERGY_HOURS {
        let cell = buckets.get(&cursor);
        out.push(EnergyHour {
            hour: cursor.hour(),
            pred: match cell {
                Some((preds, _)) => mean(preds).round() as u8,
                None => predict_at(day, cfg, model, cursor),
            },
            rep: cell.map(|(_, reps)| mean(reps).round() as u8),
        });
        let next = hour_start(cursor + Duration::hours(1));
        if next <= cursor {
            break;
        }
        cursor = next;
    }
    out
}

/// The top of `t`'s wall-clock hour, computed in absolute time: `with_minute`
/// and friends return `None` for the ambiguous hour of a DST fall-back.
fn hour_start<Z: chrono::TimeZone>(t: DateTime<Z>) -> DateTime<Z> {
    let secs = t.minute() as i64 * 60 + t.second() as i64;
    let nanos = t.nanosecond() as i64 % 1_000_000_000;
    t - Duration::seconds(secs) - Duration::nanoseconds(nanos)
}

/// What the model predicts at `t` on `day` (used for the hours the log never
/// asked about). Falls back to 3 when the day has no wake to measure `hsw`
/// from.
fn predict_at(day: Option<&DayReplay>, cfg: &Config, model: &Model, t: DateTime<Tz>) -> u8 {
    let Some(day) = day else { return 3 };
    let Some(wake) = day.wake else { return 3 };
    let wake = wake.with_timezone(&t.timezone());
    let loc = day
        .loc
        .as_deref()
        .and_then(|l| crate::model::Loc::parse(l).ok())
        .unwrap_or(crate::model::Loc::Any);
    let features = energy::Features::at(t, wake, loc).with_slept(day.slept_min);
    energy::predict(model, cfg, &features)
}

/// §12.4's Review screen for one day, rendered line by line.
pub fn render_day(r: &DayReview) -> String {
    let mut out = String::new();
    // Header.
    let mut head = format!(" Day {}", r.date);
    if let Some(loc) = &r.loc {
        let _ = write!(head, " · {loc}");
    }
    let _ = write!(head, " · {}/{} blocks", r.blocks_done, r.budget);
    let _ = write!(head, " · load {:.1}", r.load);
    if let Some((from, to)) = r.window {
        let _ = write!(
            head,
            " · window {}–{}",
            from.format("%H:%M"),
            to.format("%H:%M")
        );
    }
    let _ = write!(head, " · lost {}", fmt_lost(r.lost_min));
    if let Some(note) = &r.lost_note {
        let _ = write!(head, " ({note})");
    }
    let _ = write!(head, " · leak {}m", r.leak.total_min);
    let _ = write!(head, " · adherence {}", fmt_pct(r.adherence.started_pct));
    let _ = writeln!(out, "{head}");

    // done / demoted / underused / replans.
    let done = join_or(
        &r.done.iter().map(|i| i.to_string()).collect::<Vec<_>>(),
        " ",
        "-",
    );
    let demoted = join_or(
        &r.demoted
            .iter()
            .map(|d| {
                format!(
                    "{} ({} → {})",
                    d.id,
                    fmt_blocks_min(d.est_min, r.block_len_min),
                    d.to
                )
            })
            .collect::<Vec<_>>(),
        " ",
        "-",
    );
    let _ = writeln!(
        out,
        " {:<9} {}    demoted  {}    underused {}    replans {} · drift {}m",
        "done", done, demoted, r.mix.underused, r.replans, r.drift_min
    );

    // energy.
    let preds: Vec<String> = r.energy.hours.iter().map(|h| h.pred.to_string()).collect();
    let reps: Vec<String> = r
        .energy
        .hours
        .iter()
        .map(|h| h.rep.map_or_else(|| "·".to_string(), |v| v.to_string()))
        .collect();
    let mut energy_row = format!(
        " {:<9} pred {}   rep {}    MAE {:.1}  bias {}",
        "energy",
        preds.join(" "),
        reps.join(" "),
        r.energy.mae,
        fmt_signed(r.energy.bias)
    );
    if let Some(h) = r.energy.flip_hour {
        let _ = write!(energy_row, " after {h:02}:00");
    }
    let _ = writeln!(out, "{energy_row}");

    // estimates.
    let estimates: Vec<String> = r
        .estimates
        .iter()
        .filter(|t| t.tag != energy::DEFAULT_TAG)
        .map(|t| {
            format!(
                "{} ×{} (n={})",
                t.tag,
                energy::fmt_multiplier(t.multiplier),
                t.n
            )
        })
        .collect();
    let _ = writeln!(
        out,
        " {:<9} {}",
        "estimates",
        join_or(&estimates, "   ", "-")
    );

    // breaks.
    let mut planned: BTreeMap<u32, usize> = BTreeMap::new();
    for b in &r.breaks.breaks {
        *planned.entry(b.planned_min).or_insert(0) += 1;
    }
    let planned_txt = join_or(
        &planned
            .iter()
            .rev()
            .map(|(min, n)| format!("{min}m ×{n}"))
            .collect::<Vec<_>>(),
        " ",
        "none",
    );
    let actual_txt = join_or(
        &r.breaks
            .breaks
            .iter()
            .map(|b| match &b.place {
                Some(p) => format!("{} ({p})", b.actual_min),
                None => b.actual_min.to_string(),
            })
            .collect::<Vec<_>>(),
        " ",
        "-",
    );
    let _ = writeln!(
        out,
        " {:<9} planned {} · actual {} · rest debt {}",
        "breaks", planned_txt, actual_txt, r.rest_debt_min
    );

    // sleep.
    let mut sleep = match r.slept_min {
        Some(m) => fmt_hm(m),
        None => "-".to_string(),
    };
    if let Some(onset) = r.onset_min {
        let _ = write!(sleep, " · onset {onset}m");
    }
    let _ = writeln!(out, " {:<9} {}", "sleep", sleep);

    // tomorrow.
    let tomorrow: Vec<String> = r
        .tomorrow
        .iter()
        .enumerate()
        .map(|(i, c)| match (i, &c.note) {
            (0, Some(note)) => format!("first candidate {} ({note})", c.id),
            (0, None) => format!("first candidate {}", c.id),
            (_, Some(note)) => format!("{} {note}", c.id),
            (_, None) => c.id.to_string(),
        })
        .collect();
    let _ = writeln!(out, " {:<9} {}", "tomorrow", join_or(&tomorrow, " · ", "-"));
    out
}

// ---------------------------------------------------------------------------
// Week review (§11, §12.4)
// ---------------------------------------------------------------------------

/// What a heat-grid cell counts (§12.1's day-bar colours).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum Style {
    /// Working on an item.
    Block,
    /// A break.
    Break,
    /// A routine instance.
    Routine,
    /// An interruption.
    Interrupt,
    /// A paused timer.
    Pause,
    /// An idle gap attributed to `leak`.
    Leak,
    /// An idle gap attributed to anything else.
    Idle,
}

impl Style {
    /// The index of this style in a heat-grid cell.
    pub fn index(self) -> usize {
        match self {
            Style::Block => 0,
            Style::Break => 1,
            Style::Routine => 2,
            Style::Interrupt => 3,
            Style::Pause => 4,
            Style::Leak => 5,
            Style::Idle => 6,
        }
    }

    /// Every style, in index order.
    pub fn all() -> [Style; HEAT_STYLES] {
        [
            Style::Block,
            Style::Break,
            Style::Routine,
            Style::Interrupt,
            Style::Pause,
            Style::Leak,
            Style::Idle,
        ]
    }

    /// A short label for the week review.
    pub fn label(self) -> &'static str {
        match self {
            Style::Block => "block",
            Style::Break => "break",
            Style::Routine => "routine",
            Style::Interrupt => "interrupt",
            Style::Pause => "pause",
            Style::Leak => "leak",
            Style::Idle => "idle",
        }
    }

    fn of(kind: &SegmentKind) -> Style {
        match kind {
            SegmentKind::Block { .. } => Style::Block,
            SegmentKind::Break { .. } => Style::Break,
            SegmentKind::Routine { .. } => Style::Routine,
            SegmentKind::Interrupt { .. } => Style::Interrupt,
            SegmentKind::Pause { .. } => Style::Pause,
            SegmentKind::Idle { attributed } if attributed == "leak" => Style::Leak,
            SegmentKind::Idle { .. } => Style::Idle,
        }
    }
}

/// One day of the §11 week heat grid: minutes by style for each of the 24
/// clock hours, for the TUI to draw as a day bar.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct DayHeat {
    /// The day.
    pub date: NaiveDate,
    /// [`HEAT_HOURS`] cells of [`HEAT_STYLES`] minute counts.
    pub hours: Vec<[u32; HEAT_STYLES]>,
    /// Blocks finished that day.
    pub blocks_done: u32,
    /// Σ block minutes.
    pub block_min: u32,
}

impl DayHeat {
    /// Σ minutes of one style over the day.
    pub fn total(&self, style: Style) -> u32 {
        self.hours
            .iter()
            .fold(0u32, |a, h| a.saturating_add(h[style.index()]))
    }
}

fn heat_of(day: Option<&DayReplay>, date: NaiveDate, tz: Tz) -> DayHeat {
    let mut hours = vec![[0u32; HEAT_STYLES]; HEAT_HOURS];
    if let Some(day) = day {
        for seg in &day.segments {
            let (start, end) = (seg.start.with_timezone(&tz), seg.end.with_timezone(&tz));
            if end <= start {
                continue;
            }
            let style = Style::of(&seg.kind).index();
            let mut cursor = start;
            while cursor < end {
                let hour = cursor.hour() as usize;
                // The top of the next wall-clock hour, in absolute time: a
                // DST fall-back repeats an hour (so the same cell is filled
                // twice) and a spring-forward skips one.
                let next = hour_start(cursor) + Duration::hours(1);
                let stop = next.max(cursor).min(end);
                let min = stop.signed_duration_since(cursor).num_minutes().max(0) as u32;
                if let Some(cell) = hours.get_mut(hour) {
                    cell[style] = cell[style].saturating_add(min);
                }
                if stop <= cursor {
                    break;
                }
                cursor = stop;
            }
        }
    }
    DayHeat {
        date,
        hours,
        blocks_done: day.map_or(0, |d| d.blocks_done),
        block_min: day.map_or(0, |d| d.block_min),
    }
}

/// §11 lounge rate: `P(lounge | wake hour)` and the current streak.
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
pub struct LoungeRate {
    /// `(wake hour, days, share in the lounge)`.
    pub by_wake_hour: Vec<(u32, usize, f64)>,
    /// Days spent in the lounge over days with a location.
    pub overall: Option<f64>,
    /// Consecutive most recent days in the lounge.
    pub streak: u32,
}

/// One row of §11's sleep panel: what was slept, how long it took to fall
/// asleep, and the blocks that followed — display only, never an input.
#[derive(Clone, Copy, Debug, PartialEq, Serialize)]
pub struct SleepRow {
    /// The night's day.
    pub date: NaiveDate,
    /// Minutes slept.
    pub slept_min: Option<u32>,
    /// Sleep onset.
    pub onset_min: Option<u32>,
    /// Blocks done that day.
    pub blocks_done: u32,
}

/// §11 "prior vs learned curve overlay": one energy curve, both ways.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct CurveOverlay {
    /// Curve name (`lounge`, `home`).
    pub curve: String,
    /// The config prior, per `floor(hsw)` bucket.
    pub prior: Vec<u8>,
    /// The learned curve, when the model has one.
    pub learned: Option<Vec<u8>>,
}

/// One item with repeated demotion stamps (§11 demotion churn).
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct ChurnRow {
    /// The item.
    pub id: Id,
    /// Its stamps, in order.
    pub stamps: Vec<Stamp>,
}

/// The parameters of [`week_review`] that come from outside the log.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct WeekExtras {
    /// The week file's `budget:` front matter, in blocks.
    pub budget_blocks: Option<u32>,
    /// Planned blocks, when the caller has a better number than Σ
    /// `remaining` over the week's top-level items.
    pub planned_blocks: Option<f64>,
    /// [`crate::priority::deadline_health`] for the week.
    pub deadline_health: Option<DeadlineHealth>,
}

/// Everything the §12.4 week review adds to the day review.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct WeekReview {
    /// The week.
    pub week: IsoWeek,
    /// Milestones finished.
    pub hit: Vec<Id>,
    /// Milestones demoted out of the week.
    pub demoted: Vec<Id>,
    /// `(date, blocks done)` for the seven days.
    pub blocks_per_day: Vec<(NaiveDate, u32)>,
    /// Blocks finished over the week.
    pub blocks_done: u32,
    /// Σ block minutes over the week.
    pub block_min: u32,
    /// §11 load over the week.
    pub load: f64,
    /// `cfg.day.block_min`.
    pub block_len_min: u32,
    /// The heat grid: seven [`DayHeat`] rows.
    pub heat: Vec<DayHeat>,
    /// §11 energy mix over the week, against the sum of the days' block
    /// budgets (`underused` is a day-level parameter and stays 0 here).
    pub mix: EnergyMix,
    /// §11 break integrity over the week — the `where` histogram §11 asks for.
    pub breaks: BreakIntegrity,
    /// §11 start latency per day: `(date, wake → arrive, arrive → first
    /// start)` in minutes, for the days that have both.
    pub latency: Vec<(NaiveDate, Option<i64>, Option<i64>)>,
    /// §11 sleep panel: one row per day.
    pub sleep: Vec<SleepRow>,
    /// Lounge rate.
    pub lounge: LoungeRate,
    /// `(date, n, MAE)` per day — the energy calibration trend.
    pub mae_per_day: Vec<(NaiveDate, usize, f64)>,
    /// Estimate multipliers per tag over the log up to the week's end.
    pub estimates: Vec<TagStats>,
    /// Prior versus learned curves.
    pub curves: Vec<CurveOverlay>,
    /// Blocks planned into the week.
    pub planned_blocks: f64,
    /// The week's block budget.
    pub budget_blocks: Option<u32>,
    /// `planned / (budget × plan_ratio)`; §11 warns above 1.1.
    pub plan_honesty: Option<f64>,
    /// Deadline health (a parameter).
    pub deadline_health: Option<DeadlineHealth>,
    /// Items with at least [`CUT_STAMPS`] stamps.
    pub churn: Vec<ChurnRow>,
    /// Minutes demoted *into* this week (carried from the week before).
    pub carry_in_min: u32,
    /// Minutes demoted *out of* this week.
    pub carry_out_min: u32,
}

/// The §12.4 week review (§11's week-surfaced monitors).
pub fn week_review(
    tree: &Tree,
    replay: &Replay,
    cfg: &Config,
    model: &Model,
    week: IsoWeek,
    tz: Tz,
    extras: &WeekExtras,
) -> WeekReview {
    let dates = week.dates();
    let days: Vec<Option<&DayReplay>> = dates.iter().map(|d| replay.day(*d)).collect();

    let block_len = cfg.block_min().max(1);
    let mut blocks_done = 0u32;
    let mut block_min = 0u32;
    let mut budget_min = 0u32;
    let mut mae_per_day = Vec::new();
    let mut week_breaks: Vec<BreakRecord> = Vec::new();
    let (mix_by_ci, load) = mix_and_load(days.iter().flatten().copied(), tree);
    for (date, day) in dates.iter().zip(&days) {
        let Some(day) = day else { continue };
        blocks_done = blocks_done.saturating_add(day.blocks_done);
        block_min = block_min.saturating_add(day.block_min);
        // The week's budget for §11's energy-mix share: the days the log
        // knows about, each with the budget its `arrive` set (§8.1's formula
        // when it has none). A day with no log at all counts for nothing.
        budget_min = budget_min.saturating_add(
            day.budget
                .unwrap_or_else(|| crate::capacity::budget_blocks(cfg))
                .saturating_mul(block_len),
        );
        week_breaks.extend(day.breaks.iter().cloned());
        let obs: Vec<log::EnergyObs> = replay
            .energy
            .iter()
            .filter(|o| o.day == *date)
            .cloned()
            .collect();
        if !obs.is_empty() {
            let c = energy::calibration(cfg, &obs);
            mae_per_day.push((*date, c.n, c.mae));
        }
    }

    // Milestones: the week file's top-level items (a child of another week
    // item is a task, not a milestone).
    let key = week.to_string();
    let (mut hit, mut demoted) = (Vec::new(), Vec::new());
    let mut planned_min = 0u32;
    for item in tree.week_items(week) {
        let id = Tree::key_of(item);
        if tree
            .parent(&id)
            .is_some_and(|p| tree.get(p).is_some_and(|i| i.horizon == Horizon::Week(week)))
        {
            continue;
        }
        planned_min = planned_min.saturating_add(tree.remaining(&id).unwrap_or(0));
        if item.state == State::Done || replay.is_done(id.as_str()) {
            hit.push(id);
        } else if item.state == State::Demoted
            || replay
                .demotions
                .get(id.as_str())
                .is_some_and(|ds| ds.iter().any(|d| d.from == key))
        {
            demoted.push(id);
        }
    }

    let planned_blocks = extras
        .planned_blocks
        .unwrap_or(planned_min as f64 / block_len as f64);
    let plan_honesty = extras.budget_blocks.and_then(|b| {
        let realistic = b as f64 * cfg.week.plan_ratio;
        (realistic > 0.0).then(|| round2(planned_blocks / realistic))
    });

    let prev = week.prev().to_string();
    let (mut carry_in, mut carry_out) = (0u32, 0u32);
    for d in replay.demotions.values().flatten() {
        if d.from == prev {
            carry_in = carry_in.saturating_add(d.est_min);
        }
        if d.from == key {
            carry_out = carry_out.saturating_add(d.est_min);
        }
    }

    let prior = Model::from_config(cfg);
    let curves = prior
        .energy
        .iter()
        .map(|(curve, levels)| CurveOverlay {
            curve: curve.clone(),
            prior: levels.clone(),
            learned: model.energy.get(curve).cloned(),
        })
        .collect();

    WeekReview {
        week,
        hit,
        demoted,
        blocks_per_day: dates
            .iter()
            .zip(&days)
            .map(|(d, day)| (*d, day.map_or(0, |x| x.blocks_done)))
            .collect(),
        blocks_done,
        block_min,
        load: round1(load),
        block_len_min: block_len,
        heat: dates
            .iter()
            .zip(&days)
            .map(|(d, day)| heat_of(*day, *d, tz))
            .collect(),
        mix: energy_mix(mix_by_ci, budget_min, 0),
        breaks: break_integrity(&week_breaks),
        latency: dates
            .iter()
            .zip(&days)
            .map(|(d, day)| {
                (
                    *d,
                    day.and_then(|x| x.wake_to_arrive_min()),
                    day.and_then(|x| x.arrive_to_start_min()),
                )
            })
            .collect(),
        sleep: dates
            .iter()
            .zip(&days)
            .map(|(d, day)| SleepRow {
                date: *d,
                slept_min: day.and_then(|x| x.slept_min),
                onset_min: day.and_then(|x| x.onset_min),
                blocks_done: day.map_or(0, |x| x.blocks_done),
            })
            .collect(),
        lounge: lounge_rate(replay, week),
        mae_per_day,
        estimates: energy::estimate_calibration(cfg, &replay.durations, week.sunday()),
        curves,
        planned_blocks: round2(planned_blocks),
        budget_blocks: extras.budget_blocks,
        plan_honesty,
        deadline_health: extras.deadline_health,
        churn: churn_rows(tree, CUT_STAMPS),
        carry_in_min: carry_in,
        carry_out_min: carry_out,
    }
}

fn churn_rows(tree: &Tree, min: usize) -> Vec<ChurnRow> {
    horizon::churn(tree, min)
        .into_iter()
        .map(|(id, stamps)| ChurnRow { id, stamps })
        .collect()
}

/// §11 lounge rate: `P(lounge | wake hour)` over every day the replay has a
/// location for, plus the streak of consecutive lounge days ending at (or
/// before) the end of `week`.
fn lounge_rate(replay: &Replay, week: IsoWeek) -> LoungeRate {
    let mut by_hour: BTreeMap<u32, (usize, usize)> = BTreeMap::new();
    let (mut lounge, mut total) = (0usize, 0usize);
    let mut streak = 0u32;
    let end = week.sunday();
    for day in replay.days.values() {
        let Some(loc) = day.loc.as_deref() else {
            continue;
        };
        let is_lounge = loc == "lounge";
        total += 1;
        if is_lounge {
            lounge += 1;
        }
        if let Some(wake) = day.wake {
            let e = by_hour.entry(wake.hour()).or_insert((0, 0));
            e.0 += 1;
            if is_lounge {
                e.1 += 1;
            }
        }
        if day.date <= end {
            streak = if is_lounge { streak + 1 } else { 0 };
        }
    }
    LoungeRate {
        by_wake_hour: by_hour
            .into_iter()
            .map(|(h, (n, l))| (h, n, round2(l as f64 / n as f64)))
            .collect(),
        overall: (total > 0).then(|| round2(lounge as f64 / total as f64)),
        streak,
    }
}

/// The §12.4 week review, rendered.
pub fn render_week(r: &WeekReview) -> String {
    let mut out = String::new();
    let mut head = format!(" Week {} · {} blocks", r.week, r.blocks_done);
    if let Some(b) = r.budget_blocks {
        let _ = write!(head, " / {b}");
    }
    let _ = write!(head, " · load {:.1}", r.load);
    let _ = write!(head, " · planned {:.1}b", r.planned_blocks);
    if let Some(h) = r.plan_honesty {
        let _ = write!(head, " · honesty {h:.2}");
    }
    let _ = writeln!(out, "{head}");

    let ids = |v: &[Id]| join_or(&v.iter().map(|i| i.to_string()).collect::<Vec<_>>(), " ", "-");
    let _ = writeln!(
        out,
        " {:<9} hit {} · demoted {}",
        "milestone",
        ids(&r.hit),
        ids(&r.demoted)
    );

    let blocks: Vec<String> = r
        .blocks_per_day
        .iter()
        .map(|(d, n)| format!("{} {}", d.format("%a"), n))
        .collect();
    let _ = writeln!(out, " {:<9} {}", "blocks", join_or(&blocks, " · ", "-"));

    let totals: Vec<String> = Style::all()
        .iter()
        .filter_map(|s| {
            let min: u32 = r.heat.iter().fold(0u32, |a, d| a.saturating_add(d.total(*s)));
            (min > 0).then(|| format!("{} {}", s.label(), fmt_hm(min)))
        })
        .collect();
    let _ = writeln!(
        out,
        " {:<9} {} days × {}h · {}",
        "heat",
        r.heat.len(),
        HEAT_HOURS,
        join_or(&totals, " · ", "-")
    );

    let mut lounge = match r.lounge.overall {
        Some(p) => format!("{}%", (p * 100.0).round() as i64),
        None => "-".to_string(),
    };
    let _ = write!(lounge, " · streak {}", r.lounge.streak);
    for (hour, n, p) in &r.lounge.by_wake_hour {
        let _ = write!(lounge, " · wake {hour:02} {:.2} ({n})", p);
    }
    let _ = writeln!(out, " {:<9} {}", "lounge", lounge);

    let mix: Vec<String> = r
        .mix
        .minutes_by_ci
        .iter()
        .enumerate()
        .rev()
        .filter(|(_, m)| **m > 0)
        .map(|(ci, m)| format!("ci{ci} {}", fmt_hm(*m)))
        .collect();
    let _ = writeln!(
        out,
        " {:<9} {} · ≥4 {}",
        "mix",
        join_or(&mix, " · ", "-"),
        fmt_pct(r.mix.high_share)
    );

    let places: Vec<String> = r
        .breaks
        .by_where
        .iter()
        .map(|(place, (n, min))| format!("{place} {n} ({})", fmt_hm(*min)))
        .collect();
    let _ = writeln!(
        out,
        " {:<9} planned {} · actual {} · over {} · {}",
        "breaks",
        fmt_hm(r.breaks.planned_min),
        fmt_hm(r.breaks.actual_min),
        r.breaks.over_count,
        join_or(&places, " · ", "-")
    );

    let sleep: Vec<String> = r
        .sleep
        .iter()
        .map(|s| match s.slept_min {
            Some(m) => format!("{} {} ({}b)", s.date.format("%a"), fmt_hm(m), s.blocks_done),
            None => format!("{} -", s.date.format("%a")),
        })
        .collect();
    let _ = writeln!(out, " {:<9} {}", "sleep", join_or(&sleep, " · ", "-"));

    let latency: Vec<String> = r
        .latency
        .iter()
        .filter_map(|(d, wake, start)| {
            let (wake, start) = (wake.as_ref()?, start.as_ref()?);
            Some(format!("{} {wake}/{start}", d.format("%a")))
        })
        .collect();
    let _ = writeln!(out, " {:<9} {}", "latency", join_or(&latency, " · ", "-"));

    let maes: Vec<String> = r
        .mae_per_day
        .iter()
        .map(|(d, _, mae)| format!("{} {mae:.1}", d.format("%a")))
        .collect();
    let _ = writeln!(out, " {:<9} MAE {}", "energy", join_or(&maes, " · ", "-"));

    let estimates: Vec<String> = r
        .estimates
        .iter()
        .filter(|t| t.tag != energy::DEFAULT_TAG)
        .map(|t| {
            format!(
                "{} ×{} (n={})",
                t.tag,
                energy::fmt_multiplier(t.multiplier),
                t.n
            )
        })
        .collect();
    let _ = writeln!(
        out,
        " {:<9} {}",
        "estimates",
        join_or(&estimates, "   ", "-")
    );

    for c in &r.curves {
        let cells = |v: &[u8]| {
            v.iter()
                .map(u8::to_string)
                .collect::<Vec<_>>()
                .join(" ")
        };
        let learned = match &c.learned {
            Some(l) => cells(l),
            None => "-".to_string(),
        };
        let _ = writeln!(
            out,
            " {:<9} {} prior {} · learned {}",
            "curve",
            c.curve,
            cells(&c.prior),
            learned
        );
    }

    if let Some(h) = r.deadline_health {
        let slack = h
            .min_slack_days
            .map_or_else(|| "-".to_string(), |s| format!("{s:.1}d"));
        let _ = writeln!(
            out,
            " {:<9} min slack {} · hot {} · impossible {} · overdue {}",
            "deadlines", slack, h.hot, h.impossible, h.overdue
        );
    }

    let churn: Vec<String> = r
        .churn
        .iter()
        .map(|c| {
            format!(
                "{} ({})",
                c.id,
                c.stamps
                    .iter()
                    .map(Stamp::to_string)
                    .collect::<Vec<_>>()
                    .join(",")
            )
        })
        .collect();
    let _ = writeln!(
        out,
        " {:<9} {} · carry in {} · out {}",
        "churn",
        join_or(&churn, " · ", "-"),
        fmt_blocks_min(r.carry_in_min, r.block_len_min),
        fmt_blocks_min(r.carry_out_min, r.block_len_min)
    );
    out
}

// ---------------------------------------------------------------------------
// Month review (§6.3, §11, §12.4)
// ---------------------------------------------------------------------------

/// One month outcome (§4.3's `# Outcomes`).
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct OutcomeRow {
    /// The outcome.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// Explicit `!k` on the root (§7.1).
    pub k: u8,
    /// Finished.
    pub done: bool,
    /// Logged minutes over planned minutes (§6.4), when both are known.
    pub progress: Option<f64>,
}

/// The parameters of [`month_review`] that come from outside the log.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MonthExtras {
    /// Stamps that put an item on the cut list (§6.3: "≥ 2 stamps ⇒ cut or
    /// re-scope").
    pub cut_stamps: usize,
}

impl Default for MonthExtras {
    fn default() -> MonthExtras {
        MonthExtras {
            cut_stamps: CUT_STAMPS,
        }
    }
}

/// Everything the §12.4 month review adds.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct MonthReview {
    /// The month.
    pub month: YearMonth,
    /// `cfg.day.block_min`.
    pub block_len_min: u32,
    /// Outcomes, in file order.
    pub outcomes: Vec<OutcomeRow>,
    /// Of those, finished.
    pub done_count: usize,
    /// Items in the month's `# Demoted` section.
    pub demoted: Vec<Id>,
    /// Items with at least `cut_stamps` stamps.
    pub churn: Vec<ChurnRow>,
    /// `(week key, minutes demoted out of it)` for the weeks that fed this
    /// month, ascending (`("2026-W36", 300)`).
    pub carry_over: Vec<(String, u32)>,
    /// The proposed cut list: the churned items, most stamped first.
    pub cuts: Vec<Id>,
}

/// The §12.4 month review: outcomes done and not, demotion churn, carry-over
/// week over week and the proposed cut list (§6.3).
pub fn month_review(
    tree: &Tree,
    replay: &Replay,
    cfg: &Config,
    month: YearMonth,
    tz: Tz,
    extras: &MonthExtras,
) -> MonthReview {
    let done_map: HashMap<Id, u32> = replay.done_minutes_map();
    let mut outcomes = Vec::new();
    let mut demoted = Vec::new();
    for item in tree.month_items(month) {
        let id = Tree::key_of(item);
        if item.src.section.as_deref() == Some("Demoted") || item.state == State::Demoted {
            demoted.push(id);
            continue;
        }
        let done = item.state == State::Done || replay.is_done(id.as_str());
        outcomes.push(OutcomeRow {
            id: id.clone(),
            title: item.title.clone(),
            k: tree.root_priority(&id),
            done,
            progress: tree.progress(&id, &done_map).map(round2),
        });
    }
    let done_count = outcomes.iter().filter(|o| o.done).count();

    let mut carry: BTreeMap<String, u32> = BTreeMap::new();
    for d in replay.demotions.values().flatten() {
        let date = d.t.with_timezone(&tz).date_naive();
        if !month.contains(date) {
            continue;
        }
        if matches!(d.stamp, Some(Stamp::Week(_))) {
            let e = carry.entry(d.from.clone()).or_insert(0);
            *e = e.saturating_add(d.est_min);
        }
    }

    let churn = churn_rows(tree, extras.cut_stamps);
    MonthReview {
        month,
        block_len_min: cfg.block_min().max(1),
        outcomes,
        done_count,
        demoted,
        cuts: churn.iter().map(|c| c.id.clone()).collect(),
        churn,
        carry_over: carry.into_iter().collect(),
    }
}

/// The §12.4 month review, rendered.
pub fn render_month(r: &MonthReview) -> String {
    let mut out = String::new();
    let carry_total: u32 = r.carry_over.iter().fold(0u32, |a, (_, m)| a + m);
    let _ = writeln!(
        out,
        " Month {} · outcomes {}/{} · carry-over {}",
        r.month,
        r.done_count,
        r.outcomes.len(),
        fmt_blocks_min(carry_total, r.block_len_min)
    );
    let outcomes: Vec<String> = r
        .outcomes
        .iter()
        .map(|o| {
            let mark = if o.done { "✓" } else { "○" };
            match o.progress {
                Some(p) => format!("{mark} !{} {} {}%", o.k, o.id, (p * 100.0).round() as i64),
                None => format!("{mark} !{} {}", o.k, o.id),
            }
        })
        .collect();
    let _ = writeln!(
        out,
        " {:<9} {}",
        "outcomes",
        join_or(&outcomes, " · ", "-")
    );
    let churn: Vec<String> = r
        .churn
        .iter()
        .map(|c| {
            format!(
                "{} ({})",
                c.id,
                c.stamps
                    .iter()
                    .map(Stamp::to_string)
                    .collect::<Vec<_>>()
                    .join(",")
            )
        })
        .collect();
    let _ = writeln!(out, " {:<9} {}", "churn", join_or(&churn, " · ", "-"));
    let carry: Vec<String> = r
        .carry_over
        .iter()
        .map(|(w, m)| format!("{w} {}", fmt_blocks_min(*m, r.block_len_min)))
        .collect();
    let _ = writeln!(out, " {:<9} {}", "carry", join_or(&carry, " · ", "-"));
    let cuts = join_or(
        &r.cuts.iter().map(|i| i.to_string()).collect::<Vec<_>>(),
        " · ",
        "-",
    );
    let _ = writeln!(out, " {:<9} {}", "cuts", cuts);
    out
}

// ---------------------------------------------------------------------------
// Writing the review into the day file (§6.3, §13 `tm review --write`)
// ---------------------------------------------------------------------------

/// Put `text` into the day file's `<!-- tm:review start --> … <!-- tm:review
/// end -->` block (§1.3: generated sections are replaced whole; text outside
/// the markers is never touched).
///
/// [`horizon::close_day`] leaves that block behind with a
/// [`placeholder`](crate::horizon::REVIEW_PLACEHOLDER) body, so the usual
/// path is a replacement. When the block is missing it is appended at the end
/// of the file — below `## Notes`, which is where a review belongs — and when
/// the day file itself is missing it is created with its front matter.
pub fn write_day_review(store: &dyn Store, date: NaiveDate, text: &str) -> Result<(), ReviewError> {
    let path = Horizon::Day(date).path();
    store.ensure_horizon_file(&Horizon::Day(date))?;
    let body = text.to_string();
    store.modify_file(&path, &mut |parsed: &ParsedFile| {
        if parsed.generated(REVIEW_BLOCK).is_some() {
            return Ok(Some(edit::replace_generated(
                parsed,
                REVIEW_BLOCK,
                None,
                &body,
            )));
        }
        let mut out = parsed.to_text();
        while !out.is_empty() && !out.ends_with("\n\n") {
            out.push('\n');
        }
        out.push_str(&edit::start_marker(REVIEW_BLOCK, None));
        out.push('\n');
        for line in body.trim_end_matches('\n').split('\n') {
            out.push_str(line);
            out.push('\n');
        }
        out.push_str(&edit::end_marker(REVIEW_BLOCK));
        out.push('\n');
        Ok(Some(out))
    })?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn durations_format_the_way_the_spec_writes_them() {
        assert_eq!(fmt_hm(490), "8h10m");
        assert_eq!(fmt_hm(120), "2h");
        assert_eq!(fmt_hm(45), "45m");
        assert_eq!(fmt_hm(0), "0m");
        assert_eq!(fmt_blocks_min(360, 60), "6b");
        assert_eq!(fmt_blocks_min(30, 60), "0.5b");
        assert_eq!(fmt_blocks_min(155, 60), "2.6b");
        assert_eq!(fmt_blocks_min(20, 60), "20m");
    }

    #[test]
    fn percentages_round_to_the_nearest_whole() {
        assert_eq!(pct(5, 6), Some(83));
        assert_eq!(pct(1, 2), Some(50));
        assert_eq!(pct(0, 0), None);
        assert_eq!(fmt_pct(None), "-");
        assert_eq!(fmt_signed(-0.3), "−0.3");
        assert_eq!(fmt_signed(0.25), "0.2");
    }

    #[test]
    fn the_bias_flip_hour_is_the_first_lasting_change_of_sign() {
        let rows = |rows: &[(u32, f64)]| -> Vec<(u32, usize, f64, f64)> {
            rows.iter().map(|(h, b)| (*h, 1, b.abs(), *b)).collect()
        };
        assert_eq!(
            flip_hour(&rows(&[(7, 0.0), (8, 1.0), (12, 0.0), (13, -1.0), (14, -1.0)])),
            Some(13)
        );
        // The original sign comes back: no single flip.
        assert_eq!(flip_hour(&rows(&[(8, 1.0), (13, -1.0), (15, 1.0)])), None);
        // Never changes sign.
        assert_eq!(flip_hour(&rows(&[(8, -1.0), (13, -1.0)])), None);
        assert_eq!(flip_hour(&rows(&[])), None);
        // The rows are in the day's order, not the clock's: a wake-to-wake
        // day that crosses midnight flips after 02:00, not after 20:00.
        assert_eq!(flip_hour(&rows(&[(20, 1.0), (2, -1.0)])), Some(2));
    }

    #[test]
    fn the_hourly_rows_follow_the_day_across_midnight() {
        let cfg = Config::default();
        let obs = |t: &str, pred: u8, rep: u8| log::EnergyObs {
            t: DateTime::parse_from_rfc3339(t).unwrap(),
            day: NaiveDate::from_ymd_opt(2026, 6, 1).unwrap(),
            pred,
            rep,
            hsw: 0.0,
            loc: "lounge".to_string(),
            slept_min: None,
            went: None,
            id: None,
            from_start: false,
        };
        let obs = vec![
            obs("2026-06-02T02:00:00-05:00", 3, 2),
            obs("2026-06-01T20:00:00-05:00", 3, 4),
        ];
        let calib = energy::calibration(&cfg, &obs);
        // `calibration` keys by clock hour, so its own order is 2 then 20.
        assert_eq!(
            calib.by_hour.iter().map(|r| r.0).collect::<Vec<_>>(),
            vec![2, 20]
        );
        let rows = by_hour_in_day_order(&calib, &obs, cfg.tz);
        assert_eq!(rows.iter().map(|r| r.0).collect::<Vec<_>>(), vec![20, 2]);
    }

    #[test]
    fn the_top_of_the_hour_is_defined_through_a_dst_fall_back() {
        let tz = chrono_tz::America::Chicago;
        // 01:30 CST on the fall-back day is the ambiguous hour: chrono's
        // `with_minute(0)` gives `None` there, `hour_start` does not.
        let t = DateTime::parse_from_rfc3339("2026-11-01T01:30:00-06:00")
            .unwrap()
            .with_timezone(&tz);
        assert!(t.with_minute(0).is_none());
        assert_eq!(
            hour_start(t).to_rfc3339(),
            "2026-11-01T01:00:00-06:00".to_string()
        );
        assert_eq!(
            (hour_start(t) + Duration::hours(1)).to_rfc3339(),
            "2026-11-01T02:00:00-06:00".to_string()
        );
    }
}
