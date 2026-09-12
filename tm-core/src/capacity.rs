//! Capacity — tm-spec-v1.md §8.1 (window and budget), §8.2 step 3 (cutting
//! free time into slots with breaks and energising them) and §8.4 (the week
//! lookahead the EDF pass in `priority.rs` and `tm plan --week` consume).
//!
//! Everything here is pure: instants are `DateTime<Tz>` in `config.tz`
//! (never naive, so a DST day is right), and `now`/`today` are parameters.
//!
//! # API overview
//!
//! * [`window_and_budget`]`(arrival, walls_today, cfg) -> (end, blocks)` —
//!   §8.1: `end = min(arrival + window_hours, window_cap) + Σ wall minutes
//!   inside [arrival, end]` (a fixed point, since extending the window can
//!   pull in another wall; solved exactly, see the function), `budget =
//!   floor(window_hours × 60 / block_min × budget_ratio)` (8 h → 6).
//!   [`remaining_budget`] subtracts the blocks already done.
//! * [`cut_slots`]`(from, end, walls, cfg) -> `[`Cut`] — §8.2 step 3: the
//!   free time between walls cut into `block_min` blocks with a `break_min`
//!   break after every `break_after_blocks` blocks. The [`Cut`] carries both
//!   the [`Slot`]s and the [`Break`]s (the planner places both);
//!   [`Cut::timeline`] interleaves them. A stretch's last block may be short
//!   (≥ `min_last_block_min`, [`SlotKind::ShortBlock`]) or dropped.
//!   [`cut_slots_from`] takes the blocks already done since the last break;
//!   [`cut_slots_around`] also takes the *restful* occupied intervals (a
//!   placed lunch), which satisfy a pending break.
//! * [`energize`]`(slots, ctx)` — §8.2 step 3's second half: each slot gets
//!   [`energy::predict`] + the [`Posterior`] correction + the home cap
//!   (`min(energy, home_max_ci)` when the location is home and
//!   `--allow-home` was not given). The arguments live in [`EnergyCtx`].
//! * [`DayCapacity`]`{ date, minutes_at_level: [u32; 6] }` and
//!   [`lookahead`] — §8.4: today from the slots the planner already cut,
//!   future days from the expected arrival and location (learned, else
//!   `config.expected`), the calendar walls, the prior curve and the budget.
//!   [`available_until`] and [`reserve`] are the cumulative helpers §7.3's
//!   EDF pass uses; [`week_grid`] renders the grid for `tm plan --week`.
//! * [`local_dt`] resolves a local date + time in a zone (DST-safe);
//!   [`free_intervals`] and [`wall_minutes`] are the wall arithmetic §8.1
//!   and §8.2 are written in.
//!
//! # Interpretation notes (where the spec needed a decision)
//!
//! * **Breaks around walls.** A wall is work, so it does not reset the break
//!   counter: a break due when a wall ends is placed right after it. A
//!   *rest* passed to [`cut_slots_around`] does reset it — you have just
//!   rested. A break that would not fit before the next wall is dropped
//!   along with the rest of that stretch.
//! * **A stretch never ends on a break.** §8.2 orders a break "after every
//!   `break_after_blocks` blocks", i.e. between blocks. A break is therefore
//!   placed only when a block (full, or short ≥ `min_last_block_min`) still
//!   fits after it; otherwise the stretch simply ends and the tail is left
//!   free. Without that rule a day could end on a 20 m rest that rests
//!   nobody, and [`Cut::break_minutes`] would over-report planned rest to
//!   §11's rest-debt monitor.
//! * **Short blocks.** §8.2 says "the last block may be short (≥ 30 m) or
//!   dropped". The same rule is applied at the end of *every* free stretch,
//!   not only at the end of the day — a wall ends a stretch exactly as the
//!   window end does.
//! * **The §4.3 timeline.** `cut_slots` alone cannot reproduce the printed
//!   day file: step 2 has already placed the routines (lunch at 11:20 there)
//!   before step 3 cuts what is left. With only the 12:50–13:50 wall the cut
//!   is 07:00, 08:00, break 09:00, 09:20, 10:20, break 11:20, 11:40 (12:40
//!   → 12:50 is 10 m and is dropped), wall, 13:50, break 14:50, 15:10–16:00
//!   short. Passing lunch to [`cut_slots_around`] as a rest gives the day
//!   file's midday: 10:20 block, lunch, then a full 11:50–12:50 block. The
//!   day file's afternoon (break at 13:50 after a single block) additionally
//!   implies that the 12:50 meeting counts towards break accrual; v1 does
//!   not model that, so the cut breaks at 14:50 instead.
//! * **Today in the lookahead** is taken from the slots handed in, exactly
//!   as they are: the planner knows whether it wants them limited to the
//!   remaining budget. Future days *are* limited to `budget × block_min`
//!   minutes, taking the highest-energy slots first (a day's best slots are
//!   the ones you actually spend).

use std::collections::BTreeMap;
use std::fmt::Write as _;

use chrono::{DateTime, Datelike, Duration, LocalResult, NaiveDate, NaiveTime, TimeZone};
use chrono_tz::Tz;
use serde::{Deserialize, Serialize};

use crate::config::Config;
use crate::energy::{self, Features, Model, Posterior};
use crate::model::Loc;

/// A blocked interval: an Interval instance (calendar event, exam, meeting,
/// interruption) the planner must flow around (§8.2 step 1).
pub type Wall = (DateTime<Tz>, DateTime<Tz>);

/// Walls grouped by the day they belong to, as the lookahead wants them.
pub type WallsByDate = BTreeMap<NaiveDate, Vec<Wall>>;

/// What a slot is: a full block, or the short remainder of a stretch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SlotKind {
    /// A full `block_min` block.
    Block,
    /// The short last block of a stretch (≥ `min_last_block_min`).
    ShortBlock,
}

/// One schedulable slot (§8.2 step 3).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Slot {
    /// Start instant.
    pub start: DateTime<Tz>,
    /// End instant.
    pub end: DateTime<Tz>,
    /// Predicted energy 0..=5 ([`energize`] fills it; [`cut_slots`] leaves 0).
    pub energy: u8,
    /// Full block or short remainder.
    pub kind: SlotKind,
}

impl Slot {
    /// Length in minutes.
    pub fn minutes(&self) -> u32 {
        (self.end - self.start).num_minutes().max(0) as u32
    }
    /// True when the slot can hold an item with this min-energy.
    pub fn fits(&self, ci: u8) -> bool {
        ci <= self.energy
    }
}

/// A planned break between slots (§8.2 step 3).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Break {
    /// Start instant.
    pub start: DateTime<Tz>,
    /// End instant.
    pub end: DateTime<Tz>,
}

impl Break {
    /// Length in minutes.
    pub fn minutes(&self) -> u32 {
        (self.end - self.start).num_minutes().max(0) as u32
    }
}

/// One entry of an interleaved timeline.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum SlotOrBreak {
    /// A slot.
    Slot(Slot),
    /// A break.
    Break(Break),
}

impl SlotOrBreak {
    /// Start instant.
    pub fn start(&self) -> DateTime<Tz> {
        match self {
            SlotOrBreak::Slot(s) => s.start,
            SlotOrBreak::Break(b) => b.start,
        }
    }
    /// End instant.
    pub fn end(&self) -> DateTime<Tz> {
        match self {
            SlotOrBreak::Slot(s) => s.end,
            SlotOrBreak::Break(b) => b.end,
        }
    }
}

/// The result of cutting free time: the slots and the breaks between them.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Cut {
    /// The slots, in time order.
    pub slots: Vec<Slot>,
    /// The breaks, in time order.
    pub breaks: Vec<Break>,
}

impl Cut {
    /// Slots and breaks interleaved, in time order.
    pub fn timeline(&self) -> Vec<SlotOrBreak> {
        let mut out: Vec<SlotOrBreak> = self
            .slots
            .iter()
            .map(|s| SlotOrBreak::Slot(*s))
            .chain(self.breaks.iter().map(|b| SlotOrBreak::Break(*b)))
            .collect();
        out.sort_by_key(|p| p.start());
        out
    }
    /// Σ slot minutes.
    pub fn slot_minutes(&self) -> u32 {
        self.slots.iter().map(|s| s.minutes()).sum()
    }
    /// Σ break minutes.
    pub fn break_minutes(&self) -> u32 {
        self.breaks.iter().map(|b| b.minutes()).sum()
    }
}

/// Local date + time in a zone, DST-safe: the earlier instant of an
/// ambiguous local time, and the first valid instant after a spring-forward
/// gap.
pub fn local_dt(tz: Tz, date: NaiveDate, time: NaiveTime) -> DateTime<Tz> {
    let naive = date.and_time(time);
    match tz.from_local_datetime(&naive) {
        LocalResult::Single(t) => t,
        LocalResult::Ambiguous(earliest, _) => earliest,
        LocalResult::None => {
            for m in 1..=180 {
                if let Some(t) = tz.from_local_datetime(&(naive + Duration::minutes(m))).earliest() {
                    return t;
                }
            }
            tz.from_utc_datetime(&naive)
        }
    }
}

// ---------------------------------------------------------------------------
// §8.1 window and budget
// ---------------------------------------------------------------------------

/// Σ minutes of the walls lying inside `[from, to)` (clipped and merged, so
/// overlapping walls are counted once).
pub fn wall_minutes(from: DateTime<Tz>, to: DateTime<Tz>, walls: &[Wall]) -> i64 {
    normalize_walls(from, to, walls)
        .iter()
        .map(|(a, b)| (*b - *a).num_minutes())
        .sum()
}

/// §8.1: the end of today's working window and the block budget.
///
/// `end = min(arrival + window_hours, window_cap today) + Σ wall minutes
/// inside [arrival, end]` — a fixed point, since extending the window pulls
/// in more wall minutes, which extend it further. It is solved exactly (not
/// by a capped iteration): the walls are clipped to start at the arrival,
/// merged, and walked in order, and a wall that has come inside the window
/// extends it by its *whole* remaining duration.
///
/// That is the least solution of the equation. A wall `[a, b)` that starts
/// before the current end contributes `b − a` in one step, because the
/// window must then reach at least `b`: writing `e' = e + (min(b, e') − a)`,
/// `e' = e + b − a` satisfies it (and `e' ≥ b` whenever `a ≤ e`). Walls are
/// sorted, so once one starts at or after the end, no later one can be
/// inside either and the walk stops.
///
/// The window never ends before the arrival, so arriving after `window_cap`
/// gives an empty window rather than a negative one.
///
/// `budget = floor(window_hours × 60 / block_min × budget_ratio)` — a
/// function of the *configured* window, not of today's actual length, so a
/// late start keeps the same budget (§8.1).
pub fn window_and_budget(
    arrival: DateTime<Tz>,
    walls_today: &[Wall],
    cfg: &Config,
) -> (DateTime<Tz>, u32) {
    let tz = arrival.timezone();
    let window_min = (cfg.day.window_hours * 60.0).round().max(0.0) as i64;
    let cap = local_dt(tz, arrival.date_naive(), cfg.day.window_cap);
    let base_end = (arrival + Duration::minutes(window_min)).min(cap).max(arrival);
    let mut end = base_end;
    for (a, b) in walls_after(arrival, walls_today) {
        if a >= end {
            break; // sorted: this wall and every later one are outside
        }
        end += b - a;
    }
    (end, budget_blocks(cfg))
}

/// §8.1: `floor(window_hours × 60 / block_min × budget_ratio)`.
pub fn budget_blocks(cfg: &Config) -> u32 {
    let block_min = cfg.block_min().max(1) as f64;
    let blocks = cfg.day.window_hours * 60.0 / block_min * cfg.day.budget_ratio;
    blocks.floor().max(0.0) as u32
}

/// §8.1: `budget − blocks_done_today`, never below zero.
pub fn remaining_budget(budget: u32, blocks_done: u32) -> u32 {
    budget.saturating_sub(blocks_done)
}

// ---------------------------------------------------------------------------
// §8.2 step 3: cutting slots
// ---------------------------------------------------------------------------

/// Sort and merge a list of intervals (touching ones merge too).
fn merge_walls(mut walls: Vec<Wall>) -> Vec<Wall> {
    walls.sort_by_key(|(a, _)| *a);
    let mut merged: Vec<Wall> = Vec::new();
    for (a, b) in walls {
        match merged.last_mut() {
            Some(last) if a <= last.1 => last.1 = last.1.max(b),
            _ => merged.push((a, b)),
        }
    }
    merged
}

/// Walls clipped to `[from, to)`, sorted and merged.
fn normalize_walls(
    from: DateTime<Tz>,
    to: DateTime<Tz>,
    walls: &[Wall],
) -> Vec<Wall> {
    merge_walls(
        walls
            .iter()
            .map(|(a, b)| (a.max(&from).to_owned(), b.min(&to).to_owned()))
            .filter(|(a, b)| b > a)
            .collect(),
    )
}

/// Walls clipped to start at `from` (no upper bound), sorted and merged —
/// what [`window_and_budget`]'s fixed point walks.
fn walls_after(from: DateTime<Tz>, walls: &[Wall]) -> Vec<Wall> {
    merge_walls(
        walls
            .iter()
            .map(|(a, b)| (a.max(&from).to_owned(), *b))
            .filter(|(a, b)| b > a)
            .collect(),
    )
}

/// The free stretches of `[from, to)` left by the walls.
pub fn free_intervals(
    from: DateTime<Tz>,
    to: DateTime<Tz>,
    walls: &[Wall],
) -> Vec<Wall> {
    if to <= from {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut cursor = from;
    for (a, b) in normalize_walls(from, to, walls) {
        if a > cursor {
            out.push((cursor, a));
        }
        cursor = cursor.max(b);
    }
    if cursor < to {
        out.push((cursor, to));
    }
    out
}

/// §8.2 step 3: cut `[from, end)` around the walls into blocks and breaks.
///
/// Slots come back with `energy = 0`; [`energize`] fills that in.
pub fn cut_slots(
    from: DateTime<Tz>,
    end: DateTime<Tz>,
    walls: &[Wall],
    cfg: &Config,
) -> Cut {
    cut_slots_from(from, end, walls, cfg, 0)
}

/// [`cut_slots`] starting with `blocks_since_break` blocks already worked
/// since the last break (a replan in the middle of the day).
pub fn cut_slots_from(
    from: DateTime<Tz>,
    end: DateTime<Tz>,
    walls: &[Wall],
    cfg: &Config,
    blocks_since_break: u32,
) -> Cut {
    cut_slots_around(from, end, walls, &[], cfg, blocks_since_break)
}

/// [`cut_slots_from`] with the *restful* occupied intervals named separately.
///
/// `walls` and `rests` both block time; the difference is the break counter.
/// A `rest` of at least `break_min` — a lunch or a workout the planner has
/// already placed in §8.2 step 2 — satisfies a pending break, so work
/// resumes with a full block when it ends instead of resting twice in a row
/// (the §4.3 day file's `11:20 lunch 30m` / `11:50 … 1b`). A wall is work:
/// it never resets the counter.
pub fn cut_slots_around(
    from: DateTime<Tz>,
    end: DateTime<Tz>,
    walls: &[Wall],
    rests: &[Wall],
    cfg: &Config,
    blocks_since_break: u32,
) -> Cut {
    let mut cut = Cut::default();
    let block_min = cfg.day.block_min;
    if block_min == 0 {
        return cut;
    }
    let block = Duration::minutes(block_min as i64);
    let brk = Duration::minutes(cfg.day.break_min as i64);
    let min_last = cfg.day.min_last_block_min.min(block_min).max(1) as i64;
    let mut since_break = blocks_since_break;

    let occupied: Vec<Wall> = walls.iter().chain(rests).copied().collect();
    // A rest long enough to count as a break, by the instant it ends.
    let restful_end = |t: DateTime<Tz>| {
        rests
            .iter()
            .any(|(a, b)| *b == t && (*b - *a).num_minutes() >= cfg.day.break_min as i64)
    };

    for (start, stop) in free_intervals(from, end, &occupied) {
        let mut t = start;
        if restful_end(start) {
            since_break = 0;
        }
        while t < stop {
            let breaks_on = cfg.day.break_after_blocks > 0 && cfg.day.break_min > 0;
            if breaks_on && since_break >= cfg.day.break_after_blocks {
                // Only rest when work still follows: a stretch that would end
                // on a break drops it and leaves the tail free instead.
                if (stop - (t + brk)).num_minutes() < min_last {
                    break;
                }
                cut.breaks.push(Break {
                    start: t,
                    end: t + brk,
                });
                t += brk;
                since_break = 0;
                continue;
            }
            let remain = (stop - t).num_minutes();
            if remain >= block_min as i64 {
                cut.slots.push(Slot {
                    start: t,
                    end: t + block,
                    energy: 0,
                    kind: SlotKind::Block,
                });
                t += block;
            } else if remain >= min_last {
                cut.slots.push(Slot {
                    start: t,
                    end: stop,
                    energy: 0,
                    kind: SlotKind::ShortBlock,
                });
                t = stop;
            } else {
                break; // too short to use
            }
            since_break += 1;
        }
    }
    cut
}

// ---------------------------------------------------------------------------
// §8.2 step 3: energising slots
// ---------------------------------------------------------------------------

/// Everything [`energize`] needs besides the slots.
///
/// (§8.2 lists these as separate arguments; a context struct keeps the call
/// sites readable and lets the planner reuse one value for the whole day.)
#[derive(Clone, Debug)]
pub struct EnergyCtx<'a> {
    /// The learned model (empty = config priors).
    pub model: &'a Model,
    /// Configuration.
    pub cfg: &'a Config,
    /// Today's energy reports.
    pub posterior: &'a Posterior,
    /// When you woke (for `hsw`).
    pub wake: DateTime<Tz>,
    /// Where you are.
    pub loc: Loc,
    /// Minutes slept last night, when known.
    pub slept_min: Option<u32>,
    /// Blocks already done today (a v2 feature; also the slot numbering).
    pub blocks_done: u32,
    /// `tm plan --allow-home`: skip the home cap.
    pub allow_home: bool,
}

impl<'a> EnergyCtx<'a> {
    /// A context with no sleep information, no blocks done and the home cap
    /// in force.
    pub fn new(
        model: &'a Model,
        cfg: &'a Config,
        posterior: &'a Posterior,
        wake: DateTime<Tz>,
        loc: Loc,
    ) -> EnergyCtx<'a> {
        EnergyCtx {
            model,
            cfg,
            posterior,
            wake,
            loc,
            slept_min: None,
            blocks_done: 0,
            allow_home: false,
        }
    }
    /// Set the minutes slept.
    pub fn with_slept(mut self, slept_min: Option<u32>) -> EnergyCtx<'a> {
        self.slept_min = slept_min;
        self
    }
    /// Set the blocks already done today.
    pub fn with_blocks_done(mut self, blocks_done: u32) -> EnergyCtx<'a> {
        self.blocks_done = blocks_done;
        self
    }
    /// Set `--allow-home`.
    pub fn with_allow_home(mut self, allow_home: bool) -> EnergyCtx<'a> {
        self.allow_home = allow_home;
        self
    }

    /// The home cap: `min(energy, home_max_ci)` at home unless `--allow-home`.
    pub fn cap_for_location(&self, energy: u8) -> u8 {
        if self.loc == Loc::Home && !self.allow_home {
            energy.min(self.cfg.location.home_max_ci)
        } else {
            energy
        }
    }

    /// Energy at an instant: prediction, posterior correction, home cap.
    pub fn energy_at(&self, t: DateTime<Tz>, blocks_done: u32, since_break_min: u32) -> u8 {
        let f = Features::at(t, self.wake, self.loc.clone())
            .with_slept(self.slept_min)
            .with_progress(blocks_done, since_break_min);
        let pred = energy::predict(self.model, self.cfg, &f);
        let corrected = self.posterior.correct(t, pred);
        self.cap_for_location(corrected)
    }
}

/// §8.2 step 3: give every slot its energy.
///
/// `blocks_done` counts up from `ctx.blocks_done` over the slots;
/// `since_break_min` accumulates over slots that touch, and resets whenever
/// there is a gap (a break or a wall) before a slot.
pub fn energize(slots: &[Slot], ctx: &EnergyCtx) -> Vec<Slot> {
    let mut out = Vec::with_capacity(slots.len());
    let mut blocks_done = ctx.blocks_done;
    let mut since_break = 0u32;
    let mut prev_end: Option<DateTime<Tz>> = None;
    for slot in slots {
        if prev_end != Some(slot.start) {
            since_break = 0;
        }
        let mut s = *slot;
        s.energy = ctx.energy_at(slot.start, blocks_done, since_break);
        out.push(s);
        blocks_done += 1;
        since_break += slot.minutes();
        prev_end = Some(slot.end);
    }
    out
}

// ---------------------------------------------------------------------------
// §8.4 lookahead
// ---------------------------------------------------------------------------

/// Expected slot minutes at each energy level on one day (§8.4).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DayCapacity {
    /// The day.
    pub date: NaiveDate,
    /// Minutes at each energy level; index = energy 0..=5.
    pub minutes_at_level: [u32; 6],
}

impl DayCapacity {
    /// An empty day.
    pub fn empty(date: NaiveDate) -> DayCapacity {
        DayCapacity {
            date,
            minutes_at_level: [0; 6],
        }
    }
    /// Sum energised slots into a day capacity.
    pub fn from_slots(date: NaiveDate, slots: &[Slot]) -> DayCapacity {
        let mut day = DayCapacity::empty(date);
        for s in slots {
            day.minutes_at_level[(s.energy as usize).min(5)] += s.minutes();
        }
        day
    }
    /// Σ minutes at every level.
    pub fn total(&self) -> u32 {
        self.minutes_at_level.iter().sum()
    }
    /// Σ minutes at levels ≥ `min_ci` — the capacity an item with that `ci`
    /// can use (§7.1).
    pub fn at_least(&self, min_ci: u8) -> u32 {
        self.minutes_at_level
            .iter()
            .enumerate()
            .filter(|(level, _)| *level as u8 >= min_ci)
            .map(|(_, m)| *m)
            .sum()
    }
}

/// Keep only `budget × block_min` minutes, highest energy first (§8.4).
fn limit_to_budget(slots: &[Slot], budget: u32, block_min: u32) -> Vec<(u8, u32)> {
    let mut ordered: Vec<&Slot> = slots.iter().collect();
    ordered.sort_by(|a, b| b.energy.cmp(&a.energy).then(a.start.cmp(&b.start)));
    let mut left = budget.saturating_mul(block_min);
    let mut out = Vec::new();
    for s in ordered {
        if left == 0 {
            break;
        }
        let take = s.minutes().min(left);
        left -= take;
        out.push((s.energy, take));
    }
    out
}

/// §8.4 capacity lookahead: expected slot minutes per energy level per day.
///
/// Day 0 (`from`) is today and comes from `today_slots` — the slots the
/// planner actually cut for the rest of the day — exactly as handed in.
/// Later days are simulated: expected arrival from `model.expected_arrival`
/// (else `config.expected.arrival`), expected location `lounge` when
/// `P(lounge | weekday) ≥ 0.5` else `home` (so the home cap applies), the
/// walls from `walls_by_date`, the prior/learned curve, and only
/// `budget × block_min` minutes kept, highest-energy slots first.
/// `wake_default` is the wake time assumed on future days.
pub fn lookahead(
    walls_by_date: &WallsByDate,
    cfg: &Config,
    model: &Model,
    today_slots: &[Slot],
    from: NaiveDate,
    days: u32,
    wake_default: NaiveTime,
) -> Vec<DayCapacity> {
    let tz = cfg.tz;
    let posterior = Posterior::none(cfg);
    let mut out = Vec::with_capacity(days as usize);
    for i in 0..days as i64 {
        let Some(date) = from.checked_add_signed(Duration::days(i)) else {
            break;
        };
        if i == 0 {
            out.push(DayCapacity::from_slots(date, today_slots));
            continue;
        }
        let wd = date.weekday();
        let arrival = local_dt(tz, date, model.expected_arrival_on(wd, cfg));
        let wake = local_dt(tz, date, wake_default);
        let loc = if model.p_lounge_on(wd, cfg) >= 0.5 {
            Loc::Lounge
        } else {
            Loc::Home
        };
        let walls: &[Wall] = walls_by_date.get(&date).map(|v| v.as_slice()).unwrap_or(&[]);
        let (end, budget) = window_and_budget(arrival, walls, cfg);
        let cut = cut_slots(arrival, end, walls, cfg);
        let ctx = EnergyCtx::new(model, cfg, &posterior, wake, loc);
        let slots = energize(&cut.slots, &ctx);
        let mut day = DayCapacity::empty(date);
        for (level, minutes) in limit_to_budget(&slots, budget, cfg.block_min()) {
            day.minutes_at_level[(level as usize).min(5)] += minutes;
        }
        out.push(day);
    }
    out
}

/// §7.1/§7.3: minutes available at energy ≥ `min_ci` on every day up to and
/// including `due`.
pub fn available_until(caps: &[DayCapacity], due: NaiveDate, min_ci: u8) -> u32 {
    caps.iter()
        .filter(|d| d.date <= due)
        .map(|d| d.at_least(min_ci))
        .sum()
}

/// §7.3: take `minutes` of capacity at energy ≥ `min_ci` out of `caps`,
/// earliest days first and, within a day, the highest matching level first.
/// Returns the minutes actually reserved (less than asked when the days run
/// out).
pub fn reserve(caps: &mut [DayCapacity], minutes: u32, min_ci: u8) -> u32 {
    let mut left = minutes;
    let mut taken = 0;
    for day in caps.iter_mut() {
        if left == 0 {
            break;
        }
        for level in (min_ci as usize..6).rev() {
            if left == 0 {
                break;
            }
            let take = day.minutes_at_level[level].min(left);
            day.minutes_at_level[level] -= take;
            left -= take;
            taken += take;
        }
    }
    taken
}

/// How many leading entries of `caps` fall on or before `due` — the slice
/// the EDF pass reserves from (`reserve(&mut caps[..upto(&caps, due)], …)`).
pub fn upto(caps: &[DayCapacity], due: NaiveDate) -> usize {
    caps.iter().take_while(|d| d.date <= due).count()
}

/// Minutes as `6h`, `1h20`, `45m`, `·` for zero.
fn fmt_min(minutes: u32) -> String {
    match minutes {
        0 => "·".to_string(),
        m if m % 60 == 0 => format!("{}h", m / 60),
        m if m < 60 => format!("{m}m"),
        m => format!("{}h{:02}", m / 60, m % 60),
    }
}

/// The `tm plan --week` capacity grid.
pub fn week_grid(caps: &[DayCapacity]) -> String {
    fn row(label: &str, total: u32, levels: &[u32; 6]) -> String {
        let cells: String = (0..6)
            .rev()
            .map(|l| format!("{:>6}", fmt_min(levels[l])))
            .collect();
        format!("{label:<10}{:>6}{cells}", fmt_min(total))
    }
    let mut s = String::new();
    let header: String = (0..6).rev().map(|l| format!("{l:>6}")).collect();
    writeln!(s, "{:<10}{:>6}{header}", "day", "tot").ok();
    let mut totals = [0u32; 6];
    for day in caps {
        let label = format!("{} {}", day.date.weekday(), day.date.format("%m-%d"));
        writeln!(s, "{}", row(&label, day.total(), &day.minutes_at_level)).ok();
        for (total, minutes) in totals.iter_mut().zip(day.minutes_at_level) {
            *total += minutes;
        }
    }
    writeln!(s, "{}", row("total", totals.iter().sum::<u32>(), &totals)).ok();
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use chrono_tz::America::Chicago;

    fn cfg() -> Config {
        Config::default()
    }

    fn t(h: u32, m: u32) -> DateTime<Tz> {
        Chicago
            .with_ymd_and_hms(2026, 9, 7, h, m, 0)
            .single()
            .expect("valid local time")
    }

    #[test]
    fn budget_of_an_eight_hour_window() {
        let (end, budget) = window_and_budget(t(7, 0), &[], &cfg());
        assert_eq!(budget, 6);
        assert_eq!(end, t(15, 0));
    }

    #[test]
    fn walls_extend_the_window() {
        let walls = [(t(12, 50), t(13, 50))];
        let (end, budget) = window_and_budget(t(7, 0), &walls, &cfg());
        assert_eq!(budget, 6);
        assert_eq!(end, t(16, 0));
    }

    #[test]
    fn the_cap_bounds_the_window() {
        // Arriving at 14:00 the 8 h window would end at 22:00; the cap is 19:00.
        let (end, _) = window_and_budget(t(14, 0), &[], &cfg());
        assert_eq!(end, t(19, 0));
    }

    #[test]
    fn free_intervals_merge_overlapping_walls() {
        let walls = [(t(9, 0), t(10, 0)), (t(9, 30), t(11, 0))];
        let free = free_intervals(t(7, 0), t(13, 0), &walls);
        assert_eq!(free, vec![(t(7, 0), t(9, 0)), (t(11, 0), t(13, 0))]);
    }

    #[test]
    fn reserve_takes_the_best_levels_earliest() {
        let mut caps = vec![
            DayCapacity {
                date: NaiveDate::from_ymd_opt(2026, 9, 7).unwrap(),
                minutes_at_level: [0, 0, 0, 60, 60, 60],
            },
            DayCapacity {
                date: NaiveDate::from_ymd_opt(2026, 9, 8).unwrap(),
                minutes_at_level: [0, 0, 0, 60, 0, 0],
            },
        ];
        let got = reserve(&mut caps, 90, 4);
        assert_eq!(got, 90);
        assert_eq!(caps[0].minutes_at_level, [0, 0, 0, 60, 30, 0]);
        assert_eq!(caps[1].minutes_at_level, [0, 0, 0, 60, 0, 0]);
        // Nothing left at ci ≥ 5 anywhere.
        assert_eq!(reserve(&mut caps, 60, 5), 0);
    }
}
