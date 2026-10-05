//! Capacity — tm-spec-v1.md §8.1 (window and budget), the shapes of §8.2
//! step 3's cut, and the exact units of §8.4's lookahead as the host holds
//! them.
//!
//! Everything here is pure: instants are `DateTime<Tz>` in `config.tz`
//! (never naive, so a DST day is right), and `now`/`today` are parameters.
//!
//! **Since R3 the kernel cuts, energises and looks ahead** (stage 6, W-46;
//! README gap 4752).  Fork 4748911's slot cut, its energy pass, its lookahead
//! and the cumulative helpers its §7.3 pass used lived here until R3 deleted
//! them with the rest of the class the switch orphans (W-46 track C §5):
//! their port is the kernel's (`Look.cutSlots`, `Look.energize`,
//! `Look.lookahead`), and their answers are fork 4748911's, frozen by value
//! and asked of `tm-oracle capacity` (`tm/tests/support/forkcap.rs`).
//!
//! # API overview
//!
//! * [`window_and_budget`]`(arrival, walls_today, cfg) -> (end, blocks)` —
//!   §8.1: `end = min(arrival + window_hours, window_cap) + Σ wall minutes
//!   inside [arrival, end]` (a fixed point, since extending the window can
//!   pull in another wall; solved exactly, see the function), `budget =
//!   floor(window_hours × 60 / block_min × budget_ratio)` (8 h → 6), which
//!   [`budget_blocks`] is.
//! * The cut's shapes — [`Slot`], [`SlotKind`], [`Break`], [`Cut`] and
//!   [`SlotOrBreak`] — the types §8.2 step 3's cut is written in.  Nothing
//!   in the binary cuts a day any more; the frozen fork answers decode their
//!   slots into them, and `tm/tests/no_second_planner.rs` reads a literal of
//!   one, beside a day built, as a planner's shape (README gap 4815).
//! * [`EnergyCtx`] — what the energy at an instant needs (the curve, the
//!   posterior, the home cap); [`DayCapacity`] and [`week_grid`] — a day's
//!   whole minutes per level and the grid `tm plan --week` drew from them.
//! * **Exact units** (stage 5 D10 L8, the owner's D10, D15 and D17): the
//!   kernel's lookahead is an exact mixture, so a capacity is a count of
//!   units over [`CAP_DEN`]` = 10^18` per minute, held as `u128`.
//!   [`UnitCapacity`] is one day of them; [`reserve_units`] and
//!   [`available_until_units`] are the reserves the Rust still runs over the
//!   kernel's days (the Queue's "fits"; gap 94 — fork 4748911's week
//!   allocation in its `planner.rs` was the other, until R3 deleted it), in
//!   exact units; [`week_grid_units`] renders floors, each the
//!   floor of **its own** exact value; [`Exact`] is a `{num, den}` pair for
//!   `--json`. A floor only ever displays.
//! * [`local_dt`] resolves a local date + time in a zone (DST-safe).
//!
//! # Interpretation notes, as fork 4748911's cut decided them
//!
//! These are the decisions the fork's cut took where the spec needed one;
//! the kernel's port keeps them, and the parity register names where it
//! does not.
//!
//! * **Breaks around walls.** A wall is work, so it does not reset the break
//!   counter: a break due when a wall ends is placed right after it. A
//!   *rest* (a placed routine) does reset it — you have just rested. A break
//!   that would not fit before the next wall is dropped along with the rest
//!   of that stretch.
//! * **A stretch never ends on a break.** §8.2 orders a break "after every
//!   `break_after_blocks` blocks", i.e. between blocks. A break is therefore
//!   placed only when a block (full, or short ≥ `min_last_block_min`) still
//!   fits after it; otherwise the stretch simply ends and the tail is left
//!   free. Without that rule a day could end on a 20 m rest that rests
//!   nobody, and the planned rest would be over-reported to §11's rest-debt
//!   monitor.
//! * **Short blocks.** §8.2 says "the last block may be short (≥ 30 m) or
//!   dropped". The same rule is applied at the end of *every* free stretch,
//!   not only at the end of the day — a wall ends a stretch exactly as the
//!   window end does.
//! * **The §4.3 timeline.** A cut around the walls alone cannot reproduce the
//!   printed day file: step 2 has already placed the routines (lunch at 11:20
//!   there) before step 3 cuts what is left. With only the 12:50–13:50 wall
//!   the cut is 07:00, 08:00, break 09:00, 09:20, 10:20, break 11:20, 11:40
//!   (12:40 → 12:50 is 10 m and is dropped), wall, 13:50, break 14:50,
//!   15:10–16:00 short. Passing lunch to the cut as a rest gives the day
//!   file's midday: 10:20 block, lunch, then a full 11:50–12:50 block. The
//!   day file's afternoon (break at 13:50 after a single block) additionally
//!   implies that the 12:50 meeting counts towards break accrual; v1 does
//!   not model that, so the cut breaks at 14:50 instead.
//! * **Today in the lookahead** is taken from the slots the day's cut gave,
//!   exactly as they are; future days *are* limited to `budget × block_min`
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
    /// Predicted energy 0..=5 (the cut leaves 0 and its energy pass fills it).
    pub energy: u8,
    /// Full block or short remainder.
    pub kind: SlotKind,
}

impl Slot {
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

/// **The latest instant at or before `now` whose local clock in `tz` is
/// `clock`** — the owner's D75 clock where the log holds no instant (W-41
/// track T). A bare `HH:MM` names the LAST time that clock was read, never a
/// time still to come: `tm stop --at 23:40` typed at 07:05 ends the block last
/// night (the owner's **D79**, README gap 3823), and `.tm/state.json`'s
/// `break.started` of a break begun at 23:50 is still the evening's after
/// midnight (the campaign's **D81** call on README gap 3820, parity **P73** —
/// for a break the log holds no `break_start` for, one a binary before the
/// owner's D105 began, the cache's clock is all there is). [`local_dt`] is the
/// other rule, a clock on a GIVEN date, and what fork 4748911 read both on
/// (today's).
///
/// Today's instants with that clock, then the day before's, then the day
/// before that's, each latest first — an ambiguous local time (a fall-back
/// hour) is two instants and the later is tried first, and a date on which the
/// clock does not exist (a spring-forward gap, Apia's missing 2011-12-30)
/// holds none and is passed over — and the first that is not after `now`.
/// Yesterday's or the day before's always is: both are wholly before today's
/// local midnight, and no zone of the tz database lacks one clock on two
/// consecutive dates. So the fallback `now` is unreachable; it is written so
/// the function is total, and it too is at or before `now`
/// (`the_latest_clock_at_or_before_now`).
pub fn latest_at_or_before(tz: Tz, now: DateTime<Tz>, clock: NaiveTime) -> DateTime<Tz> {
    let today = now.date_naive();
    let dates = [Some(today), today.pred_opt(), today.pred_opt().and_then(|d| d.pred_opt())];
    for date in dates.into_iter().flatten() {
        let latest_first = match tz.from_local_datetime(&date.and_time(clock)) {
            LocalResult::Single(t) => [Some(t), None],
            LocalResult::Ambiguous(early, late) => [Some(late), Some(early)],
            LocalResult::None => [None, None],
        };
        if let Some(t) = latest_first.into_iter().flatten().find(|t| *t <= now) {
            return t;
        }
    }
    now
}

/// **How far after `now` a reported clock may still name today**, in hours —
/// the owner's **D86** (README gap 4135): twelve.
pub const REPORT_AHEAD_HOURS: i64 = 12;

/// **The instant `tm energy --at HH:MM` names** — the owner's **D86** (README
/// gap 4135, W-42 track H, parity **P82**): `clock` on TODAY's date
/// ([`local_dt`], the reading `tm energy` always took and fork 4748911's), unless
/// that instant is MORE than [`REPORT_AHEAD_HOURS`] after `now`, when it is the
/// same clock on YESTERDAY's date. So `--at 23:40` typed at 00:40 is last night,
/// `--at 10:30` at 09:00 is still a forward report on the same day (the one
/// `cli_day.rs`' `energy_logs_a_report_against_the_prediction` and its snapshot
/// pin), and a clock exactly twelve hours ahead is today's.
///
/// It is NOT [`latest_at_or_before`], D79's rule for `tm stop --at` and `tm done
/// --at`, and the difference is the owner's: an END is a time the block ran
/// through, never one still to come, while a REPORT may name a time a little
/// ahead on the same day. One parser reads the clock for every `--at`
/// (`tm_core::model::parse_time`); each rule has this one definition.
///
/// "More than twelve hours" is ELAPSED time between instants, so across a DST
/// change it is not the wall clock's difference: at 00:40 CDT on the day DST
/// ends, `--at 12:30` is 12 h 50 m ahead (yesterday's), and at 00:30 CST on the
/// day it starts, `--at 13:00` is 11 h 30 m ahead (today's)
/// (`a_report_names_today_unless_more_than_twelve_hours_ahead`).
pub fn report_at(tz: Tz, now: DateTime<Tz>, clock: NaiveTime) -> DateTime<Tz> {
    let today = local_dt(tz, now.date_naive(), clock);
    match now.date_naive().pred_opt() {
        Some(yesterday) if today - now > Duration::hours(REPORT_AHEAD_HOURS) => local_dt(tz, yesterday, clock),
        _ => today,
    }
}

// ---------------------------------------------------------------------------
// §8.1 window and budget
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// §8.2 step 3: energising slots
// ---------------------------------------------------------------------------

/// Everything the energy at an instant needs besides the instant.
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
    /// Σ minutes at every level.
    pub fn total(&self) -> u32 {
        self.minutes_at_level.iter().sum()
    }
}

// ---------------------------------------------------------------------------
// Exact units (stage 5 D10 L8)
// ---------------------------------------------------------------------------

/// Units per minute: the kernel's `Look.capDen` (the owner's D17). A capacity
/// in units is `minutes × CAP_DEN` for a whole-minute day, and any natural
/// number of units for a mixed one.
pub const CAP_DEN: u128 = 1_000_000_000_000_000_000;

/// An exact non-negative rational `num / den`, reduced, for `--json`'s
/// `…_exact` fields (the owner's D15). Both parts cross as digit strings
/// (D17: a unit count passes 2^53), so a consumer never narrows them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Exact {
    /// The numerator.
    pub num: u128,
    /// The denominator, at least 1.
    pub den: u128,
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

impl Exact {
    /// `num / den`, reduced; a zero denominator is read as 1 (never produced).
    pub fn new(num: u128, den: u128) -> Exact {
        let den = den.max(1);
        let g = gcd(num, den).max(1);
        Exact { num: num / g, den: den / g }
    }
    /// A count of units over [`CAP_DEN`], as minutes.
    pub fn of_units(units: u128) -> Exact {
        Exact::new(units, CAP_DEN)
    }
    /// The floor, saturating at `u32::MAX` — the documented integer beside it.
    pub fn floor_u32(&self) -> u32 {
        u32::try_from(self.num / self.den).unwrap_or(u32::MAX)
    }
}

impl Default for Exact {
    fn default() -> Exact {
        Exact { num: 0, den: 1 }
    }
}

impl Serialize for Exact {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut st = s.serialize_struct("Exact", 2)?;
        st.serialize_field("num", &self.num.to_string())?;
        st.serialize_field("den", &self.den.to_string())?;
        st.end()
    }
}

/// Units as whole minutes, rounded down: **display only**.
pub fn floor_minutes(units: u128) -> u32 {
    u32::try_from(units / CAP_DEN).unwrap_or(u32::MAX)
}

/// One day of the kernel's lookahead: units at each energy level over
/// [`CAP_DEN`] (the owner's D10: an exact mixture of the day at the lounge and
/// the day at home).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct UnitCapacity {
    /// The day.
    pub date: NaiveDate,
    /// Units at each energy level; index = energy 0..=5.
    pub units: [u128; 6],
}

impl UnitCapacity {
    /// An empty day.
    pub fn empty(date: NaiveDate) -> UnitCapacity {
        UnitCapacity { date, units: [0; 6] }
    }
    /// Σ units at every level.
    pub fn total_units(&self) -> u128 {
        self.units.iter().sum()
    }
    /// Σ units at levels ≥ `min_ci` (§7.1's capacity for that `ci`).
    pub fn at_least_units(&self, min_ci: u8) -> u128 {
        self.units.iter().skip(usize::from(min_ci.min(6))).sum()
    }
    /// Each level's minutes, the floor of its own exact value (display).
    pub fn minutes_at_level_floor(&self) -> [u32; 6] {
        self.units.map(floor_minutes)
    }
    /// The day's minutes, the floor of the exact total (display; not the sum
    /// of the level floors).
    pub fn total_floor(&self) -> u32 {
        floor_minutes(self.total_units())
    }
}

impl Serialize for UnitCapacity {
    /// `{date, minutes_at_level, minutes_at_level_exact, total, total_exact}`:
    /// each integer the floor of its own exact value (the owner's D15).
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut st = s.serialize_struct("UnitCapacity", 5)?;
        st.serialize_field("date", &self.date)?;
        st.serialize_field("minutes_at_level", &self.minutes_at_level_floor())?;
        st.serialize_field("minutes_at_level_exact", &self.units.map(Exact::of_units))?;
        st.serialize_field("total", &self.total_floor())?;
        st.serialize_field("total_exact", &Exact::of_units(self.total_units()))?;
        st.end()
    }
}

/// §7.1/§7.3 in units: units at levels ≥ `min_ci` on every day up to and
/// including `due` (the kernel's `availUntil`).
pub fn available_until_units(caps: &[UnitCapacity], due: NaiveDate, min_ci: u8) -> u128 {
    caps.iter().filter(|d| d.date <= due).map(|d| d.at_least_units(min_ci)).sum()
}

/// §7.3's reservation in units (the kernel's `reserveRest`/`reserveOut`): take
/// `units` at energy ≥ `min_ci` out of `caps`, earliest day first and, within a
/// day, the highest matching level first. Returns the units actually reserved.
/// T16 (`tm/tests/kernel_unit_reserve.rs`) holds it to the kernel's pass.
pub fn reserve_units(caps: &mut [UnitCapacity], units: u128, min_ci: u8) -> u128 {
    let mut left = units;
    let mut taken = 0;
    for day in caps.iter_mut() {
        if left == 0 {
            break;
        }
        for level in (usize::from(min_ci.min(6))..6).rev() {
            if left == 0 {
                break;
            }
            let take = day.units[level].min(left);
            day.units[level] -= take;
            left -= take;
            taken += take;
        }
    }
    taken
}

/// How many leading days fall on or before `due` (the slice [`reserve_units`]
/// reserves from).
pub fn upto_units(caps: &[UnitCapacity], due: NaiveDate) -> usize {
    caps.iter().take_while(|d| d.date <= due).count()
}

/// The `tm plan --week` capacity grid over exact units: every cell is the
/// floor of its own exact value, and the `total` row and column are the
/// floors of the exact sums (the owner's D15), so a row may read one more than
/// the sum of its cells.
pub fn week_grid_units(caps: &[UnitCapacity]) -> String {
    fn row(label: &str, total: u128, levels: &[u128; 6]) -> String {
        let cells: String = (0..6)
            .rev()
            .map(|l| format!("{:>6}", fmt_min(floor_minutes(levels[l]))))
            .collect();
        format!("{label:<10}{:>6}{cells}", fmt_min(floor_minutes(total)))
    }
    let mut s = String::new();
    let header: String = (0..6).rev().map(|l| format!("{l:>6}")).collect();
    writeln!(s, "{:<10}{:>6}{header}", "day", "tot").ok();
    let mut totals = [0u128; 6];
    for day in caps {
        let label = format!("{} {}", day.date.weekday(), day.date.format("%m-%d"));
        writeln!(s, "{}", row(&label, day.total_units(), &day.units)).ok();
        for (total, units) in totals.iter_mut().zip(day.units) {
            *total += units;
        }
    }
    writeln!(s, "{}", row("total", totals.iter().sum::<u128>(), &totals)).ok();
    s
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

    /// **`latest_at_or_before` is the latest instant at or before `now` with
    /// that clock** (W-41 track T; D79, D81/P73): never after `now`; its local
    /// clock IS the clock; and no instant between it and `now` reads that clock
    /// — swept minute by minute over Chicago's two DST changes, Santiago's
    /// midnight gap, Lord Howe's half hour and Apia's missing 2011-12-30.
    #[test]
    fn the_latest_clock_at_or_before_now() {
        let hm = |h, m| NaiveTime::from_hms_opt(h, m, 0).expect("t");
        // The drive's own world: `--at 23:40` typed at Wednesday 07:05.
        let now = Chicago.with_ymd_and_hms(2026, 9, 9, 7, 5, 0).single().expect("now");
        let last_night = Chicago.with_ymd_and_hms(2026, 9, 8, 23, 40, 0).single().expect("t");
        assert_eq!(latest_at_or_before(Chicago, now, hm(23, 40)), last_night);
        assert_eq!(latest_at_or_before(Chicago, now, hm(7, 5)), now, "now's own minute is today's");
        let yesterday = Chicago.with_ymd_and_hms(2026, 9, 8, 7, 6, 0).single().expect("t");
        assert_eq!(latest_at_or_before(Chicago, now, hm(7, 6)), yesterday, "a minute ahead is yesterday's");

        let zones: [(Tz, (i32, u32, u32)); 5] = [
            (chrono_tz::America::Chicago, (2026, 3, 7)),
            (chrono_tz::America::Chicago, (2026, 10, 31)),
            (chrono_tz::America::Santiago, (2026, 9, 5)),
            (chrono_tz::Australia::Lord_Howe, (2026, 10, 3)),
            (chrono_tz::Pacific::Apia, (2011, 12, 28)),
        ];
        let clocks = [hm(0, 0), hm(0, 30), hm(1, 30), hm(2, 0), hm(2, 30), hm(12, 0), hm(23, 40), hm(23, 59)];
        let mut checked = 0;
        for (tz, (y, mo, d)) in zones {
            let start = tz.from_utc_datetime(
                &NaiveDate::from_ymd_opt(y, mo, d).expect("date").and_hms_opt(0, 0, 0).expect("t"),
            );
            for step in 0..96 {
                let now = start + Duration::minutes(step * 53);
                for clock in clocks {
                    let r = latest_at_or_before(tz, now, clock);
                    assert!(r <= now, "{tz} {now} {clock}: {r} is after now");
                    assert_eq!(r.time(), clock, "{tz} {now} {clock}: {r} does not read the clock");
                    let mut t = r + Duration::minutes(1);
                    while t <= now {
                        assert!(
                            t.time() != clock,
                            "{tz} {now} {clock}: {t} reads the clock and is later than {r}"
                        );
                        t += Duration::minutes(1);
                    }
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 5 * 96 * 8);
    }

    /// **`report_at` names today's clock unless that is more than twelve hours
    /// after `now`, and then yesterday's** (the owner's D86, README gap 4135,
    /// parity P82): the owner's two examples, both sides of the edge, both DST
    /// changes read in ELAPSED time, and a sweep of the rule's two halves over
    /// the zones `the_latest_clock_at_or_before_now` sweeps.
    #[test]
    fn a_report_names_today_unless_more_than_twelve_hours_ahead() {
        let hm = |h, m| NaiveTime::from_hms_opt(h, m, 0).expect("t");
        let at = |y, mo, d, h, m| Chicago.with_ymd_and_hms(y, mo, d, h, m, 0).single().expect("t");
        // `--at 23:40` typed at 00:40 is last night; `--at 10:30` at 09:00 stays today.
        assert_eq!(report_at(Chicago, at(2026, 9, 8, 0, 40), hm(23, 40)), at(2026, 9, 7, 23, 40));
        assert_eq!(report_at(Chicago, at(2026, 9, 7, 9, 0), hm(10, 30)), at(2026, 9, 7, 10, 30));
        // Exactly twelve hours ahead is today's; a minute more is yesterday's.
        assert_eq!(report_at(Chicago, at(2026, 9, 7, 9, 0), hm(21, 0)), at(2026, 9, 7, 21, 0));
        assert_eq!(report_at(Chicago, at(2026, 9, 7, 9, 0), hm(21, 1)), at(2026, 9, 6, 21, 1));
        // A clock behind now is today's, however far behind.
        assert_eq!(report_at(Chicago, at(2026, 9, 7, 23, 59), hm(0, 0)), at(2026, 9, 7, 0, 0));
        // DST ends 2026-11-01 02:00 CDT: 00:40 CDT to 12:30 CST is 12 h 50 m — yesterday's.
        let fall = Chicago.with_ymd_and_hms(2026, 11, 1, 0, 40, 0).single().expect("CDT");
        assert_eq!(report_at(Chicago, fall, hm(12, 30)), at(2026, 10, 31, 12, 30));
        // DST starts 2026-03-08 02:00 CST: 00:30 CST to 13:00 CDT is 11 h 30 m — today's.
        let spring = Chicago.with_ymd_and_hms(2026, 3, 8, 0, 30, 0).single().expect("CST");
        assert_eq!(report_at(Chicago, spring, hm(13, 0)), at(2026, 3, 8, 13, 0));

        let zones: [(Tz, (i32, u32, u32)); 5] = [
            (chrono_tz::America::Chicago, (2026, 3, 7)),
            (chrono_tz::America::Chicago, (2026, 10, 31)),
            (chrono_tz::America::Santiago, (2026, 9, 5)),
            (chrono_tz::Australia::Lord_Howe, (2026, 10, 3)),
            (chrono_tz::Pacific::Apia, (2011, 12, 28)),
        ];
        let clocks = [hm(0, 0), hm(0, 30), hm(1, 30), hm(2, 0), hm(2, 30), hm(12, 0), hm(23, 40), hm(23, 59)];
        let ahead = Duration::hours(REPORT_AHEAD_HOURS);
        let (mut today_side, mut yesterday_side) = (0, 0);
        for (tz, (y, mo, d)) in zones {
            let start = tz.from_utc_datetime(
                &NaiveDate::from_ymd_opt(y, mo, d).expect("date").and_hms_opt(0, 0, 0).expect("t"),
            );
            for step in 0..96 {
                let now = start + Duration::minutes(step * 53);
                for clock in clocks {
                    let today = local_dt(tz, now.date_naive(), clock);
                    let r = report_at(tz, now, clock);
                    if today - now > ahead {
                        let yesterday = now.date_naive().pred_opt().expect("a day before");
                        assert_eq!(r, local_dt(tz, yesterday, clock), "{tz} {now} {clock}: yesterday's");
                        yesterday_side += 1;
                    } else {
                        assert_eq!(r, today, "{tz} {now} {clock}: today's");
                        today_side += 1;
                    }
                    assert!(r - now <= ahead, "{tz} {now} {clock}: {r} is more than twelve hours ahead");
                }
            }
        }
        assert!(today_side > 0 && yesterday_side > 0, "both halves are swept: {today_side} {yesterday_side}");
        assert_eq!(today_side + yesterday_side, 5 * 96 * 8);
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

}
