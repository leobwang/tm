//! Planner — tm-spec-v1.md §8 in full: the window and budget (§8.1), the
//! eight steps of `plan(state, now)` (§8.2), the invariants those steps
//! satisfy (§8.3), §5.2's mandatory placement, §7.5's batching, §9's dynamic
//! adjustment (replan from `now`, the Active block keeps its slot, an
//! interruption is an ad-hoc wall, the tail drops) and §9.1's "x extend →
//! drops: …" consequence, plus §12.1's timeline data and §13's
//! `tm plan [--week] [--allow-home] [--diff] [--explain ^id]`.
//!
//! Everything here is pure (§17.2): `input.now` is the only clock, no file is
//! read or written, and no randomness enters. Instants are `DateTime<Tz>` in
//! `cfg.tz`, so a DST day is right.
//!
//! # API overview
//!
//! * [`PlanInput`] — the tree, the log's [`Replay`], the config, the
//!   learned [`Model`], the runtime [`RuntimeState`] and `now`, plus five
//!   optional shortcuts: `caps` and `candidates` (a caller that already built
//!   the §8.4 lookahead or the §6.2 candidate list does not build it twice),
//!   `prios` (the kernel's ranking of those candidates, stage 5 D10 L8:
//!   [`PlanInput::with_ranking`]), `allow_home` (`tm plan --allow-home`) and
//!   `overrides` (§9.1's what-if replans). All borrowed; the struct is `Copy`.
//!   The binary always hands the kernel's ranking and lookahead in, so the
//!   planner's own §8.4 lookahead and §7 pass (`capacity::lookahead`,
//!   `priority::compute`, the fork point) run only for a caller that does not
//!   — the library's tests.
//! * [`plan`]`(&PlanInput) -> DayPlan` — §8.2 steps 1–8.
//! * [`DayPlan`] `{ date, window, budget_blocks, segments, diagnostics,
//!   priorities }` — the whole day, past *and* future: segments that ended
//!   before `now` are replayed from the log, so a replan never rewrites them
//!   (§8.3's stability invariant). [`DayPlan::hash`] is the FNV-1a digest
//!   `state.last_plan_hash` and the `plan` log event (§10.1) carry, taken over
//!   where each segment sits and what is in it — never over how the day is
//!   going — so a replan that moves nothing hashes the same.
//! * [`Segment`] `{ start, end, kind, energy, item, instance, flags }` — one
//!   row of the timeline (§4.3) and one cell run of the day bar (§12.1).
//!   [`SegKind`] names what it is; [`SegFlags`] carries the marks (`✓ ▶ ↓ ⚠`)
//!   and the `2b×1.6` display pair.
//! * [`Diagnostics`] — §8.2 step 8's list (`underused`, `a_capacity_lost`,
//!   `hot`, `impossible`, `conflicts`, `blocked`, `deferred`, `waiting`), plus
//!   §9's `dropped_tail`, §11's `plan_honesty` and `rest_debt_min`, plus
//!   `notes` for anything the planner wants to say in prose.
//! * [`PlanOverrides`] — the est/extra-block/drop overrides §9.1's overtime
//!   prompt replans with; [`overtime_drops`] runs the two plans and returns
//!   the "drops: …" list.
//! * [`diff`]`(old, new) -> `[`PlanDiff`] — `tm plan --diff`, the `plan`
//!   event's `drift_min` and §11's "Replans and drift" monitor.
//! * [`explain`]`(plan, id, cands, cfg) -> String` — §13's line, completing
//!   [`priority::explain`] with the slot/energy/gap half.
//! * [`week_plan`]`(&PlanInput) -> `[`WeekPlan`] — `tm plan --week`: the §8.4
//!   capacity grid plus a light per-day allocation (see [`WeekPlan`] for what
//!   it deliberately does not simulate).
//!
//! Every type is `Serialize` (for `tm plan --json`), `Clone`, `Debug` and
//! `PartialEq` (for the §8.3 purity property tests).
//!
//! # How §8.2 is implemented, and the choices the spec leaves open
//!
//! 1. **Walls (step 1).** Every candidate whose effective shape is an
//!    `Interval` covering today — a `calendar/` line, an exam or a meeting
//!    written in `week/` — is placed exactly where it is written. `buffer:`
//!    is emitted as its own [`SegKind::Wall`] segment in front of the event
//!    (blocked time, per §4.1) and counts as wall time in §8.1's window
//!    extension. A `travel-day` wall today **zeroes the remaining budget**:
//!    no Block is planned at all, while routines, walls and optionals stay.
//!    Overlapping walls are reported pairwise in `diagnostics.conflicts` and
//!    are *both* blocked, so nothing is placed in the overlap (§8.2 step 1).
//!    An open `state.interrupt` is an ad-hoc wall from its start to `now`
//!    (§9); unlike a real wall it does **not** extend the window, because §9
//!    says an interruption drops the tail rather than lengthening the day.
//! 2. **Routines (step 2).** Every candidate carrying a placement window
//!    (§5.1's instances of `routines.md`, `every:`/`after-done:` items and
//!    one-off `win:` lines) is a routine. Mandatory ones ([`crate::recur::is_mandatory`],
//!    surfaced as `Candidate::mandatory`) go to the earliest feasible position
//!    in their window at or after `now`; a `pref:` anchor (`wake+10m` or a
//!    clock time) is honoured when it is still ahead and free; everything else
//!    is deferred to step 6. A carried instance whose window closed before
//!    `now` may be placed anywhere left in the day. The `loc:` filter of step
//!    5 is **not** applied to routines: §8.2 lists it under ASSIGN, and a
//!    `loc:out` errand is a reason to go out, not a reason to skip the day.
//! 3. **Sleep and wind-down.** `cfg.day.wind_down` and `cfg.day.bed` define a
//!    [`SegKind::WindDown`] segment and a [`SegKind::Sleep`] segment running
//!    to the end of the planned day; the `sleep` routine instance (a routine
//!    keyed `sleep`, or an overnight window of at least six hours) is consumed
//!    by them instead of being placed as an ordinary routine. Everything from
//!    `wind_down` to midnight is blocked for slot cutting, which is the
//!    strongest form of §8.2's "no Block with `ci ≥ 4` after wind-down": no
//!    Block of any `ci` is planned there.
//! 4. **Slots (step 3).** [`capacity::cut_slots_around`] over `[max(now,
//!    window start), window end]`, with the walls as walls and the routines
//!    already placed as *rests* (a rest of at least `break_min` satisfies a
//!    pending break), continuing the break counter from the blocks already
//!    worked since today's last logged break. [`capacity::energize`] then
//!    gives each slot `energy::predict` + today's posterior + the home cap.
//! 5. **Assignment (step 5).** [`priority::batches`] over
//!    [`priority::sorted_candidates`] is the group order; a cursor walks the
//!    slots and each slot takes the first group that is still owed minutes,
//!    fits the slot's energy, matches the location, has `max:` left and — when
//!    `atomic` — has enough contiguous free slots before the next wall (a
//!    planned break does not interrupt such a run; §8.2 step 5 names only the
//!    wall). A group keeps taking consecutive slots until its planned minutes
//!    (`remaining × duration multiplier`, §8.5, capped by `max:`) are covered.
//!    §7.5 groups by `ci` and size alone, so a batch is **split** before this
//!    filter runs wherever its members disagree about the two halves of the
//!    filter that are written about the *item* — `loc:` and `atomic` — and
//!    around the item that is running. One member's `loc:out` therefore never
//!    rides another into the lounge, nor takes it out of the day; the split
//!    parts are re-sorted into §7.4's key order, so a passenger that loses its
//!    batch also loses the batch's place in the queue.
//!    5b. **The running block (§9).** `state.active` is not assigned at all:
//!    it is *reserved* — like a wall — from `now` to the end of the block it
//!    is in, before routines are placed and before slots are cut. So nothing
//!    is scheduled on top of a block that is running, the block survives a
//!    `max:`-exhausted or dep-blocked item and a spent budget (§9: "no
//!    preemption mid-block"), and it is the one work segment that carries no
//!    slot energy: it sits in no cut slot, so §8.3's energy filter — a
//!    constraint on step 5's *choice* — has nothing to say about it. The
//!    reservation ends at `started + block_min` (rolled forward a whole block
//!    at a time while that instant is past), clipped by the next wall and the
//!    wind-down, and never runs past `est_min −` the worked minutes the log
//!    knows. §8.2 step 5 protects the Active item's current *slot*, one block:
//!    reserving its whole remaining estimate would swallow every routine
//!    window and every break inside it. After that block the item re-competes
//!    for slots like any other candidate, with its group already charged for
//!    the minutes the run spends. Its block counts as one against the
//!    remaining budget however long it runs, and the stretch it has already
//!    run comes from the log (`replay.open_block`), marked [`SegFlags::open`]
//!    because it grows with every replan.
//! 6. **Deferred routines (step 6).** Each deferred instance is offered every
//!    free position inside its window — the gaps, the Rest slots and the
//!    evening, but never the wind-down — and takes the one with the **lowest
//!    predicted energy** (ties: earliest). A mandatory or last-chance instance
//!    that finds none may reach into the wind-down, and failing that displaces
//!    the lowest-energy assigned block inside its window; the displaced group
//!    returns to the pool and is re-placed in a later free slot if there is
//!    one. An instance that still has no position — its window is full — is
//!    named in `diagnostics.notes`: a day that quietly loses lunch is a day no
//!    monitor can see. (An instance whose window has *closed* is §5.3's
//!    expiry, not a placement failure, and is not reported.)
//! 7. **Rest and optionals (step 7).** Slots past the budget are Rest.
//!    `optional.md` lines (`p = 5`) then fill the free positions before
//!    wind-down — the Rest slots first, since they come earlier — each within
//!    what is left of its `max:` cap.
//! 8. **Plan honesty** (§11) is `Σ planned minutes the plan committed to
//!    today ÷ (remaining budget × block_min)`: an item that is started but
//!    cannot finish inside the budget counts in full, which is exactly the
//!    over-commitment the monitor warns about above 1.1. **Rest debt** is the
//!    planned break minutes today's log shows as skipped or cut short.
//! 9. **`a_capacity_lost`** is the Rest minutes at energy ≥ 4 on a day that
//!    had a `ci = 5` candidate none of them could take. **`deferred`** lists
//!    the candidates a *posterior downgrade* cost a slot: some slot's raw
//!    prediction was high enough for them and the corrected value was not.
//! 10. **The §4.3 day file is an illustration, not a fixture.** The planner
//!     reproduces its shape but not every row; the differences are enumerated
//!     in `tests/planner_fixtures.rs`.

use std::collections::{BTreeMap, BTreeSet};

use chrono::{DateTime, Datelike, Duration, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use serde::Serialize;

use crate::capacity::{self, EnergyCtx, Slot, UnitCapacity, Wall, WallsByDate, CAP_DEN};
use crate::config::Config;
use crate::energy::{self, Model, Posterior};
use crate::log::{Replay, SegmentKind};
use crate::model::{Horizon, Id, InstanceKey, Loc, Pref, Shape};
use crate::priority::{self, Candidate, Ineligible, Prio};
use crate::store::RuntimeState;
use crate::tree::Tree;

/// **The day's types live in [`crate::dayplan`] since stage 6 W-35** (README
/// gap 2721): they are what the renderers read and what the host decodes the
/// kernel's `plan` answer into, so they must outlive this file. Re-exported
/// here, unchanged, until R3 deletes it.
pub use crate::dayplan::{
    fmt_clock, kind_label, DayPlan, Diagnostics, PlanDiff, SegFlags, SegKind, Segment,
};

/// A window instance this long that runs past midnight is taken for sleep
/// even when it is not keyed `sleep` (see the module docs, choice 3).
const SLEEP_MIN_MINUTES: u32 = 6 * 60;

// ---------------------------------------------------------------------------
// Input
// ---------------------------------------------------------------------------

/// Everything `plan()` reads (§8).
///
/// `replay` is the replay of the event log (§10.1) — the planner never reads
/// the log or derives the replay itself, so the caller decides the range once
/// and the TUI can reuse it across replans.
#[derive(Clone, Copy, Debug)]
pub struct PlanInput<'a> {
    /// The parsed plan tree (§6).
    pub tree: &'a Tree,
    /// The replay of the event log — block minutes, instance statuses,
    /// energy and duration observations (§10.1).
    pub replay: &'a Replay,
    /// Configuration (§16).
    pub cfg: &'a Config,
    /// The learned energy and duration model (§8.5).
    pub model: &'a Model,
    /// `.tm/state.json` (§10.2): window, budget, active block, yesterday's
    /// priorities.
    pub runtime: &'a RuntimeState,
    /// The planning instant, in `cfg.tz`.
    pub now: DateTime<Tz>,
    /// The §8.4 lookahead in exact units (the kernel's, ascending by date),
    /// when the caller already has it: [`week_plan`]'s allocation reads it.
    /// `None` = the planner builds the fork point's own.
    pub caps: Option<&'a [UnitCapacity]>,
    /// The §6.2 candidates, when the caller already built them. `None` = the
    /// planner calls `priority::collect_candidates`.
    pub candidates: Option<&'a [Candidate]>,
    /// §7's priorities of `candidates`, 1:1 (the kernel's, stage 5 D10 L8),
    /// set with [`PlanInput::with_ranking`]. `None` = the planner runs the fork
    /// point's `priority::compute` over its own lookahead.
    pub prios: Option<&'a [Prio]>,
    /// `tm plan --allow-home` (§8.2 step 3): skip the `home_max_ci` cap.
    pub allow_home: bool,
    /// §9.1's what-if overrides, when this is a consequence replan.
    pub overrides: Option<&'a PlanOverrides>,
    /// **§8.2 step 5 splits each §7.5 batch into its RUNS** (the owner's D74,
    /// parity P64; README gap 3740): a member joins the LAST bucket when it
    /// carries that bucket's key, else opens a new one — the kernel's
    /// `Planner.splitPush`. `false` = fork 4748911's group-by, which is what the
    /// shipped binary plans with: nothing in `tm/src` sets this. It is the
    /// comparand's, set by the tests' fork arm ([`PlanInput::with_runs`]) the way
    /// D60's key is run in the fork by rewriting its inputs, and R3 deletes it
    /// with this file.
    pub runs: bool,
}

impl<'a> PlanInput<'a> {
    /// The required half of the input; every optional field stays unset.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        tree: &'a Tree,
        replay: &'a Replay,
        cfg: &'a Config,
        model: &'a Model,
        runtime: &'a RuntimeState,
        now: DateTime<Tz>,
    ) -> PlanInput<'a> {
        PlanInput {
            tree,
            replay,
            cfg,
            model,
            runtime,
            now,
            caps: None,
            candidates: None,
            prios: None,
            allow_home: false,
            overrides: None,
            runs: false,
        }
    }
    /// Reuse a lookahead the caller already has (exact units).
    pub fn with_caps(mut self, caps: &'a [UnitCapacity]) -> PlanInput<'a> {
        self.caps = Some(caps);
        self
    }
    /// Reuse a candidate list the caller already computed.
    pub fn with_candidates(mut self, cands: &'a [Candidate]) -> PlanInput<'a> {
        self.candidates = Some(cands);
        self
    }
    /// **Rank by priorities the caller already has** (stage 5 D10 L8: the
    /// kernel's), 1:1 with `cands`: the planner's step 4 uses them instead of
    /// running §7 itself. Under §9.1's overrides a dropped candidate's priority
    /// is dropped with it, and a candidate with more or fewer minutes keeps the
    /// priority it was ranked with (kernel/README.md gap 114).
    pub fn with_ranking(mut self, cands: &'a [Candidate], prios: &'a [Prio]) -> PlanInput<'a> {
        self.candidates = Some(cands);
        self.prios = Some(prios);
        self
    }
    /// **Split §7.5's batches into their runs** (D74, parity P64) — the comparand's
    /// [`PlanInput::runs`]; the shipped binary never calls it.
    pub fn with_runs(mut self, runs: bool) -> PlanInput<'a> {
        self.runs = runs;
        self
    }
    /// `tm plan --allow-home` (§13).
    pub fn with_allow_home(mut self, allow_home: bool) -> PlanInput<'a> {
        self.allow_home = allow_home;
        self
    }
    /// Plan a what-if day (§9.1).
    pub fn with_overrides(mut self, overrides: &'a PlanOverrides) -> PlanInput<'a> {
        self.overrides = Some(overrides);
        self
    }
    /// The local date being planned: `state.date`, else `now`'s date — the
    /// host codec's one statement of the rule since W-35
    /// ([`crate::planwire::plan_date`]), so the fork and the request it is
    /// compared with cannot resolve a start on two different days.
    pub fn date(&self) -> NaiveDate {
        crate::planwire::plan_date(self.runtime, self.now)
    }
}

/// The what-if edits §9.1's overtime prompt replans with.
///
/// The prompt shows the consequence of each option by running [`plan`] again
/// with the option applied and diffing (`x extend +1 block → drops: Review the
/// drafts (p3)`). Nothing here is written anywhere: the overrides live for one
/// call.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PlanOverrides {
    /// Replace an item's remaining estimate (minutes) — `s stop` with a
    /// different remainder, or a hand-edited `est:`.
    pub est_min: BTreeMap<Id, u32>,
    /// Add minutes to an item's remaining estimate — `x extend +1 block`.
    pub extra_min: BTreeMap<Id, u32>,
    /// Leave these items out of the day entirely — `d done`, or a drop.
    pub drop: BTreeSet<Id>,
}

impl PlanOverrides {
    /// No overrides.
    pub fn new() -> PlanOverrides {
        PlanOverrides::default()
    }
    /// Set an item's remaining estimate.
    pub fn with_est(mut self, id: &Id, minutes: u32) -> PlanOverrides {
        self.est_min.insert(id.clone(), minutes);
        self
    }
    /// Give an item more minutes (`x extend`).
    pub fn extending(mut self, id: &Id, minutes: u32) -> PlanOverrides {
        *self.extra_min.entry(id.clone()).or_insert(0) += minutes;
        self
    }
    /// Take an item out of the day (`d done`).
    pub fn dropping(mut self, id: &Id) -> PlanOverrides {
        self.drop.insert(id.clone());
        self
    }
    /// True when nothing is overridden.
    pub fn is_empty(&self) -> bool {
        self.est_min.is_empty() && self.extra_min.is_empty() && self.drop.is_empty()
    }

    /// Whether a candidate stays in the day under these overrides.
    fn keeps(&self, c: &Candidate) -> bool {
        !self.drop.contains(&c.id)
    }

    /// Apply the overrides to a candidate list in place.
    fn apply(&self, cands: &mut Vec<Candidate>, cfg: &Config) {
        if self.is_empty() {
            return;
        }
        cands.retain(|c| self.keeps(c));
        let safety = cfg.priority.safety;
        for c in cands.iter_mut() {
            let mut minutes = self.est_min.get(&c.id).copied().unwrap_or(c.remaining_min);
            minutes = minutes.saturating_add(self.extra_min.get(&c.id).copied().unwrap_or(0));
            if minutes == c.remaining_min {
                continue;
            }
            c.remaining_min = minutes;
            c.planned_min = energy::planned_minutes(minutes, c.multiplier);
            c.need_min = if safety.is_finite() && safety > 0.0 {
                (minutes as f64 * safety).round().max(0.0) as u32
            } else {
                minutes
            };
        }
    }
}

// ---------------------------------------------------------------------------
// plan()
// ---------------------------------------------------------------------------

/// `plan(state, now)` (§8) — pure, no I/O, no clock.
///
/// Runs §8.2's eight steps over `input` and returns the whole day: the
/// segments that ended before `input.now` replayed from the log, the rest
/// planned. See the module documentation for the interpretation of each step.
pub fn plan(input: &PlanInput) -> DayPlan {
    Planner::new(input).run().day
}

/// `tm plan --week` (§13, §8.4): the capacity grid plus a light allocation.
pub fn week_plan(input: &PlanInput) -> WeekPlan {
    let run = Planner::new(input).run();
    week_from_run(input, &run)
}

/// §9.1: the items the "x extend +1 block" option would drop.
///
/// Runs [`plan`] twice — once as it stands, once with `blocks` extra blocks on
/// `id` — and returns what the second plan no longer has room for, in the
/// order the first plan had them. This is exactly what the overtime prompt
/// prints after `→ drops:`.
pub fn overtime_drops(input: &PlanInput, id: &Id, blocks: u32) -> Vec<Id> {
    let base = plan(input);
    let extra = PlanOverrides::new().extending(id, blocks.saturating_mul(input.cfg.block_min()));
    let alt = plan(&input.with_overrides(&extra));
    diff(&base, &alt).removed
}

// ---------------------------------------------------------------------------
// The planner itself
// ---------------------------------------------------------------------------

/// A wall the day must flow around (§8.2 step 1).
#[derive(Clone, Debug)]
struct WallSeg {
    id: Id,
    /// Where the blocked time starts (`start − buffer:`).
    blocked_start: DateTime<Tz>,
    /// Where the event itself starts.
    start: DateTime<Tz>,
    /// Where it ends.
    end: DateTime<Tz>,
    instance: Option<InstanceKey>,
    title: String,
    travel_day: bool,
    /// An `state.interrupt` wall, not a calendar one (§9).
    adhoc: bool,
}

/// A window instance waiting for, or holding, a position (§8.2 steps 2 and 6).
#[derive(Clone, Debug)]
struct RoutineInst {
    id: Id,
    instance: Option<InstanceKey>,
    /// The span it may be placed in.
    span: (DateTime<Tz>, DateTime<Tz>),
    dur_min: u32,
    mandatory: bool,
    pref: Option<Pref>,
    placed: Option<(DateTime<Tz>, DateTime<Tz>)>,
    deferred: bool,
}

/// The block running at `now` (§9), and the minutes it still needs.
#[derive(Clone, Debug)]
struct ActiveRun {
    /// The item being worked.
    id: Id,
    /// `now`.
    start: DateTime<Tz>,
    /// `now + (est_min − worked)`, clipped to the wind-down and the next wall.
    end: DateTime<Tz>,
    /// `est_min − worked`, before the clip.
    left_min: u32,
    /// The §8.5 multiplier the estimate was sized with, for the display pair.
    multiplier: Option<f64>,
}

impl ActiveRun {
    /// Minutes the reservation actually occupies.
    fn minutes(&self) -> u32 {
        (self.end - self.start).num_minutes().max(0) as u32
    }
}

/// One assignment group: a batch (§7.5) or a single candidate.
#[derive(Clone, Debug)]
struct Group {
    /// Indices into the candidate list, in key order.
    members: Vec<usize>,
    ci: u8,
    loc: Loc,
    splittable: bool,
    multiplier: f64,
    /// Minutes the day still owes the group.
    left_min: i64,
    /// Minutes the day committed to it (for §11's plan honesty).
    commit_min: u32,
    /// §7.4's sort key: the best key among the members.
    key: priority::SortKey,
}

/// Everything one `plan()` call produced, including the pieces `week_plan`
/// reuses.
struct PlanRun {
    day: DayPlan,
    caps: Vec<UnitCapacity>,
    cands: Vec<Candidate>,
    prios: Vec<Prio>,
}

struct Planner<'a> {
    input: &'a PlanInput<'a>,
    cfg: &'a Config,
    tz: Tz,
    date: NaiveDate,
    now: DateTime<Tz>,
    day_start: DateTime<Tz>,
    day_end: DateTime<Tz>,
    wake: DateTime<Tz>,
    arrival: DateTime<Tz>,
    loc: Loc,
    slept_min: Option<u32>,
    blocks_done: u32,
    blocks_since_break: u32,
    posterior: Posterior,
    wind_down: DateTime<Tz>,
    bed: DateTime<Tz>,
}

impl<'a> Planner<'a> {
    fn new(input: &'a PlanInput<'a>) -> Planner<'a> {
        let cfg = input.cfg;
        let tz = cfg.tz;
        let date = input.date();
        let day_start = capacity::local_dt(tz, date, NaiveTime::MIN);
        let day_end = date
            .succ_opt()
            .map(|d| capacity::local_dt(tz, d, NaiveTime::MIN))
            .unwrap_or(day_start);
        let today = input.replay.day(date);

        // §8.5's `hsw` is measured from the day's `wake`: `state.json`'s, else
        // the `wake` event of the day. A day with neither falls back to the
        // weekday's expected arrival — `Model::wake_or_expected` owns that
        // decision, and the CLI's `Ctx::wake_time` reads it from there too, so
        // both agree on what an unlogged day started at.
        let logged_wake = input
            .runtime
            .wake
            .or_else(|| today.and_then(|d| d.wake).map(|t| t.with_timezone(&tz).time()));
        let wake = capacity::local_dt(
            tz,
            date,
            input
                .model
                .wake_or_expected(logged_wake, date.weekday(), cfg),
        );
        let arrival = input
            .runtime
            .arrival
            .map(|t| capacity::local_dt(tz, date, t))
            .or_else(|| today.and_then(|d| d.arrival).map(|t| t.with_timezone(&tz)))
            .unwrap_or(input.now);
        let loc = input
            .runtime
            .loc
            .as_deref()
            .or_else(|| today.and_then(|d| d.loc.as_deref()))
            .and_then(|s| Loc::parse(s).ok())
            .unwrap_or(Loc::Any);
        let slept_min = input.runtime.wake.and(today.and_then(|d| d.slept_min));

        let energy_obs: Vec<crate::log::EnergyObs> =
            input.replay.energy_on(date).cloned().collect();
        let posterior = Posterior::from_observations(&energy_obs, tz, cfg);

        let blocks_done = input.replay.blocks_done(date);
        let blocks_since_break = today.map_or(0, blocks_since_last_break);

        let wind_down = capacity::local_dt(tz, date, cfg.day.wind_down);
        let mut bed = capacity::local_dt(tz, date, cfg.day.bed);
        if bed <= wind_down {
            bed = day_end.min(wind_down + Duration::minutes(30)).max(wind_down);
        }

        Planner {
            input,
            cfg,
            tz,
            date,
            now: input.now,
            day_start,
            day_end,
            wake,
            arrival,
            loc,
            slept_min,
            blocks_done,
            blocks_since_break,
            posterior,
            wind_down,
            bed,
        }
    }

    fn run(self) -> PlanRun {
        // ---- candidates (§6.2, with §9.1's overrides) -------------------
        let mut cands: Vec<Candidate> = match self.input.candidates {
            Some(list) => list.to_vec(),
            None => priority::collect_candidates(
                self.input.tree,
                self.input.replay,
                self.cfg,
                self.input.model,
                self.date,
                self.now,
            ),
        };
        if let Some(ov) = self.input.overrides {
            ov.apply(&mut cands, self.cfg);
        }

        // ---- step 1: walls ----------------------------------------------
        let walls = self.collect_walls(&cands);
        let conflicts = wall_conflicts(&walls);
        let calendar_walls: Vec<Wall> = walls
            .iter()
            .filter(|w| !w.adhoc)
            .map(|w| (w.blocked_start, w.end))
            .collect();
        let mut blocked: Vec<Wall> = walls.iter().map(|w| (w.blocked_start, w.end)).collect();

        // ---- §8.1 window and budget --------------------------------------
        let (window, budget_blocks) = self.window_and_budget(&calendar_walls);
        let travel_day = walls.iter().any(|w| w.travel_day);
        let mut remaining_budget = capacity::remaining_budget(budget_blocks, self.blocks_done);
        let mut notes: Vec<String> = Vec::new();
        if travel_day {
            remaining_budget = 0;
            notes.push("travel day: no blocks planned (`travel-day` wall today)".to_string());
        }

        // ---- §9: the running block reserves its remaining minutes ---------
        // It is placed before the routines and before the slots are cut, so
        // nothing is scheduled on top of a block that is running.
        let active = self.active_run(&walls, &cands);
        if let Some(run) = &active {
            blocked.push((run.start, run.end));
        }

        // ---- step 2: routines --------------------------------------------
        let (mut routines, sleep) = self.collect_routines(&cands);
        self.place_mandatory_and_pref(&mut routines, &mut blocked);

        // ---- step 3: slots -----------------------------------------------
        let rests: Vec<Wall> = routines.iter().filter_map(|r| r.placed).collect();
        let mut slot_blocked = blocked.clone();
        slot_blocked.push(self.night());
        let from = self.now.max(window.0).min(window.1);
        let cut = capacity::cut_slots_around(
            from,
            window.1,
            &slot_blocked,
            &rests,
            self.cfg,
            self.blocks_since_break,
        );
        let ectx = self.energy_ctx(&self.posterior);
        let slots = capacity::energize(&cut.slots, &ectx);
        let flat = Posterior::none(self.cfg);
        let raw_slots = capacity::energize(&cut.slots, &self.energy_ctx(&flat));

        // ---- step 4: priorities ------------------------------------------
        // The caller's ranking (the kernel's, stage 5 D10 L8) when it handed
        // one in, restricted to the candidates §9.1's overrides keep; else the
        // fork point's lookahead and pass, for a library caller.
        let (prios, caps): (Vec<Prio>, Vec<UnitCapacity>) = match (self.input.prios, self.input.candidates) {
            (Some(given), Some(ranked)) => {
                let prios = ranked
                    .iter()
                    .zip(given)
                    .filter(|(c, _)| self.input.overrides.is_none_or(|ov| ov.keeps(c)))
                    .map(|(_, p)| p.clone())
                    .collect();
                (prios, self.input.caps.map(<[UnitCapacity]>::to_vec).unwrap_or_default())
            }
            _ => {
                let days = priority::lookahead_days(&cands, self.date);
                let minutes = capacity::lookahead(
                    &self.walls_by_date(days),
                    self.cfg,
                    self.input.model,
                    &slots,
                    self.date,
                    days,
                    self.wake.time(),
                );
                let prios = priority::compute(
                    &cands,
                    &minutes,
                    &self.input.runtime.priorities_yesterday,
                    self.cfg,
                    self.date,
                );
                let caps = match self.input.caps {
                    Some(c) => c.to_vec(),
                    None => minutes.iter().map(UnitCapacity::from_minutes).collect(),
                };
                (prios, caps)
            }
        };

        // ---- step 5: assign ----------------------------------------------
        let ranked = priority::sorted_candidates(&prios, &cands);
        let mut groups = self.build_groups(&cands, &prios, &ranked, active.as_ref());
        let mut assign: Vec<Option<usize>> = vec![None; slots.len()];
        // The running block already spent part of the budget, and part of the
        // work its own group was owed. It costs exactly **one** block however
        // long it runs: §8.1 counts `blocks_done` in `done` events, and this
        // block will close as one of them.
        let mut used = u32::from(active.is_some());
        if let Some(run) = &active {
            if let Some(gi) = groups
                .iter()
                .position(|g| g.members.iter().any(|i| cands[*i].id == run.id))
            {
                groups[gi].left_min -= i64::from(run.minutes());
            }
        }
        for i in 0..slots.len() {
            if assign[i].is_some() || used >= remaining_budget {
                continue;
            }
            if let Some(g) = self.pick(&slots[i], i, &slots, &groups, &assign, &cut.breaks) {
                assign[i] = Some(g);
                groups[g].left_min -= i64::from(slots[i].minutes());
                used += 1;
            }
        }

        // ---- step 6: deferred routines -----------------------------------
        // The breaks step 3 cut are part of the day too: a deferred routine
        // that landed on one would be emitted on top of it (§8.2 step 3).
        let kept_breaks = kept_breaks(&cut.breaks, &slots, &assign);
        self.place_deferred(
            &mut routines,
            &slots,
            &mut assign,
            &mut groups,
            &blocked,
            &kept_breaks,
            &cut.breaks,
            &ectx,
            remaining_budget,
            &mut used,
        );
        // A window instance that found no free position is dropped from the
        // day. Say so: §8.2 step 8's diagnostics are where the planner
        // reports what it could not place, and a day that quietly loses lunch
        // is a day no monitor can see. An instance whose window has already
        // closed is not a placement failure — §5.3's expiry owns that — and
        // has an empty remaining span, so it is passed over here.
        for r in routines.iter().filter(|r| r.placed.is_none()) {
            let from = r.span.0.max(self.now);
            if r.span.1 <= from {
                continue;
            }
            notes.push(format!(
                "{}: no free {}m position in {}–{}; not planned today",
                r.id.as_str(),
                r.dur_min,
                fmt_clock(from),
                fmt_clock(r.span.1),
            ));
        }

        // ---- steps 7 and 8 ------------------------------------------------
        let mut day = DayPlan::empty(self.date, window, budget_blocks);
        day.priorities = cands
            .iter()
            .zip(&prios)
            .map(|(c, p)| (c.id.clone(), p.clone()))
            .collect();
        day.segments = self.emit_segments(
            &cands,
            &prios,
            &walls,
            &routines,
            sleep.as_ref(),
            &slots,
            &assign,
            &groups,
            &cut.breaks,
            &blocked,
            active.as_ref(),
        );
        day.segments
            .sort_by(|a, b| a.start.cmp(&b.start).then(a.end.cmp(&b.end)));
        day.diagnostics = self.diagnose(
            &cands,
            &prios,
            &groups,
            &slots,
            &raw_slots,
            &day.segments,
            conflicts,
            remaining_budget,
            notes,
        );
        PlanRun {
            day,
            caps,
            cands,
            prios,
        }
    }

    // -----------------------------------------------------------------
    // §8.1
    // -----------------------------------------------------------------

    /// §8.1: `state.json`'s window and budget when `tm arrive` stored them,
    /// otherwise the formula, with today's walls extending the end.
    fn window_and_budget(&self, walls: &[Wall]) -> ((DateTime<Tz>, DateTime<Tz>), u32) {
        let (window, computed) = match self.input.runtime.window {
            Some((from, to)) => {
                let start = capacity::local_dt(self.tz, self.date, from);
                let mut end = capacity::local_dt(self.tz, self.date, to);
                if end < start {
                    end += Duration::days(1);
                }
                ((start, end), None)
            }
            None => {
                let (end, budget) = capacity::window_and_budget(self.arrival, walls, self.cfg);
                ((self.arrival, end), Some(budget))
            }
        };
        let budget = self
            .input
            .runtime
            .budget
            .or(computed)
            .unwrap_or_else(|| capacity::budget_blocks(self.cfg));
        (window, budget)
    }

    fn energy_ctx<'p>(&self, posterior: &'p Posterior) -> EnergyCtx<'p>
    where
        'a: 'p,
    {
        EnergyCtx::new(
            self.input.model,
            self.cfg,
            posterior,
            self.wake,
            self.loc.clone(),
        )
        .with_slept(self.slept_min)
        .with_blocks_done(self.blocks_done)
        .with_allow_home(self.input.allow_home)
    }

    // -----------------------------------------------------------------
    // §8.2 step 1
    // -----------------------------------------------------------------

    fn collect_walls(&self, cands: &[Candidate]) -> Vec<WallSeg> {
        let tree = self.input.tree;
        let mut out: Vec<WallSeg> = Vec::new();
        let mut seen: BTreeSet<(Id, Option<InstanceKey>)> = BTreeSet::new();
        for c in cands.iter().filter(|c| c.is_wall && c.wall_today) {
            if !c.state.is_open() || !seen.insert((c.id.clone(), c.instance)) {
                continue;
            }
            let Some(item) = tree.get(&c.id) else { continue };
            let (start, end) = match c.window {
                Some(w) => w,
                None => match tree.effective_shape(&c.id) {
                    Shape::Interval { start, end } => (
                        capacity::local_dt(self.tz, start.date(), start.time()),
                        capacity::local_dt(self.tz, end.date(), end.time()),
                    ),
                    _ => continue,
                },
            };
            let buffer = item.buffer.map_or(0, |d| d.as_minutes());
            let blocked_start = start - Duration::minutes(i64::from(buffer));
            let (s, e) = (
                blocked_start.max(self.day_start),
                end.min(self.day_end).max(blocked_start.max(self.day_start)),
            );
            if e <= s {
                continue;
            }
            out.push(WallSeg {
                id: c.id.clone(),
                blocked_start: s,
                start: start.max(s),
                end: e,
                instance: c.instance,
                title: c.title.clone(),
                travel_day: item.is_travel_day(),
                adhoc: false,
            });
        }
        // §9: an interruption that has not been resumed is an ad-hoc wall
        // running to `now`.
        if let Some(interrupt) = &self.input.runtime.interrupt {
            if let Some(started) = interrupt.started {
                let start = capacity::local_dt(self.tz, self.date, started).max(self.day_start);
                if self.now > start {
                    out.push(WallSeg {
                        id: interrupt.id.clone().unwrap_or_else(|| Id::new("")),
                        blocked_start: start,
                        start,
                        end: self.now,
                        instance: None,
                        title: "interruption".to_string(),
                        travel_day: false,
                        adhoc: true,
                    });
                }
            }
        }
        out.sort_by(|a, b| a.blocked_start.cmp(&b.blocked_start).then(a.id.as_str().cmp(b.id.as_str())));
        out
    }

    /// Every open Interval in the tree, clipped per day — what the §8.4
    /// lookahead flows around on future days.
    fn walls_by_date(&self, days: u32) -> WallsByDate {
        let tree = self.input.tree;
        let mut out: WallsByDate = WallsByDate::new();
        for item in tree.iter() {
            if !item.state.is_open() {
                continue;
            }
            let key = Tree::key_of(item);
            let Shape::Interval { start, end } = tree.effective_shape(&key) else {
                continue;
            };
            let buffer = item.buffer.map_or(0, |d| d.as_minutes());
            let s = capacity::local_dt(self.tz, start.date(), start.time())
                - Duration::minutes(i64::from(buffer));
            let e = capacity::local_dt(self.tz, end.date(), end.time());
            if e <= s {
                continue;
            }
            for i in 0..i64::from(days) {
                let Some(d) = self.date.checked_add_signed(Duration::days(i)) else {
                    break;
                };
                let from = capacity::local_dt(self.tz, d, NaiveTime::MIN);
                let Some(next) = d.succ_opt() else { break };
                let to = capacity::local_dt(self.tz, next, NaiveTime::MIN);
                let (a, b) = (s.max(from), e.min(to));
                if b > a {
                    out.entry(d).or_default().push((a, b));
                }
            }
        }
        out
    }

    // -----------------------------------------------------------------
    // §8.2 step 2
    // -----------------------------------------------------------------

    /// Today's stretch of an item's `win:HH:MM-HH:MM` daily range, when it has
    /// one (an overnight range runs into tomorrow).
    fn daily_window(&self, id: &Id) -> Option<(DateTime<Tz>, DateTime<Tz>)> {
        let item = self.input.tree.get(id)?;
        let crate::model::Shape::Window {
            range: crate::model::WindowRange::Daily { from, to },
            ..
        } = item.shape
        else {
            return None;
        };
        let start = capacity::local_dt(self.tz, self.date, from);
        let mut end = capacity::local_dt(self.tz, self.date, to);
        if end <= start {
            end += Duration::days(1);
        }
        Some((start, end))
    }

    /// Today's window instances, and the one that is sleep.
    fn collect_routines(&self, cands: &[Candidate]) -> (Vec<RoutineInst>, Option<RoutineInst>) {
        let mut out: Vec<RoutineInst> = Vec::new();
        let mut sleep: Option<RoutineInst> = None;
        for c in cands {
            if c.is_wall || c.is_optional || !c.eligible() {
                continue;
            }
            let Some((ws, we)) = c.window else { continue };
            let dur_min = if c.remaining_min > 0 {
                c.remaining_min
            } else {
                continue;
            };
            // A carried instance whose window has closed may go anywhere left
            // in the day (§5.3: it is still mandatory today) — but a `win:`
            // with a daily range keeps its hours: laundry carried from last
            // week is still a 09:00–21:00 job.
            //
            // So does an occurrence that has *not* closed. §5.1: `win:` is the
            // daily window on the date. An occurrence that spans several days
            // (`every:week`, `after-done:2d~1d`) reports one span covering all
            // of them — 2026-09-07T09:00..2026-09-13T21:00 for a weekly
            // 09:00–21:00 chore — and clipping that to today alone would leave
            // 00:00–24:00, letting §8.2 steps 2 and 6 place the routine hours
            // outside its stated window.
            let hours = self.daily_window(&c.id);
            let span = if we <= self.now {
                let (a, b) = hours.unwrap_or((self.day_start, self.day_end));
                (a.max(self.now).max(self.day_start), b.max(self.now))
            } else {
                let (mut a, mut b) = (ws.max(self.day_start), we.min(self.day_end));
                if let Some((ha, hb)) = hours {
                    a = a.max(ha);
                    b = b.min(hb);
                }
                (a, b)
            };
            let inst = RoutineInst {
                id: c.id.clone(),
                instance: c.instance,
                span,
                dur_min,
                mandatory: c.mandatory,
                pref: self.input.tree.get(&c.id).and_then(|i| i.pref),
                placed: None,
                deferred: false,
            };
            let overnight = we.date_naive() > ws.date_naive();
            if sleep.is_none()
                && (c.id.as_str().eq_ignore_ascii_case("sleep")
                    || (overnight && dur_min >= SLEEP_MIN_MINUTES))
            {
                sleep = Some(inst);
                continue;
            }
            out.push(inst);
        }
        // Mandatory first, then by the moment the window closes: the tightest
        // window claims its position first.
        out.sort_by(|a, b| {
            b.mandatory
                .cmp(&a.mandatory)
                .then(a.span.1.cmp(&b.span.1))
                .then(a.id.as_str().cmp(b.id.as_str()))
        });
        (out, sleep)
    }

    /// The evening the day is over: everything from `wind_down` on. Nothing is
    /// cut, placed or filled there (§8.2 step 2's "sleep and wind-down define
    /// the hard end of the day"); only a mandatory instance with nowhere else
    /// to go may reach into it.
    ///
    /// It runs to the end of *tomorrow*, not to midnight: §8.1's wall
    /// extension can push the window past midnight (a six-hour evening wall on
    /// a late day does), and the small hours are not a second working evening.
    fn night(&self) -> Wall {
        (
            self.wind_down.min(self.day_end),
            self.day_end + Duration::days(1),
        )
    }

    /// §8.2 step 2: mandatory instances take the earliest feasible position in
    /// their window; a free `pref:` anchor is honoured; the rest defer.
    fn place_mandatory_and_pref(&self, routines: &mut [RoutineInst], blocked: &mut Vec<Wall>) {
        for r in routines.iter_mut() {
            let dur = Duration::minutes(i64::from(r.dur_min));
            let from = r.span.0.max(self.now);
            let mut day_only = blocked.clone();
            day_only.push(self.night());
            if r.mandatory {
                // Before the wind-down if at all possible; inside it only when
                // the window leaves no other choice.
                let start = earliest_free(from, r.span.1, dur, &day_only)
                    .or_else(|| earliest_free(from, r.span.1, dur, blocked));
                if let Some(start) = start {
                    r.placed = Some((start, start + dur));
                    blocked.push((start, start + dur));
                    continue;
                }
                r.deferred = true;
                continue;
            }
            let anchor = match &r.pref {
                Some(Pref::WakePlus(d)) => {
                    Some(self.wake + Duration::minutes(i64::from(d.as_minutes())))
                }
                Some(Pref::At(t)) => Some(capacity::local_dt(self.tz, self.date, *t)),
                None => None,
            };
            if let Some(anchor) = anchor {
                if anchor >= from
                    && anchor + dur <= r.span.1
                    && !overlaps_any(anchor, anchor + dur, &day_only)
                {
                    r.placed = Some((anchor, anchor + dur));
                    blocked.push((anchor, anchor + dur));
                    continue;
                }
            }
            r.deferred = true;
        }
    }

    // -----------------------------------------------------------------
    // §8.2 step 5
    // -----------------------------------------------------------------

    fn build_groups(
        &self,
        cands: &[Candidate],
        prios: &[Prio],
        ranked: &[&Candidate],
        active: Option<&ActiveRun>,
    ) -> Vec<Group> {
        let index = |c: &Candidate| {
            cands
                .iter()
                .position(|x| std::ptr::eq(x, c))
                .expect("ranked candidates come from cands")
        };
        let mut out = Vec::new();
        for batch in priority::batches(ranked, self.cfg) {
            let members: Vec<usize> = batch
                .ids
                .iter()
                .filter_map(|id| {
                    ranked
                        .iter()
                        .find(|c| c.id == *id && !c.is_wall && !c.is_optional && c.window.is_none())
                        .map(|c| index(c))
                })
                .collect();
            if members.is_empty() {
                continue; // a wall, an optional or a window instance
            }
            // §8.2 step 5's `loc` and `atomic` filters are written about the
            // *item*, and §7.5 batches by `ci` and size alone: a batch may
            // well mix a `loc:out` errand, an `atomic` job and a desk task.
            // Splitting the batch by both keeps the filters honest in both
            // directions — the errand does not ride into the lounge, and it
            // does not take the rest of its batch out of the day with it. The
            // item that is *running* is split out for the same reason: the
            // minutes its block still needs are its own, not its batch's.
            for members in split_by_filters(cands, &members, active.map(|r| &r.id), self.input.runs) {
                let first = &cands[members[0]];
                let planned: u32 = members.iter().map(|i| cands[*i].planned_min).sum();
                let cap_left = members
                    .iter()
                    .filter_map(|i| cands[*i].cap_left_min())
                    .min()
                    .unwrap_or(u32::MAX);
                let commit = planned.min(cap_left);
                out.push(Group {
                    ci: batch.ci,
                    loc: first.loc.clone(),
                    splittable: first.splittable,
                    multiplier: first.multiplier,
                    left_min: i64::from(commit),
                    commit_min: commit,
                    key: members
                        .iter()
                        .map(|m| priority::sort_key(&prios[*m], &cands[*m]))
                        .min()
                        .expect("a group has members"),
                    members,
                });
            }
        }
        // §7.4's key order, restored: §7.5's batching gathers *forward*, so a
        // batch sits at its leader's position and carries its members with it
        // — but a member split off above is on its own again and takes its own
        // place in the queue. The sort is stable, so an unsplit batch does not
        // move.
        out.sort_by(|a, b| a.key.cmp(&b.key));
        out
    }

    /// §9: the block running at `now` reserves the rest of *its block*.
    ///
    /// This is a *fact*, not an assignment: it is not filtered by §8.2 step 5
    /// (there is no preemption mid-block), it survives a spent budget and an
    /// item `collect_candidates` calls ineligible, and it is reserved before
    /// step 2 so nothing is planned on top of it. It yields only to a wall —
    /// §8.2 step 1 places those first and puts nothing in their overlap — and
    /// to the wind-down.
    ///
    /// The reservation ends at the end of the block in progress (`started +
    /// block_min`, rolled forward while that instant is past), never at the
    /// end of the item's whole remaining estimate: §8.2 step 5 protects "its
    /// current slot", one block. Reserving the estimate made a six-block item
    /// swallow the afternoon in one uninterrupted segment — every routine
    /// window inside it (lunch, dinner) vanished from the plan with no
    /// diagnostic, and step 3's `break_after_blocks` break never fell due
    /// because there were no slots to count. After its block the item
    /// re-competes for slots like any other candidate (with its group's
    /// `left_min` already reduced by what the run spends), which is what
    /// makes an Active item that is still the best candidate simply keep
    /// going, one block at a time.
    fn active_run(&self, walls: &[WallSeg], cands: &[Candidate]) -> Option<ActiveRun> {
        let active = self.input.runtime.active.as_ref()?;
        if active.paused {
            return None; // the timer is stopped; the block is not running
        }
        // §9: an interruption pauses the Active block. Its ad-hoc wall covers
        // `now`, so there is nothing to reserve.
        if walls.iter().any(|w| w.adhoc && w.end >= self.now) {
            return None;
        }
        // §9.1's `d done` what-if: the block is finished in that plan.
        if self
            .input
            .overrides
            .is_some_and(|ov| ov.drop.contains(&active.id))
        {
            return None;
        }
        let started = capacity::local_dt(self.tz, self.date, active.started);
        // The log knows the worked minutes exactly (pauses excluded); the
        // clock is the fallback when it holds no open block.
        let worked = self
            .input
            .replay
            .open_block
            .as_ref()
            .filter(|b| b.id == active.id.as_str())
            .map(|b| b.worked_min_at(self.now.fixed_offset()))
            .unwrap_or_else(|| (self.now - started).num_minutes().max(0) as u32);
        let left = active.est_min.saturating_sub(worked);
        if left == 0 {
            return None; // overtime: §9.1's prompt owns the day from here
        }
        // Never past the wind-down, never into a wall.
        let limit = if self.now < self.wind_down {
            self.wind_down.min(self.day_end)
        } else {
            self.day_end
        };
        if limit <= self.now {
            return None;
        }
        let wall_spans: Vec<Wall> = walls.iter().map(|w| (w.blocked_start, w.end)).collect();
        let (free_from, free_to) = capacity::free_intervals(self.now, limit, &wall_spans)
            .into_iter()
            .next()?;
        if free_from > self.now {
            return None; // a wall covers `now`
        }
        let end = (self.now + Duration::minutes(i64::from(left)))
            .min(free_to)
            .min(self.current_block_end(started));
        if end <= self.now {
            return None;
        }
        Some(ActiveRun {
            id: active.id.clone(),
            start: self.now,
            end,
            left_min: left,
            multiplier: cands
                .iter()
                .find(|c| c.id == active.id)
                .map(|c| c.multiplier),
        })
    }

    /// The end of the `block_min` block that started at `started` and is
    /// still running at `now` — always strictly after `now`.
    ///
    /// A block that has overrun its length is still the block you are in
    /// (§9.1's overrun prompt is what ends it, not the clock), so the
    /// boundary rolls forward a whole block at a time rather than falling
    /// behind `now`. A zero `block_min` (a hand-edited config; §10.2 says
    /// saturate rather than panic) puts no bound on the run at all.
    fn current_block_end(&self, started: DateTime<Tz>) -> DateTime<Tz> {
        let block_min = i64::from(self.cfg.block_min());
        if block_min <= 0 {
            return self.day_end;
        }
        let elapsed = (self.now - started).num_minutes().max(0);
        started + Duration::minutes((elapsed / block_min + 1) * block_min)
    }

    /// §8.2 step 5's filter, applied to one slot.
    fn pick(
        &self,
        slot: &Slot,
        i: usize,
        slots: &[Slot],
        groups: &[Group],
        assign: &[Option<usize>],
        breaks: &[capacity::Break],
    ) -> Option<usize> {
        for (gi, g) in groups.iter().enumerate() {
            if g.left_min <= 0 || g.ci > slot.energy || !self.loc_ok(&g.loc) {
                continue;
            }
            // §8.2 step 3's rule again, defensively: nothing demanding runs
            // after wind-down.
            if slot.start >= self.wind_down && g.ci >= 4 {
                continue;
            }
            if !g.splittable && !contiguous_fits(slots, assign, i, g.left_min as u32, breaks) {
                continue;
            }
            return Some(gi);
        }
        None
    }

    /// `loc:` compatibility (§8.2 step 5). An item with no constraint fits
    /// anywhere, and an unknown current location constrains nothing.
    fn loc_ok(&self, item: &Loc) -> bool {
        match item {
            Loc::Any => true,
            other => self.loc == Loc::Any || *other == self.loc,
        }
    }

    // -----------------------------------------------------------------
    // §8.2 step 6
    // -----------------------------------------------------------------

    #[allow(clippy::too_many_arguments)]
    fn place_deferred(
        &self,
        routines: &mut [RoutineInst],
        slots: &[Slot],
        assign: &mut [Option<usize>],
        groups: &mut [Group],
        blocked: &[Wall],
        kept_breaks: &[capacity::Break],
        breaks: &[capacity::Break],
        ectx: &EnergyCtx,
        remaining_budget: u32,
        used: &mut u32,
    ) {
        for ri in 0..routines.len() {
            if routines[ri].placed.is_some() {
                continue;
            }
            let dur = Duration::minutes(i64::from(routines[ri].dur_min));
            let (span_from, span_to) = routines[ri].span;
            let from = span_from.max(self.now);
            if span_to <= from {
                continue;
            }
            let mut occupied = occupied_now(blocked, routines, slots, assign);
            occupied.extend(kept_breaks.iter().map(|b| (b.start, b.end)));
            occupied.push(self.night());
            // Every free position inside the window; the lowest predicted
            // energy wins, ties by the earlier start (§8.2 step 6).
            let best = capacity::free_intervals(from, span_to, &occupied)
                .into_iter()
                .filter(|(a, b)| *b - *a >= dur)
                .map(|(a, _)| (ectx.energy_at(a, self.blocks_done, 0), a))
                .min();
            if let Some((_, start)) = best {
                routines[ri].placed = Some((start, start + dur));
                routines[ri].deferred = true;
                continue;
            }
            if !routines[ri].mandatory {
                continue; // it can wait; the day has no room for it
            }
            // A mandatory instance displaces the lowest-energy assigned block
            // inside its window; the group returns to the pool.
            occupied.pop(); // a last-chance instance may reach into the night
            if let Some((_, start)) = capacity::free_intervals(from, span_to, &occupied)
                .into_iter()
                .filter(|(a, b)| *b - *a >= dur)
                .map(|(a, _)| (ectx.energy_at(a, self.blocks_done, 0), a))
                .min()
            {
                routines[ri].placed = Some((start, start + dur));
                routines[ri].deferred = true;
                continue;
            }
            let victim = slots
                .iter()
                .enumerate()
                .filter(|(i, s)| {
                    assign[*i].is_some()
                        && s.start >= from
                        && s.end <= span_to
                        && s.end - s.start >= dur
                })
                .min_by(|(ai, a), (bi, b)| {
                    a.energy.cmp(&b.energy).then(bi.cmp(ai)).then(a.start.cmp(&b.start))
                })
                .map(|(i, _)| i);
            let Some(vi) = victim else { continue };
            let gi = assign[vi].expect("victim slots are assigned");
            groups[gi].left_min += i64::from(slots[vi].minutes());
            assign[vi] = None;
            *used = used.saturating_sub(1);
            routines[ri].placed = Some((slots[vi].start, slots[vi].start + dur));
            routines[ri].deferred = true;
            // Re-place the displaced group in a later free slot, if any.
            for j in vi + 1..slots.len() {
                if assign[j].is_some() || *used >= remaining_budget {
                    continue;
                }
                if let Some(g) = self.pick(&slots[j], j, slots, groups, assign, breaks) {
                    assign[j] = Some(g);
                    groups[g].left_min -= i64::from(slots[j].minutes());
                    *used += 1;
                    break;
                }
            }
        }
    }

    // -----------------------------------------------------------------
    // §8.2 steps 7 and 8: the timeline
    // -----------------------------------------------------------------

    #[allow(clippy::too_many_arguments)]
    fn emit_segments(
        &self,
        cands: &[Candidate],
        prios: &[Prio],
        walls: &[WallSeg],
        routines: &[RoutineInst],
        sleep: Option<&RoutineInst>,
        slots: &[Slot],
        assign: &[Option<usize>],
        groups: &[Group],
        breaks: &[capacity::Break],
        blocked: &[Wall],
        active: Option<&ActiveRun>,
    ) -> Vec<Segment> {
        let mut out: Vec<Segment> = self.past_segments(walls);
        // §9: while an interruption runs, nothing is running.
        let interrupted = walls.iter().any(|w| w.adhoc && w.end >= self.now);
        out.extend(self.open_block_segment(active.is_none() && !interrupted, walls));

        // §9: the block that is running — a reservation, not a slot, so it
        // carries no slot energy (see the module docs, choice 5b).
        if let Some(run) = active {
            out.push(Segment {
                start: run.start,
                end: run.end,
                kind: SegKind::Block,
                energy: None,
                item: Some(run.id.clone()),
                instance: None,
                flags: SegFlags {
                    current: true,
                    planned_min: Some(run.left_min),
                    multiplier: run.multiplier,
                    note: Some(format!("running · {}m left", run.left_min)),
                    ..SegFlags::default()
                },
            });
        }

        // Walls, and the blocked time a `buffer:` puts in front of them.
        for w in walls {
            if w.adhoc {
                out.push(Segment {
                    start: w.blocked_start,
                    end: w.end,
                    kind: SegKind::Lost,
                    energy: None,
                    item: (!w.id.is_empty()).then(|| w.id.clone()),
                    instance: None,
                    flags: SegFlags {
                        // It has not ended: the next replan shows it longer.
                        open: w.end >= self.now,
                        note: Some("interruption".to_string()),
                        ..SegFlags::default()
                    },
                });
                continue;
            }
            if w.start > w.blocked_start {
                out.push(Segment {
                    start: w.blocked_start,
                    end: w.start,
                    kind: SegKind::Wall,
                    energy: None,
                    item: Some(w.id.clone()),
                    instance: w.instance,
                    flags: SegFlags {
                        note: Some(format!("buffer before {}", w.title)),
                        ..SegFlags::default()
                    },
                });
            }
            out.push(Segment {
                start: w.start,
                end: w.end,
                kind: SegKind::Wall,
                energy: None,
                item: Some(w.id.clone()),
                instance: w.instance,
                flags: SegFlags {
                    note: w.travel_day.then(|| "travel day".to_string()),
                    ..SegFlags::default()
                },
            });
        }

        // Routines — and the Window-shaped *tasks* step 2 places the same way.
        //
        // §4.3 draws the two differently: a `routines.md` / `optional.md` line
        // is the day's furniture and takes the `·` glyph (`11:20 ·  lunch
        // 30m`), while `^a3`'s `Pick up package win:… dur:20m` is a backlog
        // item on §7's scale and keeps its `ci`, its `pN` and its `⚠`
        // (`15:10  1 p0 ⚠  Pick up package  20m  due today`). The segment says
        // which by carrying an `energy` (and `hot` at `p = 0`) or not.
        for r in routines {
            let Some((start, end)) = r.placed else { continue };
            let item = self.input.tree.get(&r.id);
            let scheduled =
                item.is_some_and(|i| !matches!(i.horizon, Horizon::Routine | Horizon::Optional));
            let energy = if scheduled { item.map(|i| i.ci) } else { None };
            let hot = scheduled
                && cands
                    .iter()
                    .position(|c| c.id == r.id)
                    .is_some_and(|i| prios[i].p == 0);
            out.push(Segment {
                start,
                end,
                kind: SegKind::Routine,
                energy,
                item: Some(r.id.clone()),
                instance: r.instance,
                flags: SegFlags {
                    mandatory: r.mandatory,
                    deferred: r.deferred,
                    hot,
                    planned_min: Some(r.dur_min),
                    ..SegFlags::default()
                },
            });
        }

        // Blocks and batches; the Rest slots are emitted last, once the
        // deferred routines and the optionals have taken their share of them.
        for (i, slot) in slots.iter().enumerate() {
            if let Some(gi) = assign[i] {
                let g = &groups[gi];
                let ids: Vec<Id> = g.members.iter().map(|m| cands[*m].id.clone()).collect();
                let kind = if ids.len() > 1 {
                    SegKind::Batch(ids.clone())
                } else {
                    SegKind::Block
                };
                let gap = slot.energy.saturating_sub(g.ci);
                // `⚠` is §7.2's `p = 0` — the priority, not the `hot` key.
                let hot = g.members.iter().any(|m| prios[*m].p == 0);
                out.push(Segment {
                    start: slot.start,
                    end: slot.end,
                    kind,
                    energy: Some(slot.energy),
                    item: (ids.len() == 1).then(|| ids[0].clone()),
                    instance: None,
                    flags: SegFlags {
                        underused: gap >= 2,
                        hot,
                        planned_min: Some(g.commit_min),
                        multiplier: Some(g.multiplier),
                        note: (gap >= 2)
                            .then(|| format!("↓ slot {}, item {}", slot.energy, g.ci)),
                        ..SegFlags::default()
                    },
                });
            }
        }

        // Breaks: a break belongs to the day only when work touches it —
        // between two blocks, or right after the last one — and never when a
        // routine has taken that stretch (§8.2 step 6 places into the free
        // positions; a break it could not avoid is time it took over).
        let kept_breaks: Vec<capacity::Break> = kept_breaks(breaks, slots, assign)
            .into_iter()
            .filter(|b| {
                !routines
                    .iter()
                    .filter_map(|r| r.placed)
                    .any(|(a, z)| b.start < z && a < b.end)
            })
            .collect();
        for b in &kept_breaks {
            out.push(Segment {
                start: b.start,
                end: b.end,
                kind: SegKind::Break,
                energy: None,
                item: None,
                instance: None,
                flags: SegFlags {
                    planned_min: Some(b.minutes()),
                    ..SegFlags::default()
                },
            });
        }

        // §8.2 step 7: optionals fill what is left before wind-down.
        let mut occupied: Vec<Wall> = blocked.to_vec();
        occupied.extend(routines.iter().filter_map(|r| r.placed));
        occupied.extend(
            slots
                .iter()
                .enumerate()
                .filter(|(i, _)| assign[*i].is_some())
                .map(|(_, s)| (s.start, s.end)),
        );
        occupied.extend(kept_breaks.iter().map(|b| (b.start, b.end)));
        let mut taken: Vec<Wall> = Vec::new();
        let mut free =
            capacity::free_intervals(self.now.max(self.day_start), self.wind_down, &occupied);
        for c in cands.iter().filter(|c| c.is_optional && c.eligible()) {
            let want = c.cap_left_min().map_or(c.remaining_min, |l| c.remaining_min.min(l));
            if want == 0 {
                continue;
            }
            let dur = Duration::minutes(i64::from(want));
            let Some(k) = free.iter().position(|(a, b)| *b - *a >= dur) else {
                continue;
            };
            let (a, b) = free[k];
            out.push(Segment {
                start: a,
                end: a + dur,
                kind: SegKind::Optional,
                energy: None,
                item: Some(c.id.clone()),
                instance: c.instance,
                flags: SegFlags {
                    planned_min: Some(want),
                    ..SegFlags::default()
                },
            });
            taken.push((a, a + dur));
            if b - (a + dur) > Duration::zero() {
                free[k] = (a + dur, b);
            } else {
                free.remove(k);
            }
        }

        // What is left of the unassigned slots is Rest (§8.2 step 7).
        taken.extend(routines.iter().filter_map(|r| r.placed));
        for (i, slot) in slots.iter().enumerate() {
            if assign[i].is_some() {
                continue;
            }
            for (a, b) in capacity::free_intervals(slot.start, slot.end, &taken) {
                out.push(Segment {
                    start: a,
                    end: b,
                    kind: SegKind::Rest,
                    energy: Some(slot.energy),
                    item: None,
                    instance: None,
                    flags: SegFlags::default(),
                });
            }
        }

        // Wind-down and sleep close the day.
        if self.wind_down > self.now && self.wind_down < self.day_end {
            out.push(Segment {
                start: self.wind_down,
                end: self.bed.min(self.day_end),
                kind: SegKind::WindDown,
                energy: None,
                item: None,
                instance: None,
                flags: SegFlags::default(),
            });
        }
        let sleep_start = self.bed.max(self.now).min(self.day_end);
        if sleep_start < self.day_end {
            out.push(Segment {
                start: sleep_start,
                end: self.day_end,
                kind: SegKind::Sleep,
                energy: None,
                item: sleep.map(|s| s.id.clone()),
                instance: sleep.and_then(|s| s.instance),
                flags: SegFlags {
                    planned_min: sleep.map(|s| s.dur_min),
                    ..SegFlags::default()
                },
            });
        }
        out
    }

    /// The stretch of the running block that has already happened (§12.1:
    /// left of the cursor the timeline renders the log).
    ///
    /// [`Replay`] closes a block's sub-segment only when something interrupts
    /// it, so the minutes a block has been running for are in no segment;
    /// without this the day bar shows a hole where the current block is.
    /// `mark_current` is true when there is nothing left to reserve (the block
    /// is in overtime), and the `▶` belongs on this half instead. An
    /// interruption ends the stretch where it started: §9 pauses the block.
    fn open_block_segment(&self, mark_current: bool, walls: &[WallSeg]) -> Option<Segment> {
        let open = self.input.replay.open_block.as_ref()?;
        let since = open.since?.with_timezone(&self.tz);
        if since < self.day_start || since >= self.now {
            return None;
        }
        let mut end = self.now.min(self.day_end);
        for w in walls.iter().filter(|w| w.adhoc && w.blocked_start > since) {
            end = end.min(w.blocked_start);
        }
        if end <= since {
            return None;
        }
        Some(Segment {
            start: since,
            end,
            kind: SegKind::Block,
            energy: None,
            item: Some(Id::new(open.id.clone())),
            instance: None,
            flags: SegFlags {
                current: mark_current,
                // It is still running: the next replan shows it longer.
                open: true,
                note: Some(format!("{}m so far", open.worked_min_at(self.now.fixed_offset()))),
                ..SegFlags::default()
            },
        })
    }

    /// §8.3's stability half: everything that ended before `now` comes from
    /// the log, so a replan cannot move it.
    ///
    /// **A Pause is drawn only where no calendar wall of the day is** — the
    /// owner's D65 (parity P56, README gaps 3044, 3141, 3142), the kernel's
    /// `Planner.pastSpans`. D61 stops a running block's timer at a wall with
    /// the log's own `pause`/`unpause` pair, and this function drew that Pause
    /// as a `paused` Lost row over the meeting beside the meeting's own Wall
    /// row — a span `tm review day` counts as no lost time. The part of a
    /// paused row a wall's blocked span covers is cut out ([`cut_out`]); a
    /// pause no wall touches is drawn whole, and no other kind is cut. This is
    /// fork 4748911's function changed on purpose, so that the shipped `tm
    /// plan` and the kernel's day draw the same rows until R3 deletes it.
    fn past_segments(&self, walls: &[WallSeg]) -> Vec<Segment> {
        let Some(day) = self.input.replay.day(self.date) else {
            return Vec::new();
        };
        let blocked: Vec<(DateTime<Tz>, DateTime<Tz>)> = walls
            .iter()
            .filter(|w| !w.adhoc)
            .map(|w| (w.blocked_start, w.end))
            .collect();
        let mut out = Vec::new();
        for seg in &day.segments {
            let start = seg.start.with_timezone(&self.tz).max(self.day_start);
            let end = seg.end.with_timezone(&self.tz).min(self.now);
            if end <= start {
                continue;
            }
            let spans = match &seg.kind {
                SegmentKind::Pause { .. } => cut_out(&blocked, start, end),
                _ => vec![(start, end)],
            };
            for (start, end) in spans {
                out.push(self.past_segment(day, &seg.kind, start, end));
            }
        }
        out
    }

    /// One replayed row of [`Self::past_segments`] over one span.
    fn past_segment(
        &self,
        day: &crate::log::DayReplay,
        kind: &SegmentKind,
        start: DateTime<Tz>,
        end: DateTime<Tz>,
    ) -> Segment {
        let (kind, item, instance, note) = match kind {
            SegmentKind::Block { id } => {
                (SegKind::Block, Some(Id::new(id.clone())), None, None)
            }
            SegmentKind::Pause { id } => (
                SegKind::Lost,
                Some(Id::new(id.clone())),
                None,
                Some(crate::dayplan::PAUSED_NOTE.to_string()),
            ),
            SegmentKind::Interrupt { id } => (
                SegKind::Lost,
                id.clone().map(Id::new),
                None,
                Some("interruption".to_string()),
            ),
            SegmentKind::Break { r#where } => {
                (SegKind::Break, None, None, r#where.clone())
            }
            SegmentKind::Routine { item, inst } => (
                SegKind::Routine,
                Some(Id::new(item.clone())),
                parse_instance_key(inst),
                None,
            ),
            SegmentKind::Idle { attributed } => (
                SegKind::Lost,
                None,
                None,
                Some(attributed.clone()),
            ),
        };
        // A logged routine segment *is* the completion; a block segment is
        // done when the log closed the item today.
        let done = kind == SegKind::Routine
            || item
                .as_ref()
                .is_some_and(|id| day.done.iter().any(|d| d == id.as_str()));
        Segment {
            start,
            end,
            kind,
            energy: None,
            item,
            instance,
            flags: SegFlags {
                done,
                note,
                ..SegFlags::default()
            },
        }
    }

    // -----------------------------------------------------------------
    // §8.2 step 8
    // -----------------------------------------------------------------

    #[allow(clippy::too_many_arguments)]
    fn diagnose(
        &self,
        cands: &[Candidate],
        prios: &[Prio],
        groups: &[Group],
        slots: &[Slot],
        raw_slots: &[Slot],
        segments: &[Segment],
        conflicts: Vec<(Id, Id)>,
        remaining_budget: u32,
        mut notes: Vec<String>,
    ) -> Diagnostics {
        let mut d = Diagnostics {
            conflicts,
            ..Diagnostics::default()
        };

        for seg in segments.iter().filter(|s| s.flags.underused && s.kind.is_work()) {
            let energy = seg.energy.unwrap_or(0);
            for id in seg.items() {
                let ci = cands
                    .iter()
                    .find(|c| c.id == id)
                    .map_or(0, |c| c.ci);
                d.underused.push((id, energy, ci));
            }
        }

        let assigned: BTreeSet<Id> = segments
            .iter()
            .filter(|s| s.kind.is_work())
            .flat_map(Segment::items)
            .collect();

        // §8.2 step 8: A-capacity that went to Rest while a ci-5 item waited.
        let rest_high: u32 = segments
            .iter()
            .filter(|s| s.kind == SegKind::Rest && s.energy.unwrap_or(0) >= 4)
            .map(Segment::minutes)
            .sum();
        if rest_high > 0
            && cands
                .iter()
                .any(|c| c.ci == 5 && !c.is_wall && !c.is_optional && !assigned.contains(&c.id))
        {
            d.a_capacity_lost = rest_high;
        }

        for (c, p) in cands.iter().zip(prios) {
            if c.is_wall {
                continue;
            }
            if (p.is_hot() || p.class == priority::PrioClass::HotFlag) && !d.hot.contains(&c.id) {
                d.hot.push(c.id.clone());
            }
            if p.is_impossible() {
                if let Some(until) = p.until {
                    d.impossible.push((c.id.clone(), p.shortfall_min, until));
                }
            }
            if c.waiting && !d.waiting.contains(&c.id) {
                d.waiting.push(c.id.clone());
            }
            if let Some(Ineligible::Blocked(deps)) = c.ineligible_reason() {
                d.blocked.push((c.id.clone(), deps));
            }
            // A posterior downgrade cost this item its slot (§8.2 step 8).
            if !assigned.contains(&c.id)
                && c.eligible()
                && !c.is_optional
                && c.window.is_none()
                && slots
                    .iter()
                    .zip(raw_slots)
                    .any(|(s, raw)| raw.energy >= c.ci && s.energy < c.ci)
                && !d.deferred.contains(&c.id)
            {
                d.deferred.push(c.id.clone());
            }
        }

        // §9: what the tail dropped — eligible work that got no slot at all.
        for g in groups {
            for m in &g.members {
                let c = &cands[*m];
                if !assigned.contains(&c.id) && !d.dropped_tail.contains(&c.id) {
                    d.dropped_tail.push(c.id.clone());
                }
            }
        }

        // §11 plan honesty: what the day committed to, over what it can spend.
        // **Saturating** (W-36 track T, README gap 2929's residue): an estimate
        // at the host's `u32` width is legal on the edit wire, and two such
        // commitments summed with `+` panicked a debug build here (`tm plan`
        // and `tm now` exited 101 once the kernel stopped faulting first) and
        // wrap in a release one. Identical on every sum that fits.
        let committed: u32 = groups
            .iter()
            .filter(|g| g.members.iter().any(|m| assigned.contains(&cands[*m].id)))
            .map(|g| g.commit_min)
            .fold(0u32, u32::saturating_add);
        // `budget` comes from `state.json`, which is hand-editable: saturate
        // rather than panic on a nonsense value (§10.2).
        let budget_min = remaining_budget.saturating_mul(self.cfg.block_min());
        d.plan_honesty = (budget_min > 0).then(|| f64::from(committed) / f64::from(budget_min));

        // §11 rest debt: planned break minutes today's log lost.
        if let Some(day) = self.input.replay.day(self.date) {
            d.rest_debt_min = day
                .breaks
                .iter()
                .map(|b| b.planned_min.saturating_sub(b.actual_or_planned()))
                .sum();
        }

        if remaining_budget == 0 && self.blocks_done > 0 {
            notes.push(format!(
                "budget spent: {} blocks done, the rest of the day is rest",
                self.blocks_done
            ));
        }
        d.notes = notes;
        d
    }
}

/// Blocks worked since today's last logged break (§8.2 step 3's counter on a
/// mid-day replan).
fn blocks_since_last_break(day: &crate::log::DayReplay) -> u32 {
    let last_break = day.breaks.iter().map(|b| b.t).max();
    day.starts
        .iter()
        .filter(|s| last_break.is_none_or(|t| s.t > t))
        .count() as u32
}

/// **`[a, b)` with every span of `spans` cut out** — the kernel's
/// `Planner.cutAll`, span by span in the order given: each piece loses what
/// the span covers and keeps what is left before it and after it; an empty
/// span cuts nothing. The pieces come out in ascending order and never empty.
fn cut_out(
    spans: &[(DateTime<Tz>, DateTime<Tz>)],
    a: DateTime<Tz>,
    b: DateTime<Tz>,
) -> Vec<(DateTime<Tz>, DateTime<Tz>)> {
    let mut pieces = vec![(a, b)];
    for &(lo, hi) in spans {
        if hi <= lo {
            continue;
        }
        pieces = pieces
            .into_iter()
            .flat_map(|(x, y)| {
                let mut left = Vec::new();
                if x < y.min(lo) {
                    left.push((x, y.min(lo)));
                }
                if x.max(hi) < y {
                    left.push((x.max(hi), y));
                }
                left
            })
            .collect();
    }
    pieces
}

/// §8.2 step 1: overlapping walls, each pair once, at the later one.
fn wall_conflicts(walls: &[WallSeg]) -> Vec<(Id, Id)> {
    let mut out = Vec::new();
    for (i, a) in walls.iter().enumerate() {
        for b in walls.iter().skip(i + 1) {
            if a.adhoc || b.adhoc {
                continue;
            }
            if b.start < a.end && a.start < b.end {
                out.push((a.id.clone(), b.id.clone()));
            }
        }
    }
    out
}

fn overlaps_any(start: DateTime<Tz>, end: DateTime<Tz>, walls: &[Wall]) -> bool {
    walls.iter().any(|(a, b)| start < *b && *a < end)
}

/// The earliest `t ≥ from` with `[t, t + dur) ⊆ [from, to)` free of `walls`.
fn earliest_free(
    from: DateTime<Tz>,
    to: DateTime<Tz>,
    dur: Duration,
    walls: &[Wall],
) -> Option<DateTime<Tz>> {
    capacity::free_intervals(from, to, walls)
        .into_iter()
        .find(|(a, b)| *b - *a >= dur)
        .map(|(a, _)| a)
}

/// Everything a deferred routine must flow around right now.
fn occupied_now(
    blocked: &[Wall],
    routines: &[RoutineInst],
    slots: &[Slot],
    assign: &[Option<usize>],
) -> Vec<Wall> {
    let mut out: Vec<Wall> = blocked.to_vec();
    out.extend(routines.iter().filter_map(|r| r.placed));
    out.extend(
        slots
            .iter()
            .enumerate()
            .filter(|(i, _)| assign[*i].is_some())
            .map(|(_, s)| (s.start, s.end)),
    );
    out
}

/// §8.2 step 5's `atomic` rule: enough free, time-contiguous slots from `i`.
///
/// "Contiguous ... before the next wall" is read as the spec writes it: a
/// **wall** (or a routine, or anything else that took the time) ends the run,
/// a planned break does not. Sitting through the 20-minute break the planner
/// itself inserted is not a context switch, and counting it as one would make
/// every `atomic` item longer than `break_after_blocks × block_min`
/// unplaceable on any day.
///
/// The test is the spec's, and only the spec's: **free slots**, not slots the
/// day's remaining budget can pay for. Bounding the run by the budget instead
/// would break §8.3's tail-drop invariant — shrinking the budget by one block
/// makes a non-splittable item skip its slot and a *different* candidate take
/// it, which is a re-shuffle rather than the removal of a suffix.
fn contiguous_fits(
    slots: &[Slot],
    assign: &[Option<usize>],
    i: usize,
    need: u32,
    breaks: &[capacity::Break],
) -> bool {
    let mut have = 0u32;
    let mut j = i;
    while j < slots.len() {
        if assign[j].is_some() {
            return false;
        }
        if j > i && slots[j].start != slots[j - 1].end {
            let gap = (slots[j - 1].end, slots[j].start);
            if !breaks.iter().any(|b| b.start == gap.0 && b.end == gap.1) {
                return false; // a wall or a routine interrupts the run
            }
        }
        have += slots[j].minutes();
        if have >= need {
            return true;
        }
        j += 1;
    }
    false
}

/// The breaks that belong to the day: a break is planned only when work
/// touches it — between two blocks, or right after the last one (§8.2 step 3).
fn kept_breaks(
    breaks: &[capacity::Break],
    slots: &[Slot],
    assign: &[Option<usize>],
) -> Vec<capacity::Break> {
    breaks
        .iter()
        .filter(|b| {
            slots
                .iter()
                .enumerate()
                .any(|(i, s)| assign[i].is_some() && (s.end == b.start || s.start == b.end))
        })
        .copied()
        .collect()
}

/// One batch's members split into runs of equal `(loc:, splittable, running)`
/// — the halves of §8.2 step 5's filter that are written about the item, not
/// about the batch, plus the block that is already running (§9). Each run keeps
/// the batch's key order.
fn split_by_filters(
    cands: &[Candidate],
    members: &[usize],
    active: Option<&Id>,
    runs: bool,
) -> Vec<Vec<usize>> {
    let mut out: Vec<((Loc, bool, bool), Vec<usize>)> = Vec::new();
    for m in members {
        let key = (
            cands[*m].loc.clone(),
            cands[*m].splittable,
            active == Some(&cands[*m].id),
        );
        // D74 (P64): the runs join only the LAST bucket; the fork's group-by, the first
        // bucket with the key wherever it sits.
        let bucket = if runs {
            out.last_mut().filter(|(k, _)| *k == key)
        } else {
            out.iter_mut().find(|(k, _)| *k == key)
        };
        match bucket {
            Some((_, group)) => group.push(*m),
            None => out.push((key, vec![*m])),
        }
    }
    out.into_iter().map(|(_, group)| group).collect()
}

/// The `inst` field of a §10.1 `routine` event as an [`InstanceKey`].
fn parse_instance_key(s: &str) -> Option<InstanceKey> {
    if let Some(n) = s.strip_prefix('#') {
        return n.parse::<u32>().ok().map(InstanceKey::Nth);
    }
    NaiveDate::parse_from_str(s, "%Y-%m-%d")
        .ok()
        .map(InstanceKey::Date)
}

// ---------------------------------------------------------------------------
// diff (§13 `tm plan --diff`, §11 "Replans and drift")
// ---------------------------------------------------------------------------

/// `tm plan --diff` (§13): what the replan moved, added and dropped.
///
/// Items are compared by the start of their **first** segment, so an item that
/// keeps its opening slot but gains another one does not count as moved.
/// `drift_min` is the Σ of the absolute moves, which is what the `plan` event
/// records and §11's "Replans and drift" monitor adds up.
pub fn diff(old: &DayPlan, new: &DayPlan) -> PlanDiff {
    let starts = |p: &DayPlan| -> BTreeMap<Id, DateTime<Tz>> {
        let mut out: BTreeMap<Id, DateTime<Tz>> = BTreeMap::new();
        for seg in &p.segments {
            if matches!(seg.kind, SegKind::Rest | SegKind::Break) {
                continue;
            }
            for id in seg.items() {
                out.entry(id).and_modify(|t| *t = (*t).min(seg.start)).or_insert(seg.start);
            }
        }
        out
    };
    let (a, b) = (starts(old), starts(new));
    let mut out = PlanDiff::default();
    for (id, old_start) in &a {
        match b.get(id) {
            Some(new_start) if new_start != old_start => {
                let drift = (*new_start - *old_start).num_minutes().unsigned_abs() as u32;
                out.moved.push((id.clone(), *old_start, *new_start));
                out.drift_min += drift;
            }
            Some(_) => {}
            None => out.removed.push(id.clone()),
        }
    }
    for id in b.keys() {
        if !a.contains_key(id) {
            out.added.push(id.clone());
        }
    }
    out
}

// ---------------------------------------------------------------------------
// explain (§13)
// ---------------------------------------------------------------------------

/// `tm plan --explain ^id` (§13), the whole line.
///
/// [`priority::explanation`] gives §7's half (`p = k(3) + bin(u=0.31 → +1) =
/// 4; need 2b, avail 6b by 2026-09-11; deps ok; cap 2b/d: 1b used`); this adds
/// §8's (`slot 11:50 energy 4, ci 3, gap 1`) from the plan, and says why the
/// item has no slot when it has none.
pub fn explain(day: &DayPlan, id: &Id, cands: &[Candidate], cfg: &Config) -> String {
    let prios: Vec<Prio> = day.priorities.iter().map(|(_, p)| p.clone()).collect();
    let Some(mut ex) = priority::explanation(id, cands, &prios, cfg) else {
        return format!("{} is not a candidate today", id.token());
    };
    let ci = cands.iter().find(|c| c.id == *id).map_or(0, |c| c.ci);
    match day.segment_of(id) {
        Some(seg) => {
            let start = seg.start.format("%H:%M");
            ex.slot_part = Some(match seg.energy {
                Some(energy) => format!(
                    "slot {start} energy {energy}, ci {ci}, gap {}",
                    energy.saturating_sub(ci)
                ),
                None => format!("slot {start} ({})", kind_label(&seg.kind)),
            });
        }
        None => {
            let why = if day.diagnostics.deferred.contains(id) {
                "no slot (energy downgrade deferred it)"
            } else if day.diagnostics.dropped_tail.contains(id) {
                "no slot (dropped from the tail)"
            } else if day.diagnostics.waiting.contains(id) {
                "no slot (waiting)"
            } else {
                "no slot today"
            };
            ex.slot_part = Some(why.to_string());
        }
    }
    ex.to_string()
}

// ---------------------------------------------------------------------------
// tm plan --week (§8.4, §13)
// ---------------------------------------------------------------------------

/// One day of [`WeekPlan`].
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct WeekDay {
    /// The date.
    pub date: NaiveDate,
    /// Expected slot minutes at every energy level (§8.4).
    pub capacity_min: u32,
    /// Minutes this allocation gives to work.
    pub planned_min: u32,
    /// Blocks of work. **Today** it is the number of blocks [`plan`] actually
    /// scheduled (§8.4: "the actual remaining slots from §8.2 step 3"), which
    /// is not `planned_min / block_min` — a day ends in a short block, and a
    /// slot cut off by a wall is a whole block of the budget all the same. The
    /// later days have no slots, so there it is `planned_min / block_min`.
    pub blocks: u32,
    /// `(item, minutes)`, in assignment order.
    pub items: Vec<(Id, u32)>,
}

/// `tm plan --week` (§13): the §8.4 capacity grid and a light allocation.
///
/// Today is the real [`plan`] — every segment it produced. The later days are
/// **not** simulated: no routines, no breaks, no batching, no `atomic`
/// contiguity, no interruptions and no posterior; each candidate simply takes
/// capacity at energy ≥ its `ci`, earliest day first, in §7.4's key order,
/// never past its deadline and never past its `max:` cap. It answers "does the
/// week hold the work" — which is what the grid is for — and nothing finer.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct WeekPlan {
    /// The first day (today).
    pub from: NaiveDate,
    /// The per-day allocation.
    pub days: Vec<WeekDay>,
    /// The §8.4 lookahead itself, in exact units.
    pub capacity: Vec<UnitCapacity>,
    /// [`capacity::week_grid_units`] over `capacity` (floors, display only).
    pub grid: String,
    /// Every candidate's priority (§7).
    pub priorities: Vec<(Id, Prio)>,
    /// What did not fit anywhere in the week.
    pub unplaced: Vec<Id>,
    /// Prose worth printing.
    pub notes: Vec<String>,
}

fn week_from_run(input: &PlanInput, run: &PlanRun) -> WeekPlan {
    let cfg = input.cfg;
    let block_min = cfg.block_min().max(1);
    let from = run.day.date;
    let horizon = run.caps.len().min(7);
    let capacity: Vec<UnitCapacity> = run.caps.iter().take(horizon).copied().collect();
    // The allocation reserves in exact units (the owner's D10: the kernel's
    // lookahead is a mixture, so a day's capacity is no longer whole minutes;
    // kernel/README.md gap 94). Minutes appear only as floors, for display.
    let mut work = capacity.clone();
    let mut planned_units: Vec<u128> = vec![0; capacity.len()];

    let mut days: Vec<WeekDay> = capacity
        .iter()
        .map(|c| WeekDay {
            date: c.date,
            capacity_min: c.total_floor(),
            planned_min: 0,
            blocks: 0,
            items: Vec::new(),
        })
        .collect();

    // Today comes from the real plan.
    if let Some(today) = days.first_mut() {
        for seg in run.day.segments.iter().filter(|s| s.kind.is_work()) {
            today.planned_min += seg.minutes();
            today.blocks += 1;
            for id in seg.items() {
                match today.items.iter_mut().find(|(i, _)| *i == id) {
                    Some(entry) => entry.1 += seg.minutes(),
                    None => today.items.push((id, seg.minutes())),
                }
            }
        }
        work[0] = UnitCapacity::empty(from);
        planned_units[0] = u128::from(today.planned_min) * CAP_DEN;
    }

    let ranked = priority::sorted_candidates(&run.prios, &run.cands);
    let mut unplaced = Vec::new();
    for c in ranked {
        if c.is_wall || c.is_optional || c.window.is_some() {
            continue;
        }
        let today_min: u32 = days
            .first()
            .map(|d| {
                d.items
                    .iter()
                    .filter(|(i, _)| *i == c.id)
                    .map(|(_, m)| *m)
                    .sum()
            })
            .unwrap_or(0);
        let cap_left = c.cap_left_min().unwrap_or(u32::MAX);
        let mut left = u128::from(c.planned_min.min(cap_left).saturating_sub(today_min)) * CAP_DEN;
        if left == 0 {
            continue;
        }
        let due = c.effective_due.map(|d| d.date_naive());
        for (i, day) in work.iter_mut().enumerate().skip(1) {
            if left == 0 {
                break;
            }
            if due.is_some_and(|d| day.date > d) {
                break;
            }
            let take = left.min(day.at_least_units(c.ci));
            if take == 0 {
                continue;
            }
            capacity::reserve_units(std::slice::from_mut(day), take, c.ci);
            left -= take;
            planned_units[i] += take;
            days[i].items.push((c.id.clone(), capacity::floor_minutes(take)));
        }
        if left > 0 {
            unplaced.push(c.id.clone());
        }
    }
    for (d, units) in days.iter_mut().zip(&planned_units).skip(1) {
        d.planned_min = capacity::floor_minutes(*units);
        d.blocks = d.planned_min / block_min;
    }

    // Both figures are the floors of their exact sums.
    let planned = capacity::floor_minutes(planned_units.iter().sum());
    let total = capacity::floor_minutes(capacity.iter().map(UnitCapacity::total_units).sum());
    let mut notes = Vec::new();
    if total > 0 {
        notes.push(format!(
            "planned {} of {} ({}%)",
            priority::fmt_blocks(planned, block_min),
            priority::fmt_blocks(total, block_min),
            (f64::from(planned) / f64::from(total) * 100.0).round() as u32
        ));
    }
    WeekPlan {
        from,
        days,
        grid: capacity::week_grid_units(&capacity),
        capacity,
        priorities: run.day.priorities.clone(),
        unplaced,
        notes,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn instance_keys_round_trip() {
        assert_eq!(
            parse_instance_key("2026-09-07"),
            Some(InstanceKey::Date(
                NaiveDate::from_ymd_opt(2026, 9, 7).expect("date")
            ))
        );
        assert_eq!(parse_instance_key("#6"), Some(InstanceKey::Nth(6)));
        assert_eq!(parse_instance_key("nonsense"), None);
    }

    #[test]
    fn overrides_change_the_minutes_they_name() {
        let cfg = Config::default();
        let id = Id::new("t3");
        let mut cands = vec![Candidate::new(id.clone(), 4, 3, 60, &cfg)];
        PlanOverrides::new().extending(&id, 60).apply(&mut cands, &cfg);
        assert_eq!(cands[0].remaining_min, 120);
        assert_eq!(cands[0].planned_min, 120);
        PlanOverrides::new().dropping(&id).apply(&mut cands, &cfg);
        assert!(cands.is_empty());
    }

    /// **D58's comparand, while the fork is here to be compared with** (stage 6
    /// W-35, README gap 2680): the host's `planwire::grown` is `apply`'s own
    /// arithmetic on every candidate this sweep builds — the three facts
    /// `apply` rewrites, or `None` exactly where it leaves them alone.
    ///
    /// 8,820 cases: seven safeties (the shipped 1.3, 1, 0, a negative and a
    /// NaN among them — `apply` and `safety_minutes` both fall back to the
    /// minutes), nine multipliers (0, a negative and a NaN, which
    /// `energy::planned_minutes` sizes as the minutes), seven remainders up to
    /// the `u32` edge, four `est` overrides and five extensions up to
    /// `u32::MAX`. `planwire`'s own test holds the answers by value, so the
    /// arithmetic stays pinned after this file is deleted at R3.
    #[test]
    fn the_host_grows_the_facts_apply_grows() {
        let mut compared = 0usize;
        let mut grew = 0usize;
        for safety in [1.3, 1.0, 0.0, -2.0, f64::NAN, 1.15, 2.5] {
            let mut cfg = Config::default();
            cfg.priority.safety = safety;
            for mult in [1.0, 1.6, 0.5, 0.0, -1.0, f64::NAN, 1.25, 1.3333333333333333, 2.2] {
                for remaining in [0u32, 1, 29, 60, 123, 481, u32::MAX - 7] {
                    for est in [None, Some(0u32), Some(30), Some(remaining)] {
                        for extra in [0u32, 1, 60, 90, u32::MAX] {
                            let id = Id::new("x1");
                            let mut c = Candidate::new(id.clone(), 3, 2, remaining, &cfg);
                            c.multiplier = mult;
                            c.planned_min = energy::planned_minutes(remaining, mult);
                            let mut ov = PlanOverrides::new();
                            if let Some(e) = est {
                                ov = ov.with_est(&id, e);
                            }
                            if extra > 0 {
                                ov = ov.extending(&id, extra);
                            }
                            let mut cands = vec![c.clone()];
                            ov.apply(&mut cands, &cfg);
                            let fork = (cands[0].remaining_min, cands[0].planned_min, cands[0].need_min);
                            let host = match crate::planwire::grown(&c, est, extra, &cfg) {
                                Some(g) => {
                                    grew += 1;
                                    (g.remaining_min, g.planned_min, g.need_min)
                                }
                                None => (c.remaining_min, c.planned_min, c.need_min),
                            };
                            assert_eq!(
                                host, fork,
                                "safety {safety} multiplier {mult} remaining {remaining} est {est:?} extra {extra}"
                            );
                            compared += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(compared, 7 * 9 * 7 * 4 * 5);
        // Both branches were taken, so neither half of the comparison is vacuous.
        assert!(grew > 0 && grew < compared, "{grew} of {compared} grew");
    }
}
