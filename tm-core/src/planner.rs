//! Planner — the types of tm-spec-v1.md §8: what `plan(state, now)` takes
//! ([`PlanInput`]) and what it returns ([`DayPlan`], [`Segment`],
//! [`SegKind`], [`SegFlags`], [`Diagnostics`]).
//!
//! **The algorithm of §8.2 is not here yet.** [`plan`] returns an empty day
//! with the window and budget from `state.json` and a note in
//! `diagnostics.notes` saying so, which is enough for `emit.rs`, the CLI and
//! the TUI to be written against the real shapes. Everything else in §8 —
//! walls, routines, slot cutting, assignment, deferred routines, rest and
//! optionals — lands in a later milestone (M4).
//!
//! # API overview
//!
//! * [`PlanInput`] — the tree, the log and its [`Replay`], the config, the
//!   learned [`Model`], the runtime [`RuntimeState`] and `now`, plus two
//!   optional shortcuts (`caps`, `candidates`) so a caller that has already
//!   built the §8.4 lookahead or the §6.2 candidate list does not build it
//!   twice. All borrowed; the struct is `Copy`.
//! * [`plan`]`(&PlanInput) -> DayPlan` — pure, no I/O, no clock (§17.2).
//! * [`DayPlan`] `{ date, window, budget_blocks, segments, diagnostics,
//!   priorities }` — the whole plan. [`DayPlan::hash`] is the FNV-1a digest
//!   `state.last_plan_hash` and the `plan` log event (§10.1) carry, taken
//!   over where each segment sits and what is in it — never over how the day
//!   is going — so a replan that moves nothing hashes the same.
//! * [`Segment`] `{ start, end, kind, energy, item, instance, flags }` — one
//!   row of the timeline (§4.3) and one cell run of the day bar (§12.1).
//!   [`SegKind`] names what it is; [`SegFlags`] carries the marks (`✓ ▶ ↓ ⚠`)
//!   and the `2b×1.6` display pair.
//! * [`Diagnostics`] — §8.2 step 8's list, plus §11's `plan_honesty` and
//!   `rest_debt_min`, plus a `notes` field for anything the planner wants to
//!   say in prose.
//!
//! Every type is `Serialize` (for `tm plan --json`), `Clone`, `Debug` and
//! `PartialEq` (for the §8.3 purity property tests). Instants are
//! `DateTime<Tz>` in `cfg.tz`.

use chrono::{DateTime, NaiveDate};
use chrono_tz::Tz;
use serde::Serialize;

use crate::capacity::{self, DayCapacity};
use crate::config::Config;
use crate::energy::Model;
use crate::log::{Log, Replay};
use crate::model::{Dep, Id, InstanceKey};
use crate::priority::{Candidate, Prio};
use crate::store::RuntimeState;
use crate::tree::Tree;

/// The offset basis of the 64-bit FNV-1a hash behind [`DayPlan::hash`].
const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
/// The prime of the 64-bit FNV-1a hash.
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

/// Everything `plan()` reads (§8).
///
/// `log` is the raw event log (§10.1) and `replay` is `log::replay(...)` over
/// it — the planner never derives the replay itself, so the caller decides
/// the range once and the TUI can reuse it across replans.
#[derive(Clone, Copy, Debug)]
pub struct PlanInput<'a> {
    /// The parsed plan tree (§6).
    pub tree: &'a Tree,
    /// The raw event log (§10.1).
    pub log: &'a Log,
    /// `log::replay(...)` over `log` — block minutes, instance statuses,
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
    /// The §8.4 lookahead, when the caller already built it (ascending by
    /// date). `None` = the planner builds its own.
    pub caps: Option<&'a [DayCapacity]>,
    /// The §6.2 candidates, when the caller already built them. `None` = the
    /// planner calls `priority::collect_candidates`.
    pub candidates: Option<&'a [Candidate]>,
}

impl<'a> PlanInput<'a> {
    /// The required half of the input; `caps` and `candidates` stay `None`.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        tree: &'a Tree,
        log: &'a Log,
        replay: &'a Replay,
        cfg: &'a Config,
        model: &'a Model,
        runtime: &'a RuntimeState,
        now: DateTime<Tz>,
    ) -> PlanInput<'a> {
        PlanInput {
            tree,
            log,
            replay,
            cfg,
            model,
            runtime,
            now,
            caps: None,
            candidates: None,
        }
    }
    /// Reuse a lookahead the caller already computed.
    pub fn with_caps(mut self, caps: &'a [DayCapacity]) -> PlanInput<'a> {
        self.caps = Some(caps);
        self
    }
    /// Reuse a candidate list the caller already computed.
    pub fn with_candidates(mut self, cands: &'a [Candidate]) -> PlanInput<'a> {
        self.candidates = Some(cands);
        self
    }
    /// The local date being planned: `state.date`, else `now`'s date.
    pub fn date(&self) -> NaiveDate {
        self.runtime.date.unwrap_or_else(|| self.now.date_naive())
    }
}

/// What a segment of the day is (§8, §4.3's timeline marks).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum SegKind {
    /// One item working in one slot.
    Block,
    /// Several small items sharing one block (§7.5).
    Batch(Vec<Id>),
    /// A planned break (§8.2 step 3).
    Break,
    /// A window instance: meal, shower, laundry (§5.2).
    Routine,
    /// An Interval instance: meeting, exam, flight (§8.2 step 1).
    Wall,
    /// A slot no candidate could take (§8.2 step 7).
    Rest,
    /// An `optional.md` item in a rest slot (§7.2, §8.2 step 7).
    Optional,
    /// The wind-down before bed (§16 `wind_down`).
    WindDown,
    /// Sleep (the `sleep` routine's window).
    Sleep,
    /// Time lost to an interruption or a leak (§9, §11).
    Lost,
}

/// The marks and display values of one segment (§4.3's `✓ ▶ ↓ ⚠`, §12.1).
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
pub struct SegFlags {
    /// `✓` — already logged done.
    pub done: bool,
    /// `▶` — the block running at `now`.
    pub current: bool,
    /// `↓` — slot energy exceeds the item's `ci` by ≥ 2 (§8.2 step 5).
    pub underused: bool,
    /// `⚠` — the item is `p = 0` (§7.2).
    pub hot: bool,
    /// A mandatory window instance (§5.2).
    pub mandatory: bool,
    /// A routine deferred to §8.2 step 6.
    pub deferred: bool,
    /// Drawn as the "plan as it stood at arrival" ghost row (§12.1).
    pub ghost: bool,
    /// Minutes the planner set aside: `est × multiplier` (§8.5).
    pub planned_min: Option<u32>,
    /// The duration multiplier behind `planned_min` (`2b×1.6`).
    pub multiplier: Option<f64>,
    /// Free text for the timeline's trailing note (`due today`, `↓ slot 4,
    /// item 3`).
    pub note: Option<String>,
}

/// One row of the day (§8).
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Segment {
    /// Start instant, in `cfg.tz`.
    pub start: DateTime<Tz>,
    /// End instant, in `cfg.tz`.
    pub end: DateTime<Tz>,
    /// What it is.
    pub kind: SegKind,
    /// Predicted slot energy 0..=5 (§8.5), when the segment has one.
    pub energy: Option<u8>,
    /// The item it belongs to.
    pub item: Option<Id>,
    /// The instance, for routines and calendar walls (§5.1).
    pub instance: Option<InstanceKey>,
    /// Marks and display values.
    pub flags: SegFlags,
}

impl Segment {
    /// Length in minutes.
    pub fn minutes(&self) -> u32 {
        (self.end - self.start).num_minutes().max(0) as u32
    }
}

/// What the plan could not do, and why (§8.2 step 8, §11).
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
pub struct Diagnostics {
    /// `(item, slot energy, item ci)` for every slot with a gap ≥ 2.
    pub underused: Vec<(Id, u8, u8)>,
    /// Minutes of energy ≥ 4 left Rest while ci-5 items existed but were
    /// ineligible.
    pub a_capacity_lost: u32,
    /// Items at `p = 0` through `u ≥ 1` (§7.3).
    pub hot: Vec<Id>,
    /// `(item, shortfall minutes, deadline)` for IMPOSSIBLE items (§7.3).
    pub impossible: Vec<(Id, u32, NaiveDate)>,
    /// Overlapping walls the planner refused to resolve (§8.2 step 1).
    pub conflicts: Vec<(Id, Id)>,
    /// Items held out by an unsatisfied dependency (§5.5).
    pub blocked: Vec<(Id, Vec<Dep>)>,
    /// ci-5 items that lost their slot to a posterior downgrade (§8.2 step 8).
    pub deferred: Vec<Id>,
    /// Items in `[?]` (§5.1).
    pub waiting: Vec<Id>,
    /// Items dropped from the tail when the day lost minutes (§9).
    pub dropped_tail: Vec<Id>,
    /// §11: planned blocks ÷ realistic budget; warn above 1.1.
    pub plan_honesty: Option<f64>,
    /// §11: planned break minutes skipped or cut, cumulative today.
    pub rest_debt_min: u32,
    /// Anything else worth saying in prose (`tm plan` prints these).
    pub notes: Vec<String>,
}

/// What [`DayPlan::hash`] digests: where a segment sits and what is in it,
/// without the marks that only say how the day is going.
#[derive(Debug, Serialize)]
struct Placement<'a> {
    start: &'a DateTime<Tz>,
    end: &'a DateTime<Tz>,
    kind: &'a SegKind,
    energy: Option<u8>,
    item: Option<&'a Id>,
    instance: Option<&'a InstanceKey>,
    planned_min: Option<u32>,
    multiplier: Option<f64>,
}

impl<'a> Placement<'a> {
    fn of(seg: &'a Segment) -> Placement<'a> {
        Placement {
            start: &seg.start,
            end: &seg.end,
            kind: &seg.kind,
            energy: seg.energy,
            item: seg.item.as_ref(),
            instance: seg.instance.as_ref(),
            planned_min: seg.flags.planned_min,
            multiplier: seg.flags.multiplier,
        }
    }
}

/// One planned day (§8).
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct DayPlan {
    /// The date planned.
    pub date: NaiveDate,
    /// The working window `[start, end]` (§8.1).
    pub window: (DateTime<Tz>, DateTime<Tz>),
    /// Blocks the day may spend (§8.1).
    pub budget_blocks: u32,
    /// The timeline, in start order.
    pub segments: Vec<Segment>,
    /// What could not be done.
    pub diagnostics: Diagnostics,
    /// Every candidate's priority (§7), for the Queue and `--explain`.
    pub priorities: Vec<(Id, Prio)>,
}

impl DayPlan {
    /// An empty day with the given window and budget.
    pub fn empty(
        date: NaiveDate,
        window: (DateTime<Tz>, DateTime<Tz>),
        budget_blocks: u32,
    ) -> DayPlan {
        DayPlan {
            date,
            window,
            budget_blocks,
            segments: Vec::new(),
            diagnostics: Diagnostics::default(),
            priorities: Vec::new(),
        }
    }

    /// The plan's identity: a 64-bit FNV-1a digest of the day's *placement*,
    /// as 16 lowercase hex digits.
    ///
    /// This is what `state.last_plan_hash` stores and what the `plan` log
    /// event carries (§10.1, §10.2): two plans that put the same items in the
    /// same slots hash the same, so a replan that moves nothing is not logged
    /// as a replan and does not count towards §11's "Replans and drift".
    ///
    /// Hashed: each segment's `start`, `end`, `kind`, `energy`, `item`,
    /// `instance` and the `planned_min` / `multiplier` it was sized with.
    /// Not hashed: [`Diagnostics`] and [`DayPlan::priorities`] (they move with
    /// the capacity lookahead without the day itself moving) and every
    /// progress or display flag — `done`, `current`, `ghost`, `note`,
    /// `underused`, `hot`, `mandatory`, `deferred`. Those change with each
    /// `tm done` and at every block boundary; hashing them would make a
    /// standing day look replanned all afternoon.
    pub fn hash(&self) -> String {
        let placement: Vec<Placement<'_>> = self.segments.iter().map(Placement::of).collect();
        let body = serde_json::to_string(&placement)
            .unwrap_or_else(|_| format!("{placement:?}"));
        let mut h = FNV_OFFSET;
        for byte in body.as_bytes() {
            h ^= u64::from(*byte);
            h = h.wrapping_mul(FNV_PRIME);
        }
        format!("{h:016x}")
    }

    /// Σ minutes of `Block` and `Batch` segments — the §8.3 "no overbooking"
    /// invariant's left-hand side.
    pub fn block_minutes(&self) -> u32 {
        self.segments
            .iter()
            .filter(|s| matches!(s.kind, SegKind::Block | SegKind::Batch(_)))
            .map(Segment::minutes)
            .sum()
    }
}

/// `plan(state, now)` (§8) — pure, no I/O.
///
/// **Not implemented yet.** The returned [`DayPlan`] has §8.1's window and
/// budget, no segments, and a note in `diagnostics.notes` saying the planner
/// is not implemented. It is a valid, hashable `DayPlan`, so callers can be
/// written and tested against it today.
///
/// The window is `state.json`'s when `tm arrive` stored one; without one
/// (before the first `tm arrive`, or after a rollover cleared it) it is
/// §8.1's formula, through [`capacity::window_and_budget`]: `arrival =
/// runtime.arrival, else now`, `end = min(arrival + window_hours,
/// window_cap)`. The `+ Σ duration(walls inside the window)` half of §8.1
/// arrives with the algorithm (M4): it needs today's walls, which is step 1's
/// work, so this fallback is the wall-free lower bound.
pub fn plan(input: &PlanInput) -> DayPlan {
    let cfg = input.cfg;
    let date = input.date();
    let (window, computed_budget) = match input.runtime.window {
        Some((from, to)) => (
            (
                capacity::local_dt(cfg.tz, date, from),
                capacity::local_dt(cfg.tz, date, to),
            ),
            None,
        ),
        None => {
            let arrival = input
                .runtime
                .arrival
                .map_or(input.now, |t| capacity::local_dt(cfg.tz, date, t));
            let (end, budget) = capacity::window_and_budget(arrival, &[], cfg);
            ((arrival, end), Some(budget))
        }
    };
    let budget_blocks = input
        .runtime
        .budget
        .or(computed_budget)
        .unwrap_or_else(|| capacity::budget_blocks(cfg));
    let mut day = DayPlan::empty(date, window, budget_blocks);
    day.diagnostics
        .notes
        .push("planner not implemented".to_string());
    day
}
