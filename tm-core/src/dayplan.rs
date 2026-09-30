//! **The host's representation of one planned day** — [`DayPlan`], its
//! [`Segment`]s with their [`SegKind`] and [`SegFlags`], §8.2 step 8's
//! [`Diagnostics`], §13's [`PlanDiff`], the plan hash, and the two words every
//! surface shares, [`kind_label`] and [`fmt_clock`].
//!
//! # Why these are not `planner.rs`'s any more (stage 6 W-35, README gap 2721)
//!
//! They were declared in `tm-core/src/planner.rs`, the fork's planner, and R3
//! deletes that file (D48, D50). But they are not the fork's planning: they are
//! the shape the **renderers** read — `emit.rs` (the one padder, D43), the day
//! file, `tm plan --json`, `.tm/last_plan.json`, the TUI's timeline, the ghost
//! row `cli/ghost.rs` builds from recorded starts — and the shape the host
//! decodes the kernel's `plan` answer into (`crate::planwire`, README gap
//! 2720). A day the kernel planned still has to reach those surfaces after R3,
//! so the types had to leave the file before it could be deleted whole.
//!
//! **The move is byte for byte**: every declaration below, its doc comment and
//! its `Serialize` derive are exactly what `planner.rs` held at `fe49a8b`, so
//! `tm plan --json`, `.tm/last_plan.json` and every snapshot are unchanged
//! (serde's derive names no module path). `planner.rs` re-exports all of them
//! until R3, so a caller that still names them through `planner::` compiles
//! unchanged — `tm/tests/planner_invariants.rs` does, and is not this step's to
//! touch.
//!
//! What stayed in `planner.rs`, because it is the fork's planning and dies with
//! it: `plan`, `week_plan`, `overtime_drops`, `diff`, `explain`, `PlanInput`,
//! `PlanOverrides` and `WeekPlan`.

use std::collections::BTreeSet;

use chrono::{DateTime, NaiveDate, Timelike};
use chrono_tz::Tz;
use serde::Serialize;

use crate::model::{Dep, Id, InstanceKey};
use crate::priority::Prio;

/// The offset basis of the 64-bit FNV-1a hash behind [`DayPlan::hash`].
const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
/// The prime of the 64-bit FNV-1a hash.
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

// ---------------------------------------------------------------------------
// Output types
// ---------------------------------------------------------------------------

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

impl SegKind {
    /// True for the two kinds that spend the block budget.
    pub fn is_work(&self) -> bool {
        matches!(self, SegKind::Block | SegKind::Batch(_))
    }
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
    /// The segment is still **open**: its `end` is `now` because the thing it
    /// records has not finished yet — the running interruption (§9) and the
    /// stretch of the running block that has already happened (§12.1).
    ///
    /// §8.3's stability invariant ("a replan changes no segment with `end ≤
    /// now`") is about *settled* segments; an open one necessarily grows with
    /// every replan, because at 13:05 the truth is "interrupted since 12:10"
    /// and at 13:35 it is "interrupted since 12:10" for half an hour longer.
    /// A later plan therefore holds the same segment with a later `end`, never
    /// a different start, kind or item.
    pub open: bool,
    /// Minutes the planner set aside: `est × multiplier` (§8.5).
    pub planned_min: Option<u32>,
    /// The duration multiplier behind `planned_min` (`2b×1.6`).
    pub multiplier: Option<f64>,
    /// Free text for the timeline's trailing note (`due today`, `↓ slot 4,
    /// item 3`).
    ///
    /// It is the **note column** only, so it never repeats what another
    /// column of §4.3's row already prints: not the item's title (that is the
    /// title cell, and `emit` builds `lunch 30m` / `wind-down · bed 22:00`
    /// from the segment itself) and not a finished block's actual (that is
    /// the `(actual)` cell). A renderer prints it verbatim, so a title here
    /// shows up twice on the row.
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
    /// Every item this segment holds (one, or a batch's members).
    pub fn items(&self) -> Vec<Id> {
        match &self.kind {
            SegKind::Batch(ids) => ids.clone(),
            _ => self.item.iter().cloned().collect(),
        }
    }
}

/// What the plan could not do, and why (§8.2 step 8, §9, §11).
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
    ///
    /// Here: Σ over the groups the day *starts* of the minutes they still
    /// need (`remaining × multiplier`, capped by `max:`), over
    /// `remaining_budget × block_min`. A day that opens three six-block
    /// milestones inside a six-block budget scores well above 1 — which is
    /// the over-commitment the monitor is for. `None` when the budget is
    /// zero (a travel day, or a budget already spent).
    ///
    /// Any measure taken over the blocks the plan *assigns* is ≤ 1 by
    /// construction — step 5 stops at the budget — so it could never reach
    /// §11's 1.1 threshold. The ratio is therefore about what the day *takes
    /// on*: on the §4.3 fixture day (which starts `^t3`, `^m1` and `^m2`, 780
    /// minutes of remaining estimate against a 360-minute budget) it reads
    /// 2.17, and the monitor is right to say so — two of those three will not
    /// be finished today. `tests/planner_regressions.rs` pins the reading.
    pub plan_honesty: Option<f64>,
    /// §11: planned break minutes skipped or cut, cumulative today — the
    /// `break` events of today's log whose `actual_min` fell short of their
    /// `planned_min`.
    pub rest_debt_min: u32,
    /// Anything else worth saying in prose (`tm plan` prints these).
    pub notes: Vec<String>,
    /// **Why §8.2 step 5 left an impossible item it admitted without a row**
    /// (the owner's D67, parity P58): the kernel's `Diagnostics.unplaced`,
    /// one `(item, reason)` per listed item step 5's filter admitted before
    /// the walk and the day does not hold. Fork 4748911 names none, so the
    /// fork's own planner leaves it empty.
    ///
    /// **Printed, and not serialised** (README gap 3351): the banner
    /// (`emit::render_banners`) and the TUI's impossible row read it, and
    /// `tm plan --json` and `.tm/last_plan.json` keep the fork's diagnostics
    /// shape. Serialising it would change the diagnostics of 11 of the 41
    /// frozen comparand days (measured at W-38), which the comparand compares
    /// by value; that is a D64(a) re-bless under P58, the comparand's owner's
    /// to take, not this field's to force.
    #[serde(skip)]
    pub unplaced: Vec<(Id, NoPlace)>,
}

/// **Why an impossible item has no row today** — the kernel's
/// `Planner.NoPlace`, the walk's own reasons (D67, parity P58): every run or
/// every slot the item fits went to work ranked before it, or the budget was
/// spent before a place it fits came free.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum NoPlace {
    /// An atomic item: every unbroken run it fits went to other work.
    NoRunLeft,
    /// A splittable item: every slot it fits went to other work.
    NoSlotLeft,
    /// The day's budget was spent before a place it fits came free.
    BudgetSpent,
}

impl NoPlace {
    /// The kernel's name for the reason on the wire (`PlanWire.noPlaceName`).
    pub fn wire_name(self) -> &'static str {
        match self {
            NoPlace::NoRunLeft => "noRunLeft",
            NoPlace::NoSlotLeft => "noSlotLeft",
            NoPlace::BudgetSpent => "budgetSpent",
        }
    }

    /// The reason read back from its wire name; `None` for a name the kernel
    /// does not write.
    pub fn of_wire(name: &str) -> Option<NoPlace> {
        [NoPlace::NoRunLeft, NoPlace::NoSlotLeft, NoPlace::BudgetSpent]
            .into_iter()
            .find(|w| w.wire_name() == name)
    }

    /// The words the banner prints.
    pub fn words(self) -> &'static str {
        match self {
            NoPlace::NoRunLeft => "no run left",
            NoPlace::NoSlotLeft => "no slot left",
            NoPlace::BudgetSpent => "budget spent",
        }
    }
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
        let body =
            serde_json::to_string(&placement).unwrap_or_else(|_| format!("{placement:?}"));
        let mut h = FNV_OFFSET;
        for byte in body.as_bytes() {
            h ^= u64::from(*byte);
            h = h.wrapping_mul(FNV_PRIME);
        }
        format!("{h:016x}")
    }

    /// Σ minutes of every `Block` and `Batch` segment, the replayed morning
    /// included. [`DayPlan::planned_block_minutes`] is the half §8.3's "no
    /// overbooking" invariant bounds.
    pub fn block_minutes(&self) -> u32 {
        self.segments
            .iter()
            .filter(|s| s.kind.is_work())
            .map(Segment::minutes)
            .sum()
    }

    /// Σ minutes of the `Block` and `Batch` segments that start at or after
    /// `from` — the *planned* half of the day, which is what §8.3's "no
    /// overbooking" bounds by `remaining_budget × block_min`
    /// ([`DayPlan::block_minutes`] also counts the blocks the log already
    /// holds, and those were paid for out of `blocks_done`).
    pub fn planned_block_minutes(&self, from: DateTime<Tz>) -> u32 {
        self.segments
            .iter()
            .filter(|s| s.kind.is_work() && s.start >= from)
            .map(Segment::minutes)
            .sum()
    }

    /// The items the plan gives a Block or a Batch to, in time order, without
    /// repeats — §8.3's "assigned set".
    pub fn assigned(&self) -> Vec<Id> {
        let mut seen: BTreeSet<Id> = BTreeSet::new();
        let mut out = Vec::new();
        for seg in self.segments.iter().filter(|s| s.kind.is_work()) {
            for id in seg.items() {
                if seen.insert(id.clone()) {
                    out.push(id);
                }
            }
        }
        out
    }

    /// [`DayPlan::assigned`] restricted to the blocks that start at or after
    /// `from` — the work the plan is *proposing*, without the blocks the log
    /// already holds.
    pub fn assigned_from(&self, from: DateTime<Tz>) -> Vec<Id> {
        let mut seen: BTreeSet<Id> = BTreeSet::new();
        let mut out = Vec::new();
        for seg in self
            .segments
            .iter()
            .filter(|s| s.kind.is_work() && s.start >= from)
        {
            for id in seg.items() {
                if seen.insert(id.clone()) {
                    out.push(id);
                }
            }
        }
        out
    }

    /// The block running at `now` — the `▶` row (§9, §12.1), if any.
    ///
    /// Its minutes are a fact rather than a placement: §8.3's budget bound is
    /// over the blocks the plan *proposes*, so a caller checking that bound
    /// subtracts this segment (see the module docs, choice 5b).
    pub fn current_segment(&self) -> Option<&Segment> {
        self.segments
            .iter()
            .find(|s| s.flags.current && s.kind.is_work())
    }

    /// The first segment holding `id`, if any.
    pub fn segment_of(&self, id: &Id) -> Option<&Segment> {
        self.segments
            .iter()
            .find(|s| s.item.as_ref() == Some(id) || s.items().iter().any(|i| i == id))
    }
}

// ---------------------------------------------------------------------------
// What changed between two plans (§13 `tm plan --diff`, §11 "Replans and drift")
// ---------------------------------------------------------------------------

/// What changed between two plans of the same day (§13, §11).
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
pub struct PlanDiff {
    /// `(item, old start, new start)` for everything that moved.
    pub moved: Vec<(Id, DateTime<Tz>, DateTime<Tz>)>,
    /// Items the new plan has and the old one did not.
    pub added: Vec<Id>,
    /// Items the old plan had and the new one does not — §9's dropped tail.
    pub removed: Vec<Id>,
    /// Σ minutes segments moved — the `plan` event's `drift_min` (§10.1).
    pub drift_min: u32,
}

impl PlanDiff {
    /// True when nothing moved, was added or was removed.
    pub fn is_empty(&self) -> bool {
        self.moved.is_empty() && self.added.is_empty() && self.removed.is_empty()
    }
}

// ---------------------------------------------------------------------------
// The two words every surface shares
// ---------------------------------------------------------------------------

/// **A `SegKind` as one word** — `block`, `batch`, `break`, … — the *wire*
/// word, not a display cell: it is what `tm plan --json`'s `kind` field and
/// `.tm/last_plan.json` carry, and what `--explain` names a slot by. It is never
/// padded, truncated or printed in a column; `emit::title_cell` is the cell.
///
/// **Public since W-23** (AGENTS §5.3). `tm/src/cli/render.rs::kind_name` held a
/// byte-for-byte copy of these ten arms, found by body shape rather than by
/// name, and is gone. Design §8.2's table says this word becomes the kernel's
/// `SegKind` name when the wire carries the plan (README gap **1105**); until
/// then there is one of it here.
pub fn kind_label(kind: &SegKind) -> &'static str {
    match kind {
        SegKind::Block => "block",
        SegKind::Batch(_) => "batch",
        SegKind::Break => "break",
        SegKind::Routine => "routine",
        SegKind::Wall => "wall",
        SegKind::Rest => "rest",
        SegKind::Optional => "optional",
        SegKind::WindDown => "wind-down",
        SegKind::Sleep => "sleep",
        SegKind::Lost => "lost",
    }
}

/// One §4.3 timeline row's leading `HH:MM`.
pub fn fmt_clock(t: DateTime<Tz>) -> String {
    format!("{:02}:{:02}", t.hour(), t.minute())
}
