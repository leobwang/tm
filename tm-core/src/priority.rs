//! Priority — tm-spec-v1.md §7 in full: the definitions (§7.1), the rule
//! (§7.2), the EDF feasibility pass (§7.3), the sort key and hysteresis
//! (§7.4) and batching (§7.5); plus what §7 consumes — §3.2 derived fields,
//! §5.2 mandatory instances, §5.3 overdue/persist, §5.5 deps → eligibility,
//! §6.2 candidates, §8.4 capacity lookahead and §8.5 duration multipliers —
//! and what §7 feeds — §10.2 `priorities_yesterday`, §11 "Deadline health",
//! §12.2's `u`/`fits` columns and §13's `tm plan --explain ^id`.
//!
//! Everything here is pure: `today` and `now` are parameters, instants are
//! `DateTime<Tz>` in `cfg.tz`, and no function reads a clock, a file or a
//! random number.
//!
//! # API overview
//!
//! * [`collect_candidates`]`(tree, replay, cfg, model, today, now) ->
//!   Vec<Candidate>` — §6.2's candidate set, resolved: every field §7 needs,
//!   computed once. The sources are [`Tree::day_candidate_ids`] (week + the
//!   day file's `# Pinned` + `backlog.md` + series heads), the instances of
//!   `routines.md` and `optional.md` due today ([`recur::today_instances`]),
//!   `optional.md` lines themselves, and the `calendar/` intervals that
//!   touch today. Ineligible candidates are **kept** (§5.5: "a blocked
//!   high-priority item shows in diagnostics as blocked by ^id rather than
//!   silently vanishing") — [`Candidate::eligible`] and
//!   [`Candidate::ineligible_reason`] say why.
//! * [`compute`]`(cands, caps, yesterday, cfg, today) -> Vec<Prio>` — §7.2 +
//!   §7.3 + §7.4, one [`Prio`] per candidate **in the same order**. `caps` is
//!   [`capacity::lookahead`]'s output, ascending by date and long enough to
//!   reach the furthest deadline ([`lookahead_days`] says how long);
//!   `yesterday` is `state.priorities_yesterday` (§10.2).
//! * [`sort_key`]`(prio, cand) -> (p, root_order, own_order)` (§7.4) and
//!   [`sorted`] — the assignable ids, walls first (they are placed by §8.2
//!   step 1, not competed), then by key. [`blocked`] is the list §8.2 step 8
//!   puts in `diagnostics.blocked`.
//! * [`batches`]`(sorted_cands, cfg) -> Vec<Batch>` (§7.5) — the assignment
//!   order as groups: runs of small equal-`ci` candidates merged into one
//!   block-sized batch, everything else a one-item group, so the planner can
//!   consume the vector linearly.
//! * [`explain`]`(id, cands, prios, cfg) -> String` (§13) —
//!   `p = k(3) + bin(u=0.31 → +1) = 4; need 2b, avail 6b by 2026-09-11;
//!   deps ok; cap 2b/d: 1b used`. [`explanation`] returns the structured
//!   [`Explanation`], whose `slot_part`/`extra` are the hook the planner
//!   fills with the slot, energy and gap half of the same line.
//! * [`deadline_health`] (§11), [`priorities_for_state`] (§10.2),
//!   [`done_this_period`] and [`period_range`] (the `min:`/`max:` periods),
//!   [`utilization`] and [`bin_of`] (§7.1's `u` and its bins),
//!   [`fmt_blocks`] (minutes as `6b` / `2.6b` / `20m`).
//!
//! # How the rule is implemented (§7.2)
//!
//! ```text
//! walls (Interval shape)                       class Wall   — off the scale, placed by §8.2 step 1
//! optional.md                                  p = 5        — never competes
//! overdue with on_miss = persist               p = 0
//! mandatory window instance (§5.2)             p = 0
//! `hot` flag                                   p = 0
//! dated (own or derived due), u ≥ 1            p = 0        — IMPOSSIBLE when need > avail, else HOT
//! dated, u < 1                                 p = k + bin(u)
//! open with a floor, u_floor ≥ 1               p = 0        — same split
//! open with a floor                            p = k + bin(u_floor)
//! anything else                                p = k + 2    — pure rank
//! clamped to 0..=7, then hysteresis (§7.4)
//! ```
//!
//! The classes are tried in that order, so the first that matches names the
//! [`PrioClass`]; a candidate that is both overdue and impossible is reported
//! as `Overdue` (the more specific fact) while still carrying the EDF
//! numbers.
//!
//! # Choices the spec leaves open (deviations)
//!
//! 1. **`need` for a floor.** §7.2 writes `need = floor − done_this_period`
//!    while §7.1 defines `need` as `remaining × safety` for everything. The
//!    floor need is `(floor − done_this_period) × safety`, i.e. §7.1's
//!    multiplier applied to §7.2's remainder — the M3 definition of done
//!    ("`min:6b/w` with 2b done → need 4b × safety") settles it.
//! 2. **Which candidates enter the EDF pass.** Only non-wall, non-optional
//!    candidates with a *tree* due (`due:` or the §3.2 derived prep due) —
//!    not instance candidates. A routine window instance also has a `due`
//!    (its window's close), but it is a placement window, not a deadline:
//!    letting it reserve lookahead capacity would double-count the day.
//!    Overdue items *do* take part; their window `[today, past due]` is
//!    empty, so they reserve nothing and score `u = ∞`, which is the honest
//!    answer ("that deadline cannot be met any more").
//! 3. **`u` when nothing is needed.** §7.1 says capacity 0 → `u = ∞`. A
//!    candidate that needs 0 minutes (everything already done) scores
//!    `u = 0` instead, so a finished item is not reported HOT.
//! 4. **Floors do not reserve.** The floor pass reads the capacity left
//!    after the EDF pass (§7.1: capacity is "net of reservations made by
//!    earlier deadlines"), but does not itself subtract: two floors in one
//!    period are independent claims on the same rest-of-period, and the
//!    spec gives them no order.
//! 5. **Hysteresis applies to every non-wall class**, not only to the binned
//!    ones — §7.4 states it as a property of `p`, and the classes with a
//!    constant `p` (optional, pure rank) are unaffected in practice.
//! 6. **`yesterday` / [`priorities_for_state`] use a `BTreeMap`**, the type
//!    `store::RuntimeState::priorities_yesterday` already has, so the round
//!    trip through `state.json` needs no conversion (the scope said
//!    `HashMap`).
//! 7. **`min_slack_days`** (§11 gives no formula) is
//!    `days_until_due × (1 − u)`: the deadline window is `d` days long and
//!    the item needs the fraction `u` of it. Only deadlines that are still
//!    ahead count (overdue items have their own column); `u = ∞` scores
//!    `−d`.
//! 8. **Batching gathers forward.** §7.5 says small equal-`ci` candidates
//!    are grouped "in key order"; small items are rarely adjacent, so
//!    [`batches`] starts a batch at the first ungrouped small candidate and
//!    scans forward for the others of the same `ci` that still fit in a
//!    block. Every candidate appears exactly once, and the groups are in the
//!    key order of their first member.

use std::collections::{BTreeMap, HashSet};

use chrono::{DateTime, NaiveDate};
use chrono_tz::Tz;
use serde::Serialize;
use thiserror::Error;

use crate::capacity::{self, available_until, DayCapacity};
use crate::config::Config;
use crate::energy::{self, Model};
use crate::log::Replay;
use crate::model::{
    Dep, Horizon, Id, Instance, InstanceKey, IsoWeek, Loc, OnMiss, Period, Rate, Scope, Shape,
    State, YearMonth,
};
use crate::recur;
use crate::tree::Tree;

// ---------------------------------------------------------------------------
// Candidates (§6.2)
// ---------------------------------------------------------------------------

/// Why a candidate cannot be assigned a slot right now (§5.5, §6.2, §8.2
/// step 5). Deps, waiting and an exhausted `max:` cap are item facts; the
/// slot-dependent filters (`ci ≤ slot energy`, `loc`, contiguity for an
/// `atomic` item) belong to the planner.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum Ineligible {
    /// State is not Todo or Active.
    #[error("state {}", .0.as_str())]
    Closed(State),
    /// `[?]` — waiting for an event (§5.1).
    #[error("waiting")]
    Waiting,
    /// `after:` dependencies that are not satisfied yet (§5.5).
    #[error("blocked by {}", fmt_deps(.0))]
    Blocked(Vec<Dep>),
    /// The `max:` cap for the period is used up (§6.2).
    #[error("cap {cap} reached ({done_min}m used)")]
    CapReached {
        /// The cap as written.
        cap: Rate,
        /// Minutes already spent in the cap's period.
        done_min: u32,
    },
}

fn fmt_deps(deps: &[Dep]) -> String {
    deps.iter()
        .map(|d| match d {
            Dep::Item(id) => id.token(),
            Dep::Event(name) => format!("event:{name}"),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// One item (or one instance of a recurring item) competing for today's
/// slots, with every §7 input resolved (§6.2).
///
/// Built by [`collect_candidates`]; [`Candidate::new`] makes the bare
/// arithmetic-only candidate the unit tests and the planner's fixtures use.
#[derive(Clone, Debug, PartialEq, Default, Serialize)]
pub struct Candidate {
    /// The item's key (`^id`, or the title for an id-less routine/optional
    /// line — [`Tree::key_of`]).
    pub id: Id,
    /// Title, for the Queue and for `--explain`.
    pub title: String,
    /// Resolved min-energy 0..=5 (§3.1).
    pub ci: u8,
    /// `k` = [`Tree::root_priority`] ∈ 1..=4 (§7.1).
    pub k: u8,
    /// [`Tree::remaining`] in minutes (§6.4), or the instance's `dur:`.
    pub remaining_min: u32,
    /// `remaining × duration multiplier` (§8.5) — what the planner places.
    pub planned_min: u32,
    /// `remaining × config.priority.safety` (§7.1) — what §7 competes with.
    pub need_min: u32,
    /// The duration multiplier behind `planned_min` (§8.5).
    pub multiplier: f64,
    /// Effective due (§3.2): the `due:`, the derived prep due, the interval
    /// start, or the instance's due.
    pub effective_due: Option<DateTime<Tz>>,
    /// The span a window instance must be placed in (§5.2).
    pub window: Option<(DateTime<Tz>, DateTime<Tz>)>,
    /// Finite or `open` (§3.1).
    pub scope: Scope,
    /// `min:` floor in minutes and its period (§7.2).
    pub floor: Option<Rate>,
    /// Minutes already done in the floor's period (§7.2).
    pub floor_done_min: u32,
    /// `max:` cap and its period (§6.2).
    pub cap: Option<Rate>,
    /// Minutes already done in the cap's period.
    pub cap_done_min: u32,
    /// The line's state.
    pub state: State,
    /// Unsatisfied `after:` dependencies (§5.5).
    pub blocked_by: Vec<Dep>,
    /// `[?]` — waiting for an event (§5.1).
    pub waiting: bool,
    /// `loc:` constraint (§8.2 step 5).
    pub loc: Loc,
    /// `atomic` clears this (§8.2 step 5).
    pub splittable: bool,
    /// The `hot` flag (§7.2).
    pub hot: bool,
    /// Overdue with `on_miss = persist` (§5.3, §7.2).
    pub overdue: bool,
    /// A mandatory window instance (§5.2).
    pub mandatory: bool,
    /// `optional.md` (§7.2: `p = 5`).
    pub is_optional: bool,
    /// Interval shape — a wall, off the priority scale (§7.2, §8.2 step 1).
    pub is_wall: bool,
    /// The instance this candidate stands for, when it is one (§5.1).
    pub instance: Option<InstanceKey>,
    /// `(file index, line)` of the item's root — the first rank key (§7.4).
    pub root_order: (usize, usize),
    /// `(file index, line)` of the item itself — the second rank key (§7.4).
    pub own_order: (usize, usize),
    /// Effective tags (own ∪ ancestors'), the multiplier's lookup key.
    pub tags: Vec<String>,
}

impl Candidate {
    /// A bare candidate: id, `ci`, root priority `k` and remaining minutes,
    /// with `need_min = remaining × safety` and `planned_min = remaining`
    /// (multiplier 1.0). Every other field takes its default — finite scope,
    /// state Todo, splittable, no due, no deps.
    ///
    /// This is the constructor for arithmetic tests and synthetic planner
    /// fixtures; [`collect_candidates`] builds the real ones.
    pub fn new(id: Id, ci: u8, k: u8, remaining_min: u32, cfg: &Config) -> Candidate {
        Candidate {
            id,
            ci,
            k,
            remaining_min,
            planned_min: remaining_min,
            need_min: safety_minutes(remaining_min, cfg),
            multiplier: 1.0,
            splittable: true,
            state: State::Todo,
            ..Candidate::default()
        }
    }

    /// True when nothing about the item itself keeps it out of a slot
    /// (§8.2 step 5): open state, deps satisfied, not waiting, `max:` not
    /// used up. The slot-dependent filters are the planner's.
    pub fn eligible(&self) -> bool {
        self.ineligible_reason().is_none()
    }

    /// Why [`Candidate::eligible`] is false — the reason §8.2 step 8 shows in
    /// `diagnostics.blocked` and §12.2 prints as `⛔ after t4`.
    pub fn ineligible_reason(&self) -> Option<Ineligible> {
        if self.waiting {
            return Some(Ineligible::Waiting);
        }
        if !self.state.is_open() {
            return Some(Ineligible::Closed(self.state));
        }
        if !self.blocked_by.is_empty() {
            return Some(Ineligible::Blocked(self.blocked_by.clone()));
        }
        if let Some(cap) = &self.cap {
            if self.cap_done_min >= cap.amount.as_minutes() {
                return Some(Ineligible::CapReached {
                    cap: *cap,
                    done_min: self.cap_done_min,
                });
            }
        }
        None
    }

    /// Minutes of the `max:` cap left in its period (`None` without a cap).
    pub fn cap_left_min(&self) -> Option<u32> {
        self.cap
            .as_ref()
            .map(|c| c.amount.as_minutes().saturating_sub(self.cap_done_min))
    }

    /// `(floor − done_this_period) × safety` — §7.2's floor need, `None`
    /// when the item has no `min:` (see deviation 1).
    pub fn floor_need_min(&self, cfg: &Config) -> Option<u32> {
        let floor = self.floor.as_ref()?;
        let left = floor
            .amount
            .as_minutes()
            .saturating_sub(self.floor_done_min);
        Some(safety_minutes(left, cfg))
    }
}

/// `round(minutes × config.priority.safety)` — §7.1's `need`.
fn safety_minutes(minutes: u32, cfg: &Config) -> u32 {
    let s = cfg.priority.safety;
    if !s.is_finite() || s <= 0.0 {
        return minutes;
    }
    (minutes as f64 * s).round().max(0.0) as u32
}

/// The inclusive date range of a `min:`/`max:` period containing `today`.
pub fn period_range(per: Period, today: NaiveDate) -> (NaiveDate, NaiveDate) {
    match per {
        Period::Day => (today, today),
        Period::Week => IsoWeek::from_date(today).range(),
        Period::Month => YearMonth::from_date(today).range(),
    }
}

/// Logged block minutes for `id` and its descendants inside the period of
/// `per` containing `today`, up to and including `today` (§7.2's
/// `done_this_period`, §6.2's `max:` filter).
pub fn done_this_period(
    replay: &Replay,
    tree: &Tree,
    id: &Id,
    per: Period,
    today: NaiveDate,
) -> u32 {
    let (from, _) = period_range(per, today);
    let mut ids = vec![id.clone()];
    ids.extend(tree.descendants(id));
    let mut total: u32 = 0;
    let mut day = from;
    loop {
        if day > today {
            break;
        }
        for i in &ids {
            total = total.saturating_add(replay.block_minutes_on(i.as_str(), day));
        }
        match day.succ_opt() {
            Some(next) => day = next,
            None => break,
        }
    }
    total
}

/// How many days of [`capacity::lookahead`] the EDF pass needs: through the
/// furthest effective due among `cands`, and never fewer than seven (the
/// week `tm plan --week` shows).
///
/// §7.3 sums capacity over every day up to a deadline, so a lookahead that
/// stops before the deadline reports a false shortfall. The caller sizes the
/// lookahead with this before calling [`compute`].
pub fn lookahead_days(cands: &[Candidate], today: NaiveDate) -> u32 {
    let furthest = cands
        .iter()
        .filter(|c| !c.is_wall)
        .filter_map(|c| c.effective_due)
        .map(|d| d.date_naive())
        .max();
    let days = furthest
        .map(|d| (d - today).num_days() + 1)
        .unwrap_or(7)
        .clamp(7, i64::from(u32::MAX));
    days as u32
}

/// §6.2's candidate set for `today`, with every §7 input resolved.
///
/// `replay` is `log::replay(...)` over enough history to know what is done
/// (deps), what each instance's status is, and how many minutes went into
/// each `min:`/`max:` period. `now` is the planning instant in `cfg.tz`.
///
/// Ineligible candidates are returned too, with their reason (§5.5); the
/// order is the tree's (file, line) order, then routines, then optional
/// lines, then today's calendar walls.
pub fn collect_candidates(
    tree: &Tree,
    replay: &Replay,
    cfg: &Config,
    model: &Model,
    today: NaiveDate,
    now: DateTime<Tz>,
) -> Vec<Candidate> {
    let week = IsoWeek::from_date(today);
    let mut c = Collect {
        tree,
        replay,
        cfg,
        model,
        today,
        now_naive: now.naive_local(),
        done: replay
            .done_items
            .iter()
            .map(|s| Id::new(s.clone()))
            .collect(),
        events: replay.events.keys().cloned().collect(),
        overdue: tree.overdue(now.naive_local()).into_iter().collect(),
        seen: HashSet::new(),
        out: Vec::new(),
    };
    for id in tree.day_candidate_ids(today, week) {
        c.add(&id, false, false);
    }
    // A routine with no instance today is simply not a candidate.
    for id in tree.routine_ids() {
        c.add(&id, false, true);
    }
    for id in tree.optional_ids() {
        c.add(&id, true, false);
    }
    for id in tree.calendar_ids(week) {
        let touches_today = match tree.get(&id).map(|i| &i.shape) {
            Some(Shape::Interval { start, end }) => start.date() <= today && end.date() >= today,
            _ => false,
        };
        if touches_today {
            c.add(&id, false, false);
        }
    }
    c.out
}

/// The working state of [`collect_candidates`].
struct Collect<'a> {
    tree: &'a Tree,
    replay: &'a Replay,
    cfg: &'a Config,
    model: &'a Model,
    today: NaiveDate,
    now_naive: chrono::NaiveDateTime,
    done: HashSet<Id>,
    events: HashSet<String>,
    overdue: HashSet<Id>,
    seen: HashSet<(Id, Option<InstanceKey>)>,
    out: Vec<Candidate>,
}

impl Collect<'_> {
    /// Add one item: one candidate per instance due today, or — unless
    /// `require_instance` — one plain candidate when it has no instances.
    fn add(&mut self, id: &Id, optional: bool, require_instance: bool) {
        let Some(item) = self.tree.get(id) else {
            return;
        };
        let insts =
            recur::today_instances([item], self.today, self.now_naive, self.replay, self.cfg);
        if insts.is_empty() {
            if !require_instance && self.seen.insert((id.clone(), None)) {
                let cand = self.build(id, None, optional);
                self.out.push(cand);
            }
            return;
        }
        for (inst, info) in insts {
            if self.seen.insert((id.clone(), Some(inst.key))) {
                let cand = self.build(id, Some((&inst, &info)), optional);
                self.out.push(cand);
            }
        }
    }

    fn build(
        &self,
        id: &Id,
        inst: Option<(&Instance, &recur::InstanceInfo)>,
        optional: bool,
    ) -> Candidate {
        build_candidate(
            self.tree,
            self.replay,
            self.cfg,
            self.model,
            self.today,
            id,
            inst,
            optional,
            &self.done,
            &self.events,
            &self.overdue,
        )
    }
}

#[allow(clippy::too_many_arguments)]
fn build_candidate(
    tree: &Tree,
    replay: &Replay,
    cfg: &Config,
    model: &Model,
    today: NaiveDate,
    id: &Id,
    inst: Option<(&Instance, &recur::InstanceInfo)>,
    optional: bool,
    done: &HashSet<Id>,
    events: &HashSet<String>,
    overdue: &HashSet<Id>,
) -> Candidate {
    let item = tree.get(id).expect("candidate id is in the tree");
    let tz = cfg.tz;
    let local = |t: chrono::NaiveDateTime| capacity::local_dt(tz, t.date(), t.time());

    let tree_remaining = tree.remaining(id).unwrap_or(0);
    let remaining_min = inst
        .and_then(|(_, info)| info.dur_min)
        .unwrap_or(tree_remaining);
    let tags = tree.tags_effective(id);
    let ci = item.ci;
    let multiplier = energy::duration_multiplier(model, ci, &tags);
    let is_optional = optional || item.horizon == Horizon::Optional;
    let is_wall = matches!(tree.effective_shape(id), Shape::Interval { .. });

    let effective_due = match inst {
        Some((i, _)) => i.due.map(local),
        None => tree.effective_due(id).map(local),
    };
    let window = inst
        .and_then(|(i, _)| i.window)
        .map(|(a, b)| (local(a), local(b)));

    let overdue_flag = match inst {
        Some((_, info)) => info.overdue && item.on_miss == OnMiss::Persist,
        None => overdue.contains(id),
    };
    let mandatory = inst.is_some_and(|(_, info)| info.mandatory);

    let floor = item.budget.floor;
    let cap = item.budget.cap;
    let floor_done_min = floor
        .as_ref()
        .map_or(0, |r| done_this_period(replay, tree, id, r.per, today));
    let cap_done_min = cap
        .as_ref()
        .map_or(0, |r| done_this_period(replay, tree, id, r.per, today));

    let root = tree.root(id);
    let order = |k: &Id| tree.order(k).unwrap_or((usize::MAX, usize::MAX));

    Candidate {
        id: id.clone(),
        title: item.title.clone(),
        ci,
        k: tree.root_priority(id),
        remaining_min,
        planned_min: energy::planned_minutes(remaining_min, multiplier),
        need_min: safety_minutes(remaining_min, cfg),
        multiplier,
        effective_due,
        window,
        scope: item.scope,
        floor,
        floor_done_min,
        cap,
        cap_done_min,
        state: item.state,
        blocked_by: tree.blocked_by(id, done, events),
        waiting: item.state == State::Waiting,
        loc: item.loc.clone(),
        splittable: item.splittable,
        hot: item.is_hot(),
        overdue: overdue_flag,
        mandatory,
        is_optional,
        is_wall,
        instance: inst.map(|(i, _)| i.key),
        root_order: order(&root),
        own_order: order(id),
        tags,
    }
}

// ---------------------------------------------------------------------------
// Priority (§7.2)
// ---------------------------------------------------------------------------

/// Which line of §7.2 gave a candidate its `p`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum PrioClass {
    /// Interval instance — off the scale, placed by §8.2 step 1.
    Wall,
    /// `u ≥ 1` and the need still fits: `p = 0`.
    Hot,
    /// `u ≥ 1` and `need > avail`: `p = 0`, carries the shortfall.
    Impossible,
    /// Past due with `on_miss = persist` (§5.3): `p = 0`.
    Overdue,
    /// Mandatory window instance (§5.2): `p = 0`.
    Mandatory,
    /// The `hot` flag: `p = 0`.
    HotFlag,
    /// Finite with a due: `p = k + bin(u)`.
    Dated,
    /// Open with a `min:` floor: `p = k + bin(u_floor)`.
    Floor,
    /// No due, no floor: `p = k + 2`.
    Rank,
    /// `optional.md`: `p = 5`.
    Optional,
}

impl PrioClass {
    /// The label §12/§13 print: `HOT`, `IMPOSSIBLE`, `overdue`, …
    pub fn label(&self) -> &'static str {
        match self {
            PrioClass::Wall => "wall",
            PrioClass::Hot => "HOT",
            PrioClass::Impossible => "IMPOSSIBLE",
            PrioClass::Overdue => "overdue",
            PrioClass::Mandatory => "mandatory",
            PrioClass::HotFlag => "hot",
            PrioClass::Dated => "dated",
            PrioClass::Floor => "floor",
            PrioClass::Rank => "rank",
            PrioClass::Optional => "optional",
        }
    }
    /// True for the three classes that force `p = 0` through deadline
    /// pressure or a flag (§7.2's first line).
    pub fn is_urgent(&self) -> bool {
        matches!(
            self,
            PrioClass::Hot
                | PrioClass::Impossible
                | PrioClass::Overdue
                | PrioClass::Mandatory
                | PrioClass::HotFlag
        )
    }
}

/// One candidate's computed priority (§7.2–§7.4).
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Prio {
    /// The candidate's key.
    pub id: Id,
    /// Priority, 0 = highest, clamped to 0..=7 (`p` in the UI).
    pub p: u8,
    /// Which §7.2 line produced it.
    pub class: PrioClass,
    /// `k` = root priority (§7.1).
    pub k: u8,
    /// Utilization `need / capacity` (§7.1); `None` when no pass applied.
    /// `f64::INFINITY` when the capacity is zero.
    pub u: Option<f64>,
    /// `bin(u)` ∈ 0..=3 (§7.1); `None` when `u` is `None` or `u ≥ 1`.
    pub bin: Option<u8>,
    /// Minutes needed (the EDF need, or the floor need).
    pub need_min: u32,
    /// Minutes available up to `until`, before this item reserved (§7.3).
    pub avail_min: u32,
    /// `min(need, avail)` — §7.2's `allocation`, the Queue's "fits".
    pub allocation_min: u32,
    /// `need − avail` when IMPOSSIBLE, else 0 (§7.3's "needs 8b, 5b
    /// available by Fri").
    pub shortfall_min: u32,
    /// The date the capacity was summed to: the deadline, or the end of the
    /// floor's period.
    pub until: Option<NaiveDate>,
    /// True when §7.4's hysteresis held `p` above `raw_p`.
    pub hysteresis_applied: bool,
    /// `p` before hysteresis.
    pub raw_p: u8,
}

impl Prio {
    /// A wall's placeholder priority: off the scale (§7.2).
    fn wall(id: Id, k: u8) -> Prio {
        Prio {
            id,
            p: 0,
            class: PrioClass::Wall,
            k,
            u: None,
            bin: None,
            need_min: 0,
            avail_min: 0,
            allocation_min: 0,
            shortfall_min: 0,
            until: None,
            hysteresis_applied: false,
            raw_p: 0,
        }
    }
    /// True when the item is HOT or IMPOSSIBLE (§7.3).
    pub fn is_hot(&self) -> bool {
        matches!(self.class, PrioClass::Hot | PrioClass::Impossible)
    }
}

/// §7.1's `u = need / capacity`: capacity 0 → `∞`, need 0 → 0.
pub fn utilization(need_min: u32, avail_min: u32) -> f64 {
    if need_min == 0 {
        return 0.0;
    }
    if avail_min == 0 {
        return f64::INFINITY;
    }
    need_min as f64 / avail_min as f64
}

/// §7.1's `bin(u)` against `config.priority.bins` (edges descending, default
/// `[0.5, 0.25, 0.1]` → `+0 / +1 / +2 / +3`). `None` means HOT (`u ≥ 1`, or
/// a non-finite `u`).
pub fn bin_of(u: f64, bins: &[f64]) -> Option<u8> {
    if !u.is_finite() || u >= 1.0 {
        return None;
    }
    for (i, edge) in bins.iter().enumerate() {
        if u >= *edge {
            return Some(i as u8);
        }
    }
    Some(bins.len() as u8)
}

/// The outcome of one EDF reservation (§7.3).
#[derive(Clone, Copy, Debug)]
struct Edf {
    avail_min: u32,
    allocation_min: u32,
    u: f64,
    until: NaiveDate,
}

/// §7.2 + §7.3 + §7.4: one [`Prio`] per candidate, in the order of `cands`.
///
/// `caps` is the §8.4 lookahead, **ascending by date** and reaching at least
/// the furthest deadline ([`lookahead_days`]); it is not modified — the EDF
/// pass runs on a working copy. `yesterday` is `state.priorities_yesterday`
/// (§10.2); pass an empty map on the first day.
pub fn compute(
    cands: &[Candidate],
    caps: &[DayCapacity],
    yesterday: &BTreeMap<Id, u8>,
    cfg: &Config,
    today: NaiveDate,
) -> Vec<Prio> {
    let mut work: Vec<DayCapacity> = caps.to_vec();

    // §7.3: the EDF pass, over dated non-wall, non-optional, non-instance
    // candidates, by due ascending (ties: line order, then input order).
    let mut order: Vec<usize> = (0..cands.len())
        .filter(|&i| {
            let c = &cands[i];
            !c.is_wall && !c.is_optional && c.instance.is_none() && c.effective_due.is_some()
        })
        .collect();
    order.sort_by(|&a, &b| {
        let (ca, cb) = (&cands[a], &cands[b]);
        ca.effective_due
            .cmp(&cb.effective_due)
            .then(ca.own_order.cmp(&cb.own_order))
            .then(a.cmp(&b))
    });

    let mut edf: Vec<Option<Edf>> = vec![None; cands.len()];
    for i in order {
        let c = &cands[i];
        let due = c.effective_due.expect("filtered to dated").date_naive();
        let avail_min = available_until(&work, due, c.ci);
        let n = capacity::upto(&work, due);
        let take = c.need_min.min(avail_min);
        let allocation_min = capacity::reserve(&mut work[..n], take, c.ci);
        edf[i] = Some(Edf {
            avail_min,
            allocation_min,
            u: utilization(c.need_min, avail_min),
            until: due,
        });
    }

    // §7.2, in rule order.
    let mut out = Vec::with_capacity(cands.len());
    for (i, c) in cands.iter().enumerate() {
        if c.is_wall {
            out.push(Prio::wall(c.id.clone(), c.k));
            continue;
        }
        let floor = floor_pass(c, &work, cfg, today);
        let pass = edf[i].or(floor);
        let mut prio = Prio {
            id: c.id.clone(),
            p: 0,
            class: PrioClass::Rank,
            k: c.k,
            u: pass.map(|e| e.u),
            bin: pass.and_then(|e| bin_of(e.u, &cfg.priority.bins)),
            need_min: if edf[i].is_some() {
                c.need_min
            } else if floor.is_some() {
                c.floor_need_min(cfg).unwrap_or(0)
            } else {
                c.need_min
            },
            avail_min: pass.map_or(0, |e| e.avail_min),
            allocation_min: pass.map_or(0, |e| e.allocation_min),
            shortfall_min: 0,
            until: pass.map(|e| e.until),
            hysteresis_applied: false,
            raw_p: 0,
        };
        let over = pass.is_some_and(|e| !e.u.is_finite() || e.u >= 1.0);
        if over {
            prio.shortfall_min = prio.need_min.saturating_sub(prio.avail_min);
        }

        let (class, raw_p) = if c.is_optional {
            (PrioClass::Optional, 5)
        } else if c.overdue {
            (PrioClass::Overdue, 0)
        } else if c.mandatory {
            (PrioClass::Mandatory, 0)
        } else if c.hot {
            (PrioClass::HotFlag, 0)
        } else if let Some(e) = pass {
            if !e.u.is_finite() || e.u >= 1.0 {
                let class = if prio.shortfall_min > 0 {
                    PrioClass::Impossible
                } else {
                    PrioClass::Hot
                };
                (class, 0)
            } else {
                let base = if edf[i].is_some() {
                    PrioClass::Dated
                } else {
                    PrioClass::Floor
                };
                let bin = prio.bin.unwrap_or(0);
                (base, clamp_p(u32::from(c.k) + u32::from(bin)))
            }
        } else {
            (PrioClass::Rank, clamp_p(u32::from(c.k) + 2))
        };
        prio.class = class;
        prio.raw_p = raw_p;
        prio.p = apply_hysteresis(raw_p, yesterday.get(&c.id).copied(), cfg);
        prio.hysteresis_applied = prio.p != prio.raw_p;
        out.push(prio);
    }
    out
}

/// §7.2's floor line: `need = (floor − done_this_period) × safety`, capacity
/// = what is left of the period at levels ≥ `ci` after the EDF pass.
fn floor_pass(c: &Candidate, work: &[DayCapacity], cfg: &Config, today: NaiveDate) -> Option<Edf> {
    let rate = c.floor.as_ref()?;
    let need = c.floor_need_min(cfg)?;
    let until = period_range(rate.per, today).1;
    let avail_min = available_until(work, until, c.ci);
    Some(Edf {
        avail_min,
        allocation_min: need.min(avail_min),
        u: utilization(need, avail_min),
        until,
    })
}

fn clamp_p(p: u32) -> u8 {
    p.min(7) as u8
}

/// §7.4: `p` may improve (decrease) by at most one per day relative to
/// yesterday's stored value, unless the new value is 0; worsening is free.
fn apply_hysteresis(raw_p: u8, yesterday: Option<u8>, cfg: &Config) -> u8 {
    if !cfg.priority.hysteresis || raw_p == 0 {
        return raw_p;
    }
    match yesterday {
        Some(y) if raw_p + 1 < y => y - 1,
        _ => raw_p,
    }
}

/// `state.priorities_yesterday` for the next day (§10.2). Walls are left out
/// — they are off the scale, so hysteresis never applies to them.
pub fn priorities_for_state(prios: &[Prio]) -> BTreeMap<Id, u8> {
    prios
        .iter()
        .filter(|p| p.class != PrioClass::Wall)
        .map(|p| (p.id.clone(), p.p))
        .collect()
}

// ---------------------------------------------------------------------------
// Sorting (§7.4)
// ---------------------------------------------------------------------------

/// §7.4's sort key: `(p, root line order, own line order)`.
pub type SortKey = (u8, (usize, usize), (usize, usize));

/// §7.4: `(p, root_line_order, own_line_order)`. Walls are off the scale —
/// [`sorted`] puts them first rather than giving them a key.
pub fn sort_key(prio: &Prio, cand: &Candidate) -> SortKey {
    (prio.p, cand.root_order, cand.own_order)
}

/// The assignment order (§7.4, §8.2 step 5): walls first (placed by step 1),
/// then eligible candidates by [`sort_key`]. Ineligible candidates are left
/// out — [`blocked`] keeps them with their reason (§5.5).
pub fn sorted(prios: &[Prio], cands: &[Candidate]) -> Vec<Id> {
    sorted_candidates(prios, cands)
        .into_iter()
        .map(|c| c.id.clone())
        .collect()
}

/// [`sorted`], keeping the candidates themselves — the input [`batches`]
/// wants.
pub fn sorted_candidates<'a>(prios: &[Prio], cands: &'a [Candidate]) -> Vec<&'a Candidate> {
    // Walls sort first; a candidate with no computed priority (the caller
    // passed a shorter list) sorts last rather than first.
    let mut keyed: Vec<((u8, SortKey), usize)> = (0..cands.len())
        .filter(|&i| cands[i].eligible())
        .map(|i| {
            let c = &cands[i];
            let p = if c.is_wall {
                7
            } else {
                prio_at(i, &c.id, prios).map_or(7, |p| p.p)
            };
            ((u8::from(!c.is_wall), (p, c.root_order, c.own_order)), i)
        })
        .collect();
    keyed.sort();
    keyed.into_iter().map(|(_, i)| &cands[i]).collect()
}

/// The [`Prio`] of the candidate at index `i`.
///
/// [`compute`] returns one [`Prio`] per candidate in the same order, so the
/// index is the pairing; the id lookup is only the fallback for a caller that
/// passed a shorter or reordered list. Two candidates *can* share an id — a
/// carried `on-miss:persist` routine instance and today's fresh one (§5.3) —
/// so the index is the only reliable pairing.
fn prio_at<'a>(i: usize, id: &Id, prios: &'a [Prio]) -> Option<&'a Prio> {
    match prios.get(i) {
        Some(p) if p.id == *id => Some(p),
        _ => prios.iter().find(|p| p.id == *id),
    }
}

/// The [`Candidate`] of the priority at index `i` — the inverse of
/// [`prio_at`].
fn cand_at<'a>(i: usize, id: &Id, cands: &'a [Candidate]) -> Option<&'a Candidate> {
    match cands.get(i) {
        Some(c) if c.id == *id => Some(c),
        _ => cands.iter().find(|c| c.id == *id),
    }
}

/// The candidates §8.2 step 8 lists in `diagnostics.blocked`, in candidate
/// order, each with the reason it cannot take a slot (§5.5).
pub fn blocked(cands: &[Candidate]) -> Vec<(Id, Ineligible)> {
    cands
        .iter()
        .filter_map(|c| c.ineligible_reason().map(|r| (c.id.clone(), r)))
        .collect()
}

// ---------------------------------------------------------------------------
// Batching (§7.5)
// ---------------------------------------------------------------------------

/// One assignment group: several small equal-`ci` candidates that share a
/// block (§7.5), or a single candidate that takes its own.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Batch {
    /// Members, in key order.
    pub ids: Vec<Id>,
    /// The shared min-energy.
    pub ci: u8,
    /// Σ `planned_min` — what the block has to hold.
    pub total_min: u32,
    /// Σ `remaining_min` — what the estimates say.
    pub total_remaining_min: u32,
}

impl Batch {
    /// True when this group really batches (more than one member).
    pub fn is_batch(&self) -> bool {
        self.ids.len() > 1
    }
}

/// §7.5: the assignment order as groups. Candidates with
/// `remaining ≤ config.priority.batch_max_min` and equal `ci` are gathered
/// into one group of at most `block_min` planned minutes ("batch: package ·
/// insurance · bank (3)"); every other candidate is a one-item group. The
/// groups come back in the key order of their first member, so the planner
/// walks the vector once.
pub fn batches(sorted: &[&Candidate], cfg: &Config) -> Vec<Batch> {
    let block_min = cfg.block_min();
    let max_small = cfg.priority.batch_max_min;
    // Walls are placed as intervals and optionals only fill rest slots, so
    // neither ever shares a block with a task.
    let small = |c: &Candidate| {
        c.remaining_min > 0 && c.remaining_min <= max_small && !c.is_wall && !c.is_optional
    };

    let mut used = vec![false; sorted.len()];
    let mut out: Vec<Batch> = Vec::new();
    for i in 0..sorted.len() {
        if used[i] {
            continue;
        }
        used[i] = true;
        let c = sorted[i];
        let mut batch = Batch {
            ids: vec![c.id.clone()],
            ci: c.ci,
            total_min: c.planned_min,
            total_remaining_min: c.remaining_min,
        };
        if small(c) {
            for (j, other) in sorted.iter().enumerate().skip(i + 1) {
                if used[j] || other.ci != c.ci || !small(other) {
                    continue;
                }
                if batch.total_min + other.planned_min > block_min {
                    continue;
                }
                used[j] = true;
                batch.ids.push(other.id.clone());
                batch.total_min += other.planned_min;
                batch.total_remaining_min += other.remaining_min;
            }
        }
        out.push(batch);
    }
    out
}

// ---------------------------------------------------------------------------
// Explain (§13)
// ---------------------------------------------------------------------------

/// The parts of `tm plan --explain ^id` (§13).
///
/// `priority_part`, `need_part`, `deps_part` and `cap_part` are §7's half:
///
/// ```text
/// p = k(3) + bin(u=0.31 → +1) = 4; need 2b, avail 6b by 2026-09-11; deps ok; cap 2b/d: 1b used
/// ```
///
/// `slot_part` and `extra` are the documented hook for `planner.rs`: once a
/// plan exists it fills in `slot 11:50 energy 4, ci 3, gap 1` (and anything
/// else it wants to add) and the same [`Display`](std::fmt::Display) prints
/// the whole §13 line.
#[derive(Clone, Debug, PartialEq, Default, Serialize)]
pub struct Explanation {
    /// The candidate.
    pub id: Id,
    /// `p = k(3) + bin(u=0.31 → +1) = 4`.
    pub priority_part: String,
    /// `need 2b, avail 6b by 2026-09-11`.
    pub need_part: Option<String>,
    /// The planner's `slot 11:50 energy 4, ci 3, gap 1`.
    pub slot_part: Option<String>,
    /// `deps ok` / `blocked by ^t4`.
    pub deps_part: String,
    /// `cap 2b/d: 1b used`.
    pub cap_part: Option<String>,
    /// Anything else the planner appends.
    pub extra: Vec<String>,
}

impl std::fmt::Display for Explanation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts: Vec<&str> = vec![&self.priority_part];
        if let Some(n) = &self.need_part {
            parts.push(n);
        }
        if let Some(s) = &self.slot_part {
            parts.push(s);
        }
        parts.push(&self.deps_part);
        if let Some(c) = &self.cap_part {
            parts.push(c);
        }
        parts.extend(self.extra.iter().map(String::as_str));
        write!(f, "{}", parts.join("; "))
    }
}

/// `tm plan --explain ^id` (§13) — why the item is where it is, or a short
/// message when it is not a candidate today.
pub fn explain(id: &Id, cands: &[Candidate], prios: &[Prio], cfg: &Config) -> String {
    match explanation(id, cands, prios, cfg) {
        Some(e) => e.to_string(),
        None => format!("{} is not a candidate today", id.token()),
    }
}

/// [`explain`] structured, so the planner can fill in the slot half.
pub fn explanation(
    id: &Id,
    cands: &[Candidate],
    prios: &[Prio],
    cfg: &Config,
) -> Option<Explanation> {
    let cand = cands.iter().find(|c| c.id == *id)?;
    let prio = prios.iter().find(|p| p.id == *id)?;
    let block = cfg.block_min();

    let mut priority_part = match prio.class {
        PrioClass::Wall => "p = — (wall: placed as an interval)".to_string(),
        PrioClass::Optional => "p = 5 (optional)".to_string(),
        PrioClass::Overdue => "p = 0 (overdue, on-miss persist)".to_string(),
        PrioClass::Mandatory => "p = 0 (mandatory window instance)".to_string(),
        PrioClass::HotFlag => "p = 0 (hot flag)".to_string(),
        PrioClass::Hot => format!("p = 0 (HOT: u={} ≥ 1)", fmt_u(prio.u)),
        PrioClass::Impossible => format!(
            "p = 0 (IMPOSSIBLE: needs {}, {} available by {})",
            fmt_blocks(prio.need_min, block),
            fmt_blocks(prio.avail_min, block),
            fmt_until(prio.until),
        ),
        PrioClass::Dated | PrioClass::Floor => format!(
            "p = k({}) + bin(u={} → +{}) = {}",
            prio.k,
            fmt_u(prio.u),
            prio.bin.unwrap_or(0),
            prio.raw_p,
        ),
        PrioClass::Rank => format!("p = k({}) + 2 (no due, no floor) = {}", prio.k, prio.raw_p),
    };
    if prio.hysteresis_applied {
        priority_part.push_str(&format!(" (hysteresis: {} → {})", prio.raw_p, prio.p));
    }

    // The IMPOSSIBLE line already spells the same two numbers out.
    let need_part =
        if matches!(prio.class, PrioClass::Wall | PrioClass::Impossible) || prio.until.is_none() {
            None
        } else {
            Some(format!(
                "need {}, avail {} by {}",
                fmt_blocks(prio.need_min, block),
                fmt_blocks(prio.avail_min, block),
                fmt_until(prio.until),
            ))
        };

    let deps_part = match cand.ineligible_reason() {
        Some(reason) => reason.to_string(),
        None => "deps ok".to_string(),
    };

    let cap_part = cand
        .cap
        .as_ref()
        .map(|c| format!("cap {}: {} used", c, fmt_blocks(cand.cap_done_min, block)));

    Some(Explanation {
        id: id.clone(),
        priority_part,
        need_part,
        slot_part: None,
        deps_part,
        cap_part,
        extra: Vec::new(),
    })
}

fn fmt_u(u: Option<f64>) -> String {
    match u {
        Some(v) if v.is_finite() => format!("{v:.2}"),
        Some(_) => "∞".to_string(),
        None => "—".to_string(),
    }
}

fn fmt_until(until: Option<NaiveDate>) -> String {
    until.map_or_else(|| "—".to_string(), |d| d.format("%Y-%m-%d").to_string())
}

/// Minutes as the plan talks about them: `6b` when whole blocks, `2.6b` when
/// a fraction of one, `20m` below a block.
pub fn fmt_blocks(minutes: u32, block_min: u32) -> String {
    if block_min == 0 {
        return format!("{minutes}m");
    }
    if minutes.is_multiple_of(block_min) {
        return format!("{}b", minutes / block_min);
    }
    if minutes >= block_min {
        return format!("{:.1}b", minutes as f64 / block_min as f64);
    }
    format!("{minutes}m")
}

// ---------------------------------------------------------------------------
// Deadline health (§11)
// ---------------------------------------------------------------------------

/// §11's "Deadline health" monitor: min slack, #HOT, #IMPOSSIBLE, #overdue.
#[derive(Clone, Copy, Debug, Default, PartialEq, Serialize)]
pub struct DeadlineHealth {
    /// The tightest deadline's slack in days: `days_until_due × (1 − u)`,
    /// over deadlines that are still ahead (see deviation 7). `None` when
    /// nothing is dated.
    pub min_slack_days: Option<f64>,
    /// Candidates with `u ≥ 1` that still fit (§7.3).
    pub hot: usize,
    /// Candidates whose need exceeds the capacity before the deadline.
    pub impossible: usize,
    /// Past-due candidates with `on_miss = persist` (§5.3).
    pub overdue: usize,
}

/// §11's deadline health over one day's priorities.
pub fn deadline_health(prios: &[Prio], cands: &[Candidate], today: NaiveDate) -> DeadlineHealth {
    let mut health = DeadlineHealth::default();
    for (i, prio) in prios.iter().enumerate() {
        match prio.class {
            PrioClass::Hot => health.hot += 1,
            PrioClass::Impossible => health.impossible += 1,
            PrioClass::Overdue => health.overdue += 1,
            _ => {}
        }
        let is_dated =
            cand_at(i, &prio.id, cands).is_some_and(|c| c.effective_due.is_some() && !c.is_wall);
        let (Some(until), Some(u), true) = (prio.until, prio.u, is_dated) else {
            continue;
        };
        if until < today {
            continue;
        }
        let days = (until - today).num_days() as f64;
        let slack = if u.is_finite() {
            days * (1.0 - u)
        } else {
            -days
        };
        health.min_slack_days = Some(match health.min_slack_days {
            Some(m) if m <= slack => m,
            _ => slack,
        });
    }
    health
}
