//! **The planner's comparand, keyed by CLASS** (stage 6 W-36 track H; README
//! gaps 2925 and 2871).
//!
//! # The finding this answers
//!
//! W-35 froze the fork's answer for four NAMED fixture days
//! (`support/forkday.rs`, `planner_fixtures.rs`' `DAYS`). None of them runs a
//! block, a break, an interruption, overtime or a wall on `now` — the §9 states
//! where gap 550 and the owner's D57 divergences (parity P45-P47) live — and
//! every GENERATED day `planner_invariants.rs`' differential arms draw compares
//! the kernel against `planner::plan`, which R3 deletes. So at R3 every
//! generated class would lose its comparand at once, on the least reviewable
//! commit of the stage: a LIST where the rule is a CLASS (W-35's critic).
//!
//! # What a class is, and why it is a property and not a list
//!
//! A generated day's class is [`class_of`] — a FUNCTION of the stored world
//! (its documents, its log, `.tm/state.json` and `now`), never a label the file
//! chooses: a frozen line whose world does not classify as its own key FAILS.
//! It has two coordinates, each the dimension on which the planner's code path
//! changes and on which one of the differential arms widens the shared
//! generator:
//!
//! * [`Run`] — §9's running state: nothing, a running block, a block in
//!   overtime (P46), a block with a wall on `now` (P47), a running break with or
//!   without a paused block (P45), an open interruption with or without a block.
//! * [`DayShape`] — §8.1/§8.2's day: in the lounge, at home (the home cap), a
//!   late day (no stored window, §8.1's formula past the wind-down), a travel
//!   day (step 1's zeroing) or a day whose budget is spent (step 8's note).
//!
//! Both enumerations are DERIVED from an exhaustive `match` ([`Run::next`],
//! [`DayShape::next`]): a variant added without a successor does not compile.
//! The class space [`class_space`] is their product less the pairs NO arm
//! draws, stated as the rule the arms follow — a running break is drawn only by
//! `planner_invariants`' W-35 arm, a travel or spent day only by its step-8
//! arm, and no arm draws both ([`drawn_by_an_arm`]). The coverage test asserts
//! the frozen file holds a day of EVERY class in that space and nothing
//! outside it.
//!
//! # What is frozen, per class, and what each part is compared with
//!
//! One line per class (`tests/fixtures/fork-4748911-planner-classes.jsonl`):
//! the world, and the fork's answers for it taken while the fork was still
//! here (the re-bless in `planner_classes.rs`' fork region):
//!
//! * `day` — **the comparand**: the fork as the shipped binary runs it (D53:
//!   `planner::plan` over the KERNEL's grants for this request, which is
//!   `planning::build_ranked`'s call), with the D57 rule applied by its
//!   PROPERTY exactly as `planner_invariants`' `w35_fork_plan` applies it —
//!   P46 (the running block in overtime keeps its block: the fork planned with
//!   the estimate raised past the day, its note the fork's own saturating
//!   `left`) and P47 (a wall whose blocked span covers `now` pauses the open
//!   row: no `▶`, clipped at the wall's rows) — and, since the W-36 land step,
//!   P51 (the owner's D60: `p = 0` impossible ties ranked by `until` and request
//!   position, before every other `p = 0` answer), run IN the fork by rewriting
//!   the two order fields its sorts read ([`d60_cands`], one copy since W-37,
//!   README gaps 3121 and 3122). On every other day it IS the
//!   shipped fork's day, byte for byte.
//! * `shipped` — the shipped fork's day, kept only where the comparand departs
//!   from it (a P46, P47 or P51 day), so the divergence stays visible by value.
//! * `d60` — `{"p51": …}`: whether D60's key moved the fork's §7.4 order.
//! * `whatif` — on a day with a running block: §9.1's what-if as the shipped
//!   TUI builds it (`full`: the estimate grown AND `PlanOverrides::extending`)
//!   and the estimate alone (`est`); where they differ the kernel is held to
//!   `est`, which is parity P44 by its property (D34).
//!
//! A **P45** day (a running break) has no fork analogue at all — fork
//! `planner::plan` reads no `runtime.break_` and plans over it — so the kernel
//! is checked against P45's RULE ([`p45_rule`]): one Break row where the break
//! is, open once overrun, carrying its place; nothing §8.2 places over it; and
//! (README gap 2925's second half) every §8.2 step-5 row from `now` on starts
//! at or after the break's end. What the fork's day still says on such a day —
//! the date, the window, the budget and the walls — is compared by value.
//!
//! # Neither side of a comparison here is the fork's code
//!
//! One side is a day the KERNEL planned, read back by the host's codec
//! (`tm_core::planwire`, what R3 swaps in); the other is bytes on disk. So R3's
//! deletion cannot turn this into a self-comparison.
//!
//! # Where the worlds came from — re-drawn from the tree (README gap 3080)
//!
//! Each world was DRAWN from the shared generator (`support/plangen.rs`:
//! `case_strategy`, `build`, and each arm's widenings as that arm applies
//! them) — never written by hand. Until W-37 the draw was a harness in a
//! scratchpad, because the generator was private to `planner_invariants.rs`;
//! since W-37 track H it is [`class_draws`] and [`world_of`], here, and
//! `planner_classes.rs`' `every_frozen_world_is_the_generators_own_draw`
//! RE-DRAWS every line at its recorded seed, draw index and arm and demands
//! the stored world byte for byte. So "this line came from draw 346" is a
//! checked fact, and a change to the generator that moves a frozen world fails
//! by name — the next step decides whether that is a re-draw under the owner's
//! D64(b) or a change to take back.
//!
//! # Every frozen world is one the binary can hold (owner D64(b), README gap 3138)
//!
//! The class of a world is read the way the binary reads it: the running block
//! and the open interruption are the LOG's (D42's reconcile, `tm/src/cli/
//! ctx.rs`' `derived_state`: the log wins on what is open), and a running
//! break is `.tm/state.json`'s alone (`HOST_ONLY_STATE`: a break is logged when
//! it ENDS) — [`running`]. [`binary_holds`] is the property every stored world
//! is held to: the cache and the log agree on what is open, a running break
//! began after the last `start`/`done`/`stop` (each ends one), and a paused
//! block has a reason the binary would have paused it for. Until W-37 twelve
//! lines failed it — the ten interruptions set in `state.json` alone and two
//! breaks begun before the block under them — and all twelve were re-drawn
//! under D64(b) by the generator that now logs the one and orders the other.

#![allow(dead_code)]

use std::collections::BTreeSet;
use std::sync::OnceLock;

use chrono::{DateTime, Duration, NaiveTime};
use chrono_tz::Tz;
use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{RngAlgorithm, TestRng, TestRunner};
use serde_json::{json, Value};

use tm_core::capacity::{self, local_dt};
use tm_core::config::Config;
use tm_core::dayplan::{DayPlan, SegKind};
use tm_core::energy::{Model, DEFAULT_TAG};
use tm_core::log::{Event, Interruption, LogEntry, OpenBlock, Replay};
use tm_core::model::{Id, Shape};
use tm_core::planwire::{self, KernelDay};
use tm_core::priority::{self, Candidate, Prio};
use tm_core::store::{BreakState, RuntimeState};
use tm_core::tree::Tree;

use crate::{chokepoint, forkday, plangen, planreq};

// ---------------------------------------------------------------------------
// The stored world
// ---------------------------------------------------------------------------

/// **One generated day, as bytes**: what the differential arms hand both
/// planners. `Config::default()` is the configuration of every generated day
/// (`planner_invariants`' `build`), so it is not stored.
#[derive(Clone, Debug, PartialEq)]
pub struct ClassWorld {
    /// The plan's documents as `(path, text)`.
    pub docs: Vec<(String, String)>,
    /// `.tm/log.jsonl`'s text.
    pub log: String,
    /// `.tm/state.json`.
    pub state: RuntimeState,
    /// The instant planned at.
    pub now: DateTime<Tz>,
    /// The learned `_default` duration multiplier, when the arm drew one
    /// (`the_kernel_hashes_the_day_the_fork_hashes`); `Model::default()` else.
    /// Kept as its shortest decimal text so the double is read back exactly.
    pub mult: Option<String>,
}

impl ClassWorld {
    /// The world as a frozen line carries it.
    pub fn to_json(&self) -> Value {
        json!({
            "docs": self.docs.iter().map(|(p, t)| json!([p, t])).collect::<Vec<_>>(),
            "log": self.log,
            "state": serde_json::to_value(&self.state).expect("a state serialises"),
            "now": self.now.to_rfc3339(),
            "mult": self.mult,
        })
    }

    /// The world a frozen line carries, or why it cannot be read.
    pub fn of_json(v: &Value, tz: Tz) -> Result<ClassWorld, String> {
        let docs = v["docs"]
            .as_array()
            .ok_or("world.docs is not an array")?
            .iter()
            .map(|d| match (d[0].as_str(), d[1].as_str()) {
                (Some(p), Some(t)) => Ok((p.to_string(), t.to_string())),
                _ => Err(format!("world.docs holds {d}, not a [path, text] pair")),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let log = v["log"].as_str().ok_or("world.log is not a string")?.to_string();
        let state: RuntimeState =
            serde_json::from_value(v["state"].clone()).map_err(|e| format!("world.state: {e}"))?;
        let now = DateTime::parse_from_rfc3339(v["now"].as_str().ok_or("world.now is not a string")?)
            .map_err(|e| format!("world.now: {e}"))?
            .with_timezone(&tz);
        let mult = match &v["mult"] {
            Value::Null => None,
            Value::String(s) => Some(s.clone()),
            other => return Err(format!("world.mult is {other}, not a decimal's text")),
        };
        Ok(ClassWorld { docs, log, state, now, mult })
    }
}

/// A stored world, rebuilt into what both planners read.
pub struct Built {
    pub world: ClassWorld,
    pub cfg: Config,
    pub tree: Tree,
    pub replay: Replay,
    pub model: Model,
    pub cands: Vec<Candidate>,
}

impl Built {
    /// Rebuild: the tree the host parses from the same documents, the replay the
    /// kernel derives from the same log (`support/replay.rs`), the model with the
    /// drawn multiplier, and `priority::collect_candidates` over all of it.
    pub fn of(world: ClassWorld) -> Built {
        let cfg = Config::default();
        let files: Vec<(&str, &str)> =
            world.docs.iter().map(|(p, t)| (p.as_str(), t.as_str())).collect();
        let tree = Tree::from_texts(&files, &cfg);
        let replay = chokepoint::replay_of_text(&world.log, cfg.tz);
        let mut model = Model::default();
        if let Some(m) = &world.mult {
            let m: f64 = m.parse().expect("a stored multiplier is a decimal");
            model.duration.insert(DEFAULT_TAG.to_string(), m);
        }
        let date = planwire::plan_date(&world.state, world.now);
        let cands = priority::collect_candidates(&tree, &replay, &cfg, &model, date, world.now);
        Built { world, cfg, tree, replay, model, cands }
    }

    /// The request's builder, over this world.
    pub fn request_world(&self) -> planreq::World<'_> {
        planreq::World {
            docs: &self.world.docs,
            log: &self.world.log,
            tree: &self.tree,
            cfg: &self.cfg,
            state: &self.world.state,
            now: self.world.now,
            cands: &self.cands,
        }
    }

    /// The planned date.
    pub fn date(&self) -> chrono::NaiveDate {
        planwire::plan_date(&self.world.state, self.world.now)
    }

    /// Local midnight of the planned date, and of the next.
    pub fn day_bounds(&self) -> (DateTime<Tz>, DateTime<Tz>) {
        let d = self.date();
        let tz = self.cfg.tz;
        (local_dt(tz, d, NaiveTime::MIN), local_dt(tz, d + Duration::days(1), NaiveTime::MIN))
    }

    /// **The worked minutes of the running block, as fork `active_run` reads
    /// them**: the log's open block when it is this item's
    /// (`OpenBlock::worked_min_at`), the clock since `started` otherwise —
    /// `planner_invariants`' `w35_fork_worked`.
    pub fn worked(&self) -> Option<u32> {
        self.worked_for(&self.world.state)
    }

    /// [`Built::worked`] for another state over the same world (the P46
    /// comparand asks it of a state whose estimate it has raised).
    pub fn worked_for(&self, st: &RuntimeState) -> Option<u32> {
        let a = st.active.as_ref()?;
        let started = local_dt(self.cfg.tz, self.date(), a.started);
        Some(
            self.replay
                .open_block
                .as_ref()
                .filter(|b| b.id == a.id.as_str())
                .map(|b| b.worked_min_at(self.world.now.fixed_offset()))
                .unwrap_or_else(|| (self.world.now - started).num_minutes().max(0) as u32),
        )
    }

    /// **The walls of the day and their blocked spans** `(item, blocked start,
    /// end)` — the candidates §8.2 step 1 turns into Wall rows, each from its
    /// run-up (`buffer:`) to its end, clipped to the day: the span P47's rule
    /// asks about. `travel` says whether the wall is a `travel-day`.
    pub fn walls(&self) -> Vec<(Id, DateTime<Tz>, DateTime<Tz>, bool)> {
        let tz = self.cfg.tz;
        let (lo, hi) = self.day_bounds();
        let mut out = Vec::new();
        for c in self.cands.iter().filter(|c| c.is_wall) {
            let Some(item) = self.tree.get(&c.id) else { continue };
            let (start, end) = match c.window {
                Some(w) => w,
                None => match self.tree.effective_shape(&c.id) {
                    Shape::Interval { start, end } => (
                        local_dt(tz, start.date(), start.time()),
                        local_dt(tz, end.date(), end.time()),
                    ),
                    _ => continue,
                },
            };
            let buffer = item.buffer.map_or(0, |d| d.as_minutes());
            let blocked = (start - Duration::minutes(i64::from(buffer))).max(lo);
            let end = end.min(hi);
            if end > blocked {
                out.push((c.id.clone(), blocked, end, item.is_travel_day()));
            }
        }
        out
    }
}

// ---------------------------------------------------------------------------
// The classes
// ---------------------------------------------------------------------------

/// §9's running state of a day — the first coordinate of its class.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Run {
    /// Nothing running, no break, no interruption.
    Idle,
    /// A running block inside its estimate, no wall on `now`.
    Running,
    /// A running block at or past its estimate: parity **P46**.
    Overtime,
    /// A running block and a wall whose blocked span covers `now`: parity **P47**.
    WallOnNow,
    /// A running break and no block: parity **P45**.
    Break,
    /// A running break over a paused block (`tm break` pauses it): **P45**.
    BreakBlock,
    /// An open interruption and no block.
    Interrupted,
    /// An open interruption over a running block.
    InterruptedBlock,
}

impl Run {
    /// **The enumeration, derived from an exhaustive `match`**: every variant
    /// names its successor, so one added without a place in the chain does not
    /// compile, and [`Run::all`] cannot leave it out.
    pub fn next(self) -> Option<Run> {
        match self {
            Run::Idle => Some(Run::Running),
            Run::Running => Some(Run::Overtime),
            Run::Overtime => Some(Run::WallOnNow),
            Run::WallOnNow => Some(Run::Break),
            Run::Break => Some(Run::BreakBlock),
            Run::BreakBlock => Some(Run::Interrupted),
            Run::Interrupted => Some(Run::InterruptedBlock),
            Run::InterruptedBlock => None,
        }
    }

    /// Every run state, in the chain's order.
    pub fn all() -> Vec<Run> {
        std::iter::successors(Some(Run::Idle), |r| r.next()).collect()
    }

    /// The word a class key spells it with.
    pub fn word(self) -> &'static str {
        match self {
            Run::Idle => "idle",
            Run::Running => "running",
            Run::Overtime => "overtime",
            Run::WallOnNow => "wall-on-now",
            Run::Break => "break",
            Run::BreakBlock => "break-block",
            Run::Interrupted => "interrupted",
            Run::InterruptedBlock => "interrupted-block",
        }
    }

    /// A running break — drawn only by the W-35 arm.
    pub fn is_break(self) -> bool {
        matches!(self, Run::Break | Run::BreakBlock)
    }
}

/// The day's shape — the second coordinate of its class.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DayShape {
    /// A stored window, in the lounge.
    Lounge,
    /// A stored window, at home: §8.2 step 3's `home_max_ci`.
    Home,
    /// No stored window: §8.1's formula, the evening wall past the wind-down.
    Late,
    /// A `travel-day` wall: §8.2 step 1 zeroes the budget.
    Travel,
    /// The budget is spent by the blocks already done: step 8's note.
    Spent,
}

impl DayShape {
    /// The enumeration, derived as [`Run::next`]'s is.
    pub fn next(self) -> Option<DayShape> {
        match self {
            DayShape::Lounge => Some(DayShape::Home),
            DayShape::Home => Some(DayShape::Late),
            DayShape::Late => Some(DayShape::Travel),
            DayShape::Travel => Some(DayShape::Spent),
            DayShape::Spent => None,
        }
    }

    /// Every shape, in the chain's order.
    pub fn all() -> Vec<DayShape> {
        std::iter::successors(Some(DayShape::Lounge), |s| s.next()).collect()
    }

    /// The word a class key spells it with.
    pub fn word(self) -> &'static str {
        match self {
            DayShape::Lounge => "lounge",
            DayShape::Home => "home",
            DayShape::Late => "late",
            DayShape::Travel => "travel",
            DayShape::Spent => "spent",
        }
    }

    /// A widening only the step-8 arm draws.
    pub fn is_step8_widening(self) -> bool {
        matches!(self, DayShape::Travel | DayShape::Spent)
    }
}

/// A generated day's class.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Class {
    pub run: Run,
    pub shape: DayShape,
}

impl Class {
    /// `run/shape` — the key a frozen line is filed under.
    pub fn key(self) -> String {
        format!("{}/{}", self.run.word(), self.shape.word())
    }
}

/// **Does some differential arm draw this class?** The rule the arms follow,
/// not a list of pairs: `planner_invariants`' W-35 arm is the only one that
/// draws a running break, its step-8 arm (`widen_for_notes`) the only one that
/// draws a travel or spent day, and neither applies the other's widening. Every
/// other pair is the shared generator's own (`case_strategy` draws `active`,
/// `interrupt`, `home` and `late` independently, and the arms that add nothing
/// draw it bare).
pub fn drawn_by_an_arm(c: Class) -> bool {
    !(c.run.is_break() && c.shape.is_step8_widening())
}

/// **The class space**: every `(run, shape)` some arm draws.
pub fn class_space() -> Vec<Class> {
    let mut out = Vec::new();
    for run in Run::all() {
        for shape in DayShape::all() {
            let c = Class { run, shape };
            if drawn_by_an_arm(c) {
                out.push(c);
            }
        }
    }
    out
}

/// **What is running in a world, read the way the binary reads it** (owner
/// D64(b), README gap 3138) — D42's reconcile (`tm/src/cli/ctx.rs`'
/// `derived_state` / `reconcile_state`): the running block and the open
/// interruption are the LOG's, and the log wins against `.tm/state.json` on
/// what is open; a running break is the cache's alone, because a break is
/// logged when it ENDS (`HOST_ONLY_STATE`).
pub struct Running<'a> {
    /// `Replay::open_block` — the block the log has started and not closed.
    pub block: Option<&'a OpenBlock>,
    /// `Replay::open_interrupt`, not yet resumed.
    pub interrupt: Option<&'a Interruption>,
    /// `state.break`, started.
    pub brk: Option<&'a BreakState>,
}

/// [`Running`] of a built world.
pub fn running(b: &Built) -> Running<'_> {
    Running {
        block: b.replay.open_block.as_ref(),
        interrupt: b.replay.open_interrupt.as_ref().filter(|i| i.end.is_none()),
        brk: b.world.state.break_.as_ref().filter(|x| x.started.is_some()),
    }
}

/// **A world's class**, computed from the world and nothing else — and its
/// running state read as the binary reads it ([`running`]): until W-37 this
/// read `state.interrupt` and `state.active`, so a world whose interruption
/// was in `.tm/state.json` alone classified as interrupted while the binary,
/// handed it, planned an ordinary day (README gap 3138).
///
/// The run state, first match wins: a running break (whatever else is
/// running, since `tm break` pauses the block), then an open interruption, then
/// a running block — P47 when a wall's blocked span covers `now`, P46 when it
/// is not paused and its worked minutes have reached its estimate (fork
/// `active_run`'s `left == 0`; the estimate and the pause are the cache's,
/// which the reconcile keeps while the log names the same block), running
/// otherwise.
///
/// The shape, first match wins: a `travel-day` wall; a budget the blocks done
/// have spent (`capacity::remaining_budget` is 0 after at least one); no stored
/// window; `loc: home`; the lounge.
pub fn class_of(b: &Built) -> Class {
    let st = &b.world.state;
    let now = b.world.now;
    let r = running(b);
    // The cache's facts about the block the log names, as the reconcile keeps them.
    let cached = |ob: &OpenBlock| st.active.as_ref().filter(|a| a.id.as_str() == ob.id);
    let walls = b.walls();
    let run = if r.brk.is_some() {
        if r.block.is_some() {
            Run::BreakBlock
        } else {
            Run::Break
        }
    } else if r.interrupt.is_some() {
        if r.block.is_some() {
            Run::InterruptedBlock
        } else {
            Run::Interrupted
        }
    } else if let Some(ob) = r.block {
        if walls.iter().any(|(_, lo, hi, _)| *lo <= now && now < *hi) {
            Run::WallOnNow
        } else if cached(ob).is_some_and(|a| !a.paused && b.worked().unwrap_or(0) >= a.est_min) {
            Run::Overtime
        } else {
            Run::Running
        }
    } else {
        Run::Idle
    };
    let done = b.replay.blocks_done(b.date());
    let shape = if walls.iter().any(|w| w.3) {
        DayShape::Travel
    } else if done > 0 && st.budget.is_some_and(|x| capacity::remaining_budget(x, done) == 0) {
        DayShape::Spent
    } else if st.window.is_none() {
        DayShape::Late
    } else if st.loc.as_deref() == Some("home") {
        DayShape::Home
    } else {
        DayShape::Lounge
    };
    Class { run, shape }
}

/// **Is this a world the shipped binary can hold?** (owner D64(b), README gap
/// 3138) — the property every frozen world is held to, one clause per way the
/// binary's own verbs and D42's reconcile would move `.tm/state.json` off the
/// stored one. `Err` names every clause that fails.
///
/// 1. **The cache names the block the log holds open.** `reconcile_state`
///    compares the two by identity and the log wins.
/// 2. **The cache's interruption is the log's**, by identity (the reconcile's
///    comparison) and by start (a rebuild reads `started` off the log's line).
/// 3. **A running break began after the last `start`, `done` or `stop` the
///    log holds**: `tm start`, `tm done` and `tm stop` each end one
///    (`tm/src/cli/day.rs`' `end_break`), so one still running began after all
///    of them.
/// 4. **A paused block was paused by something the binary pauses it for**: the
///    log's own `pause` (`OpenBlock::paused`), the running break (`tm break`
///    pauses it), or an interruption that began while it ran (`tm interrupt`
///    names and pauses it) — and a block that is not paused has none of them.
///    `est_min` is the cache's alone (`HOST_ONLY_STATE`) and is not asked.
pub fn binary_holds(b: &Built) -> Result<(), Vec<String>> {
    let st = &b.world.state;
    let r = running(b);
    let tz = b.cfg.tz;
    let mut bad = Vec::new();
    let cached_block = st.active.as_ref().map(|a| a.id.as_str().to_string());
    let logged_block = r.block.map(|ob| ob.id.clone());
    if cached_block != logged_block {
        bad.push(format!("1: .tm/state.json runs {cached_block:?} and the log holds {logged_block:?} open"));
    }
    let cached_int = st.interrupt.as_ref().map(|i| (i.id.as_ref().map(|x| x.as_str().to_string()), i.started));
    let logged_int = r.interrupt.map(|i| (i.id.clone(), i.start.map(|t| t.with_timezone(&tz).time())));
    if cached_int != logged_int {
        bad.push(format!("2: .tm/state.json's interruption is {cached_int:?} and the log's {logged_int:?}"));
    }
    if let Some(started) = r.brk.and_then(|x| x.started) {
        let at = local_dt(tz, b.date(), started).fixed_offset();
        let last = b
            .replay
            .view()
            .iter()
            .filter(|row| !row.cancelled && matches!(row.tag.as_str(), "start" | "done" | "stop"))
            .map(|row| row.t)
            .max();
        if let Some(last) = last.filter(|l| *l > at) {
            bad.push(format!("3: a break running since {started} began before the log's last start/done/stop at {last}"));
        }
    }
    if let (Some(a), Some(ob)) = (st.active.as_ref(), r.block) {
        let by_interrupt = r.interrupt.is_some_and(|i| i.id.as_deref() == Some(ob.id.as_str()));
        let reason = ob.paused || r.brk.is_some() || by_interrupt;
        if a.paused != reason {
            bad.push(format!(
                "4: the block is {}paused and the log pauses it {ob_p}, a break runs {}, an interruption names it {by_interrupt}",
                if a.paused { "" } else { "not " },
                r.brk.is_some(),
                ob_p = ob.paused,
            ));
        }
    }
    if bad.is_empty() {
        Ok(())
    } else {
        Err(bad)
    }
}

// ---------------------------------------------------------------------------
// The frozen file
// ---------------------------------------------------------------------------

/// The frozen classes: one JSON line per class.
pub const FROZEN_CLASSES: &str = "fork-4748911-planner-classes.jsonl";

/// Where it lives.
pub fn frozen_path() -> std::path::PathBuf {
    forkday::frozen_path().with_file_name(FROZEN_CLASSES)
}

/// The frozen lines, read once, in file order.
pub fn frozen_lines() -> &'static Vec<Value> {
    static FROZEN: OnceLock<Vec<Value>> = OnceLock::new();
    FROZEN.get_or_init(|| {
        let path = frozen_path();
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("{}: {e} — see support/forkclass.rs", path.display()));
        text.lines()
            .filter(|l| !l.trim().is_empty())
            .map(|l| serde_json::from_str(l).expect("a frozen class line is JSON"))
            .collect()
    })
}

/// A day and its digest, as a frozen line carries it — `forkday`'s shape.
pub fn frozen_day(day: &DayPlan) -> Value {
    json!({"hash": day.hash(), "day": serde_json::to_value(day).expect("a day serialises")})
}

// ---------------------------------------------------------------------------
// Where every world came from: the class draw, from the tree (README gap 3080)
// ---------------------------------------------------------------------------

/// **Which arm's widenings a draw applied, and the values it drew for them** —
/// the W-36 class draw's protocol, re-run from the tree. Each arm's widening is
/// `plangen`'s one function, called here as the arm calls it.
///
/// **The protocol is the draw's, not today's arms'.** Its value order is the
/// one W-36 track H's harness drew in — the case, the arm (`0..4`), then that
/// arm's values: the hash arm's multiplier and logged break, the W-35 arm's
/// running break and forced overtime, the step-8 arm's travel day and spent
/// budget. The hash ARM has since drawn a third value (`errands`, the W-36 land
/// step's batch widening, README gap 3126); the draw does not, because a value
/// drawn in the middle of the sequence re-maps every later draw index, and the
/// recorded indices are what makes a frozen world checkable.
#[derive(Clone, Debug, PartialEq)]
pub enum Widening {
    /// No widening: the shared generator's day.
    Base,
    /// `the_kernel_hashes_the_day_the_fork_hashes`': a multiplier and a break in the log.
    Hash { mult: Option<f64>, brk: Option<(u32, u32)> },
    /// `the_kernel_keeps_the_break_the_overtime_block_and_the_wall_pause`': a running
    /// break (`ago`, `planned`, `place`) and a forced overtime.
    W35 { brk: Option<(u32, u32, &'static str)>, over: bool },
    /// `the_kernel_writes_the_rest_of_step_8_as_the_fork_does`': a travel day and a spent budget.
    Step8 { travel: bool, spent: bool },
}

impl Widening {
    /// The arm's name, as a frozen line records it.
    pub fn arm(&self) -> &'static str {
        match self {
            Widening::Base => "base",
            Widening::Hash { .. } => "hash",
            Widening::W35 { .. } => "w35",
            Widening::Step8 { .. } => "step8",
        }
    }

    /// The arm's number in the draw (`0..4`), by its name.
    pub fn number_of(arm: &str) -> Option<u8> {
        ["base", "hash", "w35", "step8"].iter().position(|a| *a == arm).and_then(|i| u8::try_from(i).ok())
    }
}

/// One draw of the class draw.
#[derive(Clone, Debug)]
pub struct Draw {
    /// Its index in the sequence from its seed.
    pub index: usize,
    /// The shared generator's case.
    pub case: plangen::Case,
    /// The arm and its widening values.
    pub widening: Widening,
}

/// **The class draw from `seed`**: an endless sequence of [`Draw`]s, each the
/// shared generator's `Case`, then one arm and that arm's values — or, for a
/// TARGETED draw (W-36's `wall-on-now/spent`), the arm forced to `force` while
/// its number is still drawn and discarded, as W-36's harness did. The seed is
/// the text's bytes, space-padded to 32, as a ChaCha seed.
pub fn class_draws(seed: &str, force: Option<u8>) -> impl Iterator<Item = Draw> {
    let mut bytes = [b' '; 32];
    for (d, s) in bytes.iter_mut().zip(seed.bytes()) {
        *d = s;
    }
    let mut runner = TestRunner::new_with_rng(
        ProptestConfig::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &bytes),
    );
    let mult_s = prop::sample::select(vec![
        None, Some(1.6), Some(0.25), Some(2.0), Some(1.125), Some(0.3), Some(0.000001),
        Some(0.00001), Some(0.1 + 0.2), Some(123.456),
    ]);
    let lbrk_s = prop::option::of((5u32..=30, 0u32..=40));
    let brk_s = prop::option::of((0u32..=40, 5u32..=30, prop::sample::select(vec!["walk", "seat", "bed", "phone"])));
    let over_s = prop_oneof![1 => Just(false), 1 => Just(true)];
    let travel_s = prop_oneof![3 => Just(false), 1 => Just(true)];
    let spent_s = prop_oneof![3 => Just(false), 1 => Just(true)];
    let arm_s = 0u8..4;
    let case_s = plangen::case_strategy();
    (0usize..).map(move |index| {
        let case = case_s.new_tree(&mut runner).expect("a case").current();
        let drawn = arm_s.new_tree(&mut runner).expect("an arm").current();
        let widening = match force.unwrap_or(drawn) {
            1 => Widening::Hash {
                mult: mult_s.new_tree(&mut runner).expect("a multiplier").current(),
                brk: lbrk_s.new_tree(&mut runner).expect("a break").current(),
            },
            2 => Widening::W35 {
                brk: brk_s.new_tree(&mut runner).expect("a break").current(),
                over: over_s.new_tree(&mut runner).expect("an overtime").current(),
            },
            3 => Widening::Step8 {
                travel: travel_s.new_tree(&mut runner).expect("a travel day").current(),
                spent: spent_s.new_tree(&mut runner).expect("a spent day").current(),
            },
            _ => Widening::Base,
        };
        Draw { index, case, widening }
    })
}

/// **The world a draw builds** — the shared generator's day, widened by its
/// arm's one function each (`plangen`'s `World::set_multiplier`,
/// `log_a_break`, `run_a_break`, `force_overtime` and `widen_for_notes`), in
/// the order that arm applies them.
pub fn world_of(draw: &Draw) -> ClassWorld {
    let mut w = plangen::build(&draw.case);
    let mut mult = None;
    match &draw.widening {
        Widening::Base => {}
        Widening::Hash { mult: m, brk } => {
            w.set_multiplier(*m);
            mult = m.map(|m| format!("{m}"));
            w.log_a_break(&draw.case, *brk);
        }
        Widening::W35 { brk, over } => {
            w.force_overtime(&draw.case, *over, brk.is_some());
            w.run_a_break(&draw.case, *brk);
        }
        Widening::Step8 { travel, spent } => {
            plangen::widen_for_notes(&mut w, &draw.case, *travel, *spent);
        }
    }
    ClassWorld { docs: w.docs, log: w.log, state: w.state, now: w.now, mult }
}

/// **The draws a frozen line's provenance can name** — its seed, index and
/// arm, re-run: the arm DRAWN at that index when it is the recorded one, and
/// the TARGETED draw with the recorded arm forced at every index (W-36 drew
/// `wall-on-now/spent` and the `rest_debt` day that way, and a line does not
/// record which). A targeted line whose untargeted draw happens to land on the
/// same arm at the same index names two draws; the verification takes the one
/// that rebuilds its world, and a re-draw the first.
pub fn draws_of_line(line: &Value) -> Vec<Draw> {
    let (Some(seed), Some(index), Some(arm)) = (
        line["seed"].as_str(),
        line["draw"].as_u64().and_then(|d| usize::try_from(d).ok()),
        line["arm"].as_str(),
    ) else {
        return Vec::new();
    };
    let mut out: Vec<Draw> = class_draws(seed, None).nth(index).filter(|d| d.widening.arm() == arm).into_iter().collect();
    out.extend(Widening::number_of(arm).and_then(|n| class_draws(seed, Some(n)).nth(index)));
    out
}

// ---------------------------------------------------------------------------
// D61's worlds: the pause the binary logs at a wall's start (README gap 3123)
// ---------------------------------------------------------------------------

/// **The worlds D61 derives from a stored one** (the owner's D61, W-36 track T;
/// README gap 3123): when a block runs, unpaused, with no break and no
/// interruption, and a wall's blocked span that began AFTER the block started
/// covers `now`, the first verb after the wall began logs `pause{id}` stamped at
/// the span's start and marks the block paused (`tm/src/cli/day.rs`'
/// `stop_the_timer_at_walls`, spans merged as its `merged_spans` merges them) —
/// and, for an earlier span of the same kind that has ended by `now`, its
/// `pause` and its `unpause`, in order, as that loop logs them.
/// So the binary holds that world, not the stored one, from then on. Returned
/// at `now` and again twenty minutes into the meeting (the drive's `tm now` at
/// 13:20), each with the pause's instant; empty when the rule does not fire.
pub fn d61_worlds(parent: &ClassWorld) -> Vec<(ClassWorld, DateTime<Tz>)> {
    let b = Built::of(parent.clone());
    let r = running(&b);
    let Some(ob) = r.block else { return Vec::new() };
    let Some(a) = parent.state.active.clone().filter(|a| !a.paused && a.id.as_str() == ob.id) else {
        return Vec::new();
    };
    if r.brk.is_some() || r.interrupt.is_some() {
        return Vec::new();
    }
    let tz = b.cfg.tz;
    let started = local_dt(tz, b.date(), a.started);
    let now = parent.now;
    let mut spans: Vec<(DateTime<Tz>, DateTime<Tz>)> = b.walls().iter().map(|(_, lo, hi, _)| (*lo, *hi)).collect();
    spans.sort();
    let mut merged: Vec<(DateTime<Tz>, DateTime<Tz>)> = Vec::new();
    for (lo, hi) in spans {
        match merged.last_mut() {
            Some(m) if lo <= m.1 => m.1 = m.1.max(hi),
            _ => merged.push((lo, hi)),
        }
    }
    // The span covering `now` that began after the block started: the world D61 pauses.
    let Some((lo, hi)) = merged.iter().copied().find(|(lo, hi)| *lo <= now && now < *hi && *lo > started) else {
        return Vec::new();
    };
    // Every span that began after the block started and by `now`, in order, as the loop
    // logs them: `pause` at its start, and `unpause` at its end once it has ended.
    let line = |t: DateTime<Tz>, ev: Event| {
        LogEntry::new(t.fixed_offset(), ev).to_json().expect("a timer entry serialises") + "\n"
    };
    let id = a.id.as_str().to_string();
    let mut paused = parent.clone();
    for (l, h) in merged.iter().copied().filter(|(l, _)| *l > started && *l <= now) {
        paused.log.push_str(&line(l, Event::Pause { id: id.clone() }));
        if h <= now {
            paused.log.push_str(&line(h, Event::Unpause { id: id.clone() }));
        }
    }
    if let Some(x) = paused.state.active.as_mut() {
        x.paused = true;
    }
    let mid = (lo + Duration::minutes(20)).min(hi - Duration::minutes(1));
    [now, mid]
        .into_iter()
        .filter(|at| *at >= now && *at < hi)
        .fold(Vec::new(), |mut out: Vec<(ClassWorld, DateTime<Tz>)>, at| {
            if out.iter().all(|(w, _)| w.now != at) {
                let mut w = paused.clone();
                w.now = at;
                out.push((w, lo));
            }
            out
        })
}

// ---------------------------------------------------------------------------
// The owner's D64: the rule a re-bless is held to (README gap 3133)
// ---------------------------------------------------------------------------

/// The keys of a frozen line that are the fork's answers — what a re-bless
/// recomputes. Everything else on the line is the world and its provenance.
pub const ANSWERS: [&str; 5] = ["day", "shipped", "d57", "d60", "whatif"];

/// **The parity flags a line carries**: every key spelled `p<n>` with a boolean
/// value, in any object the line carries beside the world and the days — the
/// comparand's own flags are named by their parity number (`d57.p46`,
/// `d57.p47`, `d60.p51`), so the flag IS the number. `(n, set)`.
pub fn parity_flags(line: &Value) -> Vec<(u32, bool)> {
    let mut out = Vec::new();
    for (k, v) in line.as_object().into_iter().flatten() {
        if matches!(k.as_str(), "world" | "day" | "shipped" | "whatif") {
            continue;
        }
        for (f, set) in v.as_object().into_iter().flatten() {
            let n = f.strip_prefix('p').and_then(|d| d.parse::<u32>().ok()).filter(|_| f[1..].bytes().all(|c| c.is_ascii_digit()));
            if let (Some(n), Some(set)) = (n, set.as_bool()) {
                out.push((n, set));
            }
        }
    }
    out
}

/// **The parity numbers `kernel/parity.txt` registers** — every row that is
/// not a `hole` (check 10's register, `kernel/parity.py`'s specification).
pub fn registered_parity() -> BTreeSet<u32> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/parity.txt");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    text.lines()
        .filter_map(|l| l.split_whitespace().next())
        .filter_map(|w| w.strip_prefix('P'))
        .filter_map(|d| d.parse().ok())
        .collect()
}

/// **What one frozen line's re-bless changed, and whether D64 allows it** —
/// the rule the re-bless path is held to. `old` is the committed line, `new`
/// the line with the fork's answers recomputed; `because` the parity numbers
/// the re-bless was run for (`TM_PLANNER_BLESS_BECAUSE`); `registered` the
/// register's numbers. `Ok` names what changed (empty when nothing did);
/// `Err` says why a change is NOT allowed.
///
/// * A line whose answers were cleared (a world re-drawn under D64(b), or a
///   derived D61 world added) takes whatever the fork answers — the re-draw
///   is where D64(b)'s reason was demanded.
/// * Otherwise a change is allowed exactly when (a) a number the re-bless was
///   run for is REGISTERED and its flag is set on the line, before or after.
/// * In every case the shipped fork's day stays by value: where the comparand
///   departs from it, `shipped` holds it.
pub fn d64_allows(
    old: &Value,
    new: &Value,
    shipped_day: &Value,
    because: &[u32],
    registered: &BTreeSet<u32>,
) -> Result<Vec<String>, String> {
    let key = old["class"].as_str().unwrap_or("<no class>");
    let what = |w: &Value| new["secondary"].as_str().map_or(key.to_string(), |s| format!("{key} ({s})")) + &format!(" at {}", w["now"].as_str().unwrap_or("?"));
    let who = what(&new["world"]);
    if new["day"]["day"] != *shipped_day && new["shipped"]["day"] != *shipped_day {
        return Err(format!("{who}: the comparand departs from the shipped fork's day and `shipped` does not hold it by value"));
    }
    if old["day"].is_null() {
        return Ok(Vec::new());
    }
    let changed: Vec<String> = ANSWERS.iter().filter(|k| old[**k] != new[**k]).map(|k| (*k).to_string()).collect();
    if changed.is_empty() {
        return Ok(changed);
    }
    for n in because {
        if !registered.contains(n) {
            return Err(format!("{who}: re-blessed for P{n}, which kernel/parity.txt does not register"));
        }
    }
    let set: BTreeSet<u32> = parity_flags(old).into_iter().chain(parity_flags(new)).filter(|f| f.1).map(|f| f.0).collect();
    if because.iter().any(|n| set.contains(n)) {
        Ok(changed)
    } else if because.is_empty() {
        Err(format!(
            "{who}: `{}` changed and the re-bless names no reason — the owner's D64 allows (a) a registered parity \
             number whose flag the line carries, or (b) a world the binary cannot build, re-drawn with its reason",
            changed.join("`, `")
        ))
    } else {
        Err(format!(
            "{who}: `{}` changed and the line carries no flag of P{} — the parity numbers set on it are {set:?}",
            changed.join("`, `"),
            because.iter().map(u32::to_string).collect::<Vec<_>>().join(", P")
        ))
    }
}

// ---------------------------------------------------------------------------
// The planner's own order among p = 0 answers: D60 and D63 (README gap 3122)
// ---------------------------------------------------------------------------

/// **A `p = 0` answer with a positive shortfall** — the kernel's D60 condition
/// (`Planner.Ranked.imp`: `key.p = 0 ∧ 0 < shortfall`), read off the kernel's
/// own §7 answer.
pub fn is_impossible_tie(p: &Prio) -> bool {
    p.p == 0 && p.shortfall_min_exact.num > 0
}

/// **The candidates re-keyed to the planner's own §7.4 order** (the owner's D60
/// and D63; W-36 land, README gap 3121): a `p = 0` answer with a positive
/// shortfall — read off the kernel's answer FOR THAT ID — is ranked by its
/// `until` and then its REQUEST position (`planreq::send_order`, which is
/// `kernel_capacity::send_order`), before every other `p = 0` answer, and the
/// other answers keep the fork's `(root_order, own_order)`. Both fork sorts
/// (`sorted_candidates`, `build_groups`) read only those two fields of a
/// `with_ranking` day, so rewriting them runs D60's key IN the fork: an
/// impossible tie gets `(0, until)` and `(0, position)`, and every other
/// candidate's root moves one file down (a uniform shift, which keeps the
/// fork's order among them). It is also the order D63 says §8.3's monotone-rank
/// check reads.
///
/// **One copy since W-37 track H (README gap 3122)**: `planner_classes.rs` found
/// the answer by id and `planner_invariants.rs`' own copy (w36_d60_cands, deleted) by
/// index and id — the same rule where the answers are keyed 1:1, which is the only case
/// either caller hands it (a grant list an id names twice is refused before).
pub fn d60_cands(cands: &[Candidate], prios: &[Prio]) -> Vec<Candidate> {
    let mut pos = vec![0usize; cands.len()];
    for (k, &i) in planreq::send_order(cands).iter().enumerate() {
        pos[i] = k;
    }
    cands
        .iter()
        .enumerate()
        .map(|(i, c)| {
            let mut d = c.clone();
            match prios.iter().find(|p| p.id == c.id).filter(|p| is_impossible_tie(p)) {
                Some(p) if !c.is_wall => {
                    let until = p.until.map_or(0, |u| {
                        usize::try_from(chrono::Datelike::num_days_from_ce(&u)).unwrap_or(0)
                    });
                    d.root_order = (0, until);
                    d.own_order = (0, pos[i]);
                }
                _ => d.root_order = (c.root_order.0.saturating_add(1), c.root_order.1),
            }
            d
        })
        .collect()
}

// ---------------------------------------------------------------------------
// P45's rule, on the day the kernel planned
// ---------------------------------------------------------------------------

/// **P45's rule, checked on a decoded day**: the running break drawn at `t`
/// for `planned` minutes is exactly one Break row `[max(t, day start),
/// max(min(t + planned, day end), now))`, open exactly when it has overrun,
/// carrying its place; no row §8.2 PLACES from `now` on — a Block, Batch,
/// Routine, Optional or Rest — overlaps it; and **every §8.2 step-5 row from
/// `now` on starts at or after its end** (README gap 2925: the cut restarts
/// there). Returns the row's span and whether it is open; `Err` names what
/// failed, so the perturbation test can show the rule bites.
pub fn p45_rule(
    day: &DayPlan,
    t: DateTime<Tz>,
    planned: u32,
    place: Option<&str>,
    now: DateTime<Tz>,
    day_span: (DateTime<Tz>, DateTime<Tz>),
) -> Result<(DateTime<Tz>, DateTime<Tz>, bool), String> {
    let brks: Vec<_> = day.segments.iter().filter(|s| s.kind == SegKind::Break).collect();
    if brks.len() != 1 {
        return Err(format!("{} Break rows, want the running break's one", brks.len()));
    }
    let b = brks[0];
    let end = t + Duration::minutes(i64::from(planned));
    let (lo, hi) = (t.max(day_span.0), end.min(day_span.1).max(now));
    let open = end <= now;
    if (b.start, b.end) != (lo, hi) {
        return Err(format!("the Break row is {}–{}, the rule says {lo}–{hi}", b.start, b.end));
    }
    if b.flags.open != open {
        return Err(format!("the Break row's `open` is {}, the rule says {open}", b.flags.open));
    }
    if b.flags.note.as_deref() != place {
        return Err(format!("the Break row's note is {:?}, want its place {place:?}", b.flags.note));
    }
    for s in &day.segments {
        let placed = matches!(
            s.kind,
            SegKind::Block | SegKind::Batch(_) | SegKind::Routine | SegKind::Optional | SegKind::Rest
        );
        if placed && s.start >= now && s.start < hi && lo < s.end {
            return Err(format!("a {:?} row {}–{} is scheduled over the break {lo}–{hi}", s.kind, s.start, s.end));
        }
        // §8.2 step 5's rows are the work rows in a slot (they carry its energy).
        if s.kind.is_work() && s.energy.is_some() && s.start >= now && s.start < hi {
            return Err(format!("a step-5 row starts at {}, before the break's end {hi}", s.start));
        }
    }
    Ok((lo, hi, open))
}

// ---------------------------------------------------------------------------
// The comparison
// ---------------------------------------------------------------------------

/// What the class comparison counted, so "no disagreement" is never confused
/// with "never ran" (AGENTS §7.3).
#[derive(Default, Debug)]
pub struct ClassTally {
    /// The day comparison's own tally, over every day that is not a P45 day.
    pub day: forkday::DayTally,
    /// The classes compared.
    pub classes: BTreeSet<String>,
    /// P45 days checked against the rule, of them still running, of them
    /// overrun, and on how many the shipped fork scheduled over the break.
    pub p45: usize,
    pub p45_running: usize,
    pub p45_overrun: usize,
    pub p45_shipped_over: usize,
    /// Values compared by value on the P45 days (date, window, budget, walls).
    pub p45_values: usize,
    /// Days whose comparand departs from the shipped fork's day: P46, P47.
    pub p46: usize,
    pub p47: usize,
    /// Days whose comparand departs from the shipped fork's day by D60's key
    /// (parity P51, the W-36 land step): the fork ran D60's order.
    pub p51: usize,
    /// Under-used rows whose `↓` note the renderer derived as the fork wrote it.
    pub notes_rendered: usize,
    /// §9.1 what-ifs compared, of them parity P44 days, and ids compared.
    pub whatifs: usize,
    pub p44: usize,
    pub whatif_ids: usize,
}

impl ClassTally {
    /// One line: what was compared and what was not.
    pub fn line(&self, findings: usize) -> String {
        format!(
            "frozen fork classes — {} class(es); {}; P45 days {} against the rule (running {}, overrun {}; \
             the shipped fork scheduled over the break on {}; {} values by value); P46 comparand days {}, \
             P47 {}, P51 {}; under-used notes the renderer derived as the fork wrote them {}; what-ifs {} ({} \
             parity-P44 days, {} ids); {findings} difference(s) in all",
            self.classes.len(),
            self.day.line("the non-P45 days", findings),
            self.p45,
            self.p45_running,
            self.p45_overrun,
            self.p45_shipped_over,
            self.p45_values,
            self.p46,
            self.p47,
            self.p51,
            self.notes_rendered,
            self.whatifs,
            self.p44,
            self.whatif_ids,
        )
    }
}

/// **The block §9.1's what-if is asked about**: the running block, when no
/// break is running — `tm break` pauses it, and the TUI's overtime prompt asks
/// only of a block that runs (`App::extend_drops`' one reachable branch).
pub fn whatif_item(st: &RuntimeState) -> Option<&Id> {
    let breaking = st.break_.as_ref().is_some_and(|x| x.started.is_some());
    st.active.as_ref().filter(|_| !breaking).map(|a| &a.id)
}

/// The kernel's answer for a world, and the grants it ranked by: the day, and
/// on a day [`whatif_item`] names a block for, §9.1's what-if for one block on
/// it.
pub fn kernel_answer_with_grants(b: &Built) -> Result<(KernelDay, Vec<priority::Prio>), String> {
    let overtime = whatif_item(&b.world.state).map(|id| planwire::overtime_json(id, 1, None));
    planreq::kernel_day(&b.request_world(), overtime).map(|(k, ans)| (k, ans.prios))
}

/// [`kernel_answer_with_grants`]' day alone.
pub fn kernel_answer(b: &Built) -> Result<KernelDay, String> {
    kernel_answer_with_grants(b).map(|(k, _)| k)
}

/// **Compare one frozen class line with the kernel's answer**, by value.
/// Returns every difference outside the declared classes, by name.
pub fn compare_line(line: &Value, t: &mut ClassTally) -> Vec<String> {
    let tz = Config::default().tz;
    let key = line["class"].as_str().unwrap_or("<no class>").to_string();
    let mut findings = Vec::new();
    let world = match ClassWorld::of_json(&line["world"], tz) {
        Ok(w) => w,
        Err(e) => return vec![format!("{key}: {e}")],
    };
    let b = Built::of(world);
    let class = class_of(&b).key();
    if class != key {
        findings.push(format!("{key}: the stored world classifies as `{class}` — a line may not choose its class"));
    }
    t.classes.insert(key.clone());
    let k = match kernel_answer(&b) {
        Ok(k) => k,
        Err(e) => return vec![format!("{key}: the kernel did not plan the day: {e}")],
    };
    let fork = &line["day"];
    let now = b.world.now;
    let st = &b.world.state;
    if let Some(brk) = st.break_.as_ref().filter(|x| x.started.is_some()) {
        // P45: the rule, and what the fork's day still says by value.
        let started = local_dt(tz, b.date(), brk.started.expect("filtered"));
        match p45_rule(&k.day, started, brk.planned_min, brk.place.as_deref(), now, b.day_bounds()) {
            Err(e) => findings.push(format!("{key}: P45: {e}")),
            Ok((lo, hi, open)) => {
                t.p45 += 1;
                t.p45_running += usize::from(!open);
                t.p45_overrun += usize::from(open);
                // The SHIPPED fork's day, where the comparand departs from it.
                let shipped = line.get("shipped").filter(|v| !v.is_null()).unwrap_or(fork);
                let over = shipped["day"]["segments"].as_array().map(Vec::as_slice).unwrap_or_default().iter().any(|s| {
                    let placed = matches!(s["kind"].as_str(), Some("block" | "batch" | "rest" | "routine" | "optional"));
                    let at = |v: &Value| DateTime::parse_from_rfc3339(v.as_str().unwrap_or_default()).ok();
                    placed
                        && at(&s["start"]).is_some_and(|a| a >= now.fixed_offset() && a < hi.fixed_offset())
                        && at(&s["end"]).is_some_and(|z| lo.fixed_offset() < z)
                });
                t.p45_shipped_over += usize::from(over);
            }
        }
        let kv = serde_json::to_value(&k.day).expect("the kernel's day serialises");
        for key2 in ["date", "window", "budget_blocks"] {
            t.p45_values += 1;
            if kv[key2] != fork["day"][key2] {
                findings.push(format!("{key}: {key2}: kernel {} fork {}", kv[key2], fork["day"][key2]));
            }
        }
        let walls = |v: &Value| -> Vec<Value> {
            v["segments"].as_array().map(Vec::as_slice).unwrap_or_default().iter()
                .filter(|s| s["kind"] == "wall").cloned().collect()
        };
        let (kw, fw) = (walls(&kv), walls(&fork["day"]));
        t.p45_values += fw.len();
        if kw != fw {
            findings.push(format!("{key}: the walls moved: kernel {} fork {}", kw.len(), fw.len()));
        }
    } else {
        findings.extend(forkday::compare_day_with_fork(&key, &k, fork, now, &mut t.day));
        // The under-used note the kernel leaves to the renderer (by design,
        // `forkday`'s fourth class): the renderer must derive the fork's exact
        // sentence from the kernel's own row.
        let fork_rows = fork["day"]["segments"].as_array().map(Vec::as_slice).unwrap_or_default();
        for seg in k.day.segments.iter().filter(|s| s.flags.underused && s.flags.note.is_none()) {
            let sv = serde_json::to_value(seg).expect("a row serialises");
            let twin = fork_rows.iter().find(|f| f["start"] == sv["start"] && f["end"] == sv["end"] && f["item"] == sv["item"]);
            let derived = tm_core::emit::note_cell(seg, &b.tree, &k.day);
            match twin.and_then(|f| f["flags"]["note"].as_str()) {
                Some(note) if note == derived => t.notes_rendered += 1,
                other => findings.push(format!(
                    "{key}: the renderer derives `{derived}` for the kernel's under-used row at {} and the fork wrote {other:?}",
                    sv["start"]
                )),
            }
        }
    }
    if line.get("shipped").is_some_and(|v| !v.is_null()) {
        let d57 = &line["d57"];
        t.p46 += usize::from(d57["p46"] == true);
        t.p47 += usize::from(d57["p47"] == true);
        t.p51 += usize::from(line["d60"]["p51"] == true);
    }
    // §9.1's what-if, on a day with a running block.
    match (&k.overtime, line.get("whatif").filter(|v| !v.is_null())) {
        (Some(kd), Some(w)) => {
            let kv = serde_json::to_value(kd).expect("a diff serialises");
            let want = if w["full"] == w["est"] { &w["full"] } else { &w["est"] };
            t.whatifs += 1;
            t.p44 += usize::from(w["full"] != w["est"]);
            t.whatif_ids += kd.removed.len() + kd.added.len() + kd.moved.len();
            if &kv != want {
                findings.push(format!(
                    "{key}: the overtime what-if differs from the {}: kernel {kv} fork {want}",
                    if w["full"] == w["est"] { "shipped TUI's" } else { "estimate's (a parity-P44 day)" }
                ));
            }
        }
        (None, None) => {}
        (Some(_), None) => findings.push(format!("{key}: the kernel answered a what-if no frozen line holds")),
        (None, Some(_)) => findings.push(format!("{key}: a frozen what-if the kernel did not answer")),
    }
    findings
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gaps 3121, 3122)
/// **A P51 day**: D60's key moves the fork's §7.4 order — `sorted_candidates`
/// over the candidates as collected, and over [`d60_cands`]'. Counted, never
/// asserted: the comparand runs D60's key on every day, so this says only which
/// days it changed. One copy (README gap 3122), for both fork arms.
pub fn is_p51(cands: &[Candidate], prios: &[Prio]) -> bool {
    let dvec = d60_cands(cands, prios);
    let a: Vec<&str> = priority::sorted_candidates(prios, cands).iter().map(|c| c.id.as_str()).collect();
    let b: Vec<&str> = priority::sorted_candidates(prios, &dvec).iter().map(|c| c.id.as_str()).collect();
    a != b
}
// END THE FORK PLANNER
