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
//!   and the estimate alone (`est`). **Since W-38 the kernel is asked as R3's
//!   host will ask it** ([`kernel_answer_with_grants`]: the host's GROWN
//!   facts, D58, and the host's worked minutes) and is held to `full` on every
//!   day — parity P44's class (`full ≠ est`) is counted, and on it too the
//!   kernel must answer `full`; until W-38 the request sent no grown facts and
//!   the kernel was held to `est` there. A day
//!   the grown facts re-rank carries `grown` (the fork's full what-if ranked as
//!   the kernel ranks the grown request) and is held to it: parity P52.
//! * **W-38's four answers, each an object named by its parity number and
//!   present only where its rule departs** (README gaps 3207, 3282, 3320):
//!   `p45` — on a break day, the fork's day planned where P45 restarts the
//!   cut, its rows from there (`from`, `rows`); `p52` — the what-if's `grown`
//!   is the comparand; `p55` — the comparand reads the host's worked minutes
//!   (`planner_invariants`' `w36_fork_plan`, on the grown what-if too); `p56` —
//!   a meeting's closed pause is drawn as the wall alone and `shipped` is fork
//!   4748911's drawing (`b3c29a3`'s `past_segments`; the in-tree fork was
//!   changed to agree at W-37 track T).
//!
//! A **P45** day (a running break) has no fork analogue at all — fork
//! `planner::plan` reads no `runtime.break_` and plans over it — so the kernel
//! is checked against P45's RULE ([`p45_rule`]): one Break row where the break
//! is, open once overrun, carrying its place; nothing §8.2 places over it; and
//! (README gap 2925's second half) every §8.2 step-5 row from `now` on starts
//! at or after the break's end. What the fork's day still says on such a day —
//! the date, the window, the budget and the walls — is compared by value; and
//! since W-38 (README gap 3207) the open row of the block the break paused
//! ([`p45_paused_row`]) and every row from where the cut restarts — the
//! step-5 assignment, the rests and the KEPT BREAKS — against `p45`, the fork's
//! own day planned there.
//!
//! # The lines that are not a class's one primary day
//!
//! A SECONDARY line is drawn for a floor no primary reached (`rest_debt`,
//! `whatif` at W-36; `p52` at W-38) or DERIVED from a primary line by a rule
//! stated here: [`d61_worlds`] (the pause the binary logs at a wall's start —
//! and since W-38 the world after the meeting, the closed pause P56 draws),
//! [`window_worlds`] (a dated window task: the routine row's `⚠`, gap 3200),
//! [`worked_worlds`] (a break logged inside the running block: P55) and
//! [`overrun_worlds`] (a running break carried past `break_min`, so P45's
//! comparand resets the counter: gaps 3207 and 3480). The file holds exactly
//! what each rule derives, and every derived world is one the binary can hold
//! ([`binary_holds`]).
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
//! began after the last `start`/`done`/`stop` (each ends one), and the cache is
//! what the binary rebuilds from the log — the block's pause included, asked of
//! the binary with the running break it cannot log (clause 5, since W-39: until
//! then a hand copy of `tm start`'s pause rule, clause 4, answered for it —
//! README gap 3536). Until W-37 twelve
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
    /// The configured `budget_ratio`, when the step-8 arm's spent budget set one
    /// (`plangen::spent_ratio`, README gap 3340): a spent budget is one `tm arrive`
    /// computed from the configuration. `Config::default()`'s else. Its decimal text.
    pub ratio: Option<String>,
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
            "ratio": self.ratio,
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
        let ratio = match &v["ratio"] {
            Value::Null => None,
            Value::String(s) => Some(s.clone()),
            other => return Err(format!("world.ratio is {other}, not a decimal's text")),
        };
        Ok(ClassWorld { docs, log, state, now, mult, ratio })
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
        let mut cfg = Config::default();
        if let Some(r) = &world.ratio {
            cfg.day.budget_ratio = r.parse().expect("a stored budget ratio is a decimal");
        }
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
    /// `tm arrive`'s window ends past midnight: the evening wall past the wind-down.
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
    } else if st.window.is_none_or(|(from, to)| to <= from) {
        // A late arrival: the evening wall pushes `tm arrive`'s window past midnight
        // (README gap 3340 — until the repair the class was read off a cache with NO
        // window, which the binary never holds: `tm arrive` always stores one).
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
/// 4. **Withdrawn at W-39 (README gap 3536): the block's pause is clause 5's.**
///    Clause 4 restated `tm start`'s pause rule by hand — a paused block had to
///    be paused by the log's `pause`, the running break or an open interruption
///    — beside clause 5, which asks the binary; the land step had to edit it by
///    hand when P60 changed the rule (gap 3478), and would have had to at every
///    change after. Clause 5 now asks the binary for `active.paused` too
///    ([`binary_rebuilds`]); the number is not reused, so a `d64b.held` record
///    naming `4:` still names the clause that refused its old world.
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
    bad.extend(binary_rebuilds(&b.world));
    if bad.is_empty() {
        Ok(())
    } else {
        Err(bad)
    }
}

/// **The fields of `.tm/state.json` the log does NOT carry** — read out of the
/// binary's own table (`tm/src/cli/ctx.rs`' `HOST_ONLY_STATE`), never listed here
/// (AGENTS §5.3): every other field is D42's to derive, and clause 5 compares it.
pub fn host_only_state() -> Vec<String> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/cli/ctx.rs");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let start = text.find("pub const HOST_ONLY_STATE").expect("the binary's host-only table");
    let end = start + text[start..].find("\n];").expect("its end");
    text[start..end]
        .lines()
        .filter_map(|l| l.trim().strip_prefix("(\"`"))
        .filter_map(|l| l.split('`').next())
        .map(str::to_string)
        .collect()
}

/// **Clauses 5 and 6, asked of the shipped binary itself** (owner D42/D45 and D61;
/// W-37 repair, README gap 3340). Until the repair `binary_holds` was four named
/// clauses — the block, the interruption, a break's start and `paused` — where D42's
/// invariant covers EVERY field the log derives, and every frozen world failed it
/// (the W-37 auditor: the cache said window `[07:00, 16:00]` where the log's own
/// `arrive` said `[07:00, 15:00]`, `home` where it said `lounge`, budget 2 where it
/// said 6, and no window at all on a late day). So the property is now the binary's:
///
/// 5. **The cache is what the binary rebuilds from the log**: with `.tm/state.json`
///    deleted, `tm now` rebuilds it (D42), and every field outside the binary's own
///    `HOST_ONLY_STATE` table must equal the stored one — **and the running block's
///    `paused` must be the one the binary derives** (W-39, README gap 3536: until then
///    clause 4 restated `tm start`'s pause rule by hand). `active.paused` is in the
///    table because a RUNNING break pauses the block and logs nothing until it ends, so
///    a rebuild from the log alone cannot see that pause; so the binary is asked with
///    `.tm/state.json` holding the table's top-level fields ALONE — the running break
///    among them — and no block: the reconcile then takes the block from the log and
///    derives its pause from every writer the log records and the break the cache still
///    holds (`ctx::derived_state`'s `running_break`, `ctx::logged_pause`), and `tm --json
///    now` reports it;
/// 6. **The world is at rest**: `tm now` over the stored world appends nothing to
///    the log — no housekeeping (D61's meeting pause, §6.3's automatic close) is
///    owed, so the world the binary PLANS is the world stored.
pub fn binary_rebuilds(world: &ClassWorld) -> Vec<String> {
    let host_only = host_only_state();
    let mut bad = Vec::new();
    // The world's files, and `.tm/state.json` holding `state` when there is one.
    let write = |state: Option<&Value>| -> Result<tempfile::TempDir, String> {
        let dir = tempfile::TempDir::new().map_err(|e| format!("tempdir: {e}"))?;
        let root = dir.path();
        std::fs::create_dir_all(root.join(".tm")).map_err(|e| e.to_string())?;
        for (p, t) in &world.docs {
            let f = root.join(p);
            if let Some(parent) = f.parent() {
                std::fs::create_dir_all(parent).map_err(|e| e.to_string())?;
            }
            std::fs::write(&f, t).map_err(|e| e.to_string())?;
        }
        std::fs::write(root.join(".tm/log.jsonl"), &world.log).map_err(|e| e.to_string())?;
        let cfg = world.ratio.as_ref().map(|r| format!("[day]\nbudget_ratio = {r}\n")).unwrap_or_default();
        std::fs::write(root.join("config.toml"), cfg).map_err(|e| e.to_string())?;
        if let Some(st) = state {
            let st = serde_json::to_string(st).map_err(|e| e.to_string())?;
            std::fs::write(root.join(".tm/state.json"), st).map_err(|e| e.to_string())?;
        }
        Ok(dir)
    };
    let run = |dir: &std::path::Path, json: bool| -> Result<String, String> {
        let mut cmd = std::process::Command::new(env!("CARGO_BIN_EXE_tm"));
        cmd.arg("--dir").arg(dir).arg("--now").arg(world.now.to_rfc3339());
        if json {
            cmd.arg("--json");
        }
        let out = cmd.arg("now").output().map_err(|e| format!("tm now: {e}"))?;
        if out.status.success() {
            Ok(String::from_utf8_lossy(&out.stdout).to_string())
        } else {
            Err(format!("tm now exited {:?}: {}", out.status.code(), String::from_utf8_lossy(&out.stderr)))
        }
    };
    let stored = serde_json::to_value(&world.state).unwrap_or(Value::Null);
    // 6. at rest.
    match write(Some(&stored)) {
        Err(e) => bad.push(format!("6: the world could not be written: {e}")),
        Ok(dir) => match run(dir.path(), false) {
            Err(e) => bad.push(format!("6: {e}")),
            Ok(_) => {
                let after = std::fs::read_to_string(dir.path().join(".tm/log.jsonl")).unwrap_or_default();
                if after != world.log {
                    let added: Vec<&str> = after.strip_prefix(world.log.as_str()).unwrap_or(&after).lines().collect();
                    bad.push(format!("6: the binary's housekeeping writes to the log on this world: {added:?}"));
                }
            }
        },
    }
    // 5. the cache is the log's.
    match write(None) {
        Err(e) => bad.push(format!("5: the world could not be written: {e}")),
        Ok(dir) => match run(dir.path(), false) {
            Err(e) => bad.push(format!("5: {e}")),
            Ok(_) => {
                let rebuilt: Value = std::fs::read_to_string(dir.path().join(".tm/state.json"))
                    .ok()
                    .and_then(|t| serde_json::from_str(&t).ok())
                    .unwrap_or(Value::Null);
                let mut keys: Vec<String> = stored.as_object().into_iter().flatten().map(|(k, _)| k.clone())
                    .chain(rebuilt.as_object().into_iter().flatten().map(|(k, _)| k.clone()))
                    .collect();
                keys.sort();
                keys.dedup();
                let blank = |v: &Value| v.is_null() || v.as_object().is_some_and(serde_json::Map::is_empty);
                for k in keys.iter().filter(|k| !host_only.contains(k)) {
                    let (mut a, mut z) = (stored[k.as_str()].clone(), rebuilt[k.as_str()].clone());
                    for inner in host_only.iter().filter_map(|h| h.strip_prefix(&format!("{k}."))) {
                        if let Some(o) = a.as_object_mut() {
                            o.remove(inner);
                        }
                        if let Some(o) = z.as_object_mut() {
                            o.remove(inner);
                        }
                    }
                    if a != z && !(blank(&a) && blank(&z)) {
                        bad.push(format!("5: .tm/state.json's `{k}` is {a} and the binary rebuilds {z} from the log"));
                    }
                }
            }
        },
    }
    // 5, the block's pause (README gap 3536): the cache holding only what the log cannot
    // carry — the table's top-level fields — so the binary derives the block, and its pause,
    // from the log and the running break.
    let kept: serde_json::Map<String, Value> = stored
        .as_object()
        .into_iter()
        .flatten()
        .filter(|(k, _)| host_only.iter().any(|h| h == *k))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    match write(Some(&Value::Object(kept))) {
        Err(e) => bad.push(format!("5: the world could not be written: {e}")),
        Ok(dir) => match run(dir.path(), true) {
            Err(e) => bad.push(format!("5: {e}")),
            Ok(out) => {
                let told: Value = serde_json::from_str(&out).unwrap_or(Value::Null);
                let derived = told["active"]["paused"].as_bool();
                let cached = world.state.active.as_ref().map(|a| a.paused);
                if derived != cached {
                    bad.push(format!(
                        "5: .tm/state.json's `active.paused` is {cached:?} and the binary derives {derived:?} from the log \
                         and the fields it cannot carry"
                    ));
                }
            }
        },
    }
    bad
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

// ---------------------------------------------------------------------------
// The seeded batch (the owner's D72, README gap 3533)
// ---------------------------------------------------------------------------

/// **The seeded batch**: the class draw's first [`BATCH_DRAWS`] draws from
/// [`BATCH_SEED`] whose world the shipped binary holds ([`binary_holds`]), each frozen
/// with the fork's answers by value — one line per draw, the class file's own line shape
/// (the world, its provenance, and `forkclass::ANSWERS`), named `batch draw <index>`.
///
/// **Why a batch beside the classes** (D72): the class file holds ONE primary world per
/// class and the worlds derived from them, so a divergence in a world no frozen line
/// holds is found only by a comparison that explores; `planner_invariants`' hash arm
/// explores fresh draws on every run, and R3 deletes the planner it runs. The batch is a
/// fixed sample of what the arms draw — many worlds per class, the generator's own mix
/// of items, walls, routines, logs and widenings — that outlives R3 in plain `cargo test
/// --workspace`; `tm-oracle plan` (`support/forkplan.rs`) keeps the exploring half.
///
/// **It is a property, not a list**: which draws it holds is `binary_holds`' answer
/// (D64(b): a world the binary cannot build is not a comparand), so
/// `planner_classes.rs`' `the_frozen_batch_is_every_draw_the_binary_holds` re-draws
/// every index below [`BATCH_DRAWS`] and demands each held line's world be the draw's own
/// and each missing index be refused, by clause.
pub const FROZEN_BATCH: &str = "fork-4748911-planner-batch.jsonl";

/// The batch's ChaCha seed text (the class draw's convention: its bytes, space-padded
/// to 32; `class_draws`).
pub const BATCH_SEED: &str = "W-39 track H batch, owner D72";

/// How many draws of [`BATCH_SEED`] the batch considers.
pub const BATCH_DRAWS: usize = 128;

/// Where the batch lives.
pub fn batch_path() -> std::path::PathBuf {
    forkday::frozen_path().with_file_name(FROZEN_BATCH)
}

/// The batch's lines, read once, in file order; a draw carried twice FAILS.
pub fn batch_lines() -> &'static Vec<Value> {
    static BATCH: OnceLock<Vec<Value>> = OnceLock::new();
    BATCH.get_or_init(|| {
        let path = batch_path();
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("{}: {e} — see support/forkclass.rs' FROZEN_BATCH", path.display()));
        let mut seen = BTreeSet::new();
        text.lines()
            .filter(|l| !l.trim().is_empty())
            .map(|l| {
                let v: Value = serde_json::from_str(l).expect("a frozen batch line is JSON");
                let d = v["draw"].as_u64().expect("a batch line names its draw");
                assert!(seen.insert(d), "two batch lines for draw {d}");
                v
            })
            .collect()
    })
}

/// **A drawn line** — the class file's line shape (the world and its provenance; the
/// caller writes the answers), named: a batch line `batch draw <index>`, a fresh draw of
/// the oracle arm by its seed.
pub fn drawn_line(name: String, seed: &str, index: usize, draw: &Draw, world: &ClassWorld, class: &str) -> Value {
    json!({
        "name": name, "class": class, "arm": draw.widening.arm(),
        "case": format!("{:?}", draw.case), "seed": seed, "draw": index, "world": world.to_json(),
    })
}

/// **A batch line** — [`drawn_line`] at [`BATCH_SEED`], named by its draw.
pub fn batch_line(index: usize, draw: &Draw, world: &ClassWorld, class: &str) -> Value {
    drawn_line(format!("batch draw {index}"), BATCH_SEED, index, draw, world, class)
}

// ---------------------------------------------------------------------------
// Worlds the shipped binary WROTE (README gaps 3390 and 3398)
// ---------------------------------------------------------------------------

/// **The driven worlds**: a frozen class world, the shipped binary's own verbs run over it,
/// and the world it leaves — frozen with the fork's answers by value, one line per [`DRIVES`]
/// entry (W-39, README gap 3390).
///
/// **Why they are not class lines**: every class line is held to [`binary_holds`] — among its
/// clauses D42's, that the cache is what the binary rebuilds from the log. The world of gap
/// 3390 is `tm arrive` then `tm wake`, and `tm wake` clears `arrival`, `window` and `budget`
/// while the rebuild restores all three from the day's `arrive` (README gap 3398, a host
/// decision no one has taken): the binary WRITES that world with two ordinary verbs, and its
/// own rebuild does not reproduce it. So it cannot be a class line, and freezing it as one would
/// mean weakening clause 5. It is admitted here by the stronger property — the binary wrote it:
/// `planner_classes.rs`' `every_driven_world_is_the_binarys_own_output` re-drives each line from
/// its parent and demands the world byte for byte — and
/// `the_driven_worlds_are_refused_by_binary_holds_only_where_gap_3398_says` pins that clause 5
/// refuses it on exactly those three fields, so when gap 3398 is decided the line says so.
pub const FROZEN_DRIVEN: &str = "fork-4748911-planner-driven.jsonl";

/// **One drive**: the world a verb sequence leaves when the shipped binary runs it over a
/// primary class line's world.
pub struct Drive {
    /// Its name, which its line carries.
    pub name: &'static str,
    /// The primary class line it starts from, by class.
    pub from: &'static str,
    /// The verbs, in order, each with the instant it runs at (`tm --now`).
    pub verbs: &'static [(&'static str, &'static [&'static str])],
    /// The instant the day is planned at.
    pub now: &'static str,
    /// **A gap whose fix another track of the same run owns**, while the kernel still plans
    /// the day otherwise: the comparison then DEMANDS the named difference, and fails, naming
    /// this field, the moment the kernel agrees — so the step that composes the fix deletes it
    /// and the line compares like any other. `None` once composed.
    pub pending: Option<&'static str>,
}

/// **The drives.** Gap 3390's world: `idle/lounge` (woke 06:30, arrived 07:00), `tm wake 06:30`
/// at 07:30 — the day re-opened at the wake it already logged, so the second `wake` line moves
/// no other field (a wake at another time also moves `wake`: README gap 3661) — planned at
/// 10:30: fork `Planner::new` falls back to the day's first logged `arrive` for the
/// arrival the state no longer holds, and plans `07:00–16:00`; the kernel's
/// `Look.Today.planArrivalSec` read `now` at W-39's fork of `rebuild-on-lean`, and reads the
/// logged arrival since track A's fix composed at W-39's land step (README gap 3390 closed,
/// gap 3663's `pending` deleted there): the line compares like any other.
pub const DRIVES: [Drive; 1] = [Drive {
    name: "arrive then wake (gap 3390)",
    from: "idle/lounge",
    verbs: &[("2026-09-07T07:30:00-05:00", &["wake", "06:30", "--slept", "8h"])],
    now: "2026-09-07T10:30:00-05:00",
    pending: None,
}];

/// Where the driven lines live.
pub fn driven_path() -> std::path::PathBuf {
    forkday::frozen_path().with_file_name(FROZEN_DRIVEN)
}

/// The driven lines, read once, in file order.
pub fn driven_lines() -> &'static Vec<Value> {
    static DRIVEN: OnceLock<Vec<Value>> = OnceLock::new();
    DRIVEN.get_or_init(|| {
        let path = driven_path();
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("{}: {e} — see support/forkclass.rs' FROZEN_DRIVEN", path.display()));
        text.lines().filter(|l| !l.trim().is_empty()).map(|l| serde_json::from_str(l).expect("a driven line is JSON")).collect()
    })
}

/// **Run a drive's verbs with the shipped binary over `parent`, and read back the world it
/// leaves** — its documents (the parent's in their order, then any the verbs created, by
/// path), its log and its `.tm/state.json`, planned at the drive's `now`.
pub fn drive(parent: &ClassWorld, d: &Drive) -> Result<ClassWorld, String> {
    let dir = tempfile::TempDir::new().map_err(|e| format!("tempdir: {e}"))?;
    let root = dir.path();
    std::fs::create_dir_all(root.join(".tm")).map_err(|e| e.to_string())?;
    for (p, t) in &parent.docs {
        let f = root.join(p);
        if let Some(up) = f.parent() {
            std::fs::create_dir_all(up).map_err(|e| e.to_string())?;
        }
        std::fs::write(&f, t).map_err(|e| e.to_string())?;
    }
    std::fs::write(root.join(".tm/log.jsonl"), &parent.log).map_err(|e| e.to_string())?;
    let cfg = parent.ratio.as_ref().map(|r| format!("[day]\nbudget_ratio = {r}\n")).unwrap_or_default();
    std::fs::write(root.join("config.toml"), cfg).map_err(|e| e.to_string())?;
    std::fs::write(root.join(".tm/state.json"), serde_json::to_string(&parent.state).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    for (at, args) in d.verbs {
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_tm"))
            .arg("--dir")
            .arg(root)
            .arg("--now")
            .arg(at)
            .args(*args)
            .output()
            .map_err(|e| format!("tm {args:?}: {e}"))?;
        if !out.status.success() {
            return Err(format!("tm {args:?} at {at} exited {:?}: {}", out.status.code(), String::from_utf8_lossy(&out.stderr)));
        }
    }
    let now = DateTime::parse_from_rfc3339(d.now).map_err(|e| format!("{}: {e}", d.now))?.with_timezone(&parent.now.timezone());
    let written: Vec<(String, String)> = planreq::docs_of_dir(root);
    let mut docs: Vec<(String, String)> = parent
        .docs
        .iter()
        .filter_map(|(p, _)| written.iter().find(|(q, _)| q == p).cloned())
        .collect();
    let mut new: Vec<(String, String)> = written.into_iter().filter(|(p, _)| !parent.docs.iter().any(|(q, _)| q == p)).collect();
    new.sort();
    docs.extend(new);
    let log = std::fs::read_to_string(root.join(".tm/log.jsonl")).map_err(|e| e.to_string())?;
    let state: RuntimeState = serde_json::from_str(&std::fs::read_to_string(root.join(".tm/state.json")).map_err(|e| e.to_string())?)
        .map_err(|e| format!(".tm/state.json: {e}"))?;
    Ok(ClassWorld { docs, log, state, now, mult: parent.mult.clone(), ratio: parent.ratio.clone() })
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
    let ratio = (w.cfg.day.budget_ratio != Config::default().day.budget_ratio)
        .then(|| format!("{}", w.cfg.day.budget_ratio));
    ClassWorld { docs: w.docs, log: w.log, state: w.state, now: w.now, mult, ratio }
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

/// **A world as it stood before the housekeeping logged its meetings** (W-37 repair, README
/// gap 3340): the running block's `pause`/`unpause` marks taken out of the log and the block
/// unpaused. Since the generator logs the meetings a block passed, as the binary does, a
/// stored world is AT REST; the D61 tests that watch the binary WRITE the marks start from
/// this one. Only for a world whose timer marks are all D61's (the class worlds draw no typed
/// pause) and whose block nothing else paused.
pub fn before_housekeeping(w: &ClassWorld) -> ClassWorld {
    let mut out = w.clone();
    out.log = w
        .log
        .lines()
        .filter(|l| !l.contains("\"ev\":\"pause\"") && !l.contains("\"ev\":\"unpause\""))
        .map(|l| format!("{l}\n"))
        .collect();
    if let Some(a) = out.state.active.as_mut() {
        a.paused = false;
    }
    out
}

/// **The worlds D61 derives from a stored one** (the owner's D61, W-36 track T;
/// README gap 3123): when a block runs, unpaused, with no break and no
/// interruption, and a wall's blocked span that began AFTER the block started
/// covers `now`, the first verb after the wall began logs `pause{id}` stamped at
/// the span's start and marks the block paused (`tm/src/cli/day.rs`'
/// `stop_the_timer_at_walls`, which since W-37 track T asks the kernel's walls
/// form, `WallTimer.spansOf` merging the spans as the host's helper did) —
/// and, for an earlier span of the same kind that has ended by `now`, its
/// `pause` and its `unpause`, in order, as that loop logs them.
/// So the binary holds that world, not the stored one, from then on. Returned
/// at `now` and again twenty minutes into the meeting (the drive's `tm now` at
/// 13:20), each with the pause's instant, and — since W-38 (README gap 3320) —
/// ten minutes AFTER the meeting, with the `unpause` stamped at its end logged
/// and the block running again (a `running` or `overtime` world, no longer a
/// wall on `now`: the class is the world's, [`class_of`]); empty when the rule
/// does not fire.
pub fn d61_worlds(parent: &ClassWorld) -> Vec<(ClassWorld, DateTime<Tz>)> {
    let b = Built::of(parent.clone());
    let r = running(&b);
    let Some(ob) = r.block else { return Vec::new() };
    let Some(a) = parent.state.active.clone().filter(|a| a.id.as_str() == ob.id) else {
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
    // **A parent already at rest** (W-37 repair, README gap 3340): since the generator
    // logs the meetings a running block passed, as the binary does, a parent whose wall
    // covers `now` already holds that wall's pause and is paused — the world at `now` IS
    // the parent, and only the world twenty minutes into the meeting is derived.
    let at_rest = a.paused && parent.log.contains(&line(lo, Event::Pause { id: id.clone() }));
    if a.paused && !at_rest {
        return Vec::new();
    }
    let mut paused = parent.clone();
    if !at_rest {
        for (l, h) in merged.iter().copied().filter(|(l, _)| *l > started && *l <= now) {
            paused.log.push_str(&line(l, Event::Pause { id: id.clone() }));
            if h <= now {
                paused.log.push_str(&line(h, Event::Unpause { id: id.clone() }));
            }
        }
    }
    if let Some(x) = paused.state.active.as_mut() {
        x.paused = true;
    }
    let mid = (lo + Duration::minutes(20)).min(hi - Duration::minutes(1));
    let mut out = [now, mid]
        .into_iter()
        .filter(|at| !(at_rest && *at == now))
        .filter(|at| *at >= now && *at < hi)
        .fold(Vec::new(), |mut out: Vec<(ClassWorld, DateTime<Tz>)>, at| {
            if out.iter().all(|(w, _)| w.now != at) {
                let mut w = paused.clone();
                w.now = at;
                out.push((w, lo));
            }
            out
        });
    // **And AFTER the meeting** (W-38, README gap 3320): ten minutes past its end, where the
    // first verb after the wall logs the `unpause` stamped at the end and the block runs
    // again — the world whose log holds a CLOSED pause, the one shape P56 draws differently
    // from fork 4748911 (the pause over the wall is not drawn; the fork drew it as a `paused`
    // Lost row beside the wall). Only where nothing else happens between the meeting and
    // that instant: no later wall begins by then, and the day has not ended.
    let after = hi + Duration::minutes(10);
    let (_, day_end) = b.day_bounds();
    let next_wall = merged.iter().any(|(l, _)| *l > hi && *l <= after);
    if after < day_end && !next_wall {
        let mut w = paused.clone();
        w.log.push_str(&line(hi, Event::Unpause { id: id.clone() }));
        if let Some(x) = w.state.active.as_mut() {
            x.paused = false;
        }
        w.now = after;
        out.push((w, lo));
    }
    out
}

// ---------------------------------------------------------------------------
// The dated window task's worlds (README gap 3200)
// ---------------------------------------------------------------------------

/// **The world a stored one becomes with a dated window task** (W-38, README gap
/// 3200): `plangen::with_window_task` — `plan-basic`'s `^a3` under `# Untied` in
/// `backlog.md` — and nothing else. A window task is no wall, no block, no break
/// and no interruption, so the world keeps its class and its `.tm/state.json`
/// (`tm arrive`'s window is computed over the walls alone), which
/// `planner_classes.rs`' `the_frozen_window_worlds_are_every_one_the_task_derives`
/// asserts line by line. Derived from EVERY primary line: the mark is a function
/// of the day's routines and §7's answer, and both move with every coordinate of
/// the class.
pub fn window_worlds(parent: &ClassWorld) -> Vec<ClassWorld> {
    let mut w = parent.clone();
    if plangen::with_window_task(&mut w.docs) {
        vec![w]
    } else {
        Vec::new()
    }
}

// ---------------------------------------------------------------------------
// The host's worked minutes: a break logged inside the running block (README gap 3282)
// ---------------------------------------------------------------------------

/// Where [`worked_worlds`] logs its break: five minutes into the running block, for ten.
pub const INNER_BREAK: (i64, u32) = (5, 10);

/// **The world a stored one becomes when a ten-minute break was taken inside its running
/// block** (W-38, README gap 3282; parity P55): `tm break 10m` five minutes after the block
/// began and `tm break` again ten minutes later (`plangen::inner_break_line`), so the
/// block runs unpaused, `.tm/state.json` is as it was, and the log gains one `break` line
/// — which the log's reading of the block's worked minutes counts as worked and the host's
/// (`Replay::active_worked_min`, what R3's request carries) nets out. Derived where that is
/// the whole story: a block running unpaused with no break or interruption, whose `start`
/// is the log's last line (so the break's line, written when it ended, is appended), and
/// whose break ends a minute or more before `now`. Its class is the parent's: the class
/// reads the fork's reading, which the break does not move.
pub fn worked_worlds(parent: &ClassWorld) -> Vec<ClassWorld> {
    let b = Built::of(parent.clone());
    let r = running(&b);
    let (Some(ob), None, None) = (r.block, r.brk, r.interrupt) else { return Vec::new() };
    let Some(a) = parent.state.active.as_ref().filter(|a| a.id.as_str() == ob.id && !a.paused) else {
        return Vec::new();
    };
    let last = parent.log.lines().last().unwrap_or_default();
    if !(last.contains("\"ev\":\"start\"") && last.contains(&format!("\"id\":\"{}\"", a.id.as_str()))) {
        return Vec::new();
    }
    let started = local_dt(b.cfg.tz, b.date(), a.started);
    let t = started + Duration::minutes(INNER_BREAK.0);
    if t + Duration::minutes(i64::from(INNER_BREAK.1) + 1) > parent.now {
        return Vec::new();
    }
    let mut w = parent.clone();
    w.log.push_str(&plangen::inner_break_line(t, INNER_BREAK.1));
    vec![w]
}

// ---------------------------------------------------------------------------
// A running break carried past `break_min` (README gaps 3207 and 3480)
// ---------------------------------------------------------------------------

/// How far [`overrun_worlds`] carries a running break past the later of its planned end and
/// `break_min`, in minutes. Measured (README gap 3480): at one, five and fifteen minutes past,
/// `break/late`'s break — begun inside a wall, so it ends where no free stretch begins — is a
/// rest the kernel's cut does not count, where the comparand's logged break resets the fork's
/// counter; at thirty the break reaches the stretch and the two agree on every break world.
pub const OVERRUN_PAST: i64 = 30;

/// **The world a stored one becomes when its running break has run long enough to reset the
/// cut's break counter** (W-38, README gaps 3207 and 3480; parity P45): `now` carried to
/// [`OVERRUN_PAST`] minutes past the later of the break's planned end and `break_min`, and
/// nothing else — the break still runs, overrun, and P45's comparand logs it, since the fork
/// resets its counter at a logged break. No stored break day held such a break (each was
/// shorter than `break_min`, or its counter was already zero), so until W-38's mutation run
/// found it the comparand's reset clause changed no row. Derived from every PRIMARY world with
/// a running break whose carried instant is after the stored `now` and inside the day. Its
/// class is the parent's: the class reads the run state, which carrying `now` does not move.
pub fn overrun_worlds(parent: &ClassWorld) -> Vec<ClassWorld> {
    let b = Built::of(parent.clone());
    let Some((started, planned)) = parent.state.break_.as_ref().and_then(|x| x.started.map(|s| (s, x.planned_min))) else {
        return Vec::new();
    };
    let t = local_dt(b.cfg.tz, b.date(), started);
    let now = t + Duration::minutes(i64::from(planned.max(b.cfg.day.break_min)) + OVERRUN_PAST);
    let (_, day_end) = b.day_bounds();
    if now <= parent.now || now >= day_end {
        return Vec::new();
    }
    let mut w = parent.clone();
    w.now = now;
    vec![w]
}

// ---------------------------------------------------------------------------
// A TYPED pause over a meeting (README gap 3473)
// ---------------------------------------------------------------------------

/// How much wider than the meeting [`typed_worlds`]' pause is, at each end, in minutes — the
/// P56 arm's typed widening (`plangen::timer_marks`' ten minutes).
pub const TYPED_WIDER: i64 = 10;

/// **The world after a meeting, with the pause TYPED ten minutes wider than the meeting at
/// each end** (W-39, README gap 3473; parity P56) — derived from every world D61 derives
/// AFTER a meeting ([`d61_worlds`]: the running block's pause stamped at the wall's start and
/// its unpause at its end): the user typed `tm pause` [`TYPED_WIDER`] minutes before the
/// meeting and `tm pause` again as long after it, so the log holds that pause and unpause in
/// place of the wall's, and the binary's housekeeping writes nothing for the wall (the timer
/// was already stopped when it began, `plangen::timer_marks`' rule and the kernel's
/// `WallTimer`); planned [`TYPED_WIDER`] minutes after the typed unpause, as D61's world is
/// after the meeting. The pause is longer than the wall on both sides, so P56's cut leaves it
/// in two pieces — the shape the P56 arm's typed half compared live, and no frozen line held.
/// Only where the typed pause begins after the block started and nothing else is logged
/// after the meeting's pause. Its class is the world's own ([`class_of`]).
pub fn typed_worlds(parent: &ClassWorld) -> Vec<ClassWorld> {
    let wider = Duration::minutes(TYPED_WIDER);
    let mut out = Vec::new();
    for (w, lo) in d61_worlds(parent) {
        let Some(a) = w.state.active.as_ref().filter(|a| !a.paused) else { continue };
        let b = Built::of(w.clone());
        let tz = b.cfg.tz;
        let started = local_dt(tz, b.date(), a.started);
        let id = a.id.as_str().to_string();
        let line = |t: DateTime<Tz>, ev: Event| {
            LogEntry::new(t.fixed_offset(), ev).to_json().expect("a timer entry serialises") + "\n"
        };
        // The meeting's pause and its unpause, the log's last two lines (D61's world after it).
        let Some(hi) = w.log.lines().last().and_then(|l| serde_json::from_str::<Value>(l).ok()).and_then(|e| {
            (e["ev"] == "unpause" && e["id"] == id.as_str())
                .then(|| e["t"].as_str().and_then(|t| DateTime::parse_from_rfc3339(t).ok()))
                .flatten()
        }) else {
            continue;
        };
        let hi = hi.with_timezone(&tz);
        let pair = format!("{}{}", line(lo, Event::Pause { id: id.clone() }), line(hi, Event::Unpause { id: id.clone() }));
        let Some(before) = w.log.strip_suffix(pair.as_str()) else { continue };
        let now = hi + wider + wider;
        let (_, day_end) = b.day_bounds();
        let next_wall = b.walls().iter().any(|(_, l, _, _)| *l > hi && *l <= now);
        if lo - wider <= started || now >= day_end || next_wall {
            continue;
        }
        let mut t = w.clone();
        t.log = format!("{before}{}{}", line(lo - wider, Event::Pause { id: id.clone() }), line(hi + wider, Event::Unpause { id }));
        t.now = now;
        out.push(t);
    }
    out
}

// ---------------------------------------------------------------------------
// README gap 3281's order, on a frozen line (gaps 3474 and 3529)
// ---------------------------------------------------------------------------

/// **An interruption begun at a calendar wall's start, over the block it names** (W-39,
/// README gaps 3474 and 3529) — the shape on which fork `collect_walls` and the kernel
/// before W-38 track R drew step 1's rows in different orders. The fork pushes §9's running
/// interruption as an ad-hoc wall keyed `(blocked start, id)` — the id the block it paused
/// — and sorts: where a calendar wall begins at the same minute and its id sorts first (a
/// generated wall's `w..` before a generated item's `z..`), the fork draws `[wall, lost]`,
/// and the kernel before `Planner.stepOneOrder` drew `[lost, wall]`. The frozen lines holding
/// a Lost and a Wall row at one start before W-39 (`interrupted-block/spent` and its `window`
/// twin) hold them in the order both kernels draw (gap 3529). `Some(start)` when the world
/// logs an OPEN interruption naming the running block, stamped at a calendar wall's blocked
/// start, and that wall's id sorts before the block's.
pub fn an_interruption_begins_at_a_wall(b: &Built) -> Option<DateTime<Tz>> {
    let r = running(b);
    let (Some(i), Some(ob)) = (r.interrupt, r.block) else { return None };
    let named = i.id.as_deref().filter(|id| *id == ob.id)?;
    let at = i.start?.with_timezone(&b.cfg.tz);
    b.walls().iter().find(|(id, lo, _, _)| *lo == at && id.as_str() < named).map(|(_, lo, _, _)| *lo)
}

/// **The world an interruption begun at a wall's start holds at that wall's END** (W-39,
/// README gaps 3474 and 3529) — derived from every primary world
/// [`an_interruption_begins_at_a_wall`] answers for: `now` carried to the end of the wall
/// the interruption began with, so the interruption's Lost row, which runs to `now`, and the
/// Wall row tie on `(start, end)` and only step 1's walk orders them. There fork
/// `collect_walls` sorts the wall first (its id before the block's) and the kernel before
/// W-38 track R's `Planner.stepOneOrder` drew the Lost row first — the direction no frozen
/// line held (gap 3529: the lines with both rows at one start end them apart, so the final
/// `(start, end)` sort decided). Nothing else moves: the interruption still runs and the
/// block stays paused under it, so no timer mark is owed. Its class is the parent's.
pub fn order_worlds(parent: &ClassWorld) -> Vec<ClassWorld> {
    let b = Built::of(parent.clone());
    let Some(lo) = an_interruption_begins_at_a_wall(&b) else { return Vec::new() };
    let named = running(&b).interrupt.and_then(|i| i.id.clone()).unwrap_or_default();
    let Some(hi) = b.walls().iter().filter(|(id, l, _, _)| *l == lo && id.as_str() < named.as_str()).map(|(_, _, h, _)| *h).min() else {
        return Vec::new();
    };
    let (_, day_end) = b.day_bounds();
    if hi <= parent.now || hi >= day_end {
        return Vec::new();
    }
    let mut w = parent.clone();
    w.now = hi;
    vec![w]
}

// ---------------------------------------------------------------------------
// The owner's D64: the rule a re-bless is held to (README gap 3133)
// ---------------------------------------------------------------------------

/// The keys of a frozen line that are the fork's answers — what a re-bless
/// recomputes. Everything else on the line is the world and its provenance.
///
/// **W-38 adds four, each an object named by the parity number it holds**, present
/// only on a line the number's rule departs on (as `shipped` is present only where
/// the comparand departs): `p45` (the running break: the fork's day after the
/// break's end, planned where P45 restarts the cut), `p52` (the grown facts
/// re-rank the what-if; its `diff` is `whatif.grown`), `p55` (the host's worked
/// minutes move the day) and `p56` (a meeting's pause drawn as the wall alone;
/// `shipped` is fork 4748911's drawing). A line no such rule departs on carries
/// none of them, so the 41 lines frozen before W-38 did not change by carrying
/// the new list.
pub const ANSWERS: [&str; 9] = ["day", "shipped", "d57", "d60", "whatif", "p45", "p52", "p55", "p56"];

/// **The answers every line carries, `null` where there is none** — the five a
/// line has carried since W-36. The rest of [`ANSWERS`] are present only where
/// their rule departs.
pub const ALWAYS: [&str; 5] = ["day", "shipped", "d57", "d60", "whatif"];

/// **Write one answer onto a line**: an answer of [`ALWAYS`] is written as it is,
/// `null` included; any other is written when it is not `null` and REMOVED when
/// it is, so a line no W-38 rule departs on keeps its bytes (a `null` key would
/// read as absent everywhere and still change every line of the file).
pub fn set_answer(line: &mut Value, key: &str, v: Value) {
    if v.is_null() && !ALWAYS.contains(&key) {
        if let Some(o) = line.as_object_mut() {
            o.remove(key);
        }
    } else {
        line[key] = v;
    }
}

/// **The parity flags a line carries**: every key spelled `p<n>` with a boolean
/// value, in any object the line carries beside the world and the days — the
/// comparand's own flags are named by their parity number (`d57.p46`,
/// `d57.p47`, `d60.p51`), so the flag IS the number. `(n, set)`.
pub fn parity_flags(line: &Value) -> Vec<(u32, bool)> {
    flag_homes(line).into_iter().map(|(n, set, _)| (n, set)).collect()
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
/// the line with the fork's answers recomputed; `shipped_day` the shipped
/// fork's day recomputed live; `because` the parity numbers the re-bless was
/// run for (`TM_PLANNER_BLESS_BECAUSE`); `registered` the register's numbers.
/// `Ok` names what changed (empty when nothing did); `Err` says why a change is
/// NOT allowed.
///
/// * A line whose answers were cleared (a world re-drawn under D64(b), or a
///   derived D61 world added) takes whatever the fork answers — the re-draw
///   is where D64(b)'s reason was demanded.
/// * Otherwise D64(a): **a registered parity number changes the fork's day on
///   that line**, and since the W-37 repair (README gap 3331) the gate checks
///   that the NUMBER is what changed it, not only that the line carries its
///   flag. Three clauses, each a property of the line:
///   1. **The flag is the OLD line's.** Until the repair the flag set was the
///      union of the old and new lines' flags, so an unflagged line whose
///      recomputed answer SET a flag licensed its own change (driven by the
///      W-37 auditor: `idle/lounge` with `d60.p51` set by the new answer).
///   2. **The shipped fork's day did not move, by value.** Every comparand
///      parity number is a departure the comparand makes FROM the shipped
///      fork; none moves the shipped fork itself. So the live shipped day must
///      equal the old line's (its `shipped` when the comparand departed, else
///      its `day`). A change to the fork, to the kernel's ranking it is handed,
///      or to anything else under both — the W-37 critic's case, T's edit of
///      the in-tree fork's `past_segments` — moves the shipped day and is
///      refused whatever number is named.
///   3. **Each changed answer is one the named number governs**: the object
///      that carries its flag (`d57` for P46/P47, `d60` for P51 — the flag
///      lives where it governs, so this is read off the line, never listed)
///      and the comparand-derived `day` and `whatif`. `shipped` is governed by
///      no comparand number (clause 2).
///
///   With the shipped day fixed by value, what is left to change is the
///   comparand's departure from it, which `fork_answers` computes as the named
///   numbers' transformations of the shipped fork's inputs — so the change is
///   the number's. The one thing this cannot see is an edit to a governed
///   transformation's OWN code that is not that parity rule (README gap 3331,
///   residue): that is a code change, reviewed in its diff.
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
    // **Introduction** (W-38, README gap 3470): D64(a) for a number whose rule the
    // comparand did not compute when this line was frozen. Clause 1 reads the COMMITTED
    // line's flags, so a number that line carries no flag of could never license anything
    // on it — the owner's D64(a) ("a registered parity number that changes the fork's day on
    // the line") could not reach a line frozen before the number's comparand existed. An
    // introduction may only ADD: every changed answer is a key the committed line does not
    // carry, each one the home of a SET flag of a number the re-bless names and the
    // committed line carries NO flag of (not even `false` — flipping a flag the line holds
    // is clause 1's case, and it stays refused); nothing the committed line carries moves,
    // so no frozen value can be bent to meet the kernel; and clause 2 still holds the
    // shipped fork's day by value.
    let old_numbers: BTreeSet<u32> = parity_flags(old).into_iter().map(|f| f.0).collect();
    let new_homes = flag_homes(new);
    let introduced = changed.iter().all(|k| {
        old[k.as_str()].is_null()
            && new_homes
                .iter()
                .any(|(n, set, home)| home == k && *set && because.contains(n) && !old_numbers.contains(n))
    });
    if introduced {
        let old_shipped = if old["shipped"].is_null() { &old["day"]["day"] } else { &old["shipped"]["day"] };
        if old_shipped != shipped_day {
            return Err(format!(
                "{who}: the SHIPPED fork's day moved, and an introduced number does not move it either"
            ));
        }
        return Ok(changed);
    }
    // Clause 1: the OLD line's flags, and only the numbers the re-bless names.
    let named: Vec<(u32, String)> = flag_homes(old)
        .into_iter()
        .filter(|(n, set, _)| *set && because.contains(n))
        .map(|(n, _, home)| (n, home))
        .collect();
    if named.is_empty() {
        let set: BTreeSet<u32> = parity_flags(old).into_iter().filter(|f| f.1).map(|f| f.0).collect();
        return Err(if because.is_empty() {
            format!(
                "{who}: `{}` changed and the re-bless names no reason — the owner's D64 allows (a) a registered parity \
                 number that changes the fork's day on the line, or (b) a world the binary cannot build, re-drawn with its reason",
                changed.join("`, `")
            )
        } else {
            format!(
                "{who}: `{}` changed and the committed line carries no flag of P{} — the parity numbers set on it are {set:?} \
                 (a flag the recomputed answer sets licenses nothing)",
                changed.join("`, `"),
                because.iter().map(u32::to_string).collect::<Vec<_>>().join(", P")
            )
        });
    }
    // Clause 2: the shipped fork's day, by value.
    let old_shipped = if old["shipped"].is_null() { &old["day"]["day"] } else { &old["shipped"]["day"] };
    if old_shipped != shipped_day {
        return Err(format!(
            "{who}: the SHIPPED fork's day moved, and no comparand parity number moves it — a change to the fork, \
             or to the ranking it is handed, is not D64(a)"
        ));
    }
    // Clause 3: every changed answer is one a named number governs.
    for k in &changed {
        let governed = matches!(k.as_str(), "day" | "whatif") || named.iter().any(|(_, home)| home == k);
        if !governed {
            return Err(format!(
                "{who}: `{k}` changed, which P{} does not govern (a number governs the object its flag lives in, `day` \
                 and `whatif`)",
                named.iter().map(|(n, _)| n.to_string()).collect::<Vec<_>>().join(", P")
            ));
        }
    }
    Ok(changed)
}

/// **Each parity flag a line carries, with the object it lives in** —
/// [`parity_flags`]' reading, keeping where the flag was found: `(n, set,
/// home)`, `d57.p46` read as `(46, …, "d57")`. The home is what the number
/// governs ([`d64_allows`]' clause 3).
pub fn flag_homes(line: &Value) -> Vec<(u32, bool, String)> {
    let mut out = Vec::new();
    for (k, v) in line.as_object().into_iter().flatten() {
        if matches!(k.as_str(), "world" | "day" | "shipped" | "whatif") {
            continue;
        }
        for (f, set) in v.as_object().into_iter().flatten() {
            let n = f.strip_prefix('p').and_then(|d| d.parse::<u32>().ok()).filter(|_| f[1..].bytes().all(|c| c.is_ascii_digit()));
            if let (Some(n), Some(set)) = (n, set.as_bool()) {
                out.push((n, set, k.clone()));
            }
        }
    }
    out
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
            // An impossible answer with NO `until` is not an impossible tie: the kernel's
            // `Planner.Ranked.imp` is `(answerUntil x.out).map …`, `none` when the answer has
            // neither a floor nor a grant, and such an answer keys as every other (README gap
            // 3337 — this read it as `(0, 0)`, first of all, until the W-37 repair).
            match prios.iter().find(|p| p.id == c.id).filter(|p| is_impossible_tie(p)).and_then(|p| p.until) {
                Some(u) if !c.is_wall => {
                    let until = usize::try_from(chrono::Datelike::num_days_from_ce(&u)).unwrap_or(0);
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
/// max(min(t + planned, day end), now))` — the one Break row that starts
/// before that end — open exactly when it has overrun, carrying its place; no
/// row §8.2 PLACES from `now` on — a Block, Batch, Routine, Optional or Rest —
/// overlaps it; and **every §8.2 step-5 row from `now` on starts at or after its
/// end** (README gap 2925: the cut restarts there). Every OTHER Break row of the
/// day starts at or after that end: since W-37 (README gap 551 closed) the
/// kernel draws the cut's kept breaks, which the cut places after the running
/// break, and a second Break row before its end still fails. Returns the row's
/// span and whether it is open; `Err` names what failed, so the perturbation
/// test can show the rule bites.
pub fn p45_rule(
    day: &DayPlan,
    t: DateTime<Tz>,
    planned: u32,
    place: Option<&str>,
    now: DateTime<Tz>,
    day_span: (DateTime<Tz>, DateTime<Tz>),
) -> Result<(DateTime<Tz>, DateTime<Tz>, bool), String> {
    let end = t + Duration::minutes(i64::from(planned));
    let (lo, hi) = (t.max(day_span.0), end.min(day_span.1).max(now));
    let brks: Vec<_> = day.segments.iter().filter(|s| s.kind == SegKind::Break && s.start < hi).collect();
    if brks.len() != 1 {
        return Err(format!("{} Break rows before {hi}, want the running break's one", brks.len()));
    }
    let b = brks[0];
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
    /// What-ifs whose comparand is the fork's what-if ranked as the kernel ranks
    /// the GROWN request (parity P52: the grown facts re-rank the day, and the
    /// kernel departs from the shipped TUI's `diff`), since W-38.
    pub p52: usize,
    /// Open rows compared on a break day (P45 pauses the block at the break's
    /// start; P55 its `so far` is the host's minutes), since W-38 — and of those
    /// days, the ones whose host reading differs from the log's (P55 bites).
    pub p45_open: usize,
    pub p45_host: usize,
    /// Rows compared after the running break against P45's comparand (`p45`),
    /// of them kept Break rows (README gap 3207), since W-38.
    pub p45_after: usize,
    pub p45_kept: usize,
    /// Lines whose comparand reads the host's worked minutes (P55) or draws a
    /// meeting's pause as the wall alone against fork 4748911's drawing (P56).
    pub p55: usize,
    pub p56: usize,
}

impl ClassTally {
    /// One line: what was compared and what was not.
    pub fn line(&self, findings: usize) -> String {
        format!(
            "frozen fork classes — {} class(es); {}; P45 days {} against the rule (running {}, overrun {}; \
             the shipped fork scheduled over the break on {}; {} values by value); P46 comparand days {}, \
             P47 {}, P51 {}; under-used notes the renderer derived as the fork wrote them {}; what-ifs {} ({} \
             parity-P44 days, {} ids; asked with the host's grown facts, {} parity-P52); break-day open rows \
             {} (the host's minutes departing from the log's on {}); rows after a running break against P45's \
             comparand {} ({} kept breaks); P55 comparand days {}, P56 {}; {findings} difference(s) in all",
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
            self.p52,
            self.p45_open,
            self.p45_host,
            self.p45_after,
            self.p45_kept,
            self.p55,
            self.p56,
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

/// **The running block's worked minutes as the binary reads them** — the host's
/// ONE reading, `Replay::active_worked_min` (`tm/src/cli/day.rs`' `worked_min`,
/// which `tm now` prints, `tm done` logs and the TUI's timer shows): the wall
/// clock since `started` net of the day's pauses, interruptions and breaks, the
/// break `.tm/state.json` still holds running included. It is what R3's
/// `planner` section carries as `state.active.workedMin` (README gap 3043,
/// parity P55) and what [`kernel_answer_with_grants`] sends since W-38.
pub fn host_worked(b: &Built) -> Option<u32> {
    let st = &b.world.state;
    let a = st.active.as_ref()?;
    let tz = b.cfg.tz;
    let started = local_dt(tz, b.date(), a.started);
    let running_break = st
        .break_
        .as_ref()
        .and_then(|x| x.started)
        .map(|s| local_dt(tz, b.date(), s).fixed_offset());
    Some(b.replay.active_worked_min(b.date(), started.fixed_offset(), b.world.now.fixed_offset(), running_break))
}

/// **§9.1's what-if as R3's host will ask it** (owner D58): one block on the
/// running item, with that candidate's facts grown as fork
/// `PlanOverrides::apply` grows them (`planwire::grown`, the host's one reading;
/// `None` when the extension grows nothing).
pub fn whatif_json(b: &Built) -> Option<Value> {
    whatif_item(&b.world.state).map(|id| {
        let grown = b
            .cands
            .iter()
            .find(|c| c.id == *id)
            .and_then(|c| planwire::grown(c, None, b.cfg.block_min(), &b.cfg));
        planwire::overtime_json(id, 1, grown.as_ref())
    })
}

/// **The kernel's answer for a world, asked as the binary will ask it at R3**,
/// and the grants it ranked by: the day, and on a day [`whatif_item`] names a
/// block for, §9.1's what-if for one block on it.
///
/// **Since W-38 (README gap 3282) the request carries what R3's host sends and
/// the region's arms sent alone**: the what-if's GROWN candidate facts
/// ([`whatif_json`], D58 — until W-38 only `planner_invariants`' grown arm sent
/// them, so the frozen what-ifs held the kernel to the estimate's `diff` on a
/// parity-P44 day), and `state.active.workedMin` ([`host_worked`],
/// `planwire::add_worked_min`'s first caller outside a fork region — README gap
/// 3043's key). Measured on the 41 lines frozen before W-38: the what-if moves
/// on the one P44 day and on no other, to the shipped TUI's own `diff`; the
/// worked minutes move the open row's `so far` on the three running-break days
/// and nothing else — so no frozen answer changes, and [`compare_line`] holds
/// the kernel to the shipped TUI's what-if (`whatif.full`) and, on a break day,
/// the open row to the host's minutes.
pub fn kernel_answer_with_grants(b: &Built) -> Result<(KernelDay, Vec<priority::Prio>), String> {
    let pw = b.request_world();
    let (mut req, order) = planreq::request(&pw, whatif_json(b));
    if let Some(worked) = host_worked(b) {
        planwire::add_worked_min(&mut req["planner"], worked);
    }
    let resp = planreq::call(&req);
    planreq::kernel_day_of(&resp, &pw, &order).map(|(k, ans)| (k, ans.prios))
}

/// [`kernel_answer_with_grants`]' day alone.
pub fn kernel_answer(b: &Built) -> Result<KernelDay, String> {
    kernel_answer_with_grants(b).map(|(k, _)| k)
}

/// **Compare one frozen class line with the kernel's answer**, by value.
/// Returns every difference outside the declared classes, by name.
pub fn compare_line(line: &Value, t: &mut ClassTally) -> Vec<String> {
    let tz = Config::default().tz;
    let class_key = line["class"].as_str().unwrap_or("<no class>").to_string();
    // A finding names the LINE: a secondary line files under its class and carries its kind
    // (`idle/lounge (window)`), so a failure says which of a class's lines it is (W-38).
    // A batch line names itself by its draw (W-39, `batch draw 17 (running/lounge)`).
    let key = match line["name"].as_str() {
        Some(n) => format!("{n} ({class_key})"),
        None => format!("{class_key}{}", line["secondary"].as_str().map(|s| format!(" ({s})")).unwrap_or_default()),
    };
    let mut findings = Vec::new();
    let world = match ClassWorld::of_json(&line["world"], tz) {
        Ok(w) => w,
        Err(e) => return vec![format!("{key}: {e}")],
    };
    let b = Built::of(world);
    let class = class_of(&b).key();
    if class != class_key {
        findings.push(format!("{key}: the stored world classifies as `{class}` — a line may not choose its class"));
    }
    t.classes.insert(class_key.clone());
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
        // **The open row, by value** (W-38, README gap 3282): what `planner_invariants`' W-35
        // arm compared on a break day and the frozen comparand did not — the fork's open row
        // for the block the log holds open, PAUSED at the break's start as P45 pauses it (no
        // `▶`, clipped at the first break start after its own), and since the request carries
        // the host's worked minutes its `so far` is the host's reading (P55). Both rules are
        // applied to the frozen fork row by their property, never copied from the kernel's.
        let host = host_worked(&b);
        let (kopen, fopen) = (p45_open_rows(&kv), p45_open_rows(&fork["day"]));
        let want: Vec<Value> = fopen.into_iter().map(|r| p45_paused_row(r, started, host)).collect();
        t.p45_open += want.len();
        t.p45_host += usize::from(!want.is_empty() && host != b.worked());
        if kopen != want {
            findings.push(format!(
                "{key}: the open row on a break day is not the fork's paused at the break (P45) with the host's \
                 minutes (P55): kernel {} fork {}",
                Value::Array(kopen),
                Value::Array(want)
            ));
        }
        // **P45's comparand after the break, by value** (W-38, README gap 3207): every row the
        // kernel draws from where P45 restarts the cut — its step-5 assignment, its rests and
        // its KEPT BREAKS — against the fork's own day planned there (`p45`: the fork's own
        // `kept_breaks` over its own assignment), with the one declared row class (an
        // under-used row's note, left to the renderer) and nothing else.
        if let Some(p) = line.get("p45").filter(|v| !v.is_null()) {
            let from = p["from"].as_str().and_then(|x| DateTime::parse_from_rfc3339(x).ok());
            let at = |v: &Value| DateTime::parse_from_rfc3339(v.as_str().unwrap_or_default()).ok();
            let krows: Vec<Value> = kv["segments"]
                .as_array()
                .map(Vec::as_slice)
                .unwrap_or_default()
                .iter()
                .filter(|s| from.is_some_and(|f| at(&s["start"]).is_some_and(|a| a >= f)))
                .cloned()
                .collect();
            let want: Vec<Value> = p["rows"]
                .as_array()
                .map(Vec::as_slice)
                .unwrap_or_default()
                .iter()
                .map(|r| forkday::underused_note_left_to_the_renderer(r, &krows).unwrap_or_else(|| r.clone()))
                .collect();
            t.p45_after += want.len();
            t.p45_kept += want.iter().filter(|r| r["kind"] == "break").count();
            if krows != want {
                let first = krows.iter().zip(&want).position(|(a, z)| a != z).unwrap_or(krows.len().min(want.len()));
                findings.push(format!(
                    "{key}: after the running break (P45, from {}) the rows differ at {first} (fork {} rows, kernel {}):\n      \
                     fork   {}\n      kernel {}",
                    p["from"],
                    want.len(),
                    krows.len(),
                    want.get(first).map_or("—".to_string(), Value::to_string),
                    krows.get(first).map_or("—".to_string(), Value::to_string),
                ));
            }
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
        t.p55 += usize::from(line["p55"]["p55"] == true);
        t.p56 += usize::from(line["p56"]["p56"] == true);
    }
    // **P56 departs where its rule says, and only there** (W-38, README gap 3320): on a P56
    // line fork 4748911's day (`shipped`) draws a replayed pause as a `paused` Lost row a
    // Wall row of the day overlaps — the meeting the pause is — and the kernel's day draws
    // no such row (the part a wall covers is not drawn). Read off the two days, so the flag
    // cannot be set on a line where nothing was cut.
    if line["p56"]["p56"] == true {
        let paused_under_a_wall = |day: &Value| -> usize {
            let rows = day["segments"].as_array().map(Vec::as_slice).unwrap_or_default();
            let at = |v: &Value| DateTime::parse_from_rfc3339(v.as_str().unwrap_or_default()).ok();
            rows.iter()
                .filter(|r| r["kind"] == "lost" && r["flags"]["note"] == "paused")
                .filter(|r| {
                    rows.iter().any(|w| {
                        w["kind"] == "wall"
                            && at(&w["start"]) < at(&r["end"])
                            && at(&r["start"]) < at(&w["end"])
                    })
                })
                .count()
        };
        let kv = serde_json::to_value(&k.day).expect("the kernel's day serialises");
        let (shipped, kernel) = (paused_under_a_wall(&line["shipped"]["day"]), paused_under_a_wall(&kv));
        if shipped == 0 || kernel != 0 {
            findings.push(format!(
                "{key}: a P56 line whose shipped day draws {shipped} paused row(s) under a wall and the kernel's {kernel}"
            ));
        }
    }
    // §9.1's what-if, on a day with a running block.
    // **Since W-38 the request carries the host's GROWN facts** ([`whatif_json`], D58), so the
    // kernel is held to the shipped TUI's what-if (`full`: the estimate grown AND
    // `PlanOverrides::extending`) on every day — parity P44's class, the days the fork's
    // `apply` moved its own what-if beyond the estimate's (`full ≠ est`), is still counted, and
    // on it too the kernel must answer `full`: no P44 day is an exception any more. Until W-38
    // the request sent no grown facts and the kernel was held to `est` there. A line whose
    // grown facts re-rank the day carries `grown` — the fork's
    // full what-if ranked as the kernel ranks the grown request — and is held to it (parity
    // P52, `grown.p52`).
    match (&k.overtime, line.get("whatif").filter(|v| !v.is_null())) {
        (Some(kd), Some(w)) => {
            let kv = serde_json::to_value(kd).expect("a diff serialises");
            let p52 = !w["grown"].is_null();
            let want = if p52 { &w["grown"] } else { &w["full"] };
            t.whatifs += 1;
            t.p44 += usize::from(w["full"] != w["est"]);
            t.p52 += usize::from(p52);
            t.whatif_ids += kd.removed.len() + kd.added.len() + kd.moved.len();
            if &kv != want {
                findings.push(format!(
                    "{key}: the overtime what-if differs from the {}: kernel {kv} fork {want}",
                    if p52 { "fork's ranked as the kernel ranks the grown request (a parity-P52 day)" } else { "shipped TUI's" }
                ));
            }
        }
        (None, None) => {}
        (Some(_), None) => findings.push(format!("{key}: the kernel answered a what-if no frozen line holds")),
        (None, Some(_)) => findings.push(format!("{key}: a frozen what-if the kernel did not answer")),
    }
    findings
}

/// The open Block rows of a serialised day — the rows fork `open_block_segment`
/// and the kernel's `Planner.openBlockRows` draw for the block the log holds open.
pub fn p45_open_rows(day: &Value) -> Vec<Value> {
    day["segments"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default()
        .iter()
        .filter(|s| s["kind"] == "block" && s["flags"]["open"] == true)
        .cloned()
        .collect()
}

/// **P45 and P55 on a fork open row, by their properties**: `tm break` pauses the
/// block, so the row loses its `▶` and ends at the break's start when that falls
/// inside it (`planner_invariants`' `w35_pause_open_rows`); its `so far` is the
/// host's worked minutes (`w36_fork_plan`'s note).
pub fn p45_paused_row(mut row: Value, brk: DateTime<Tz>, host: Option<u32>) -> Value {
    let at = |v: &Value| DateTime::parse_from_rfc3339(v.as_str().unwrap_or_default()).ok();
    let t = brk.fixed_offset();
    if at(&row["start"]).is_some_and(|a| t > a) && at(&row["end"]).is_some_and(|z| t < z) {
        row["end"] = serde_json::to_value(brk).expect("an instant serialises");
    }
    row["flags"]["current"] = Value::Bool(false);
    if let Some(h) = host {
        row["flags"]["note"] = Value::String(format!("{h}m so far"));
    }
    row
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
