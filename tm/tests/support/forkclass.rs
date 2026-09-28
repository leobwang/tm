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
//!   row: no `▶`, clipped at the wall's rows). On every other day it IS the
//!   shipped fork's day, byte for byte.
//! * `shipped` — the shipped fork's day, kept only where the comparand departs
//!   from it (a P46 or P47 day), so the divergence stays visible by value.
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
//! # Where the worlds came from, and what that cannot do
//!
//! Each world was DRAWN from `planner_invariants.rs`' own generator
//! (`case_strategy` and `build`, and each arm's widenings as that arm applies
//! them), by a harness run once in a clone and recorded in README's W-36 track
//! H block — never written by hand. They are fixtures now, like `kernel/corpus`:
//! the re-bless recomputes the FORK'S ANSWERS from the stored worlds and cannot
//! re-draw them, because that generator is private to a file this track could
//! not touch (README gap 3080).

#![allow(dead_code)]

use std::collections::BTreeSet;
use std::sync::OnceLock;

use chrono::{DateTime, Duration, NaiveTime};
use chrono_tz::Tz;
use serde_json::{json, Value};

use tm_core::capacity::{self, local_dt};
use tm_core::config::Config;
use tm_core::dayplan::{DayPlan, SegKind};
use tm_core::energy::{Model, DEFAULT_TAG};
use tm_core::log::Replay;
use tm_core::model::{Id, Shape};
use tm_core::planwire::{self, KernelDay};
use tm_core::priority::{self, Candidate};
use tm_core::store::RuntimeState;
use tm_core::tree::Tree;

use crate::{chokepoint, forkday, planreq};

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

/// **A world's class**, computed from the world and nothing else.
///
/// The run state, first match wins: a running break (whatever else is
/// running, since `tm break` pauses the block), then an open interruption, then
/// a running block — P47 when a wall's blocked span covers `now`, P46 when it
/// is not paused and its worked minutes have reached its estimate (fork
/// `active_run`'s `left == 0`), running otherwise.
///
/// The shape, first match wins: a `travel-day` wall; a budget the blocks done
/// have spent (`capacity::remaining_budget` is 0 after at least one); no stored
/// window; `loc: home`; the lounge.
pub fn class_of(b: &Built) -> Class {
    let st = &b.world.state;
    let now = b.world.now;
    let active = st.active.as_ref();
    let walls = b.walls();
    let run = if st.break_.as_ref().is_some_and(|x| x.started.is_some()) {
        if active.is_some() {
            Run::BreakBlock
        } else {
            Run::Break
        }
    } else if st.interrupt.is_some() {
        if active.is_some() {
            Run::InterruptedBlock
        } else {
            Run::Interrupted
        }
    } else if let Some(a) = active {
        if walls.iter().any(|(_, lo, hi, _)| *lo <= now && now < *hi) {
            Run::WallOnNow
        } else if !a.paused && b.worked().unwrap_or(0) >= a.est_min {
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
             P47 {}; under-used notes the renderer derived as the fork wrote them {}; what-ifs {} ({} \
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
