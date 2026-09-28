//! **The host's half of the kernel's PLANNER wire** (`PlanWire.lean`): the
//! `planner` section's encoder, the decoder of the `ok.plan` answer into
//! [`crate::dayplan`]'s types, and the decoder of the capacity section's grants
//! that answer is read beside. Stage 6 W-35, track R (README gaps 2720 and
//! 2006; D58).
//!
//! # Why it is here and not in `tm/src`
//!
//! `tm` is a `[[bin]]` with no library target, so nothing in `tm/tests` can
//! link a function the binary declares (README gaps 2006, 2061, 2221). Every
//! test that asked the kernel for a day therefore carried its OWN encoder and
//! its own reading of the answer — `tm/tests/planner_invariants.rs`' world and
//! `kernel_planner_wire.rs` among them — and the binary had none at all (gap
//! 2720). This module is the one spelling both can call. **It is not wired into
//! any verb**: `tm plan` and the TUI still plan with `planner::plan`, and the
//! body swap is R3's (D48). What lands here is the codec R3 swaps in, built and
//! tested first so the swap is the only thing R3 changes.
//!
//! # What it encodes, and what it deliberately does not
//!
//! The `planner` section is `PlanWire.readPlannerSection` plus
//! `PlanWire.readOvertime`. Of its keys this encoder writes:
//!
//! * `state.active`, `state.break`, `state.interrupt` — §9's running records,
//!   each start resolved on the planned date in the configured zone exactly as
//!   fork `Planner::active_run` resolves `active.started`
//!   (`capacity::local_dt(tz, date, t)`).
//! * `routines` — §8.2 step 2's window instances, [`routine_instances`].
//! * `overtime` — §9.1's what-if, [`overtime_json`], carrying D58's grown
//!   facts.
//!
//! and it writes **none** of `state.lastHash`, `state.yesterday` or
//! `overrides`, because the kernel reads none of them: `kernel/inputs-exempt.txt`
//! names `RuntimeIn.lastHash`, `RuntimeIn.yesterday`, `PlanOverrides.estMin` and
//! `PlanOverrides.extraMin` as decoded and read by no definition of the day, and
//! each of their EXITs is that the field leaves the request. An encoder that
//! sent them would be the input-side composition gap W-34 found, spelled on the
//! host. (`overrides.drop` is read, by `PlanReq.activeRun`, but no shipped path
//! builds a drop what-if — the TUI's one what-if is §9.1's extension — so it has
//! no encoder until a caller wants one.)
//!
//! **No bound is minted here.** An id past `CapWire.maxCandId`, a list past
//! `Planner.maxCands`, a start after `now` or an estimate past `Look.maxDayMin`
//! is sent as the host holds it and refused BY THE KERNEL, by name
//! (`{"err":{"planner":"badActive wf"}}` and its family, read back by
//! [`planner_refusal`]); a second statement of those numbers here would be the
//! defect AGENTS §5.3 names. Minutes cross as `u32`, which is the fork's width
//! and is `Look.maxPlanMinutes` — the type is the bound.
//!
//! # What it decodes, and the one check it makes
//!
//! [`read_plan`] reads `Planner.dayPlan`'s seven keys (`PlanWire.planJson`) and
//! `overtime` (`PlanWire.overtimeJson`) into a [`DayPlan`] and a [`PlanDiff`].
//! Where the kernel's answer is narrower than the host's type it is completed
//! from what the host already holds and sent, never guessed:
//!
//! * `priorities` pairs are the host's own candidates and the [`Prio`]s
//!   [`read_capacity_answer`] decoded from the same response's grants — the
//!   kernel's `{id, p}` list is read and cross-checked against them;
//! * `diagnostics.underused` is fork `diagnose`'s triple, rebuilt from the
//!   decoded rows and the candidates' `ci`, and its id sequence must be the
//!   kernel's;
//! * `diagnostics.impossible`'s date is the grant's `until` (README gap 2640:
//!   the kernel does not write it);
//! * `diagnostics.blocked`'s dependencies are the candidate's own
//!   (`Candidate::ineligible_reason`), and the kernel must have named exactly the
//!   blocked candidates;
//! * a note is the fork's sentence for the kernel's name (`Emit.noteText`'s
//!   words), with a wall's buffer titled by its candidate.
//!
//! **The check**: the decoded day's own [`DayPlan::hash`] must be the `hash`
//! the kernel wrote. Since W-34 the kernel's digest is the fork's byte for byte,
//! so a disagreement means the decoder dropped or bent a digested field — the
//! start, end, kind, energy, item, instance, planned minutes or multiplier of
//! some row — and it is refused by name rather than handed to a renderer.

use std::collections::BTreeMap;

use chrono::{DateTime, Duration, NaiveDate, NaiveTime, TimeZone};
use chrono_tz::Tz;
use serde_json::{json, Map, Value};

use crate::capacity::{self, local_dt, Exact, UnitCapacity, CAP_DEN};
use crate::config::Config;
use crate::dayplan::{fmt_clock, kind_label, DayPlan, Diagnostics, PlanDiff, SegFlags, SegKind, Segment};
use crate::energy;
use crate::model::{Id, InstanceKey, Shape, WindowRange};
use crate::priority::{self, Candidate, Ineligible, Prio, PrioClass};
use crate::store::RuntimeState;
use crate::tree::Tree;

// ---------------------------------------------------------------------------
// Defects
// ---------------------------------------------------------------------------

/// **A response the host cannot read** — named, never a wrong answer. The
/// string says which field of which record, as `kernel_log`'s decoders do.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WireDefect(pub String);

impl WireDefect {
    fn at(what: impl Into<String>) -> WireDefect {
        WireDefect(what.into())
    }
}

impl std::fmt::Display for WireDefect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

type W<T> = Result<T, WireDefect>;

// ---------------------------------------------------------------------------
// Instants
// ---------------------------------------------------------------------------

/// Seconds from `0001-01-01T00:00:00Z` to the Unix epoch: the kernel counts
/// instants from the former (`Cal.Instant`) and `chrono` from the latter.
pub const EPOCH_FROM_CE: i64 = 62_135_596_800;

/// A zoned instant as the kernel's absolute second.
pub fn kernel_sec(t: DateTime<Tz>) -> i64 {
    t.timestamp() + EPOCH_FROM_CE
}

/// The kernel's absolute second as an instant in `tz`.
pub fn instant_of(sec: i64, tz: Tz) -> Option<DateTime<Tz>> {
    tz.timestamp_opt(sec.checked_sub(EPOCH_FROM_CE)?, 0).single()
}

// ---------------------------------------------------------------------------
// The capacity section's answer (moved from `tm/src/cli/kernel_capacity.rs`)
// ---------------------------------------------------------------------------

/// What the kernel's capacity section answered: the first `min(days, 7)` days
/// in units, and one priority per candidate in the candidates' own order.
#[derive(Clone, Debug, Default)]
pub struct CapacityAnswer {
    /// The lookahead's first days (at most seven), exact units over [`CAP_DEN`].
    pub days: Vec<UnitCapacity>,
    /// One [`Prio`] per candidate, in `collect_candidates` order.
    pub prios: Vec<Prio>,
}

/// A digit string as `u128` (D17).
fn units_of(v: &Value, what: &str) -> W<u128> {
    v.as_str()
        .filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
        .and_then(|s| s.parse::<u128>().ok())
        .ok_or_else(|| WireDefect::at(format!("{what} is not a digit string that fits u128")))
}

/// A `YYYY-MM-DD`.
fn date_of(v: &Value, what: &str) -> W<NaiveDate> {
    v.as_str()
        .and_then(|s| NaiveDate::parse_from_str(s, "%Y-%m-%d").ok())
        .ok_or_else(|| WireDefect::at(format!("{what} is not a date")))
}

/// A small natural.
fn small(v: &Value, what: &str) -> W<u8> {
    v.as_u64()
        .and_then(|n| u8::try_from(n).ok())
        .ok_or_else(|| WireDefect::at(format!("{what} is not a small natural")))
}

/// Fork `PrioClass`'s serde name.
fn class_of(name: &str) -> Option<PrioClass> {
    Some(match name {
        "wall" => PrioClass::Wall,
        "hot" => PrioClass::Hot,
        "impossible" => PrioClass::Impossible,
        "overdue" => PrioClass::Overdue,
        "mandatory" => PrioClass::Mandatory,
        "hotflag" => PrioClass::HotFlag,
        "dated" => PrioClass::Dated,
        "floor" => PrioClass::Floor,
        "rank" => PrioClass::Rank,
        "optional" => PrioClass::Optional,
        _ => return None,
    })
}

/// **One grant as a [`Prio`]**: the kernel's class, `k`, `p`, raw `p`, need,
/// `until` and bin; availability, allocation and shortfall as floors beside their
/// exact values (D15). `u` is display only: the exact `need / avail` as a
/// double, held on the kernel's side of 1 (`u ≥ 1` exactly when the kernel's bin
/// is HOT), so [`Prio::is_hot`] agrees with the kernel.
///
/// This is the shipped binary's reading, moved here from
/// `tm/src/cli/kernel_capacity.rs` at W-35 unchanged and under its own name —
/// the ledger, `Planner.lean` and `Check.lean` cite it as `kernel_capacity`'s
/// `prio_of`, and the binary still reads every grant through it — so a test
/// that ranks the fork "as the shipped binary runs it" (D53) reads the grants
/// the binary's way and not a copy's (README gap 2006's answer half).
pub fn prio_of(g: &Value) -> W<Prio> {
    let id = g["id"].as_str().ok_or_else(|| WireDefect::at("a grant has no id"))?;
    let class = g["class"]
        .as_str()
        .and_then(class_of)
        .ok_or_else(|| WireDefect::at("a grant's class is unknown"))?;
    let k = small(&g["k"], "k")?;
    let p = if g["p"].is_null() { None } else { Some(small(&g["p"], "p")?) };
    let raw = if g["rawP"].is_null() { None } else { Some(small(&g["rawP"], "rawP")?) };
    // **`need` is read at the width that holds it** (W-36 track T, README gap
    // 2929). It is `⌈remaining × safety⌉` (§7.1): `remaining` crosses the wire
    // under `CapWire.maxRemaining` (fork `u32`) and the safety under
    // `safetyOfWire`'s thousand, so a legal need can pass `u32` — and did, on a
    // tree whose one estimate was `4294967295m`: `tm plan` answered `kernel
    // fault: capacity response: need`, a fault labelled a bug, from a value the
    // edit had accepted. Every need the kernel can write fits `u64` (under
    // 2^52, so `u` below is exact too); a need past it is still a named defect.
    // The DISPLAY floor saturates at `u32`, as `avail_min`, `allocation_min`
    // and `shortfall_min` do through `capacity::floor_minutes`, and as fork
    // `safety_minutes`' own `as u32` does; `u` reads the need exactly.
    let need = g["need"].as_u64().ok_or_else(|| WireDefect::at("need"))?;
    let until = if g["until"].is_null() { None } else { Some(date_of(&g["until"], "until")?) };
    let avail = units_of(&g["avail"], "avail")?;
    let allocation = units_of(&g["allocation"], "allocation")?;
    let shortfall = units_of(&g["shortfall"], "shortfall")?;
    let bin = if g["bin"].is_null() { None } else { Some(small(&g["bin"], "bin")?) };
    let passed = until.is_some() && class != PrioClass::Wall;
    let u = passed.then(|| {
        let exact = if avail == 0 {
            f64::INFINITY
        } else {
            (u128::from(need) * CAP_DEN) as f64 / avail as f64
        };
        match bin {
            None => exact.max(1.0),
            Some(_) => exact.min(1.0 - f64::EPSILON),
        }
    });
    Ok(Prio {
        id: Id::new(id),
        p: p.unwrap_or(0),
        class,
        k,
        u,
        bin,
        need_min: u32::try_from(need).unwrap_or(u32::MAX),
        avail_min: capacity::floor_minutes(avail),
        avail_min_exact: Exact::of_units(avail),
        allocation_min: capacity::floor_minutes(allocation),
        allocation_min_exact: Exact::of_units(allocation),
        shortfall_min: capacity::floor_minutes(shortfall),
        shortfall_min_exact: Exact::of_units(shortfall),
        until,
        hysteresis_applied: p != raw,
        raw_p: raw.unwrap_or(0),
    })
}

/// **Read the capacity section's answer** of a request whose candidates were
/// sent in `order` (positions into the host's `collect_candidates` list).
pub fn read_capacity_answer(resp: &Value, order: &[usize], ranked: bool) -> W<CapacityAnswer> {
    let la = &resp["ok"]["lookahead"];
    if la["den"].as_str() != Some(CAP_DEN.to_string().as_str()) {
        return Err(WireDefect::at("den is not capDen"));
    }
    let days = la["days"]
        .as_array()
        .ok_or_else(|| WireDefect::at("no days"))?
        .iter()
        .map(|d| {
            let date = date_of(&d["day"], "a day")?;
            let at = d["numAt"]
                .as_array()
                .filter(|a| a.len() == 6)
                .ok_or_else(|| WireDefect::at("numAt"))?;
            let mut units = [0u128; 6];
            for (l, v) in at.iter().enumerate() {
                units[l] = units_of(v, "numAt")?;
            }
            Ok(UnitCapacity { date, units })
        })
        .collect::<W<Vec<_>>>()?;
    let mut prios = Vec::new();
    if ranked {
        let grants = la["grants"].as_array().ok_or_else(|| WireDefect::at("no grants"))?;
        if grants.len() != order.len() {
            return Err(WireDefect::at("one grant per candidate"));
        }
        let mut slots: Vec<Option<Prio>> = vec![None; order.len()];
        for (g, &i) in grants.iter().zip(order) {
            slots[i] = Some(prio_of(g)?);
        }
        prios = slots
            .into_iter()
            .map(|p| p.ok_or_else(|| WireDefect::at("a candidate without a grant")))
            .collect::<W<_>>()?;
    }
    Ok(CapacityAnswer { days, prios })
}

// ---------------------------------------------------------------------------
// The `planner` section — the encoder
// ---------------------------------------------------------------------------

/// **The local date being planned**: `state.date`, else `now`'s date — the one
/// rule fork `PlanInput::date` states, which calls this since W-35 so the two
/// cannot drift.
pub fn plan_date(state: &RuntimeState, now: DateTime<Tz>) -> NaiveDate {
    state.date.unwrap_or_else(|| now.date_naive())
}

/// A `state.json` `HH:MM` as the kernel's absolute second, on `date` in `tz` —
/// fork `Planner::active_run`'s `capacity::local_dt(tz, date, started)`.
fn clock_sec(tz: Tz, date: NaiveDate, t: NaiveTime) -> i64 {
    kernel_sec(local_dt(tz, date, t))
}

/// **§9's three running records** as the section's `state` object
/// (`PlanWire.readState`): `active`, `break` and `interrupt`, each present only
/// when the state holds it. `lastHash` and `yesterday` are not written (module
/// docs: the kernel reads neither).
pub fn state_json(state: &RuntimeState, date: NaiveDate, tz: Tz) -> Value {
    let mut o = Map::new();
    if let Some(a) = &state.active {
        o.insert(
            "active".to_string(),
            json!({"id": a.id.as_str(), "started": clock_sec(tz, date, a.started),
                   "estMin": a.est_min, "paused": a.paused}),
        );
    }
    if let Some(b) = &state.break_ {
        o.insert(
            "break".to_string(),
            json!({"started": b.started.map(|t| clock_sec(tz, date, t)),
                   "plannedMin": b.planned_min, "place": b.place}),
        );
    }
    if let Some(i) = &state.interrupt {
        o.insert(
            "interrupt".to_string(),
            json!({"started": i.started.map(|t| clock_sec(tz, date, t)),
                   "id": i.id.as_ref().map(Id::as_str)}),
        );
    }
    Value::Object(o)
}

/// **One §8.2 step 2 window instance**, as the host collects it and the
/// section's `routines` carries it (`PlanWire.readRoutine`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoutineInst {
    /// The item's key.
    pub id: Id,
    /// The instance, when the candidate stands for one (§5.1).
    pub inst: Option<InstanceKey>,
    /// The span it may be placed in: opens.
    pub from: DateTime<Tz>,
    /// … and closes.
    pub to: DateTime<Tz>,
    /// Its duration: the candidate's remaining minutes.
    pub dur_min: u32,
    /// §5.2's mandatory instance.
    pub mandatory: bool,
}

/// **§8.2 step 2's instances, off the candidates** — fork
/// `Planner::collect_routines`' filter and span, on the fork's own day bounds
/// (local midnight to the next local midnight, so a DST day is right).
///
/// Two things it deliberately does not do, because the kernel does them off the
/// same rule and a second spelling here would be AGENTS §5.3's defect: it does
/// not split out sleep (`Planner.splitSleep`), and it does not sort (the kernel
/// orders mandatory first, then by the moment the window closes). `pref:` is not
/// carried either: the kernel reads it out of the documents the request already
/// holds.
pub fn routine_instances(
    cands: &[Candidate],
    tree: &Tree,
    now: DateTime<Tz>,
    date: NaiveDate,
    tz: Tz,
) -> Vec<RoutineInst> {
    let day_start = local_dt(tz, date, NaiveTime::MIN);
    let day_end = date.succ_opt().map(|d| local_dt(tz, d, NaiveTime::MIN)).unwrap_or(day_start);
    let daily = |id: &Id| -> Option<(DateTime<Tz>, DateTime<Tz>)> {
        let item = tree.get(id)?;
        let Shape::Window { range: WindowRange::Daily { from, to }, .. } = item.shape else {
            return None;
        };
        let start = local_dt(tz, date, from);
        let mut end = local_dt(tz, date, to);
        if end <= start {
            end += Duration::days(1);
        }
        Some((start, end))
    };
    let mut out = Vec::new();
    for c in cands {
        if c.is_wall || c.is_optional || !c.eligible() {
            continue;
        }
        let Some((ws, we)) = c.window else { continue };
        if c.remaining_min == 0 {
            continue;
        }
        let hours = daily(&c.id);
        let (from, to) = if we <= now {
            let (a, b) = hours.unwrap_or((day_start, day_end));
            (a.max(now).max(day_start), b.max(now))
        } else {
            let (mut a, mut b) = (ws.max(day_start), we.min(day_end));
            if let Some((ha, hb)) = hours {
                a = a.max(ha);
                b = b.min(hb);
            }
            (a, b)
        };
        out.push(RoutineInst {
            id: c.id.clone(),
            inst: c.instance,
            from,
            to,
            dur_min: c.remaining_min,
            mandatory: c.mandatory,
        });
    }
    out
}

/// The instances as the section's `routines` array.
pub fn routines_json(routines: &[RoutineInst]) -> Value {
    Value::Array(
        routines
            .iter()
            .map(|r| {
                json!({"id": r.id.as_str(), "inst": r.inst.map(|k| k.to_string()),
                       "winLo": kernel_sec(r.from), "winHi": kernel_sec(r.to),
                       "durMin": r.dur_min, "mandatory": r.mandatory})
            })
            .collect(),
    )
}

/// **The candidate facts §9.1's "x extend" grows** (D58): the extended item's
/// remaining, planned and need minutes as fork `PlanOverrides::apply` rewrites
/// them. The kernel may not derive a candidate fact (D34), so the host computes
/// them — with the SAME two functions `priority::collect_candidates` derives the
/// originals with (`energy::planned_minutes`, and the safety rounding
/// `Candidate::new` uses), so they are the host's one reading of the facts and
/// not a second.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Grown {
    /// `remaining_min`, grown.
    pub remaining_min: u32,
    /// `planned_min`: `remaining × multiplier` (§8.5).
    pub planned_min: u32,
    /// `need_min`: `remaining × safety` (§7.1).
    pub need_min: u32,
}

/// **Fork `PlanOverrides::apply`, for one candidate**: `est` replaces the
/// remaining estimate when given, `extra_min` is added to it (saturating), and
/// when the result is the candidate's own remaining nothing changes — `None`,
/// exactly as `apply` leaves such a candidate's facts untouched.
pub fn grown(c: &Candidate, est: Option<u32>, extra_min: u32, cfg: &Config) -> Option<Grown> {
    let minutes = est.unwrap_or(c.remaining_min).saturating_add(extra_min);
    if minutes == c.remaining_min {
        return None;
    }
    Some(Grown {
        remaining_min: minutes,
        planned_min: energy::planned_minutes(minutes, c.multiplier),
        need_min: priority::safety_minutes(minutes, cfg),
    })
}

/// **§9.1's what-if** as the section's `overtime` object: the item and the
/// blocks (`PlanWire.readOvertime`), and — D58 — the item's grown facts under
/// `grown` when it is a candidate the extension changes.
///
/// **The kernel reads `grown` since W-36** (README gap 2873): `PlanWire.readGrown`
/// reads `remaining` and `plannedMin`, and `Planner.overtimeDiff` plans the
/// extended request with them (`Planner.PlanReq.growing`), so the what-if gives
/// the extended item the commitment fork `apply` gives it. `needMin` is sent
/// and not read: no reader of the day reads a need but §7.3's pass, which
/// derives its own from `remaining` (README gap 3004).
pub fn overtime_json(id: &Id, blocks: u32, grown: Option<&Grown>) -> Value {
    let mut o = json!({"id": id.as_str(), "blocks": blocks});
    if let Some(g) = grown {
        o["grown"] = json!({"remaining": g.remaining_min, "plannedMin": g.planned_min,
                            "needMin": g.need_min});
    }
    o
}

/// **The whole `planner` section**: `state`, `routines`, and `overtime` when a
/// what-if is asked for.
pub fn planner_json(
    state: &RuntimeState,
    now: DateTime<Tz>,
    tz: Tz,
    routines: &[RoutineInst],
    overtime: Option<Value>,
) -> Value {
    let date = plan_date(state, now);
    let mut o = json!({"state": state_json(state, date, tz), "routines": routines_json(routines)});
    if let Some(ot) = overtime {
        o["overtime"] = ot;
    }
    o
}

/// **The running block's WORKED minutes into a `planner` section** (W-36
/// track T, README gap 2920): `state.active.workedMin`, the host's ONE reading
/// — [`crate::log::Replay::active_worked_min`], fork `day::worked_min`, the
/// wall clock since `started` net of the day's pauses, interruptions and
/// breaks — which is what `tm now` prints and `tm done` logs. The kernel's
/// planner reads it for the reservation's `left` and the open row's `so far`
/// (`Planner.PlanReq.workedOf`), so the day and the header cannot print two
/// numbers for one block. A section without it gets the log's own open-block
/// reading (fork `active_run`'s), which counts a break inside the block as
/// worked: **R3's `planner` section must carry it**. A section whose `state`
/// has no `active` is left as it is (nothing is running, nothing was worked).
pub fn add_worked_min(planner: &mut Value, worked_min: u32) {
    if let Some(a) = planner
        .get_mut("state")
        .and_then(|s| s.get_mut("active"))
        .and_then(Value::as_object_mut)
    {
        a.insert("workedMin".to_string(), json!(worked_min));
    }
}

/// §16's `[priority] batch_max_min` into a capacity section's `priority`
/// object, the one place the kernel reads it (`PlanWire.readBatchMaxMin`: the
/// fourth key of the object `CapWire.readPriority` reads three of). The capacity
/// request the binary sends today does not carry it, because no shipped request
/// carries a `planner` section yet; a request that does needs it.
pub fn add_batch_max_min(capacity: &mut Value, cfg: &Config) {
    if let Some(p) = capacity.get_mut("priority").and_then(Value::as_object_mut) {
        p.insert("batchMaxMin".to_string(), json!(cfg.priority.batch_max_min));
    }
}

// ---------------------------------------------------------------------------
// The `plan` answer — the decoder
// ---------------------------------------------------------------------------

/// What the host holds that the kernel's `plan` answer is read against.
pub struct DayCtx<'a> {
    /// The configured zone: every instant is a second on the kernel's side.
    pub tz: Tz,
    /// The candidates the request sent, in `collect_candidates` order.
    pub cands: &'a [Candidate],
    /// Their priorities, 1:1 — [`read_capacity_answer`]'s, from the same
    /// response.
    pub prios: &'a [Prio],
}

/// **A day the kernel planned**, in the host's representation.
#[derive(Clone, Debug, PartialEq)]
pub struct KernelDay {
    /// The day.
    pub day: DayPlan,
    /// `plan.hash` as the kernel wrote it — equal to `day.hash()`, which
    /// [`read_plan`] checks.
    pub hash: String,
    /// `plan.overtime`, when the request asked for §9.1's what-if.
    pub overtime: Option<PlanDiff>,
}

/// `{"err":{"planner":"<name> <key>"}}` — the section's refusal
/// (`PlanWire.plannerRefusalJson`), or `None` when the response is not one.
pub fn planner_refusal(resp: &Value) -> Option<&str> {
    resp["err"]["planner"].as_str()
}

fn nat(v: &Value, what: &str) -> W<u64> {
    v.as_u64().ok_or_else(|| WireDefect::at(format!("{what} is not a natural")))
}

fn nat32(v: &Value, what: &str) -> W<u32> {
    u32::try_from(nat(v, what)?).map_err(|_| WireDefect::at(format!("{what} is past u32")))
}

fn text<'v>(v: &'v Value, what: &str) -> W<&'v str> {
    v.as_str().ok_or_else(|| WireDefect::at(format!("{what} is not a string")))
}

fn flag(v: &Value, what: &str) -> W<bool> {
    v.as_bool().ok_or_else(|| WireDefect::at(format!("{what} is not a boolean")))
}

fn array<'v>(v: &'v Value, what: &str) -> W<&'v [Value]> {
    v.as_array().map(Vec::as_slice).ok_or_else(|| WireDefect::at(format!("{what} is not an array")))
}

fn ids(v: &Value, what: &str) -> W<Vec<Id>> {
    array(v, what)?
        .iter()
        .enumerate()
        .map(|(i, x)| text(x, &format!("{what}[{i}]")).map(Id::new))
        .collect()
}

fn instant(v: &Value, tz: Tz, what: &str) -> W<DateTime<Tz>> {
    let sec = i64::try_from(nat(v, what)?).map_err(|_| WireDefect::at(format!("{what} is past i64")))?;
    instant_of(sec, tz).ok_or_else(|| WireDefect::at(format!("{what} is not an instant chrono holds")))
}

/// An exact `{num, den}` multiplier as the double the host wrote it from.
///
/// The host sends a multiplier as the shortest decimal of its double over a
/// power of ten (`kernel_capacity::written_pair`), and the kernel may reduce the
/// pair; any fraction whose denominator has no prime factor but 2 and 5 is a
/// terminating decimal, so it is rebuilt digit for digit and parsed — correctly
/// rounded — back to that double. Anything else is not a multiplier the host
/// could have sent, and is refused by name.
fn multiplier_of(v: &Value, what: &str) -> W<f64> {
    let num = u128::from(nat(&v["num"], what)?);
    let den = u128::from(nat(&v["den"], what)?);
    let bad = || WireDefect::at(format!("{what} is not a terminating decimal"));
    if den == 0 {
        return Err(bad());
    }
    let (mut places, mut pow) = (0usize, 1u128);
    while pow % den != 0 {
        if places == 36 {
            return Err(bad());
        }
        pow *= 10;
        places += 1;
    }
    let scaled = num.checked_mul(pow / den).ok_or_else(bad)?;
    let digits = format!("{scaled:0>width$}", width = places + 1);
    let (int, frac) = digits.split_at(digits.len() - places);
    format!("{int}.{frac}0").parse::<f64>().map_err(|_| bad())
}

/// The inverse of [`kind_label`], read off it and not spelled again (AGENTS
/// §5.3): the kernel's word for a row's kind is `PlanWire.kindName`, whose ten
/// fork words are `kind_label`'s. The kernel's eleventh, `ghost`, is a row kind
/// the kernel's DAY never holds (only `plan.rows` does), so meeting it here is a
/// defect, named.
fn kind_of(word: &str, batch: &[Value], what: &str) -> W<SegKind> {
    const KINDS: [SegKind; 9] = [
        SegKind::Block,
        SegKind::Break,
        SegKind::Routine,
        SegKind::Wall,
        SegKind::Rest,
        SegKind::Optional,
        SegKind::WindDown,
        SegKind::Sleep,
        SegKind::Lost,
    ];
    if word == kind_label(&SegKind::Batch(Vec::new())) {
        let members = batch
            .iter()
            .enumerate()
            .map(|(i, x)| text(x, &format!("{what}.batch[{i}]")).map(Id::new))
            .collect::<W<Vec<Id>>>()?;
        return Ok(SegKind::Batch(members));
    }
    KINDS
        .iter()
        .find(|k| kind_label(k) == word)
        .cloned()
        .ok_or_else(|| WireDefect::at(format!("{what}.kind `{word}` is no kind of a planned day")))
}

/// **A note, as the fork wrote it**: `Emit.noteText`'s words for the kernel's
/// name, which are fork `planner.rs`'s own sentences. `plannedOf` is
/// `WeekPlan`'s note and the kernel's day holds none, so it is refused by name
/// rather than rendered here on speculation.
fn note_text(v: &Value, ctx: &DayCtx<'_>, what: &str) -> W<String> {
    let name = text(&v["note"], &format!("{what}.note"))?;
    let field = |k: &str| format!("{what}.{k}");
    Ok(match name {
        "travelDay" => "travel day: no blocks planned (`travel-day` wall today)".to_string(),
        "noPosition" => format!(
            "{}: no free {}m position in {}–{}; not planned today",
            text(&v["id"], &field("id"))?,
            nat(&v["durMin"], &field("durMin"))?,
            fmt_clock(instant(&v["lo"], ctx.tz, &field("lo"))?),
            fmt_clock(instant(&v["hi"], ctx.tz, &field("hi"))?),
        ),
        "budgetSpent" => format!(
            "budget spent: {} blocks done, the rest of the day is rest",
            nat(&v["blocksDone"], &field("blocksDone"))?
        ),
        "bufferBefore" => {
            // Fork `WallSeg::title` is the candidate's title; the kernel's
            // `Emit.titleText` falls back to the key when the plan has none.
            let id = text(&v["id"], &field("id"))?;
            let title = ctx
                .cands
                .iter()
                .find(|c| c.id.as_str() == id)
                .map_or(id.to_string(), |c| c.title.clone());
            format!("buffer before {title}")
        }
        "travelDayWall" => "travel day".to_string(),
        "paused" => "paused".to_string(),
        "interruption" => "interruption".to_string(),
        "breakWhere" | "idleAttributed" => text(&v["text"], &field("text"))?.to_string(),
        "runningLeft" => format!("running · {}m left", nat(&v["leftMin"], &field("leftMin"))?),
        "soFar" => format!("{}m so far", nat(&v["workedMin"], &field("workedMin"))?),
        other => return Err(WireDefect::at(format!("{what}: `{other}` is not a note of a planned day"))),
    })
}

/// One row of the day (`PlanWire.segJson`).
fn segment_of(v: &Value, ctx: &DayCtx<'_>, what: &str) -> W<Segment> {
    let f = &v["flags"];
    let flag_at = |k: &str| flag(&f[k], &format!("{what}.flags.{k}"));
    let kind = kind_of(
        text(&v["kind"], &format!("{what}.kind"))?,
        array(&v["batch"], &format!("{what}.batch"))?,
        what,
    )?;
    // A slot energy is `Fin 6` on the kernel's side (`Planner.Seg.energy`).
    let energy = match &v["energy"] {
        Value::Null => None,
        e => match small(e, &format!("{what}.energy"))? {
            n if n <= 5 => Some(n),
            _ => return Err(WireDefect::at(format!("{what}.energy is past 5"))),
        },
    };
    let instance = match &v["inst"] {
        Value::Null => None,
        i => {
            let t = text(&i["inst"], &format!("{what}.inst.inst"))?;
            Some(InstanceKey::parse(t).ok_or_else(|| {
                WireDefect::at(format!("{what}.inst.inst `{t}` is not an instance key"))
            })?)
        }
    };
    Ok(Segment {
        start: instant(&v["start"], ctx.tz, &format!("{what}.start"))?,
        end: instant(&v["stop"], ctx.tz, &format!("{what}.stop"))?,
        kind,
        energy,
        item: match &v["item"] {
            Value::Null => None,
            i => Some(Id::new(text(i, &format!("{what}.item"))?)),
        },
        instance,
        flags: SegFlags {
            done: flag_at("done")?,
            current: flag_at("current")?,
            underused: flag_at("underused")?,
            hot: flag_at("hot")?,
            mandatory: flag_at("mandatory")?,
            deferred: flag_at("deferred")?,
            ghost: false,
            open: flag_at("open")?,
            planned_min: match &v["planned"] {
                Value::Null => None,
                p => Some(nat32(p, &format!("{what}.planned"))?),
            },
            multiplier: match &v["mult"] {
                Value::Null => None,
                m => Some(multiplier_of(m, &format!("{what}.mult"))?),
            },
            note: match &v["note"] {
                Value::Null => None,
                n => Some(note_text(n, ctx, &format!("{what}.note"))?),
            },
        },
    })
}

/// §8.2 step 8's twelve fields (`PlanWire.diagJson`), completed from the host's
/// candidates and grants where the kernel's answer is narrower than the host's
/// type (module docs).
fn diagnostics_of(v: &Value, segments: &[Segment], ctx: &DayCtx<'_>) -> W<Diagnostics> {
    let at = |k: &str| format!("plan.diagnostics.{k}");
    let cand = |id: &Id| ctx.cands.iter().find(|c| c.id == *id);

    // Fork `diagnose`'s loop over the rows, and the kernel's list must name the
    // same ids in the same order.
    let mut underused: Vec<(Id, u8, u8)> = Vec::new();
    for seg in segments.iter().filter(|s| s.flags.underused && s.kind.is_work()) {
        let energy = seg.energy.unwrap_or(0);
        for id in seg.items() {
            let ci = cand(&id).map_or(0, |c| c.ci);
            underused.push((id, energy, ci));
        }
    }
    let named = ids(&v["underused"], &at("underused"))?;
    if named != underused.iter().map(|(i, _, _)| i.clone()).collect::<Vec<Id>>() {
        return Err(WireDefect::at(format!(
            "{} names {:?} and the rows mark {:?}",
            at("underused"),
            named,
            underused.iter().map(|(i, _, _)| i.as_str()).collect::<Vec<_>>()
        )));
    }

    let impossible = array(&v["impossible"], &at("impossible"))?
        .iter()
        .enumerate()
        .map(|(i, x)| {
            let what = format!("{}[{i}]", at("impossible"));
            let id = Id::new(text(&x["id"], &format!("{what}.id"))?);
            let short = nat32(&x["shortMin"], &format!("{what}.shortMin"))?;
            let until = ctx
                .cands
                .iter()
                .zip(ctx.prios)
                .find(|(c, _)| c.id == id)
                .and_then(|(_, p)| p.until)
                .ok_or_else(|| WireDefect::at(format!("{what}: `{}` has no grant with a deadline", id.as_str())))?;
            Ok((id, short, until))
        })
        .collect::<W<Vec<_>>>()?;

    let conflicts = array(&v["conflicts"], &at("conflicts"))?
        .iter()
        .enumerate()
        .map(|(i, x)| {
            let what = format!("{}[{i}]", at("conflicts"));
            Ok((Id::new(text(&x["a"], &format!("{what}.a"))?), Id::new(text(&x["b"], &format!("{what}.b"))?)))
        })
        .collect::<W<Vec<_>>>()?;

    let blocked = ids(&v["blocked"], &at("blocked"))?
        .into_iter()
        .map(|id| match cand(&id).and_then(Candidate::ineligible_reason) {
            Some(Ineligible::Blocked(deps)) => Ok((id, deps)),
            _ => Err(WireDefect::at(format!(
                "{}: `{}` is not a candidate the host holds blocked",
                at("blocked"),
                id.as_str()
            ))),
        })
        .collect::<W<Vec<_>>>()?;

    let notes = array(&v["notes"], &at("notes"))?
        .iter()
        .enumerate()
        .map(|(i, n)| note_text(n, ctx, &format!("{}[{i}]", at("notes"))))
        .collect::<W<Vec<_>>>()?;

    let honesty = &v["planHonesty"];
    let planned = nat32(&honesty["planned"], &at("planHonesty.planned"))?;
    // The kernel's `total` is `remaining_budget × block_min` EXACTLY, and fork
    // `diagnose` divides by `remaining_budget.saturating_mul(block_min)` -- a
    // `state.json` budget is hand-editable, and the fork saturates rather than
    // refuse a nonsense one (§10.2). So the host reads the natural and takes the
    // fork's own `u32` saturation, the width the fork's division already has --
    // never a refusal (W-36 track H, README gap 3082: `budget: 100000000` made
    // this decoder refuse a day the fork plans).
    let total = u32::try_from(nat(&honesty["total"], &at("planHonesty.total"))?).unwrap_or(u32::MAX);

    // **The order the fork prints them in** (W-36 track H, README gap 3086). Fork
    // `diagnose` walks `cands` -- the host's own `collect_candidates` order, this
    // context's -- and pushes `hot`, `impossible`, `waiting`, `blocked` and
    // `deferred` as it meets them; the kernel names the same ids in the order it
    // was SENT them (`send_order`, by due date). The sets agree and the order is
    // the host's to restore, from the list it already holds: on 23 of the 30
    // generated class days `planner_classes.rs` compares them on, the kernel's
    // order was not the fork's, and `tm plan` prints these lists in order.
    let rank = |id: &Id| ctx.cands.iter().position(|c| c.id == *id).unwrap_or(usize::MAX);
    let mut hot = ids(&v["hot"], &at("hot"))?;
    hot.sort_by_key(|id| rank(id));
    let mut impossible = impossible;
    impossible.sort_by_key(|(id, _, _)| rank(id));
    let mut blocked = blocked;
    blocked.sort_by_key(|(id, _)| rank(id));
    let mut deferred = ids(&v["deferred"], &at("deferred"))?;
    deferred.sort_by_key(|id| rank(id));
    let mut waiting = ids(&v["waiting"], &at("waiting"))?;
    waiting.sort_by_key(|id| rank(id));

    Ok(Diagnostics {
        underused,
        a_capacity_lost: nat32(&v["aCapacityLost"], &at("aCapacityLost"))?,
        hot,
        impossible,
        conflicts,
        blocked,
        deferred,
        waiting,
        dropped_tail: ids(&v["droppedTail"], &at("droppedTail"))?,
        // Fork `diagnose`: `(budget_min > 0).then(|| committed / budget_min)`,
        // the same two integers divided once.
        plan_honesty: (total > 0).then(|| f64::from(planned) / f64::from(total)),
        rest_debt_min: nat32(&v["restDebtMin"], &at("restDebtMin"))?,
        notes,
    })
}

/// `plan.overtime` (`PlanWire.diffJson`) as a [`PlanDiff`].
fn diff_of(v: &Value, tz: Tz) -> W<PlanDiff> {
    let at = |k: &str| format!("plan.overtime.{k}");
    let moved = array(&v["moved"], &at("moved"))?
        .iter()
        .enumerate()
        .map(|(i, m)| {
            let what = format!("{}[{i}]", at("moved"));
            Ok((
                Id::new(text(&m["id"], &format!("{what}.id"))?),
                instant(&m["from"], tz, &format!("{what}.from"))?,
                instant(&m["to"], tz, &format!("{what}.to"))?,
            ))
        })
        .collect::<W<Vec<_>>>()?;
    Ok(PlanDiff {
        moved,
        added: ids(&v["added"], &at("added"))?,
        removed: ids(&v["removed"], &at("removed"))?,
        drift_min: nat32(&v["driftMin"], &at("driftMin"))?,
    })
}

/// **Read the kernel's day** — the `plan` object of an `ok` response
/// (`resp["ok"]["plan"]`) — into the host's representation.
///
/// `priorities` is the host's candidates paired with their grants' [`Prio`]s
/// (the fork's `DayPlan::priorities` is exactly that pairing, walls included),
/// and the kernel's own `{id, p}` list — which leaves walls out — must agree
/// with the non-wall pairs as a multiset: two answers of one call disagreeing
/// is a defect, not a choice. The decoded day's hash must be the kernel's
/// `hash` (module docs).
pub fn read_plan(plan: &Value, ctx: &DayCtx<'_>) -> W<KernelDay> {
    if ctx.cands.len() != ctx.prios.len() {
        return Err(WireDefect::at("the host holds one grant per candidate and does not here"));
    }
    let date = date_of(&plan["day"], "plan.day")?;
    let window = (
        instant(&plan["window"]["lo"], ctx.tz, "plan.window.lo")?,
        instant(&plan["window"]["hi"], ctx.tz, "plan.window.hi")?,
    );
    let segments = array(&plan["segments"], "plan.segments")?
        .iter()
        .enumerate()
        .map(|(i, s)| segment_of(s, ctx, &format!("plan.segments[{i}]")))
        .collect::<W<Vec<_>>>()?;
    let diagnostics = diagnostics_of(&plan["diagnostics"], &segments, ctx)?;

    // The kernel's `{id, p}` list against the host's pairs, as multisets.
    let mut theirs: BTreeMap<(String, u8), usize> = BTreeMap::new();
    for (i, x) in array(&plan["priorities"], "plan.priorities")?.iter().enumerate() {
        let what = format!("plan.priorities[{i}]");
        let id = text(&x["id"], &format!("{what}.id"))?.to_string();
        let p = small(&x["p"], &format!("{what}.p"))?;
        *theirs.entry((id, p)).or_default() += 1;
    }
    // A wall is off §7.2's scale and the kernel's list leaves it out
    // (`Planner.prioRow`, fork `sorted_candidates`' `7`); the grants carry it
    // as class `wall`, and the host's pairs keep it as the fork's do.
    let mut ours: BTreeMap<(String, u8), usize> = BTreeMap::new();
    for p in ctx.prios.iter().filter(|p| p.class != PrioClass::Wall) {
        *ours.entry((p.id.as_str().to_string(), p.p)).or_default() += 1;
    }
    if theirs != ours {
        return Err(WireDefect::at(format!(
            "plan.priorities disagree with the grants of the same response: kernel {theirs:?}, grants {ours:?}"
        )));
    }

    let day = DayPlan {
        date,
        window,
        budget_blocks: nat32(&plan["budgetBlocks"], "plan.budgetBlocks")?,
        segments,
        diagnostics,
        priorities: ctx.cands.iter().zip(ctx.prios).map(|(c, p)| (c.id.clone(), p.clone())).collect(),
    };
    let hash = text(&plan["hash"], "plan.hash")?.to_string();
    let ours = day.hash();
    if ours != hash {
        return Err(WireDefect::at(format!(
            "plan.hash: the kernel digested {hash} and the decoded day digests {ours} — a digested field was not read back"
        )));
    }
    let overtime = match &plan["overtime"] {
        Value::Null => None,
        o => Some(diff_of(o, ctx.tz)?),
    };
    Ok(KernelDay { day, hash, overtime })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Dep;

    fn tz() -> Tz {
        Tz::America__Chicago
    }

    fn at(h: u32, m: u32) -> DateTime<Tz> {
        local_dt(tz(), NaiveDate::from_ymd_opt(2026, 9, 7).expect("date"), NaiveTime::from_hms_opt(h, m, 0).expect("time"))
    }

    /// `kernel_capacity::written_pair`'s shape: the shortest decimal of the
    /// double over a power of ten.
    fn written(x: f64) -> Value {
        let t = format!("{x}");
        let (int, frac) = t.split_once('.').unwrap_or((t.as_str(), ""));
        let num: u64 = format!("{int}{frac}").parse().expect("digits");
        json!({"num": num, "den": 10u64.pow(frac.len() as u32)})
    }

    #[test]
    fn an_instant_crosses_as_the_kernels_second_and_back() {
        // 2026-09-07T07:00-05:00 is unix 1,788,782,400; the kernel counts from
        // year 1, 62,135,596,800 seconds earlier.
        let t = at(7, 0);
        assert_eq!(kernel_sec(t), 1_788_782_400 + 62_135_596_800);
        assert_eq!(instant_of(kernel_sec(t), tz()), Some(t));
        // The fall-back hour: a second is one instant, whatever the wall clock says.
        let d = NaiveDate::from_ymd_opt(2026, 11, 1).expect("date");
        let first = local_dt(tz(), d, NaiveTime::from_hms_opt(1, 30, 0).expect("time"));
        let second = first + Duration::hours(1);
        assert_ne!(kernel_sec(first), kernel_sec(second));
        assert_eq!(instant_of(kernel_sec(second), tz()), Some(second));
        // A second past chrono's years is not an instant, and says so.
        assert_eq!(instant_of(i64::MAX, tz()), None);
    }

    #[test]
    fn a_multiplier_reads_back_as_the_double_it_was_written_from() {
        for x in [1.0, 1.6, 1.25, 0.1, 0.35, 2.0, 1.3333333333333333, 0.7000000000000001, 12.5] {
            let v = written(x);
            let back = multiplier_of(&v, "m").expect("a written pair reads back");
            assert_eq!(back.to_bits(), x.to_bits(), "{x} came back as {back} from {v}");
        }
        // The kernel may reduce the pair: 16/10 is 8/5, and 8/5 is still 1.6.
        assert_eq!(multiplier_of(&json!({"num": 8, "den": 5}), "m").map(f64::to_bits), Ok(1.6f64.to_bits()));
        // A thirds pair is no decimal the host could have written: refused, named.
        let e = multiplier_of(&json!({"num": 1, "den": 3}), "plan.segments[2].mult").unwrap_err();
        assert!(e.0.starts_with("plan.segments[2].mult"), "{e}");
        assert!(multiplier_of(&json!({"num": 1, "den": 0}), "m").is_err());
    }

    #[test]
    fn a_kind_word_is_kind_label_read_backwards() {
        // The members are named apart from the kind: `one_renderer`'s title-word
        // needle reads a `SegKind::` beside a string literal as a second title
        // renderer, and a test fixture is not one.
        let members = vec![Id::new("a1"), Id::new("b2")];
        let all = [
            SegKind::Block,
            SegKind::Batch(members),
            SegKind::Break,
            SegKind::Routine,
            SegKind::Wall,
            SegKind::Rest,
            SegKind::Optional,
            SegKind::WindDown,
            SegKind::Sleep,
            SegKind::Lost,
        ];
        for k in all {
            let batch: Vec<Value> = k.clone().pipe_batch();
            assert_eq!(kind_of(kind_label(&k), &batch, "s").as_ref(), Ok(&k));
        }
        // The kernel's eleventh word is a rows-only kind: never in a planned day.
        let e = kind_of("ghost", &[], "plan.segments[4]").unwrap_err();
        assert!(e.0.contains("`ghost`") && e.0.starts_with("plan.segments[4]"), "{e}");
    }

    trait PipeBatch {
        fn pipe_batch(self) -> Vec<Value>;
    }
    impl PipeBatch for SegKind {
        fn pipe_batch(self) -> Vec<Value> {
            match self {
                SegKind::Batch(ids) => ids.iter().map(|i| json!(i.as_str())).collect(),
                _ => Vec::new(),
            }
        }
    }

    fn cand(id: &str, title: &str) -> Candidate {
        Candidate { id: Id::new(id), title: title.to_string(), ..Candidate::default() }
    }

    #[test]
    fn a_note_is_the_forks_own_sentence() {
        let cands = vec![cand("g3", "✈ ORD→SFO UA 1234")];
        let ctx = DayCtx { tz: tz(), cands: &cands, prios: &[] };
        let say = |v: Value| note_text(&v, &ctx, "n");
        assert_eq!(say(json!({"note": "travelDay"})).as_deref(),
                   Ok("travel day: no blocks planned (`travel-day` wall today)"));
        assert_eq!(
            say(json!({"note": "noPosition", "id": "lunch", "durMin": 30,
                       "lo": kernel_sec(at(12, 0)), "hi": kernel_sec(at(13, 30))})).as_deref(),
            Ok("lunch: no free 30m position in 12:00–13:30; not planned today")
        );
        assert_eq!(say(json!({"note": "budgetSpent", "blocksDone": 6})).as_deref(),
                   Ok("budget spent: 6 blocks done, the rest of the day is rest"));
        assert_eq!(say(json!({"note": "bufferBefore", "id": "g3"})).as_deref(),
                   Ok("buffer before ✈ ORD→SFO UA 1234"));
        // No candidate by that key: the kernel's own fallback, the key.
        assert_eq!(say(json!({"note": "bufferBefore", "id": "zz"})).as_deref(), Ok("buffer before zz"));
        assert_eq!(say(json!({"note": "travelDayWall"})).as_deref(), Ok("travel day"));
        assert_eq!(say(json!({"note": "paused"})).as_deref(), Ok("paused"));
        assert_eq!(say(json!({"note": "interruption"})).as_deref(), Ok("interruption"));
        assert_eq!(say(json!({"note": "breakWhere", "text": "walk"})).as_deref(), Ok("walk"));
        assert_eq!(say(json!({"note": "idleAttributed", "text": ""})).as_deref(), Ok(""));
        assert_eq!(say(json!({"note": "runningLeft", "leftMin": 25})).as_deref(), Ok("running · 25m left"));
        assert_eq!(say(json!({"note": "soFar", "workedMin": 12})).as_deref(), Ok("12m so far"));
        // A week's note in a day, and a name nobody declares: refused by name.
        assert!(say(json!({"note": "plannedOf", "planned": 1, "total": 2})).unwrap_err().0.contains("plannedOf"));
        assert!(say(json!({"note": "nope"})).unwrap_err().0.contains("`nope`"));
    }

    /// A day as `PlanWire.planJson` writes one — the test's own spelling of the
    /// kernel's side, for a day built by hand.
    fn kernel_shape(day: &DayPlan, notes: &[Option<Value>]) -> Value {
        let segs: Vec<Value> = day
            .segments
            .iter()
            .zip(notes)
            .map(|(s, note)| {
                let f = &s.flags;
                json!({
                    "start": kernel_sec(s.start), "stop": kernel_sec(s.end),
                    "kind": kind_label(&s.kind), "batch": s.kind.clone().pipe_batch(),
                    "energy": s.energy, "item": s.item.as_ref().map(Id::as_str),
                    "inst": s.instance.map(|k| json!({"id": s.item.as_ref().map(Id::as_str), "inst": k.to_string()})),
                    "flags": {"done": f.done, "current": f.current, "underused": f.underused,
                              "hot": f.hot, "mandatory": f.mandatory, "deferred": f.deferred,
                              "open": f.open},
                    "planned": f.planned_min,
                    "mult": f.multiplier.map(written),
                    "note": note,
                })
            })
            .collect();
        json!({
            "day": day.date.to_string(),
            "window": {"lo": kernel_sec(day.window.0), "hi": kernel_sec(day.window.1)},
            "budgetBlocks": day.budget_blocks,
            "segments": segs,
            "diagnostics": {
                "underused": day.diagnostics.underused.iter().map(|(i, _, _)| i.as_str()).collect::<Vec<_>>(),
                "aCapacityLost": day.diagnostics.a_capacity_lost,
                "hot": [], "impossible": [{"id": "d1", "shortMin": 45}],
                "conflicts": [{"a": "g1", "b": "g2"}],
                "blocked": ["t5"], "deferred": [], "waiting": ["a4"],
                "notes": [{"note": "travelDay"}],
                "droppedTail": ["m3"],
                "planHonesty": {"planned": 780, "total": 360},
                "restDebtMin": 10},
            "priorities": day.priorities.iter().map(|(i, p)| json!({"id": i.as_str(), "p": p.p})).collect::<Vec<_>>(),
            "hash": day.hash(),
        })
    }

    fn prio(id: &str, p: u8, until: Option<NaiveDate>) -> Prio {
        Prio {
            id: Id::new(id),
            p,
            class: PrioClass::Rank,
            k: 3,
            u: None,
            bin: None,
            need_min: 0,
            avail_min: 0,
            avail_min_exact: Exact::default(),
            allocation_min: 0,
            allocation_min_exact: Exact::default(),
            shortfall_min: 0,
            shortfall_min_exact: Exact::default(),
            until,
            hysteresis_applied: false,
            raw_p: p,
        }
    }

    #[test]
    fn a_day_the_kernel_writes_reads_back_whole_and_its_hash_is_checked() {
        let mut d1 = cand("d1", "Report");
        d1.ci = 3;
        let mut t5 = cand("t5", "Blocked task");
        t5.blocked_by = vec![Dep::Item(Id::new("t4"))];
        t5.state = crate::model::State::Todo;
        let mut m1 = cand("m1", "Milestone");
        m1.ci = 2;
        let cands = vec![d1, t5, m1];
        let until = NaiveDate::from_ymd_opt(2026, 9, 9);
        let prios = vec![prio("d1", 0, until), prio("t5", 4, None), prio("m1", 3, None)];
        let ctx = DayCtx { tz: tz(), cands: &cands, prios: &prios };

        let mut day = DayPlan::empty(NaiveDate::from_ymd_opt(2026, 9, 7).expect("date"), (at(7, 0), at(16, 0)), 6);
        let batch = vec![Id::new("x1"), Id::new("x2")];
        day.segments = vec![
            Segment { start: at(7, 0), end: at(8, 0), kind: SegKind::Block, energy: Some(5),
                      item: Some(Id::new("m1")), instance: None,
                      flags: SegFlags { underused: true, planned_min: Some(60), multiplier: Some(1.6), ..SegFlags::default() } },
            Segment { start: at(8, 0), end: at(8, 12), kind: SegKind::Block, energy: None,
                      item: Some(Id::new("d1")), instance: None,
                      flags: SegFlags { open: true, current: true, note: Some("12m so far".to_string()), ..SegFlags::default() } },
            Segment { start: at(11, 30), end: at(12, 0), kind: SegKind::Routine, energy: None,
                      item: Some(Id::new("lunch")),
                      instance: Some(InstanceKey::Date(NaiveDate::from_ymd_opt(2026, 9, 7).expect("date"))),
                      flags: SegFlags { mandatory: true, planned_min: Some(30), ..SegFlags::default() } },
            Segment { start: at(12, 0), end: at(13, 0), kind: SegKind::Batch(batch),
                      energy: Some(3), item: None, instance: None,
                      flags: SegFlags { planned_min: Some(40), multiplier: Some(1.0), ..SegFlags::default() } },
        ];
        day.diagnostics = Diagnostics {
            underused: vec![(Id::new("m1"), 5, 2)],
            a_capacity_lost: 0,
            hot: vec![],
            impossible: vec![(Id::new("d1"), 45, until.expect("date"))],
            conflicts: vec![(Id::new("g1"), Id::new("g2"))],
            blocked: vec![(Id::new("t5"), vec![Dep::Item(Id::new("t4"))])],
            deferred: vec![],
            waiting: vec![Id::new("a4")],
            dropped_tail: vec![Id::new("m3")],
            plan_honesty: Some(780.0 / 360.0),
            rest_debt_min: 10,
            notes: vec!["travel day: no blocks planned (`travel-day` wall today)".to_string()],
        };
        day.priorities = cands.iter().zip(&prios).map(|(c, p)| (c.id.clone(), p.clone())).collect();
        let notes = [None, Some(json!({"note": "soFar", "workedMin": 12})), None, None];
        let v = kernel_shape(&day, &notes);

        let got = read_plan(&v, &ctx).expect("the day reads back");
        assert_eq!(got.day, day, "the decoded day is the day");
        assert_eq!(got.hash, day.hash());
        assert_eq!(got.overtime, None);

        // A digested field bent on the wire: the hash names it.
        let mut bent = v.clone();
        bent["segments"][0]["energy"] = json!(4);
        let e = read_plan(&bent, &ctx).unwrap_err();
        assert!(e.0.starts_with("plan.hash"), "{e}");
        // The kernel naming an underused row the rows do not mark.
        let mut bent = v.clone();
        bent["diagnostics"]["underused"] = json!(["d1"]);
        assert!(read_plan(&bent, &ctx).unwrap_err().0.starts_with("plan.diagnostics.underused"));
        // A blocked id the host does not hold blocked.
        let mut bent = v.clone();
        bent["diagnostics"]["blocked"] = json!(["m1"]);
        assert!(read_plan(&bent, &ctx).unwrap_err().0.contains("`m1` is not a candidate the host holds blocked"));
        // An impossible item without a deadline in its grant.
        let mut bent = v.clone();
        bent["diagnostics"]["impossible"] = json!([{"id": "m1", "shortMin": 5}]);
        assert!(read_plan(&bent, &ctx).unwrap_err().0.contains("has no grant with a deadline"));
        // Two answers of one call disagreeing about a priority.
        let mut bent = v.clone();
        bent["priorities"][0]["p"] = json!(1);
        assert!(read_plan(&bent, &ctx).unwrap_err().0.starts_with("plan.priorities disagree"));
        // An energy past the scale.
        let mut bent = v.clone();
        bent["segments"][0]["energy"] = json!(6);
        assert!(read_plan(&bent, &ctx).unwrap_err().0.starts_with("plan.segments[0].energy"));
        // No budget: honesty is `None`, as the fork's `budget_min > 0` test says.
        let mut zero = v.clone();
        zero["diagnostics"]["planHonesty"] = json!({"planned": 0, "total": 0});
        assert_eq!(read_plan(&zero, &ctx).expect("reads").day.diagnostics.plan_honesty, None);
        // A budget past `u32` minutes saturates as the fork's does (W-36 track H,
        // README gap 3082): fork `diagnose` divides by
        // `remaining_budget.saturating_mul(block_min)`, the kernel's `total` is
        // the exact product, and a hand-edited `budget: 100000000` takes it past
        // `u32`. The decoder refused that day; it reads the natural and saturates.
        let mut big = v.clone();
        big["diagnostics"]["planHonesty"] = json!({"planned": 780, "total": 6_000_000_000u64});
        let sat = read_plan(&big, &ctx).expect("a total past u32 reads").day.diagnostics.plan_honesty;
        assert_eq!(sat, Some(780.0 / f64::from(u32::MAX)));
        let mut edge = v.clone();
        edge["diagnostics"]["planHonesty"] = json!({"planned": 780, "total": u32::MAX});
        assert_eq!(read_plan(&edge, &ctx).expect("reads").day.diagnostics.plan_honesty, sat, "past the edge is the edge");
    }

    #[test]
    fn the_what_if_reads_back_as_a_plan_diff() {
        let v = json!({"removed": ["m3", "t1"], "added": [],
                       "moved": [{"id": "t3", "from": kernel_sec(at(9, 0)), "to": kernel_sec(at(10, 0))}],
                       "driftMin": 60});
        let d = diff_of(&v, tz()).expect("reads");
        assert_eq!(d.removed, vec![Id::new("m3"), Id::new("t1")]);
        assert_eq!(d.moved, vec![(Id::new("t3"), at(9, 0), at(10, 0))]);
        assert_eq!(d.drift_min, 60);
    }

    /// **D58, by value** — fork `PlanOverrides::apply`'s arithmetic on one
    /// candidate, written down so it survives the fork's deletion at R3. The
    /// comparison against `apply` itself runs in `planner.rs`'s own tests while
    /// the fork is there to be compared with.
    #[test]
    fn the_grown_facts_are_apply_s_by_value() {
        let cfg = Config::default(); // safety 1.3
        let c = |remaining: u32, mult: f64| Candidate {
            remaining_min: remaining,
            planned_min: energy::planned_minutes(remaining, mult),
            need_min: priority::safety_minutes(remaining, &cfg),
            multiplier: mult,
            ..Candidate::default()
        };
        let g = |r, p, n| Some(Grown { remaining_min: r, planned_min: p, need_min: n });
        // x extend +1 block of 60 on a 60-minute item: 120, 120, round(156.0).
        assert_eq!(grown(&c(60, 1.0), None, 60, &cfg), g(120, 120, 156));
        // The multiplier sizes the plan (§8.5): round(120 × 1.6) = 192.
        assert_eq!(grown(&c(60, 1.6), None, 60, &cfg), g(120, 192, 156));
        // An `est` override replaces before the extra adds: 30 + 15 = 45.
        assert_eq!(grown(&c(60, 1.6), Some(30), 15, &cfg), g(45, 72, 59));
        // Nothing moved: `apply` leaves the facts as they were.
        assert_eq!(grown(&c(60, 1.6), None, 0, &cfg), None);
        assert_eq!(grown(&c(60, 1.6), Some(45), 15, &cfg), None);
        // Saturating at the fork's u32, and the two roundings saturating with it.
        assert_eq!(grown(&c(u32::MAX - 10, 1.0), None, 60, &cfg), g(u32::MAX, u32::MAX, u32::MAX));
        // A multiplier the model cannot use plans the minutes as they are.
        assert_eq!(grown(&c(60, 0.0), None, 60, &cfg), g(120, 120, 156));
        // A safety that is not a positive number needs the minutes as they are.
        let mut odd = cfg.clone();
        odd.priority.safety = 0.0;
        assert_eq!(grown(&c(60, 1.0), None, 60, &odd), g(120, 120, 120));
    }

    #[test]
    fn the_what_if_carries_the_grown_facts_under_their_candidate_keys() {
        let id = Id::new("t3");
        assert_eq!(overtime_json(&id, 1, None), json!({"id": "t3", "blocks": 1}));
        let gr = Grown { remaining_min: 120, planned_min: 192, need_min: 156 };
        assert_eq!(
            overtime_json(&id, 2, Some(&gr)),
            json!({"id": "t3", "blocks": 2, "grown": {"remaining": 120, "plannedMin": 192, "needMin": 156}})
        );
    }

    #[test]
    fn a_running_record_starts_on_the_planned_date() {
        use crate::store::{ActiveBlock, BreakState, InterruptState};
        let date = NaiveDate::from_ymd_opt(2026, 9, 7).expect("date");
        let state = RuntimeState {
            date: Some(date),
            active: Some(ActiveBlock { id: Id::new("m1"), started: NaiveTime::from_hms_opt(9, 5, 0).expect("t"),
                                       est_min: 60, paused: false }),
            break_: Some(BreakState { started: Some(NaiveTime::from_hms_opt(10, 0, 0).expect("t")),
                                      planned_min: 20, place: Some("walk".to_string()) }),
            interrupt: Some(InterruptState { started: None, id: Some(Id::new("m1")) }),
            last_plan_hash: Some("0123456789abcdef".to_string()),
            ..RuntimeState::default()
        };
        let v = state_json(&state, date, tz());
        assert_eq!(v["active"], json!({"id": "m1", "started": kernel_sec(at(9, 5)), "estMin": 60, "paused": false}));
        assert_eq!(v["break"], json!({"started": kernel_sec(at(10, 0)), "plannedMin": 20, "place": "walk"}));
        assert_eq!(v["interrupt"], json!({"started": null, "id": "m1"}));
        // Read by no definition of the day (kernel/inputs-exempt.txt): not sent.
        assert!(v.get("lastHash").is_none() && v.get("yesterday").is_none(), "{v}");
        assert_eq!(state_json(&RuntimeState::default(), date, tz()), json!({}));
        // The planned date is `state.date`, else `now`'s.
        assert_eq!(plan_date(&state, at(23, 0) + Duration::days(3)), date);
        assert_eq!(plan_date(&RuntimeState::default(), at(23, 0)), date);
    }

    #[test]
    fn batch_max_min_joins_the_priority_object_it_is_read_from() {
        let cfg = Config::default();
        let mut cap = json!({"priority": {"defaultPriority": 3}});
        add_batch_max_min(&mut cap, &cfg);
        assert_eq!(cap["priority"]["batchMaxMin"], json!(cfg.priority.batch_max_min));
        // No priority object, nothing invented: the kernel refuses that request by name.
        let mut bare = json!({});
        add_batch_max_min(&mut bare, &cfg);
        assert_eq!(bare, json!({}));
    }
}
