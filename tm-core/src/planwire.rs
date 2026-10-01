//! **The host's half of the kernel's PLANNER wire** (`PlanWire.lean`): the
//! `planner` section's encoder, the decoder of the `ok.plan` answer into
//! [`crate::dayplan`]'s types, and the decoder of the capacity section's grants
//! that answer is read beside. Stage 6 W-35, track R (README gaps 2720 and
//! 2006; D58).
//!
//! **And since W-40 track E (README gap 2875), the capacity section's
//! ENCODER** — [`capacity_json`], the pure half of `kernel_capacity::request`,
//! with every configured decimal read as its file writes it ([`Written`],
//! [`written_pair`]; D10, D17, parity P26) and §16's `batchMaxMin` beside
//! `[priority]` — so the section the binary sends and the one every planning
//! test sends are built by one function, and `planner_request_keys.rs` reads
//! the binary's whole request off its stderr to diff the two. The section the
//! binary sends changed by exactly one key in the move, `priority.batchMaxMin`
//! (`PlanWire.readBatchMaxMin` refuses a `planner` section beside a capacity
//! section without it, so R3's request needs it).
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
//! `Planner.maxCands`, an estimate or a break planned past `Look.maxDayMin`, or
//! a break place `PlanWire.placeOf?` does not know is sent as the host holds it
//! and refused BY THE KERNEL, by name (`{"err":{"planner":"badActive wf"}}` and
//! its family, read back by [`planner_refusal`]); a second statement of those
//! numbers here would be the defect AGENTS §5.3 names. Minutes cross as `u32`,
//! which is the fork's width and is `Look.maxPlanMinutes` — the type is the
//! bound. (README gap 2874 priced these at R3, and W-40 measured three of them
//! reachable by an ordinary verb — `tm extend` or `tm break` past a day, and
//! `tm break --where` with a fifth word — each a named gap owed before the
//! swap, 3902 and 3903.)
//!
//! **A start after `now` is a reading, not a bound** (W-40 track E, README gap
//! 2874): [`state_json`] sends each running record's start as `min(start,
//! now)`, because the fork reads such a block as nothing worked yet
//! (`Planner::active_run`'s `.max(0)`) and the kernel refuses the raw start
//! (`badActive wf`). No number of the kernel's is written to do it.
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

use chrono::{DateTime, Duration, NaiveDate, NaiveTime, TimeZone, Timelike};
use chrono_tz::Tz;
use serde_json::{json, Map, Value};

use crate::capacity::{self, local_dt, Exact, UnitCapacity, CAP_DEN};
use crate::config::Config;
use crate::dayplan::{fmt_clock, kind_label, DayPlan, Diagnostics, NoPlace, PlanDiff, SegFlags, SegKind, Segment};
use crate::energy::{self, Model};
use crate::model::{fmt_time, Id, InstanceKey, Loc, Shape, WindowRange};
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
// The capacity section — the encoder (moved from `tm/src/cli/kernel_capacity.rs`)
// ---------------------------------------------------------------------------
//
// **W-40 track E, README gap 2875.** `kernel_capacity::request` took a `Ctx` in a
// `[[bin]]`, so no test could link the capacity section the binary sends, and the
// harness (`tm/tests/support/planreq.rs`) spelled it a third time (gap 2006 counted
// two). Everything below is that function's PURE half, moved unchanged in what it
// writes: the configured decimals read as their files write them (D10, D17), the
// section's tables, the candidates in the fork's service order, and — the one
// addition — `priority.batchMaxMin` ([`add_batch_max_min`]), which the planner
// section reads off this object. `kernel_capacity::request` keeps the I/O: it reads
// the files, the documents, the zone table and the log section, and calls
// [`capacity_json`]. A defect a configured value causes is an [`InputDefect`]
// carrying the same sentence `CliError::msg` carried, byte for byte.

/// `Look.maxLookaheadDays`: the most days one capacity request covers.
pub const MAX_LOOKAHEAD_DAYS: u32 = 3660;
/// The most decimal places a lounge weight may have (`capDen = 10^18`, D17).
pub const WEIGHT_PLACES: u32 = 18;
/// The most decimal places of a `[day]` ratio or a prior range key
/// (`den ∈ [1, 10^6]`, design §13.6's table).
pub const RATIO_PLACES: u32 = 6;
/// The most decimal places of a `[priority]` edge or the safety (`den ≤ 10^18`).
pub const PRIORITY_PLACES: u32 = 18;
/// The seven weekdays, Monday first.
const WEEK: [chrono::Weekday; 7] = [
    chrono::Weekday::Mon,
    chrono::Weekday::Tue,
    chrono::Weekday::Wed,
    chrono::Weekday::Thu,
    chrono::Weekday::Fri,
    chrono::Weekday::Sat,
    chrono::Weekday::Sun,
];
/// The two curves a future day reads (`Look.readEnergyIn`).
const LOCATIONS: [&str; 2] = ["lounge", "home"];
/// The plan-relative path of the learned model, as messages name it.
pub const MODEL_FILE: &str = ".tm/model.json";
/// The configuration, as messages name it.
pub const CONFIG_FILE: &str = "config.toml";

/// **A configured value the capacity request cannot carry**, by file and key,
/// quoting its written text — the sentence the binary prints (`CliError::msg`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputDefect(pub String);

impl std::fmt::Display for InputDefect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// Why a double has no decimal pair the kernel can read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairErr {
    /// NaN or an infinity.
    NotFinite,
    /// Below zero.
    Negative,
    /// More decimal places than allowed (the count it has).
    TooManyPlaces(usize),
}

/// **A double as the decimal it is written as** (design §13.6): the shortest
/// round-trip `Display` text of `x`, read by [`written_pair`]. `-0.0` is `0/1`.
/// Refuses NaN, the infinities, negatives, and more than `max_places` decimal
/// places. The fallback for a value no file writes (a default of [`Config`]);
/// a value a file writes is sent as its file's text (D17, [`Written`]).
pub fn decimal_pair(x: f64, max_places: u32) -> Result<(String, String), PairErr> {
    written_pair(&format!("{x}"), max_places)
}

/// **A decimal literal as the exact rational it writes** (D10, D17): the text of
/// a TOML or JSON number (`0.1234567890123456789`, `+0.5`, `1e-3`, `1_000.5`,
/// `inf`, `nan`) as `(numerator, denominator)` digit strings, the denominator
/// `10^places` and `places` the literal's decimal places **of its value**
/// (trailing zeros after the point do not count: `0.500` is `5/10`). Nothing is
/// rounded: a literal with 19 places is refused as `TooManyPlaces(19)` even
/// where its nearest double has fewer. Refuses NaN and the infinities, a
/// negative value (`-0` and `-0.000` are `0/1`), text that is not a number
/// (`NotFinite`), and more than `max_places` places.
pub fn written_pair(text: &str, max_places: u32) -> Result<(String, String), PairErr> {
    let t: String = text.trim().chars().filter(|c| *c != '_').collect();
    let (neg, body) = match t.as_bytes().first() {
        Some(b'-') => (true, &t[1..]),
        Some(b'+') => (false, &t[1..]),
        _ => (false, t.as_str()),
    };
    let (mant, exp) = match body.find(['e', 'E']) {
        Some(i) => (&body[..i], Some(&body[i + 1..])),
        None => (body, None),
    };
    let (int, frac) = mant.split_once('.').unwrap_or((mant, ""));
    let digits_ok = |s: &str| s.bytes().all(|b| b.is_ascii_digit());
    if (int.is_empty() && frac.is_empty()) || !digits_ok(int) || !digits_ok(frac) {
        return Err(PairErr::NotFinite);
    }
    let exp: i64 = match exp {
        None => 0,
        Some(e) => {
            let unsigned = e.strip_prefix(['+', '-']).unwrap_or(e);
            if unsigned.is_empty() || !digits_ok(unsigned) {
                return Err(PairErr::NotFinite);
            }
            // Past 10^6 the exponent's size alone refuses (or no double holds it).
            if unsigned.len() > 6 {
                return if e.starts_with('-') { Err(PairErr::TooManyPlaces(usize::MAX)) } else { Err(PairErr::NotFinite) };
            }
            let n: i64 = unsigned.parse().unwrap_or(0);
            if e.starts_with('-') { -n } else { n }
        }
    };
    let mut digits = format!("{int}{frac}");
    let mut places = frac.len() as i64 - exp;
    if places < 0 {
        digits.push_str(&"0".repeat(places.unsigned_abs() as usize));
        places = 0;
    }
    // Trailing zeros after the point are not places of the value.
    while places > 0 && digits.ends_with('0') {
        digits.pop();
        places -= 1;
    }
    let num = digits.trim_start_matches('0');
    let num = if num.is_empty() { "0".to_string() } else { num.to_string() };
    let places = usize::try_from(places).unwrap_or(usize::MAX);
    if neg && num != "0" {
        return Err(PairErr::Negative);
    }
    if places > max_places as usize {
        return Err(PairErr::TooManyPlaces(places));
    }
    Ok((num, format!("1{}", "0".repeat(places))))
}

/// **A decimal literal as the exact rational it writes, with its sign** (stage 6 step L9, site
/// R10): the same reading as [`written_pair`], except that a negative value comes back as
/// `(true, num, den)` instead of [`PairErr::Negative`]. §8.5 fits `sleep_debt_shift` as a shrunken
/// **mean**, so the shift is genuinely signed, and the kernel rounds it half away from zero
/// (`Arith.roundAway`). `-0`, `-0.000` and `-0e3` are `(false, "0", "1")`, as they are unsigned.
pub fn signed_written_pair(text: &str, max_places: u32) -> Result<(bool, String, String), PairErr> {
    match written_pair(text, max_places) {
        Ok((n, d)) => Ok((false, n, d)),
        Err(PairErr::Negative) => {
            let t = text.trim();
            let (n, d) = written_pair(t.strip_prefix('-').unwrap_or(t), max_places)?;
            Ok((n != "0", n, d))
        }
        Err(e) => Err(e),
    }
}

/// `num / den > 1` for a pair of [`written_pair`] (digit strings, no leading zeros).
fn above_one(num: &str, den: &str) -> bool {
    num.len() > den.len() || (num.len() == den.len() && num > den)
}

/// A pair as the kernel's JSON naturals (`{"num": n, "den": d}`), for the
/// pairs whose parts are bounded well inside `u64` (`[day]`, `[priority]`, the
/// prior's keys).
fn nat_pair_of((n, d): (String, String)) -> Value {
    // `places ≤ 18`, so the denominator fits; a numerator past u64 is a value
    // no bound admits, and is sent as the largest natural so the kernel refuses it.
    json!({"num": n.parse::<u64>().unwrap_or(u64::MAX), "den": d.parse::<u64>().unwrap_or(u64::MAX)})
}

/// A pair as the kernel's digit strings (`{"num": "n", "den": "d"}`): the lounge
/// weights, read as `u128` units under `capDen` (D17).
fn str_pair_of((n, d): &(String, String)) -> Value {
    json!({"num": n, "den": d})
}

/// A signed pair (site R10): [`nat_pair_of`] with its sign beside it.
fn signed_pair_of((neg, n, d): &(bool, String, String)) -> Value {
    let mut v = nat_pair_of((n.clone(), d.clone()));
    v["neg"] = json!(neg);
    v
}

/// **The configured decimals as their files write them.** `config.toml` and
/// `.tm/model.json` are read by serde into `f64`, which rounds a literal of more
/// than 17 significant digits to its nearest double; D10 forbids rounding and
/// D17 refuses a weight of more than 18 places, so the host re-reads each
/// decimal the capacity request carries as **the literal's text** (TOML spans,
/// JSON raw values) and [`written_pair`] reads that text. A key no file writes
/// is `None` and falls back to [`decimal_pair`] of its (default) double.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Written {
    /// `.tm/model.json`'s `p_lounge`, Monday first (the last entry for a weekday wins, as in [`Model`]).
    pub model_p: [Option<String>; 7],
    /// `config.toml`'s `expected.p_lounge`, Monday first.
    pub config_p: [Option<String>; 7],
    /// `day.window_hours`.
    pub window_hours: Option<String>,
    /// `day.budget_ratio`.
    pub budget_ratio: Option<String>,
    /// `priority.bins`, index for index (`None` when the file writes no `bins`).
    pub bins: Option<Vec<String>>,
    /// `priority.safety`.
    pub safety: Option<String>,
    /// Each `energy.prior.<curve>` range key as written: `(curve, key)`.
    pub prior_keys: Vec<(String, String)>,
    /// `energy.posterior_full_hours` (stage 6 L9, site R5).
    pub posterior_full_hours: Option<String>,
    /// `energy.posterior_zero_hours`.
    pub posterior_zero_hours: Option<String>,
    /// `energy.sleep_debt.under_hours` (site R10's comparison).
    pub sleep_under_hours: Option<String>,
    /// `energy.sleep_debt.shift` (site R10).
    pub sleep_shift: Option<String>,
    /// `.tm/model.json`'s fitted `sleep_debt_shift`, when the file writes one.
    pub model_sleep_shift: Option<String>,
}

/// The shadow of `config.toml` that keeps the literals (every other key ignored).
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct CfgText {
    expected: ExpectedText,
    day: DayText,
    priority: PriorityText,
    energy: EnergyText,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct ExpectedText {
    p_lounge: BTreeMap<String, toml::Spanned<toml::Value>>,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct DayText {
    window_hours: Option<toml::Spanned<toml::Value>>,
    budget_ratio: Option<toml::Spanned<toml::Value>>,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct PriorityText {
    bins: Option<Vec<toml::Spanned<toml::Value>>>,
    safety: Option<toml::Spanned<toml::Value>>,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct EnergyText {
    prior: BTreeMap<String, BTreeMap<String, toml::Value>>,
    posterior_full_hours: Option<toml::Spanned<toml::Value>>,
    posterior_zero_hours: Option<toml::Spanned<toml::Value>>,
    sleep_debt: SleepDebtText,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct SleepDebtText {
    under_hours: Option<toml::Spanned<toml::Value>>,
    shift: Option<toml::Spanned<toml::Value>>,
}

/// The shadow of `.tm/model.json`: `p_lounge`'s entries in file order, as raw text.
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct ModelText {
    #[serde(deserialize_with = "raw_entries")]
    p_lounge: Vec<(String, Box<serde_json::value::RawValue>)>,
    sleep_debt_shift: Option<Box<serde_json::value::RawValue>>,
}

/// A JSON object's entries in file order, each value's raw text.
fn raw_entries<'de, D: serde::Deserializer<'de>>(
    d: D,
) -> Result<Vec<(String, Box<serde_json::value::RawValue>)>, D::Error> {
    struct V;
    impl<'de> serde::de::Visitor<'de> for V {
        type Value = Vec<(String, Box<serde_json::value::RawValue>)>;
        fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.write_str("a table keyed by weekday")
        }
        fn visit_map<A: serde::de::MapAccess<'de>>(self, mut m: A) -> Result<Self::Value, A::Error> {
            let mut out = Vec::new();
            while let Some(e) = m.next_entry()? {
                out.push(e);
            }
            Ok(out)
        }
    }
    d.deserialize_map(V)
}

/// The weekday index (Monday 0) of a key [`Model`] and [`Config`] accept.
fn weekday_slot(key: &str) -> Option<usize> {
    energy::parse_weekday_key(key).map(|wd| wd.num_days_from_monday() as usize)
}

impl Written {
    /// **Read the literals** of `config.toml` (`None` when absent) and
    /// `.tm/model.json` (`None` when absent): the texts the host parsed.
    pub fn parse(config: Option<&str>, model: Option<&str>) -> Result<Written, InputDefect> {
        let mut w = Written::default();
        if let Some(text) = config {
            let c: CfgText = toml::from_str(text)
                .map_err(|e| InputDefect(format!("{CONFIG_FILE}: {e}")))?;
            let lit = |v: &toml::Spanned<toml::Value>| text.get(v.span()).unwrap_or_default().to_string();
            for (k, v) in &c.expected.p_lounge {
                if let Some(i) = weekday_slot(k) {
                    w.config_p[i] = Some(lit(v));
                }
            }
            w.window_hours = c.day.window_hours.as_ref().map(lit);
            w.budget_ratio = c.day.budget_ratio.as_ref().map(lit);
            w.bins = c.priority.bins.as_ref().map(|b| b.iter().map(lit).collect());
            w.safety = c.priority.safety.as_ref().map(lit);
            for (curve, keys) in &c.energy.prior {
                w.prior_keys.extend(keys.keys().map(|k| (curve.clone(), k.clone())));
            }
            w.posterior_full_hours = c.energy.posterior_full_hours.as_ref().map(lit);
            w.posterior_zero_hours = c.energy.posterior_zero_hours.as_ref().map(lit);
            w.sleep_under_hours = c.energy.sleep_debt.under_hours.as_ref().map(lit);
            w.sleep_shift = c.energy.sleep_debt.shift.as_ref().map(lit);
        }
        if let Some(text) = model {
            let m: ModelText = serde_json::from_str(text)
                .map_err(|e| InputDefect(format!("{MODEL_FILE}: {e}")))?;
            for (k, v) in &m.p_lounge {
                if let Some(i) = weekday_slot(k) {
                    w.model_p[i] = Some(v.get().to_string());
                }
            }
            w.model_sleep_shift = m.sleep_debt_shift.as_ref().map(|v| v.get().to_string());
        }
        Ok(w)
    }
}

/// **The text a configured value is sent as**: its file's literal when the file
/// writes one, else its double's shortest text. A literal whose nearest double is
/// not (within one step of) the value the host loaded means the file changed while
/// the verb ran, and the verb stops rather than send one value and plan another.
fn text_of(file: &str, key: &str, written: Option<&str>, x: f64) -> Result<String, InputDefect> {
    let Some(lit) = written else {
        return Ok(format!("{x}"));
    };
    let parsed: Option<f64> = lit.trim().replace('_', "").parse().ok();
    let same = parsed.is_some_and(|p| {
        (p.is_nan() && x.is_nan()) || p == x || p.to_bits().abs_diff(x.to_bits()) <= 1
    });
    if !same {
        return Err(InputDefect(format!(
            "{file}: {key} = {lit} changed while tm was reading it; run the verb again"
        )));
    }
    Ok(lit.trim().to_string())
}

/// The failure of a configured value, by file and key, quoting its written text.
fn bad_value(file: &str, key: &str, text: &str, why: &str) -> InputDefect {
    InputDefect(format!(
        "{file}: {key} = {text} {why}; tm cannot compute capacity or priorities until it is fixed \
         (kernel/README.md parity P26)"
    ))
}

/// A pair's refusal, in words.
fn pair_why(e: PairErr, places: u32) -> String {
    match e {
        PairErr::NotFinite => "is not a number".to_string(),
        PairErr::Negative => "is below zero".to_string(),
        PairErr::TooManyPlaces(usize::MAX) => format!("has too many decimal places (at most {places})"),
        PairErr::TooManyPlaces(n) => format!("has {n} decimal places (at most {places})"),
    }
}

/// **A lounge weight**, as written: a decimal of at most 18 places in `[0, 1]`.
/// Returns its pair.
fn check_weight(file: &str, key: &str, written: Option<&str>, x: f64) -> Result<(String, String), InputDefect> {
    let text = text_of(file, key, written, x)?;
    let (n, d) = match written_pair(&text, WEIGHT_PLACES) {
        Err(PairErr::Negative) => return Err(bad_value(file, key, &text, "is outside [0, 1]")),
        Err(e) => return Err(bad_value(file, key, &text, &pair_why(e, WEIGHT_PLACES))),
        Ok(p) => p,
    };
    if above_one(&n, &d) {
        return Err(bad_value(file, key, &text, "is outside [0, 1]"));
    }
    Ok((n, d))
}

/// A configured decimal of `config.toml` with at most `places` places, as written.
fn check_places(key: &str, written: Option<&str>, x: f64, places: u32) -> Result<(String, String), InputDefect> {
    let text = text_of(CONFIG_FILE, key, written, x)?;
    written_pair(&text, places).map_err(|e| bad_value(CONFIG_FILE, key, &text, &pair_why(e, places)))
}

/// Every configured decimal the request carries, as the pairs it sends.
struct Pairs {
    model_p: [Option<(String, String)>; 7],
    config_p: [(String, String); 7],
    window_hours: (String, String),
    budget_ratio: (String, String),
    bins: Vec<(String, String)>,
    safety: (String, String),
    /// Stage 6 L9, site R5: `energy.posterior_full_hours` and `posterior_zero_hours`.
    posterior_full: (String, String),
    posterior_zero: (String, String),
    /// Stage 6 L9, site R10: `energy.sleep_debt.under_hours`, and the two shifts (signed).
    sleep_under: (String, String),
    sleep_shift: (bool, String, String),
    model_sleep_shift: Option<(bool, String, String)>,
}

/// A **signed** configured decimal of a file, as written (site R10).
fn check_signed(file: &str, key: &str, written: Option<&str>, x: f64, places: u32)
    -> Result<(bool, String, String), InputDefect> {
    let text = text_of(file, key, written, x)?;
    signed_written_pair(&text, places).map_err(|e| bad_value(file, key, &text, &pair_why(e, places)))
}

/// The checks of [`check_inputs`], keeping the pairs they read.
fn pairs_of(cfg: &Config, model: &Model, written: &Written) -> Result<Pairs, InputDefect> {
    let mut model_p: [Option<(String, String)>; 7] = Default::default();
    for (wd, x) in model.p_lounge.iter() {
        let i = wd.num_days_from_monday() as usize;
        let key = format!("p_lounge.{}", energy::weekday_key(wd));
        model_p[i] = Some(check_weight(MODEL_FILE, &key, written.model_p[i].as_deref(), *x)?);
    }
    let mut config_p: Vec<(String, String)> = Vec::with_capacity(7);
    for (i, wd) in WEEK.iter().enumerate() {
        let key = format!("expected.p_lounge.{}", energy::weekday_key(*wd));
        config_p.push(check_weight(CONFIG_FILE, &key, written.config_p[i].as_deref(), *cfg.expected.p_lounge.get(*wd))?);
    }
    let config_p: [(String, String); 7] = config_p.try_into().unwrap_or_else(|_| Default::default());
    let window_hours = check_places("day.window_hours", written.window_hours.as_deref(), cfg.day.window_hours, RATIO_PLACES)?;
    let budget_ratio = check_places("day.budget_ratio", written.budget_ratio.as_deref(), cfg.day.budget_ratio, RATIO_PLACES)?;
    let mut bins = Vec::with_capacity(cfg.priority.bins.len());
    for (i, edge) in cfg.priority.bins.iter().enumerate() {
        let lit = written.bins.as_ref().and_then(|b| b.get(i)).map(String::as_str);
        bins.push(check_places(&format!("priority.bins[{i}]"), lit, *edge, PRIORITY_PLACES)?);
    }
    let safety = check_places("priority.safety", written.safety.as_deref(), cfg.priority.safety, PRIORITY_PLACES)?;
    // Stage 6 L9: the four `[energy]` decimals day 0 reads (design §13.5 says two; the repo has
    // four, and the model's fitted shift is a fifth).  The shift is signed: §8.5 fits it as a mean.
    let posterior_full = check_places(
        "energy.posterior_full_hours", written.posterior_full_hours.as_deref(), cfg.energy.posterior_full_hours, RATIO_PLACES)?;
    let posterior_zero = check_places(
        "energy.posterior_zero_hours", written.posterior_zero_hours.as_deref(), cfg.energy.posterior_zero_hours, RATIO_PLACES)?;
    let sleep_under = check_places(
        "energy.sleep_debt.under_hours", written.sleep_under_hours.as_deref(), cfg.energy.sleep_debt.under_hours, RATIO_PLACES)?;
    let sleep_shift = check_signed(
        CONFIG_FILE, "energy.sleep_debt.shift", written.sleep_shift.as_deref(), cfg.energy.sleep_debt.shift, RATIO_PLACES)?;
    let model_sleep_shift = match model.sleep_debt_shift {
        None => None,
        Some(x) => Some(check_signed(MODEL_FILE, "sleep_debt_shift", written.model_sleep_shift.as_deref(), x, RATIO_PLACES)?),
    };
    // The prior's range keys, as written.  At most 6 places and at most 48 hours,
    // a key has at most 8 significant digits, so its double's shortest text is
    // exactly the written decimal and the request may send the double's pair.
    for (curve, key) in &written.prior_keys {
        let name = format!("energy.prior.{curve}.\"{key}\"");
        let parts: Vec<&str> = match key.strip_suffix('+') {
            Some(a) => vec![a],
            None => key.split_once('-').map(|(a, b)| vec![a, b]).unwrap_or_default(),
        };
        for part in parts {
            written_pair(part, RATIO_PLACES).map_err(|e| bad_value(CONFIG_FILE, &name, part.trim(), &pair_why(e, RATIO_PLACES)))?;
        }
    }
    for (curve, steps) in &cfg.energy.prior {
        for step in &steps.0 {
            let key = format!("energy.prior.{curve}.\"{}\"", crate::config::StepFn::key(step));
            check_places(&key, None, step.from, RATIO_PLACES)?;
            if let Some(to) = step.to {
                check_places(&key, None, to, RATIO_PLACES)?;
            }
        }
    }
    Ok(Pairs { model_p, config_p, window_hours, budget_ratio, bins, safety,
        posterior_full, posterior_zero, sleep_under, sleep_shift, model_sleep_shift })
}

/// **Every configured decimal the capacity request carries, checked before it is
/// built, as its file writes it** (`written`; D10, D17): the model's and the
/// config's lounge weights (§13.2: every pair is sent, so both are checked),
/// `[day]`'s two ratios, `[priority]`'s edges and safety, and the prior's range
/// keys. The message names the file and the key and quotes the written text.
pub fn check_inputs(cfg: &Config, model: &Model, written: &Written) -> Result<(), InputDefect> {
    pairs_of(cfg, model, written).map(|_| ())
}

/// **The lookahead's length** for `want` days from `today`: at most
/// [`MAX_LOOKAHEAD_DAYS`], never past 9999-12-31, at least one. Returns the
/// days and whether it clamped (README gap 98, parity P30).
pub fn horizon(today: NaiveDate, want: u32) -> (u32, bool) {
    let last = NaiveDate::from_ymd_opt(9999, 12, 31).unwrap_or(NaiveDate::MAX);
    let to_end = u32::try_from((last - today).num_days() + 1).unwrap_or(0);
    let days = want.min(MAX_LOOKAHEAD_DAYS).min(to_end).max(1);
    (days, days < want)
}

/// The ranking half of a request: the candidates in the fork's service order,
/// and yesterday's priorities.
pub struct Ranked<'a> {
    /// The candidates, in `priority::collect_candidates` order.
    pub cands: &'a [Candidate],
    /// §7.4's comparison map (`Ctx::hysteresis_input`).
    pub yesterday: &'a BTreeMap<Id, u8>,
}

/// **The order the candidates are sent in**: the fork's `(effective_due,
/// own_order, index)` (`priority::compute`'s sort), so the kernel's stable sort
/// by due date serves a date's deadlines in the fork's order (P12 does not
/// bite). Undated candidates follow, in their own order.
pub fn send_order(cands: &[Candidate]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..cands.len()).collect();
    order.sort_by(|&a, &b| {
        let (ca, cb) = (&cands[a], &cands[b]);
        (ca.effective_due.is_none(), ca.effective_due, ca.own_order, a)
            .cmp(&(cb.effective_due.is_none(), cb.effective_due, cb.own_order, b))
    });
    order
}

/// One candidate record (Boundary.lean's `readCand`, `readFloor`).
///
/// **The nine facts D27 has not yet moved into the kernel cross here**, and
/// this is where they are pinned:
/// `the_candidate_facts_cross_the_wire_as_the_host_computed_them` below drives
/// exactly this function. Until W-16's repair step nothing did — inverting one
/// line of it (`"overdue": !c.overdue`) left the whole workspace suite green at
/// 1,323 passed while visibly re-ranking `tm plan`'s dropped list — so the host
/// computed the values with no test pinning them and the kernel read them as
/// given (`Boundary.readCand`). Gap 577 records what is still owed; this at
/// least makes a wrong *copy* a failing test.
///
/// `root_prio` and `today` are parameters rather than lookups so the mapping
/// can be driven without a loaded tree.
fn cand_json(
    root_prio: Option<u8>,
    today: NaiveDate,
    c: &Candidate,
    yesterday: &BTreeMap<Id, u8>,
) -> Result<Value, InputDefect> {
    let floor = c.floor.as_ref().map(|r| {
        json!({
            "left": r.amount.as_minutes().saturating_sub(c.floor_done_min),
            "until": priority::period_range(r.per, today).1.to_string(),
        })
    });
    Ok(json!({
        "id": c.id.as_str(),
        "ci": c.ci,
        "rootPrio": root_prio,
        "remaining": c.remaining_min,
        "due": c.effective_due.map(|d| d.date_naive().to_string()),
        "window": c.window.is_some(),
        "wall": c.is_wall,
        "optional": c.is_optional,
        "overdue": c.overdue,
        "mandatory": c.mandatory,
        "hot": c.hot,
        "yesterday": yesterday.get(&c.id),
        "floor": floor,
        "plan": plan_json(c)?,
    }))
}

/// **§8.2 step 5's nine**, beside §7's twelve (`Look.PlanFacts`, kernel/README.md gap 606).
///
/// These are what `Planner::build_groups`, `Planner::pick` and
/// [`priority::sorted_candidates`]' own filter read off a [`Candidate`] and no
/// kernel call carried before stage 6 P5a. They are **host-collected, exactly
/// as the twelve above are**: D34 keeps `collect_candidates` alive until R3, so
/// D27 later changes where they come from, not what they are.
///
/// `waiting` is **not** a tenth: `collect_candidates` sets it to `state ==
/// State::Waiting`, and the kernel derives it from `state`
/// (`Look.PlanFacts.waiting`).
///
/// The multiplier is a written `.tm/model.json` decimal and crosses as the
/// exact pair every configured decimal crosses as (D17) — the kernel holds no
/// `Float`. A multiplier that is not an exact decimal of at most
/// [`PRIORITY_PLACES`] places is named here rather than rounded.
fn plan_json(c: &Candidate) -> Result<Value, InputDefect> {
    let text = format!("{}", c.multiplier);
    let mul = written_pair(&text, PRIORITY_PLACES).map_err(|e| {
        bad_value(MODEL_FILE, &format!("duration multiplier for {}", c.id.token()), &text,
            &pair_why(e, PRIORITY_PLACES))
    })?;
    Ok(json!({
        "plannedMin": c.planned_min,
        "multiplier": nat_pair_of(mul),
        "loc": c.loc.as_str(),
        "splittable": c.splittable,
        "cap": c.cap.as_ref().map(|r| json!({
            "capMin": r.amount.as_minutes(),
            "doneMin": c.cap_done_min,
        })),
        "state": c.state.glyph().to_string(),
        "blockedBy": c.blocked_by.iter().map(|d| d.to_string()).collect::<Vec<String>>(),
        "wallToday": c.wall_today,
    }))
}

/// **Everything the capacity section is built from** — what `kernel_capacity::request`
/// reads off its `Ctx`, handed in, so a test builds the section the binary sends from the
/// same values (README gap 2875).
pub struct CapacityIn<'a> {
    /// `config.toml` (§16).
    pub cfg: &'a Config,
    /// `.tm/model.json`.
    pub model: &'a Model,
    /// The literals of both files ([`Written::parse`]); `Written::default()` when the
    /// caller holds no file text, and every value is then sent as its double's text.
    pub written: &'a Written,
    /// The tree, for each candidate's root `!k`.
    pub tree: &'a Tree,
    /// `.tm/state.json`.
    pub state: &'a RuntimeState,
    /// The instant the verb runs at, in the configured zone (`Ctx::now_tz`): `at`,
    /// and its local date is the request's today.
    pub now: DateTime<Tz>,
    /// The current location (`Ctx::loc`).
    pub loc: Loc,
    /// `tm plan --allow-home`.
    pub allow_home: bool,
    /// The lookahead's length, already through [`horizon`].
    pub days: u32,
}

/// **The capacity section** the binary sends (`Boundary.readSection`, `readCands`):
/// both weekday tables raw (the kernel picks, D10-4), today's `wake` (`state.json`'s clock,
/// else the literal `"log"` — the fork's precedence, gap 261), the learned curves, the
/// prior, `[day]`, `[priority]` with `batchMaxMin`, `days`, and day 0's own host-only facts
/// — `at`, `state`, `posterior`, `sleep` — with the candidates when priorities are asked
/// for, in [`send_order`] (their facts are the host's, gap 113).
pub fn capacity_json(input: &CapacityIn<'_>, ranked: Option<&Ranked<'_>>) -> Result<Value, InputDefect> {
    // Every configured decimal as its file writes it (D10, D17): checked, then sent.
    let pairs = pairs_of(input.cfg, input.model, input.written)?;
    let cfg = input.cfg;
    let model = input.model;
    let state = input.state;
    let today = input.now.date_naive();
    let wd_slot = |wd: chrono::Weekday| wd.num_days_from_monday() as usize;
    let week_table = |f: &dyn Fn(chrono::Weekday) -> Option<Value>| -> Map<String, Value> {
        WEEK.iter().filter_map(|wd| f(*wd).map(|v| (energy::weekday_key(*wd).to_string(), v))).collect()
    };
    let p_model = week_table(&|wd| pairs.model_p[wd_slot(wd)].as_ref().map(str_pair_of));
    let p_config = week_table(&|wd| Some(str_pair_of(&pairs.config_p[wd_slot(wd)])));
    let a_model = week_table(&|wd| model.expected_arrival.get(wd).map(|t| json!(fmt_time(t.0))));
    let a_config = week_table(&|wd| Some(json!(fmt_time(*cfg.expected.arrival.get(wd)))));
    let curves: Map<String, Value> = LOCATIONS
        .iter()
        .filter_map(|loc| model.energy.get(*loc).map(|c| (loc.to_string(), json!(c))))
        .collect();
    // The prior's keys: checked as written by `pairs_of`, and exactly their doubles' text.
    let pair = |x: f64, places: u32| decimal_pair(x, places).map(nat_pair_of).unwrap_or(Value::Null);
    let prior: Map<String, Value> = cfg
        .energy
        .prior
        .iter()
        .map(|(curve, steps)| {
            let steps: Vec<Value> = steps
                .0
                .iter()
                .map(|s| {
                    json!({"from": pair(s.from, RATIO_PLACES), "to": s.to.map(|t| pair(t, RATIO_PLACES)), "level": s.level})
                })
                .collect();
            (curve.clone(), Value::Array(steps))
        })
        .collect();
    // `Ctx::logged_wake` is `state.wake`, else the replay's `wake` of today.  The first disjunct
    // is `state.json`'s and the host sends it; the second is the kernel's own fact, and since D24
    // the kernel reads it off this call's replay rather than being told (`"log"`).  Sending the
    // clock when `state.wake` is set and `"log"` otherwise **is** the fork's precedence, written
    // down here because kernel/README.md gap 261 said it was written down nowhere.
    let wake = match state.wake {
        Some(t) => json!({"sec": t.num_seconds_from_midnight(), "ns": t.nanosecond()}),
        None => json!("log"),
    };
    let mut section = json!({
        "pLounge": {"model": p_model, "config": p_config},
        "arrival": {"model": a_model, "config": a_config},
        "wake": wake,
        "energy": curves,
        "prior": prior,
        "homeMaxCi": cfg.location.home_max_ci,
        "day": {
            "breakMin": cfg.day.break_min,
            "breakAfterBlocks": cfg.day.break_after_blocks,
            "minLastBlockMin": cfg.day.min_last_block_min,
            "windowHours": nat_pair_of(pairs.window_hours.clone()),
            "windowCap": fmt_time(cfg.day.window_cap),
            "budgetRatio": nat_pair_of(pairs.budget_ratio.clone()),
            // Stage 6 step P2: `[day]`'s evening half.  §8.2 step 2 states "sleep and wind-down
            // define the hard end of the day" over exactly these two keys, and the kernel reads
            // `[day]` in one place (`Look.DayCfg`), so the whole section crosses -- sending half
            // of it was what let the planner keep a second copy.
            "windDown": fmt_time(cfg.day.wind_down),
            "bed": fmt_time(cfg.day.bed),
        },
        "priority": {
            "bins": Value::Array(pairs.bins.iter().map(|b| nat_pair_of(b.clone())).collect()),
            "safety": nat_pair_of(pairs.safety.clone()),
            "defaultPriority": cfg.priority.default_priority,
        },
        "days": input.days,
        // Stage 6 step L9 (gap 93): day 0 is the kernel's own.  What crosses is what only the host
        // knows — the instant the verb ran, `.tm/state.json`'s runtime facts and the CLI flag —
        // plus the `[energy]` decimals the posterior and the sleep debt read.  Today's sleep and
        // energy reports do **not** cross: the kernel reads them off the `log` section.
        "at": crate::log::fmt_timestamp(&input.now.fixed_offset()),
        "state": {
            "date": state.date.map(|d| d.to_string()),
            "window": state.window.map(|(f, t)| json!({"from": fmt_time(f), "to": fmt_time(t)})),
            "budget": state.budget,
            "arrival": state.arrival.map(fmt_time),
            "loc": input.loc.as_str(),
            "allowHome": input.allow_home,
        },
        "posterior": {
            "fullHours": nat_pair_of(pairs.posterior_full.clone()),
            "zeroHours": nat_pair_of(pairs.posterior_zero.clone()),
        },
        "sleep": {
            "shiftModel": pairs.model_sleep_shift.as_ref().map(signed_pair_of),
            "shiftConfig": signed_pair_of(&pairs.sleep_shift),
            "underHours": nat_pair_of(pairs.sleep_under.clone()),
        },
    });
    // §16's `[priority] batch_max_min`, which the planner section reads off this object
    // (`PlanWire.readBatchMaxMin`). README gap 2875: the request the binary sent lacked it, so a
    // `planner` section beside it — R3's — would have been refused `badPriority batchMaxMin`.
    add_batch_max_min(&mut section, cfg);
    if let Some(r) = ranked {
        let items = send_order(r.cands)
            .iter()
            .map(|&i| {
                let c = &r.cands[i];
                let root_prio = input.tree.get(&input.tree.root(&c.id)).and_then(|t| t.priority);
                cand_json(root_prio, today, c, r.yesterday)
            })
            .collect::<Result<Vec<Value>, InputDefect>>()?;
        section["candidates"] = json!({"hysteresis": cfg.priority.hysteresis, "items": Value::Array(items)});
    }
    Ok(section)
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
///
/// **A record's start is never sent after `now`** (W-40 track E, README gap
/// 2874): a `tm start` stamped by a clock ahead of this one (a synced machine)
/// or a `--now` before the stored start leaves `started` in the future, which
/// the fork reads as nothing worked yet (`active_run`'s `.max(0)`) and the
/// kernel refuses (`Planner.ActiveBlock.wf`, `badActive wf`; the break's and the
/// interruption's `wf` alike). Sent as `now`, the block has worked nothing and
/// its row starts at `now` — the fork's reading of both. This is a reading of
/// two instants, not a bound: no number of the kernel's is written here. What
/// it does NOT reproduce is the fork's END of that row: fork
/// `current_block_end` ends it at `started + block_min`, the kernel at `now +
/// block_min`, so a row whose estimate outlasts the block is shorter by the
/// skew (README gap 3905, a divergence for the Land step to number).
pub fn state_json(state: &RuntimeState, date: NaiveDate, now: DateTime<Tz>, tz: Tz) -> Value {
    let at_most_now = |t: NaiveTime| clock_sec(tz, date, t).min(kernel_sec(now));
    let mut o = Map::new();
    if let Some(a) = &state.active {
        o.insert(
            "active".to_string(),
            json!({"id": a.id.as_str(), "started": at_most_now(a.started),
                   "estMin": a.est_min, "paused": a.paused}),
        );
    }
    if let Some(b) = &state.break_ {
        o.insert(
            "break".to_string(),
            json!({"started": b.started.map(at_most_now),
                   "plannedMin": b.planned_min, "place": b.place}),
        );
    }
    if let Some(i) = &state.interrupt {
        o.insert(
            "interrupt".to_string(),
            json!({"started": i.started.map(at_most_now),
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
        // **An instance with nothing left of its span is not sent** (W-37 track R,
        // README gap 3201). A daily window that closed before `now` — `lunch`'s
        // 11:30–13:30 on an afternoon it was not logged done — leaves `from ==
        // to` above. Fork `collect_routines` keeps such an instance and then
        // passes over it everywhere (steps 2 and 6 skip `span.1 <= from`, the
        // notes loop skips it, and it draws no row), while the kernel refuses it
        // by name (`routineRefused emptyWindow`), so sending it refused the whole
        // day. Not sending it changes no day the kernel answered before.
        if to <= from {
            continue;
        }
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
/// the extended item the commitment fork `apply` gives it. `need_min` is NOT
/// sent (W-36 land, README gap 3120, closing track K's host half of gap 3004):
/// no reader of the day reads a need but §7.3's pass, which derives its own
/// from `remaining`, and check 13's sent half fails on a key the host writes
/// and no kernel reader decodes. `Grown::need_min` stays, as fork `apply`'s
/// arithmetic written down (`the_grown_facts_are_apply_s_by_value`).
pub fn overtime_json(id: &Id, blocks: u32, grown: Option<&Grown>) -> Value {
    let mut o = json!({"id": id.as_str(), "blocks": blocks});
    if let Some(g) = grown {
        o["grown"] = json!({"remaining": g.remaining_min, "plannedMin": g.planned_min});
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
    let mut o = json!({"state": state_json(state, date, now, tz), "routines": routines_json(routines)});
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
/// power of ten ([`written_pair`], this module's since W-40), and the kernel may reduce the
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
        "paused" => crate::dayplan::PAUSED_NOTE.to_string(),
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

    // **Why step 5 left an impossible item without a row** (the owner's D67,
    // parity P58): the kernel's `unplaced`, `{id, why}`, a reason by its wire
    // name (`PlanWire.noPlaceName`). Every item it names is one the impossible
    // list names — the kernel names only listed items — and a name this host
    // cannot read is refused, never guessed. Ordered as `impossible` is.
    let mut unplaced = array(&v["unplaced"], &at("unplaced"))?
        .iter()
        .enumerate()
        .map(|(i, x)| {
            let what = format!("{}[{i}]", at("unplaced"));
            let id = Id::new(text(&x["id"], &format!("{what}.id"))?);
            let name = text(&x["why"], &format!("{what}.why"))?;
            let why = NoPlace::of_wire(name)
                .ok_or_else(|| WireDefect::at(format!("{what}.why: `{name}` is no reason the kernel names")))?;
            if !impossible.iter().any(|(k, _, _)| *k == id) {
                return Err(WireDefect::at(format!(
                    "{what}: `{}` is not on the impossible list",
                    id.as_str()
                )));
            }
            Ok((id, why))
        })
        .collect::<W<Vec<_>>>()?;
    unplaced.sort_by_key(|(id, _)| rank(id));

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
        unplaced,
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

    /// [`written_pair`]'s shape: the shortest decimal of the
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
                "restDebtMin": 10,
                "unplaced": day.diagnostics.unplaced.iter()
                    .map(|(i, w)| json!({"id": i.as_str(), "why": w.wire_name()})).collect::<Vec<_>>()},
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
            unplaced: vec![(Id::new("d1"), NoPlace::NoRunLeft)],
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
        // D67 (P58): a reason the kernel does not name, and a name for an item
        // the impossible list does not hold, are refused by name.
        let mut bent = v.clone();
        bent["diagnostics"]["unplaced"] = json!([{"id": "d1", "why": "tired"}]);
        assert!(read_plan(&bent, &ctx).unwrap_err().0.contains("`tired` is no reason the kernel names"));
        let mut bent = v.clone();
        bent["diagnostics"]["unplaced"] = json!([{"id": "m1", "why": "budgetSpent"}]);
        assert!(read_plan(&bent, &ctx).unwrap_err().0.contains("`m1` is not on the impossible list"));
        // Every reason reads back as itself.
        for w in [NoPlace::NoRunLeft, NoPlace::NoSlotLeft, NoPlace::BudgetSpent, NoPlace::NoSlotAdmits] {
            let mut named = v.clone();
            named["diagnostics"]["unplaced"] = json!([{"id": "d1", "why": w.wire_name()}]);
            assert_eq!(read_plan(&named, &ctx).expect("reads").day.diagnostics.unplaced, vec![(Id::new("d1"), w)]);
        }
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
            json!({"id": "t3", "blocks": 2, "grown": {"remaining": 120, "plannedMin": 192}}),
            "the grown facts the kernel reads, and no need it does not (README gap 3120)"
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
        let v = state_json(&state, date, at(23, 0), tz());
        assert_eq!(v["active"], json!({"id": "m1", "started": kernel_sec(at(9, 5)), "estMin": 60, "paused": false}));
        assert_eq!(v["break"], json!({"started": kernel_sec(at(10, 0)), "plannedMin": 20, "place": "walk"}));
        assert_eq!(v["interrupt"], json!({"started": null, "id": "m1"}));
        // Read by no definition of the day (kernel/inputs-exempt.txt): not sent.
        assert!(v.get("lastHash").is_none() && v.get("yesterday").is_none(), "{v}");
        assert_eq!(state_json(&RuntimeState::default(), date, at(23, 0), tz()), json!({}));
        // The planned date is `state.date`, else `now`'s.
        assert_eq!(plan_date(&state, at(23, 0) + Duration::days(3)), date);
        assert_eq!(plan_date(&RuntimeState::default(), at(23, 0)), date);
    }

    /// **A start after `now` is sent as `now`** (W-40 track E, README gap 2874):
    /// a `tm start` stamped by a clock ahead of this one, or a `--now` before the
    /// stored start, is a block that has worked nothing — the fork's reading — and
    /// not a request the kernel refuses `badActive wf`. A start at or before `now`
    /// is sent as it is.
    #[test]
    fn a_running_record_never_starts_after_now() {
        use crate::store::{ActiveBlock, BreakState, InterruptState};
        let date = NaiveDate::from_ymd_opt(2026, 9, 7).expect("date");
        let t = |h, m| NaiveTime::from_hms_opt(h, m, 0).expect("t");
        let state = RuntimeState {
            date: Some(date),
            active: Some(ActiveBlock { id: Id::new("t4"), started: t(10, 0), est_min: 60, paused: false }),
            break_: Some(BreakState { started: Some(t(10, 5)), planned_min: 20, place: None }),
            interrupt: Some(InterruptState { started: Some(t(9, 50)), id: None }),
            ..RuntimeState::default()
        };
        let now = at(9, 55);
        let v = state_json(&state, date, now, tz());
        assert_eq!(v["active"]["started"], json!(kernel_sec(now)), "after now: sent as now");
        assert_eq!(v["break"]["started"], json!(kernel_sec(now)), "after now: sent as now");
        assert_eq!(v["interrupt"]["started"], json!(kernel_sec(at(9, 50))), "before now: as stored");
        let later = state_json(&state, date, at(11, 0), tz());
        assert_eq!(later["active"]["started"], json!(kernel_sec(at(10, 0))), "before now: as stored");
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

    /// **The capacity section the binary sends, key for key** (W-40 track E, README
    /// gap 2875): every key `Boundary.readSection` reads, `priority.batchMaxMin` beside
    /// the three `CapWire.readPriority` reads (the planner section's one key here,
    /// `PlanWire.readBatchMaxMin`), and the candidates only when priorities are asked.
    /// The values the binary sends are `Ctx`'s, so a constant section, a dropped
    /// table or a lost `batchMaxMin` fails here before it fails at the kernel.
    #[test]
    fn the_capacity_section_carries_the_keys_the_kernel_reads() {
        let mut cfg = Config::default();
        cfg.priority.batch_max_min = 35;
        let tree = Tree::from_texts(&[], &cfg);
        let state = RuntimeState { loc: Some("home".to_string()), budget: Some(5), ..RuntimeState::default() };
        let (model, written) = (Model::default(), Written::default());
        let input = CapacityIn {
            cfg: &cfg, model: &model, written: &written, tree: &tree, state: &state,
            now: at(9, 30), loc: Loc::Home, allow_home: true, days: 12,
        };
        let bare = capacity_json(&input, None).expect("a default configuration is carried");
        let keys = |v: &Value| -> Vec<String> {
            let mut k: Vec<String> = v.as_object().expect("an object").keys().cloned().collect();
            k.sort();
            k
        };
        assert_eq!(
            keys(&bare),
            ["arrival", "at", "day", "days", "energy", "homeMaxCi", "pLounge", "posterior", "prior",
             "priority", "sleep", "state", "wake"],
        );
        assert_eq!(keys(&bare["priority"]), ["batchMaxMin", "bins", "defaultPriority", "safety"]);
        assert_eq!(bare["priority"]["batchMaxMin"], json!(35), "the configured value, not a default");
        assert_eq!(bare["days"], json!(12));
        assert_eq!(bare["at"], json!("2026-09-07T09:30:00-05:00"));
        assert_eq!(bare["state"]["loc"], json!("home"));
        assert_eq!(bare["state"]["allowHome"], json!(true));
        assert_eq!(bare["state"]["budget"], json!(5));
        assert_eq!(bare["wake"], json!("log"), "no stored wake: the kernel's own (D24)");
        assert_eq!(keys(&bare["pLounge"]["config"]), ["Fri", "Mon", "Sat", "Sun", "Thu", "Tue", "Wed"]);
        // With candidates: the record per candidate, in `send_order`.
        let later = Candidate::new(Id::new("b2"), 0, 1, 30, &cfg);
        let mut sooner = Candidate::new(Id::new("a1"), 0, 1, 30, &cfg);
        sooner.effective_due = Some(at(18, 0));
        let cands = [later, sooner];
        let yesterday = BTreeMap::new();
        let ranked = capacity_json(&input, Some(&Ranked { cands: &cands, yesterday: &yesterday })).expect("carried");
        assert_eq!(keys(&ranked["candidates"]), ["hysteresis", "items"]);
        let ids: Vec<&str> = ranked["candidates"]["items"].as_array().expect("items").iter()
            .map(|c| c["id"].as_str().expect("an id")).collect();
        assert_eq!(ids, ["a1", "b2"], "the dated candidate is sent first (send_order)");
        assert_eq!(send_order(&cands), [1, 0]);
    }

    /// **The capacity section's encoder, moved from `tm/src/cli/kernel_capacity.rs`
    /// with its tests** (W-40 track E, README gap 2875). The T15 proptests stayed
    /// beside the binary's caller; everything that names a private function of the
    /// encoder is here.
    mod capacity_encoder {
        use super::super::*;
        use std::collections::BTreeMap;

        /// **The nine facts the host still supplies to `Look.Cand` are pinned
        /// here** — W-16 repair, gap 577.
        ///
        /// D27 (*"the kernel collects the planning candidates"*) has not landed, so
        /// `remaining`, `ci`, `due`, `overdue`, `mandatory`, `hot`, `window`,
        /// `wall` and `optional` are still computed by `priority::collect_candidates`
        /// and copied onto the wire by [`cand_json`]. The **copy** was pinned by
        /// nothing: a W-16 auditor inverted one line of it
        /// (`"overdue": !c.overdue`) and `cargo test --workspace` stayed green at
        /// **1,323 passed / 0 failed**, while `tm plan` on a fresh `tm init
        /// --example` tree visibly re-ranked its dropped list (the overdue `d1`
        /// moved from first to tenth). `priority_plan_basic.rs` snapshots the
        /// `Candidate` *before* this function and the kernel reads whatever arrives
        /// (`Boundary.readCand`), so the step between them had no test at all.
        ///
        /// Every field is given a value distinct from its neighbours' — the six
        /// booleans are not all alike, and the run is repeated with all six
        /// inverted — so a **swap** of two of them (`hot` for `overdue`) fails, not
        /// only an inversion or a drop. The key set is compared whole, so a field
        /// the kernel's decoder wants and the host stops sending fails here rather
        /// than as a `badCandidate` at run time.
        ///
        /// This does not close gap 577: it pins the copy, not the values, and the
        /// values are still the host's. What closes it is D27.
        #[test]
        fn the_candidate_facts_cross_the_wire_as_the_host_computed_them() {
            use chrono::NaiveTime;
            use crate::capacity::local_dt;
            use crate::model::{Dep, Dur, Loc, Period, Rate, State};

            let hm = |h, m| NaiveTime::from_hms_opt(h, m, 0).unwrap();

            let today = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
            let tz = chrono_tz::Tz::America__Chicago;
            let cfg = Config::default();

            let mut c = Candidate::new(Id::new("d1"), 3, 2, 95, &cfg);
            c.effective_due =
                Some(local_dt(tz, NaiveDate::from_ymd_opt(2026, 9, 11).unwrap(), hm(23, 59)));
            c.window = Some((local_dt(tz, today, hm(11, 30)), local_dt(tz, today, hm(13, 30))));
            c.floor = Some(Rate { amount: Dur::from_minutes(120), per: Period::Week });
            c.floor_done_min = 45;
            c.overdue = true;
            c.mandatory = false;
            c.hot = true;
            c.is_wall = false;
            c.is_optional = true;
            // §8.2 step 5's nine (stage 6 P5a, kernel/README.md gap 606), every one
            // a value distinct from its neighbours' and from the plain record's:
            // `capMin` differs from `doneMin`, and the two booleans disagree, so a
            // swap or a field read off another field fails here.
            c.planned_min = 152;
            c.multiplier = 1.6;
            c.loc = Loc::Out;
            c.splittable = false;
            c.cap = Some(Rate { amount: Dur::from_minutes(120), per: Period::Week });
            c.cap_done_min = 45;
            c.state = State::Waiting;
            c.blocked_by = vec![Dep::Item(Id::new("k7")), Dep::Event("visa".into())];
            c.wall_today = true;

            let yesterday: BTreeMap<Id, u8> = [(Id::new("d1"), 4u8)].into_iter().collect();

            assert_eq!(
                cand_json(Some(1), today, &c, &yesterday).expect("an exact multiplier"),
                json!({
                    "id": "d1",
                    "ci": 3,
                    "rootPrio": 1,
                    "remaining": 95,
                    "due": "2026-09-11",
                    "window": true,
                    "wall": false,
                    "optional": true,
                    "overdue": true,
                    "mandatory": false,
                    "hot": true,
                    "yesterday": 4,
                    "floor": {"left": 75, "until": "2026-09-13"},
                    "plan": {
                        "plannedMin": 152,
                        "multiplier": {"num": 16, "den": 10},
                        "loc": "out",
                        "splittable": false,
                        "cap": {"capMin": 120, "doneMin": 45},
                        "state": "?",
                        "blockedBy": ["^k7", "event:visa"],
                        "wallToday": true,
                    },
                }),
            );

            // The same candidate with every boolean the other way, and the three
            // `Option`s empty: a constant answer, or two fields read off one field,
            // cannot pass both halves.
            c.window = None;
            c.effective_due = None;
            c.floor = None;
            c.overdue = false;
            c.mandatory = true;
            c.hot = false;
            c.is_wall = true;
            c.is_optional = false;
            c.planned_min = 30;
            c.multiplier = 0.25;
            c.loc = Loc::Named("zoom".into());
            c.splittable = true;
            c.cap = None;
            c.cap_done_min = 0;
            c.state = State::Demoted;
            c.blocked_by = Vec::new();
            c.wall_today = false;
            assert_eq!(
                cand_json(None, today, &c, &BTreeMap::new()).expect("an exact multiplier"),
                json!({
                    "id": "d1",
                    "ci": 3,
                    "rootPrio": null,
                    "remaining": 95,
                    "due": null,
                    "window": false,
                    "wall": true,
                    "optional": false,
                    "overdue": false,
                    "mandatory": true,
                    "hot": false,
                    "yesterday": null,
                    "floor": null,
                    "plan": {
                        "plannedMin": 30,
                        "multiplier": {"num": 25, "den": 100},
                        "loc": "zoom",
                        "splittable": true,
                        "cap": null,
                        "state": "-",
                        "blockedBy": [],
                        "wallToday": false,
                    },
                }),
            );
        }

        /// **A multiplier that is not an exact decimal is named, not rounded**
        /// (stage 6 P5a). The kernel holds no `Float`, so §8.5's multiplier crosses
        /// as the exact pair every written decimal crosses as (D17); a
        /// `.tm/model.json` entry with more than [`PRIORITY_PLACES`] places is a
        /// value the wire cannot carry and the message says which item it belongs
        /// to.
        #[test]
        fn a_multiplier_the_wire_cannot_carry_is_named_by_item() {
            let cfg = Config::default();
            let today = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
            let mut c = Candidate::new(Id::new("d1"), 0, 1, 30, &cfg);
            c.multiplier = 1e-19;
            let err = cand_json(None, today, &c, &BTreeMap::new()).unwrap_err().to_string();
            assert!(
                err.starts_with(
                    ".tm/model.json: duration multiplier for ^d1 = 0.0000000000000000001"
                ),
                "{err}"
            );
            assert!(err.contains("decimal places (at most 18)"), "{err}");
            // And a finite, exactly written one is carried.
            c.multiplier = 2.0;
            let v = cand_json(None, today, &c, &BTreeMap::new()).expect("an exact multiplier");
            assert_eq!(v["plan"]["multiplier"], json!({"num": 2, "den": 1}));
        }

        /// Every key `Boundary.readCand` and `readFloor` ask for is a key
        /// [`cand_json`] sends, and no other (W-16 repair, gap 577).
        #[test]
        fn the_candidate_record_carries_the_keys_the_kernel_decodes() {
            let cfg = Config::default();
            let c = Candidate::new(Id::new("d1"), 0, 1, 0, &cfg);
            let v = cand_json(None, NaiveDate::from_ymd_opt(2026, 9, 7).unwrap(), &c, &BTreeMap::new())
                .expect("an exact multiplier");
            let mut keys: Vec<&str> = v.as_object().unwrap().keys().map(String::as_str).collect();
            keys.sort_unstable();
            assert_eq!(
                keys,
                // `Boundary.readCand`: id ci rootPrio remaining due window wall
                // optional overdue mandatory hot yesterday; `readFloor`: floor;
                // `readPlanFacts`: plan.
                vec![
                    "ci", "due", "floor", "hot", "id", "mandatory", "optional", "overdue",
                    "plan", "remaining", "rootPrio", "wall", "window", "yesterday",
                ],
            );
            // §8.2 step 5's nine, in eight keys: `cap` carries `cap_done_min`
            // beside the ceiling, and `waiting` is **not** here — the kernel derives
            // it from `state` (`Look.PlanFacts.waiting`), because
            // `collect_candidates` sets it to `state == State::Waiting`.
            let mut plan_keys: Vec<&str> =
                v["plan"].as_object().unwrap().keys().map(String::as_str).collect();
            plan_keys.sort_unstable();
            assert_eq!(
                plan_keys,
                vec![
                    "blockedBy", "cap", "loc", "multiplier", "plannedMin", "splittable", "state",
                    "wallToday",
                ],
            );
        }

        #[test]
        fn a_decimal_is_its_text_not_its_binary_expansion() {
            assert_eq!(decimal_pair(0.9, 18), Ok(("9".into(), "10".into())));
            assert_eq!(decimal_pair(1.0, 18), Ok(("1".into(), "1".into())));
            assert_eq!(decimal_pair(0.0, 18), Ok(("0".into(), "1".into())));
            assert_eq!(decimal_pair(-0.0, 18), Ok(("0".into(), "1".into())));
            assert_eq!(decimal_pair(0.05, 18), Ok(("5".into(), "100".into())));
            assert_eq!(decimal_pair(7.33, 6), Ok(("733".into(), "100".into())));
            assert_eq!(decimal_pair(0.1 + 0.2, 18), Ok(("30000000000000004".into(), "100000000000000000".into())));
            assert_eq!(decimal_pair(f64::NAN, 18), Err(PairErr::NotFinite));
            assert_eq!(decimal_pair(f64::INFINITY, 18), Err(PairErr::NotFinite));
            assert_eq!(decimal_pair(-0.5, 18), Err(PairErr::Negative));
            assert_eq!(decimal_pair(1e-19, 18), Err(PairErr::TooManyPlaces(19)));
            assert_eq!(decimal_pair(0.3333333, 6), Err(PairErr::TooManyPlaces(7)));
        }

        #[test]
        fn the_horizon_is_clamped_to_the_kernels_cap_and_the_calendar() {
            let d = |s: &str| NaiveDate::parse_from_str(s, "%Y-%m-%d").unwrap();
            assert_eq!(horizon(d("2026-09-14"), 7), (7, false));
            assert_eq!(horizon(d("2026-09-14"), 3660), (3660, false));
            assert_eq!(horizon(d("2026-09-14"), 3661), (3660, true));
            assert_eq!(horizon(d("9999-12-30"), 7), (2, true));
        }

        #[test]
        fn a_weight_outside_its_domain_is_named_by_file_and_key() {
            let mut model = Model::default();
            model.p_lounge.set(chrono::Weekday::Mon, 1.2);
            let err = check_inputs(&Config::default(), &model, &Written::default()).unwrap_err().to_string();
            assert!(err.starts_with(".tm/model.json: p_lounge.Mon = 1.2 is outside [0, 1]"), "{err}");
            let mut cfg = Config::default();
            cfg.expected.p_lounge.tue = 0.1234567890123456789e-3;
            let err = check_inputs(&cfg, &Model::default(), &Written::default()).unwrap_err().to_string();
            assert!(err.starts_with("config.toml: expected.p_lounge.Tue = "), "{err}");
            assert!(err.contains("decimal places (at most 18)"), "{err}");
            let mut cfg = Config::default();
            cfg.expected.p_lounge.sun = f64::NAN;
            assert!(check_inputs(&cfg, &Model::default(), &Written::default()).unwrap_err().to_string().contains("expected.p_lounge.Sun = NaN is not a number"));
            assert!(check_inputs(&Config::default(), &Model::default(), &Written::default()).is_ok());
        }

        /// The audit's defect (W-3): a weight of 19 written places whose nearest
        /// double has 17 was sent as that double.  Read as written, it is refused.
        fn parse_both(config: &str, model: &str) -> (Config, Model, Written) {
            let cfg = Config::parse(config).unwrap();
            let m: Model = serde_json::from_str(model).unwrap();
            (cfg, m, Written::parse(Some(config), Some(model)).unwrap())
        }

        #[test]
        fn a_literal_is_its_exact_decimal() {
            let ok = |t: &str, n: &str, d: &str| assert_eq!(written_pair(t, 18), Ok((n.into(), d.into())), "{t}");
            ok("0.9", "9", "10");
            ok("0.500", "5", "10");
            ok("1", "1", "1");
            ok("+0.25", "25", "100");
            ok("-0", "0", "1");
            ok("-0.000", "0", "1");
            ok("1e-3", "1", "1000");
            ok("2.5E+2", "250", "1");
            ok("1_000.5", "10005", "10");
            ok("0.123456789012345678", "123456789012345678", "1000000000000000000");
            ok(" 0.75 ", "75", "100");
            let err = |t: &str, e: PairErr| assert_eq!(written_pair(t, 18), Err(e), "{t}");
            err("0.1234567890123456789", PairErr::TooManyPlaces(19));
            err("0.1000000000000000001", PairErr::TooManyPlaces(19));
            err("1e-19", PairErr::TooManyPlaces(19));
            err("1.5e-18", PairErr::TooManyPlaces(19));
            err("1e-9999999", PairErr::TooManyPlaces(usize::MAX));
            err("-0.5", PairErr::Negative);
            err("nan", PairErr::NotFinite);
            err("inf", PairErr::NotFinite);
            err("+inf", PairErr::NotFinite);
            err("", PairErr::NotFinite);
            err(".", PairErr::NotFinite);
            err("1e", PairErr::NotFinite);
            assert!(above_one("11", "10") && above_one("2", "1") && !above_one("1", "1") && !above_one("9", "10"));
        }

        #[test]
        fn a_weight_past_18_written_places_is_refused_though_its_double_is_shorter() {
            for v in ["0.1234567890123456789", "0.1000000000000000001"] {
                let (cfg, model, w) = parse_both("", &format!("{{\"p_lounge\": {{\"Tue\": {v}}}}}"));
                let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
                assert!(err.starts_with(&format!(".tm/model.json: p_lounge.Tue = {v} has 19 decimal places (at most 18)")), "{err}");
                let (cfg, model, w) = parse_both(&format!("[expected]\np_lounge = {{ Mon = 0.9, Tue = {v}, Wed = 0.9, Thu = 0.9, Fri = 0.8, Sat = 0.5, Sun = 0.4 }}\n"), "{}");
                let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
                assert!(err.starts_with(&format!("config.toml: expected.p_lounge.Tue = {v} has 19 decimal places (at most 18)")), "{err}");
            }
            // The last entry for a weekday wins, as in the model's own reading.
            let (cfg, model, w) = parse_both("", r#"{"p_lounge": {"Tue": 0.1000000000000000001, "Tuesday": 0.5}}"#);
            assert_eq!(w.model_p[1].as_deref(), Some("0.5"));
            assert!(check_inputs(&cfg, &model, &w).is_ok());
            // 18 written places are sent exactly, not as their nearest double.
            let (cfg, model, w) = parse_both("[expected.p_lounge]\nMon = 0\nTue = 0\nWed = 0.123456789012345678\nThu = 0\nFri = 0\nSat = 0\nSun = 0\n", "{}");
            let p = pairs_of(&cfg, &model, &w).unwrap();
            assert_eq!(p.config_p[2], ("123456789012345678".into(), "1000000000000000000".into()));
            // Every other configured decimal the request carries is read as written too.
            let (cfg, model, w) = parse_both("[priority]\nsafety = 1.3000000000000000001\n", "{}");
            let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
            assert!(err.starts_with("config.toml: priority.safety = 1.3000000000000000001 has 19 decimal places (at most 18)"), "{err}");
            let (cfg, model, w) = parse_both("[priority]\nbins = [0.5, 0.2500000000000000001, 0.1]\n", "{}");
            let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
            assert!(err.starts_with("config.toml: priority.bins[1] = 0.2500000000000000001 has 19 decimal places"), "{err}");
            let (cfg, model, w) = parse_both("[day]\nwindow_hours = 8.0000000000000000001\n", "{}");
            let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
            assert!(err.starts_with("config.toml: day.window_hours = 8.0000000000000000001 has 19 decimal places (at most 6)"), "{err}");
            let (cfg, model, w) = parse_both("[energy.prior.lounge]\n\"0-1.0000000000000000001\" = 4\n", "{}");
            let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
            assert!(err.starts_with("config.toml: energy.prior.lounge.\"0-1.0000000000000000001\" = 1.0000000000000000001 has 19 decimal places (at most 6)"), "{err}");
            // A written value its double does not read is a file that changed under the verb.
            let cfg = Config::parse("[expected]\np_lounge = { Mon = 0, Tue = 0.5, Wed = 0, Thu = 0, Fri = 0, Sat = 0, Sun = 0 }\n").unwrap();
            let w = Written::parse(Some("[expected]\np_lounge = { Mon = 0, Tue = 0.25, Wed = 0, Thu = 0, Fri = 0, Sat = 0, Sun = 0 }\n"), None).unwrap();
            let err = check_inputs(&cfg, &Model::default(), &w).unwrap_err().to_string();
            assert!(err.contains("changed while tm was reading it"), "{err}");
            // Integers, signs, exponents and underscores are the literals TOML and JSON allow.
            let (cfg, model, w) = parse_both("[expected]\np_lounge = { Mon = 1, Tue = +0.5, Wed = 5e-1, Thu = 0.000_5, Fri = 0, Sat = 0, Sun = 0 }\n", r#"{"p_lounge": {"Fri": 2.5E-1}}"#);
            let p = pairs_of(&cfg, &model, &w).unwrap();
            assert_eq!(p.config_p[0], ("1".into(), "1".into()));
            assert_eq!(p.config_p[3], ("5".into(), "10000".into()));
            assert_eq!(p.model_p[4], Some(("25".into(), "100".into())));
        }
    }
}
