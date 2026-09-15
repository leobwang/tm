//! **The one encoder of the capacity request** (stage 5 D10 step L8, host half;
//! design `kernel/design/stage5/stage5-D9-D10-design.md` §13.6, §13.8).
//!
//! Since this step the shipped binary's §8.4 lookahead and every §7 priority
//! come from the kernel: `Look.lookahead` (the owner's D10: each future day an
//! exact mixture of the day at the lounge and the day at home, in units over
//! `capDen = 10^18`, D17) and `Look.prioritiesWithFloors` (step 3's EDF pass,
//! §7.1's bin at the exact availability, §7.2's row, §7.4's hysteresis, and the
//! floor pass). Nothing else in the Rust builds a capacity request, and nothing
//! else reads one back:
//!
//! * [`decimal_pair`] is the only way a configured `f64` reaches the kernel: the
//!   shortest round-trip text of the double (Rust's `Display`), split at the
//!   point, never the double's binary expansion (`0.9` is `9/10`, not
//!   `0.90000000000000002220446…`). T15 is its proptest.
//! * [`check_inputs`] runs the same encoding over `config.toml` and
//!   `.tm/model.json` before a request is built, so a weight outside `[0, 1]` or
//!   with more than 18 decimal places fails every verb that computes capacity or
//!   priority **by file and key** (§13.2, parity P26); the kernel's refusal stays
//!   the authority, and [`named_refusal`] names the file and key of every
//!   refusal a configured value can cause.
//! * [`request`] builds the whole request: the plan's documents (walls are the
//!   kernel's reading, gap 111), `now`, `blockMin`, the zone table from
//!   [`super::tz_table`] (the one zone encoder), and the `capacity` section:
//!   both weekday tables raw (the kernel picks, D10-4), today's logged wake,
//!   the learned curves, the prior, `[day]`, `[priority]`, `days` and `day0`
//!   (the host's histogram until L9, gap 93), with the candidates when priorities
//!   are asked for (their facts are the host's, gap 113).
//! * [`read_answer`] parses the response: `den` must be `capDen`, unit counts are
//!   digit strings read into `u128` (D17), and each grant becomes a [`Prio`]
//!   whose integer minutes are floors beside their exact values (D15).
//!
//! **The horizon (gap 98).** The kernel's lookahead is at most 3,660 days
//! (`Look.maxLookaheadDays`) and never runs past 9999-12-31. [`horizon`] clamps
//! the fork's `priority::lookahead_days` to both and says so on stderr when it
//! clamps (parity P30: a deadline past it sees the capacity of the days it has).

use std::collections::BTreeMap;

use chrono::{NaiveDate, Timelike};
use serde_json::{json, Map, Value};

use tm_core::capacity::{self, DayCapacity, Exact, UnitCapacity, CAP_DEN};
use tm_core::config::Config;
use tm_core::energy::{weekday_key, Model};
use tm_core::model::Id;
use tm_core::priority::{self, Candidate, Prio, PrioClass};
use tm_core::store::Store;

use super::ctx::Ctx;
use super::kernel_bridge;
use super::out::CliError;
use super::tz_table;

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

// ---------------------------------------------------------------------------
// decimal_pair
// ---------------------------------------------------------------------------

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
/// round-trip `Display` text of `x`, split at the point, as `(numerator,
/// denominator)` digit strings with the denominator `10^places`. `-0.0` is
/// `0/1`. Refuses NaN, the infinities, negatives, and more than `max_places`
/// decimal places.
pub fn decimal_pair(x: f64, max_places: u32) -> Result<(String, String), PairErr> {
    if !x.is_finite() {
        return Err(PairErr::NotFinite);
    }
    if x < 0.0 {
        return Err(PairErr::Negative);
    }
    let text = format!("{}", x.abs());
    let (int, frac) = text.split_once('.').unwrap_or((&text, ""));
    if frac.len() > max_places as usize {
        return Err(PairErr::TooManyPlaces(frac.len()));
    }
    let digits = format!("{int}{frac}");
    let num = digits.trim_start_matches('0');
    let num = if num.is_empty() { "0".to_string() } else { num.to_string() };
    let den = format!("1{}", "0".repeat(frac.len()));
    Ok((num, den))
}

/// A pair as the kernel's JSON naturals (`{"num": n, "den": d}`), for the
/// pairs whose parts are bounded well inside `u64` (`[day]`, `[priority]`, the
/// prior's keys).
fn nat_pair(x: f64, places: u32) -> Result<Value, PairErr> {
    let (n, d) = decimal_pair(x, places)?;
    // `places ≤ 18`, so the denominator fits; a numerator past u64 is a value
    // no bound admits, and is sent as the largest natural so the kernel refuses it.
    Ok(json!({"num": n.parse::<u64>().unwrap_or(u64::MAX), "den": d.parse::<u64>().unwrap_or(u64::MAX)}))
}

/// A pair as digit strings (`{"num": "…", "den": "…"}`, D17): a lounge weight.
fn str_pair(x: f64) -> Result<Value, PairErr> {
    let (n, d) = decimal_pair(x, WEIGHT_PLACES)?;
    Ok(json!({"num": n, "den": d}))
}

// ---------------------------------------------------------------------------
// The inputs, checked by file and key (§13.2, P26)
// ---------------------------------------------------------------------------

/// The plan-relative path of the learned model, as messages name it.
const MODEL_FILE: &str = ".tm/model.json";
/// The configuration, as messages name it.
const CONFIG_FILE: &str = "config.toml";

/// The failure of a configured value, by file and key.
fn bad_value(file: &str, key: &str, x: f64, why: &str) -> CliError {
    CliError::msg(format!(
        "{file}: {key} = {x} {why}; tm cannot compute capacity or priorities until it is fixed \
         (kernel/README.md parity P26)"
    ))
}

/// A pair's refusal, in words.
fn pair_why(e: PairErr, places: u32) -> String {
    match e {
        PairErr::NotFinite => "is not a number".to_string(),
        PairErr::Negative => "is below zero".to_string(),
        PairErr::TooManyPlaces(n) => format!("has {n} decimal places (at most {places})"),
    }
}

/// **A lounge weight**: a decimal pair of at most 18 places, in `[0, 1]`.
fn check_weight(file: &str, key: &str, x: f64) -> Result<(), CliError> {
    match decimal_pair(x, WEIGHT_PLACES) {
        Err(PairErr::Negative) => return Err(bad_value(file, key, x, "is outside [0, 1]")),
        Err(e) => return Err(bad_value(file, key, x, &pair_why(e, WEIGHT_PLACES))),
        Ok(_) => {}
    }
    if x > 1.0 {
        return Err(bad_value(file, key, x, "is outside [0, 1]"));
    }
    Ok(())
}

/// A configured decimal with at most `places` places.
fn check_places(key: &str, x: f64, places: u32) -> Result<(), CliError> {
    decimal_pair(x, places).map(|_| ()).map_err(|e| bad_value(CONFIG_FILE, key, x, &pair_why(e, places)))
}

/// **Every configured decimal the capacity request carries, checked before it is
/// built**: the model's and the config's lounge weights (§13.2: every pair is
/// sent, so both are checked), `[day]`'s two ratios, `[priority]`'s edges and
/// safety, and the prior's range keys. The message names the file and the key.
pub fn check_inputs(cfg: &Config, model: &Model) -> Result<(), CliError> {
    for (wd, x) in model.p_lounge.iter() {
        check_weight(MODEL_FILE, &format!("p_lounge.{}", weekday_key(wd)), *x)?;
    }
    for wd in WEEK {
        check_weight(
            CONFIG_FILE,
            &format!("expected.p_lounge.{}", weekday_key(wd)),
            *cfg.expected.p_lounge.get(wd),
        )?;
    }
    check_places("day.window_hours", cfg.day.window_hours, RATIO_PLACES)?;
    check_places("day.budget_ratio", cfg.day.budget_ratio, RATIO_PLACES)?;
    for (i, edge) in cfg.priority.bins.iter().enumerate() {
        check_places(&format!("priority.bins[{i}]"), *edge, PRIORITY_PLACES)?;
    }
    check_places("priority.safety", cfg.priority.safety, PRIORITY_PLACES)?;
    for (curve, steps) in &cfg.energy.prior {
        for step in &steps.0 {
            let key = format!("energy.prior.{curve}.\"{}\"", tm_core::config::StepFn::key(step));
            check_places(&key, step.from, RATIO_PLACES)?;
            if let Some(to) = step.to {
                check_places(&key, to, RATIO_PLACES)?;
            }
        }
    }
    Ok(())
}

/// **A capacity refusal a configured value causes, by file and key** (P26).
/// `None` for a refusal only a defect of this module can cause (the clock, the
/// zone table, the candidates' shape): those stay the kernel's named issue.
pub fn named_refusal(issue: &super::out::KernelIssue) -> Option<CliError> {
    let text = issue.message.strip_prefix("kernel refusal: ")?;
    let text = text.split(" — ").next()?;
    let (name, key) = text.split_once(' ').unwrap_or((text, ""));
    let weekday = |k: &str| k.rsplit('.').next().unwrap_or_default().to_string();
    let (file, what): (&str, String) = match name {
        "badWeight" | "weightAboveOne" | "weightPrecision" if key.starts_with("pLounge.model.") => {
            (MODEL_FILE, format!("p_lounge.{}", weekday(key)))
        }
        "badWeight" | "weightAboveOne" | "weightPrecision" => {
            (CONFIG_FILE, format!("expected.p_lounge.{}", weekday(key)))
        }
        "badClock" if key.starts_with("arrival.model.") => {
            (MODEL_FILE, format!("expected_arrival.{}", weekday(key)))
        }
        "badClock" if key == "day.windowCap" => (CONFIG_FILE, "day.window_cap".to_string()),
        "badClock" => (CONFIG_FILE, format!("expected.arrival.{}", weekday(key))),
        "badCurve" => (MODEL_FILE, key.to_string()),
        "badPrior" | "badStep" | "badLevel" => (CONFIG_FILE, format!("energy.{key}")),
        "badCap" => (CONFIG_FILE, "location.home_max_ci".to_string()),
        "badDay" => {
            let k = match key {
                "blockMin" => "day.block_min",
                "breakMin" => "day.break_min",
                "breakAfterBlocks" => "day.break_after_blocks",
                "minLastBlockMin" => "day.min_last_block_min",
                "windowHours" => "day.window_hours",
                "budgetRatio" => "day.budget_ratio",
                _ => return None,
            };
            (CONFIG_FILE, k.to_string())
        }
        "badBins" => (CONFIG_FILE, "priority.bins".to_string()),
        "badSafety" => (CONFIG_FILE, "priority.safety".to_string()),
        "badDefaultPriority" => (CONFIG_FILE, "priority.default_priority".to_string()),
        _ => return None,
    };
    Some(CliError::msg(format!(
        "{file}: {what} is outside what the kernel accepts ({text}); tm cannot compute capacity or \
         priorities until it is fixed (kernel/README.md parity P26)"
    )))
}

// ---------------------------------------------------------------------------
// The horizon (gap 98)
// ---------------------------------------------------------------------------

/// **The lookahead's length** for `want` days from `today`: at most
/// [`MAX_LOOKAHEAD_DAYS`], never past 9999-12-31, at least one. Returns the
/// days and whether it clamped.
pub fn horizon(today: NaiveDate, want: u32) -> (u32, bool) {
    let last = NaiveDate::from_ymd_opt(9999, 12, 31).unwrap_or(NaiveDate::MAX);
    let to_end = u32::try_from((last - today).num_days() + 1).unwrap_or(0);
    let days = want.min(MAX_LOOKAHEAD_DAYS).min(to_end).max(1);
    (days, days < want)
}

/// Say on stderr that the horizon clamped (not while the TUI owns the screen).
fn say_clamped(today: NaiveDate, want: u32, days: u32) {
    if kernel_bridge::capturing_kernel_stderr() {
        return;
    }
    let through = today + chrono::Duration::days(i64::from(days) - 1);
    eprintln!(
        "tm: the capacity lookahead is clamped to {days} days (through {through}; {want} were needed): a \
         deadline or floor after that sees only those days' capacity (kernel/README.md gap 98, parity P30)"
    );
}

// ---------------------------------------------------------------------------
// The request
// ---------------------------------------------------------------------------

/// `HH:MM`.
fn hhmm(t: chrono::NaiveTime) -> String {
    format!("{:02}:{:02}", t.hour(), t.minute())
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
fn send_order(cands: &[Candidate]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..cands.len()).collect();
    order.sort_by(|&a, &b| {
        let (ca, cb) = (&cands[a], &cands[b]);
        (ca.effective_due.is_none(), ca.effective_due, ca.own_order, a)
            .cmp(&(cb.effective_due.is_none(), cb.effective_due, cb.own_order, b))
    });
    order
}

/// One candidate record (Boundary.lean's `readCand`, `readFloor`).
fn cand_json(ctx: &Ctx, c: &Candidate, yesterday: &BTreeMap<Id, u8>) -> Value {
    let root_prio = ctx.tree.get(&ctx.tree.root(&c.id)).and_then(|r| r.priority);
    let floor = c.floor.as_ref().map(|r| {
        json!({
            "left": r.amount.as_minutes().saturating_sub(c.floor_done_min),
            "until": priority::period_range(r.per, ctx.today).1.to_string(),
        })
    });
    json!({
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
    })
}

/// **The capacity request** for `days` days from today, with the candidates when
/// `ranked` is given. Returns the request and the order the candidates were
/// sent in.
pub fn request(ctx: &Ctx, allow_home: bool, days: u32, ranked: Option<&Ranked<'_>>) -> Result<(Value, Vec<usize>), CliError> {
    check_inputs(&ctx.cfg, &ctx.model)?;
    let cfg = &ctx.cfg;
    let model = &ctx.model;

    // The documents: the whole tree, as `kernel_bridge::apply` sends it.
    let mut docs = Vec::new();
    for rel in ctx.store.list_files()? {
        let text = ctx.store.read_text(&rel)?;
        docs.push(kernel_bridge::doc_json(&rel, &kernel_bridge::doc_lines(&text)));
    }

    let week_table = |f: &dyn Fn(chrono::Weekday) -> Option<Value>| -> Map<String, Value> {
        WEEK.iter().filter_map(|wd| f(*wd).map(|v| (weekday_key(*wd).to_string(), v))).collect()
    };
    let weight = |x: f64| str_pair(x).unwrap_or(Value::Null);
    let p_model = week_table(&|wd| model.p_lounge.get(wd).map(|x| weight(*x)));
    let p_config = week_table(&|wd| Some(weight(*cfg.expected.p_lounge.get(wd))));
    let a_model = week_table(&|wd| model.expected_arrival.get(wd).map(|t| json!(hhmm(t.0))));
    let a_config = week_table(&|wd| Some(json!(hhmm(*cfg.expected.arrival.get(wd)))));
    let energy: Map<String, Value> = LOCATIONS
        .iter()
        .filter_map(|loc| model.energy.get(*loc).map(|c| (loc.to_string(), json!(c))))
        .collect();
    let pair = |x: f64, places: u32| nat_pair(x, places).unwrap_or(Value::Null);
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
    let wake = ctx.logged_wake().map(|t| json!({"sec": t.num_seconds_from_midnight(), "ns": t.nanosecond()}));
    let day0 = DayCapacity::from_slots(ctx.today, &ctx.today_slots(allow_home)).minutes_at_level;
    let bins: Vec<Value> = cfg.priority.bins.iter().map(|e| pair(*e, PRIORITY_PLACES)).collect();

    let mut section = json!({
        "pLounge": {"model": p_model, "config": p_config},
        "arrival": {"model": a_model, "config": a_config},
        "wake": wake,
        "energy": energy,
        "prior": prior,
        "homeMaxCi": cfg.location.home_max_ci,
        "day": {
            "breakMin": cfg.day.break_min,
            "breakAfterBlocks": cfg.day.break_after_blocks,
            "minLastBlockMin": cfg.day.min_last_block_min,
            "windowHours": pair(cfg.day.window_hours, RATIO_PLACES),
            "windowCap": hhmm(cfg.day.window_cap),
            "budgetRatio": pair(cfg.day.budget_ratio, RATIO_PLACES),
        },
        "priority": {
            "bins": bins,
            "safety": pair(cfg.priority.safety, PRIORITY_PLACES),
            "defaultPriority": cfg.priority.default_priority,
        },
        "days": days,
        "day0": day0,
    });
    let mut order = Vec::new();
    if let Some(r) = ranked {
        order = send_order(r.cands);
        let items: Vec<Value> = order.iter().map(|&i| cand_json(ctx, &r.cands[i], r.yesterday)).collect();
        section["candidates"] = json!({"hysteresis": cfg.priority.hysteresis, "items": items});
    }
    let cache = ctx.store.root().join(".tm/cache/replay");
    let request = json!({
        "docs": docs,
        "now": ctx.today.to_string(),
        "blockMin": ctx.block_min(),
        "tz": tz_table::wire_for(Some(&cache), cfg.tz),
        "capacity": section,
    });
    Ok((request, order))
}

// ---------------------------------------------------------------------------
// The answer
// ---------------------------------------------------------------------------

/// What the kernel answered: the first `min(days, 7)` days in units, and one
/// priority per candidate in the candidates' own order.
#[derive(Clone, Debug, Default)]
pub struct Answer {
    /// The lookahead's first days (at most seven), exact units over [`CAP_DEN`].
    pub days: Vec<UnitCapacity>,
    /// One [`Prio`] per candidate, in `collect_candidates` order.
    pub prios: Vec<Prio>,
}

/// A response defect: loud, named, never a wrong answer.
fn defect(what: &str) -> CliError {
    CliError::Kernel(kernel_bridge::fault_issue(&format!("capacity response: {what}"), ""))
}

/// A digit string as `u128` (D17).
fn units_of(v: &Value, what: &str) -> Result<u128, CliError> {
    v.as_str()
        .filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
        .and_then(|s| s.parse::<u128>().ok())
        .ok_or_else(|| defect(&format!("{what} is not a digit string that fits u128")))
}

/// A `YYYY-MM-DD`.
fn date_of(v: &Value, what: &str) -> Result<NaiveDate, CliError> {
    v.as_str()
        .and_then(|s| NaiveDate::parse_from_str(s, "%Y-%m-%d").ok())
        .ok_or_else(|| defect(&format!("{what} is not a date")))
}

/// A small natural.
fn small(v: &Value, what: &str) -> Result<u8, CliError> {
    v.as_u64().and_then(|n| u8::try_from(n).ok()).ok_or_else(|| defect(&format!("{what} is not a small natural")))
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
fn prio_of(g: &Value) -> Result<Prio, CliError> {
    let id = g["id"].as_str().ok_or_else(|| defect("a grant has no id"))?;
    let class = g["class"].as_str().and_then(class_of).ok_or_else(|| defect("a grant's class is unknown"))?;
    let k = small(&g["k"], "k")?;
    let p = if g["p"].is_null() { None } else { Some(small(&g["p"], "p")?) };
    let raw = if g["rawP"].is_null() { None } else { Some(small(&g["rawP"], "rawP")?) };
    let need = g["need"].as_u64().and_then(|n| u32::try_from(n).ok()).ok_or_else(|| defect("need"))?;
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
        need_min: need,
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

/// **Read the response** of a request built by [`request`] with `order`.
pub fn read_answer(resp: &Value, order: &[usize], ranked: bool) -> Result<Answer, CliError> {
    let la = &resp["ok"]["lookahead"];
    if la["den"].as_str() != Some(CAP_DEN.to_string().as_str()) {
        return Err(defect("den is not capDen"));
    }
    let days = la["days"]
        .as_array()
        .ok_or_else(|| defect("no days"))?
        .iter()
        .map(|d| {
            let date = date_of(&d["day"], "a day")?;
            let at = d["numAt"].as_array().filter(|a| a.len() == 6).ok_or_else(|| defect("numAt"))?;
            let mut units = [0u128; 6];
            for (l, v) in at.iter().enumerate() {
                units[l] = units_of(v, "numAt")?;
            }
            Ok(UnitCapacity { date, units })
        })
        .collect::<Result<Vec<_>, CliError>>()?;
    let mut prios = Vec::new();
    if ranked {
        let grants = la["grants"].as_array().ok_or_else(|| defect("no grants"))?;
        if grants.len() != order.len() {
            return Err(defect("one grant per candidate"));
        }
        let mut slots: Vec<Option<Prio>> = vec![None; order.len()];
        for (g, &i) in grants.iter().zip(order) {
            slots[i] = Some(prio_of(g)?);
        }
        prios = slots.into_iter().map(|p| p.ok_or_else(|| defect("a candidate without a grant"))).collect::<Result<_, _>>()?;
    }
    Ok(Answer { days, prios })
}

/// **Ask the kernel** for `want` days of capacity from today (clamped by
/// [`horizon`]), and the priorities of `ranked` when given.
pub fn ask(ctx: &Ctx, allow_home: bool, want: u32, ranked: Option<&Ranked<'_>>) -> Result<Answer, CliError> {
    let (days, clamped) = horizon(ctx.today, want);
    if clamped {
        say_clamped(ctx.today, want, days);
    }
    let (req, order) = request(ctx, allow_home, days, ranked)?;
    let (resp, _) = match kernel_bridge::call(&req) {
        Ok(r) => r,
        Err(CliError::Kernel(issue)) => {
            return Err(named_refusal(&issue).unwrap_or(CliError::Kernel(issue)));
        }
        Err(e) => return Err(e),
    };
    let answer = read_answer(&resp, &order, ranked.is_some())?;
    if let Some(r) = ranked {
        for (c, p) in r.cands.iter().zip(&answer.prios) {
            if c.id != p.id {
                return Err(defect("a grant answers another candidate"));
            }
        }
    }
    Ok(answer)
}

/// **§7 and §8.4 from the kernel**: the priorities of `cands` over a lookahead
/// long enough for every deadline and floor (`priority::lookahead_days`), and
/// its first days.
pub fn rank(ctx: &Ctx, cands: &[Candidate], yesterday: &BTreeMap<Id, u8>, allow_home: bool) -> Result<Answer, CliError> {
    let want = priority::lookahead_days(cands, ctx.today);
    ask(ctx, allow_home, want, Some(&Ranked { cands, yesterday }))
}

/// **`tm plan --week`'s seven days** from the kernel.
pub fn week(ctx: &Ctx, allow_home: bool) -> Result<Vec<UnitCapacity>, CliError> {
    Ok(ask(ctx, allow_home, 7, None)?.days)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

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
        let err = check_inputs(&Config::default(), &model).unwrap_err().to_string();
        assert!(err.starts_with(".tm/model.json: p_lounge.Mon = 1.2 is outside [0, 1]"), "{err}");
        let mut cfg = Config::default();
        cfg.expected.p_lounge.tue = 0.1234567890123456789e-3;
        let err = check_inputs(&cfg, &Model::default()).unwrap_err().to_string();
        assert!(err.starts_with("config.toml: expected.p_lounge.Tue = "), "{err}");
        assert!(err.contains("decimal places (at most 18)"), "{err}");
        let mut cfg = Config::default();
        cfg.expected.p_lounge.sun = f64::NAN;
        assert!(check_inputs(&cfg, &Model::default()).unwrap_err().to_string().contains("expected.p_lounge.Sun = NaN is not a number"));
        assert!(check_inputs(&Config::default(), &Model::default()).is_ok());
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(4096))]

        /// **T15**: every finite non-negative double's pair is exactly the value
        /// its shortest text writes (the pair, rendered back as a decimal, parses to
        /// the same double), the denominator is `10^places` with `places` the text's,
        /// and a pair is refused exactly when the text has more places than allowed.
        #[test]
        fn t15_decimal_pair_is_the_shortest_text(bits in any::<u64>(), max in 0u32..=20) {
            let x = f64::from_bits(bits);
            match decimal_pair(x, max) {
                Err(PairErr::NotFinite) => prop_assert!(!x.is_finite()),
                Err(PairErr::Negative) => prop_assert!(x.is_finite() && x < 0.0),
                Err(PairErr::TooManyPlaces(n)) => {
                    prop_assert!(x.is_finite() && x >= 0.0 && n > max as usize);
                    prop_assert_eq!(format!("{x}").split_once('.').map_or(0, |(_, f)| f.len()), n);
                }
                Ok((num, den)) => {
                    prop_assert!(x.is_finite() && x >= 0.0);
                    let places = den.len() - 1;
                    prop_assert!(places <= max as usize);
                    prop_assert!(den.starts_with('1') && den[1..].bytes().all(|b| b == b'0'));
                    prop_assert!(num.bytes().all(|b| b.is_ascii_digit()) && (num == "0" || !num.starts_with('0')));
                    let padded = format!("{num:0>width$}", width = places + 1);
                    let (int, frac) = padded.split_at(padded.len() - places);
                    let back: f64 = format!("{int}.{frac}0").parse().unwrap();
                    prop_assert_eq!(back.to_bits(), x.abs().to_bits());
                }
            }
        }

        /// T15 over the lounge weights a hand edit writes: every decimal of at most
        /// 18 places in [0, 1] is sent as exactly itself.
        #[test]
        fn t15_a_written_weight_is_sent_as_written(n in 0u64..=1_000_000_000_000_000u64, places in 0u32..=15) {
            let den = 10u64.pow(places);
            let n = n % (den + 1);
            let text = if places == 0 { format!("{n}") } else { format!("{}.{:0>w$}", n / den, n % den, w = places as usize) };
            let x: f64 = text.parse().unwrap();
            let (num, d) = decimal_pair(x, WEIGHT_PLACES).unwrap();
            // The pair equals the written decimal as rationals.
            let (num, d) = (num.parse::<u128>().unwrap(), d.parse::<u128>().unwrap());
            prop_assert_eq!(num * u128::from(den), u128::from(n) * d);
        }
    }
}
