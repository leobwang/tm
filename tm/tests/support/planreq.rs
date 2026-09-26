//! **A whole planning request, built from a tree the test holds** — the
//! documents, the log, the capacity section and the `planner` section — and the
//! kernel's day read back through the host's own codec
//! (`tm_core::planwire`). Stage 6 W-35, track R (README gaps 2720, 2722).
//!
//! # Whose spelling this is
//!
//! The `planner` section and the reading of the answer are **not** spelled
//! here: they are `tm_core::planwire`'s, the one host codec R3 swaps into the
//! binary. What IS spelled here is the capacity section, because its shipped
//! encoder is `tm/src/cli/kernel_capacity.rs::request`, which takes a `Ctx` and
//! lives in a `[[bin]]` no test can link (README gap 2006). This is that
//! encoder's shape — `cand_json`, `plan_json`, `send_order`, the `[day]`,
//! `[priority]`, `[energy]` and `[expected]` tables — read off the tree's own
//! `Config`, never off literals: `tm/tests/planner_invariants.rs`' world spells
//! the same section for its generated days, and the two are the second and
//! third spellings gap 2006 already counts. It is shared so that a third caller
//! does not make a fourth.
//!
//! # What it deliberately leaves out
//!
//! * `pLounge.model`, `arrival.model` and `energy` — the learned model's
//!   tables. Every caller here plans with `Model::default()`, which has none,
//!   and the kernel falls back to `config` exactly as the shipped request does
//!   when the model's tables are empty.
//! * `yesterday` on every candidate record is `null`: the callers' states carry
//!   no `priorities_yesterday`, so the fork reads an empty map too.

#![allow(dead_code)]

#[path = "../../src/cli/tz_table.rs"]
pub mod tz_table;

use chrono::{DateTime, Timelike};
use chrono_tz::Tz;
use serde_json::{json, Map, Value};

use tm_core::config::Config;
use tm_core::model::{fmt_time as hhmm, Id};
use tm_core::planwire::{self, CapacityAnswer, DayCtx, KernelDay, RoutineInst};
use tm_core::priority::{self, Candidate};
use tm_core::store::{MemStore, RuntimeState, Store};
use tm_core::tree::Tree;

/// Everything a planning request is built from.
pub struct World<'a> {
    /// The plan's documents as `(path, text)`, exactly as the files hold them.
    pub docs: &'a [(String, String)],
    /// `.tm/log.jsonl`'s text.
    pub log: &'a str,
    /// The tree the host parsed from the same documents.
    pub tree: &'a Tree,
    /// The tree's own `config.toml`.
    pub cfg: &'a Config,
    /// `.tm/state.json`.
    pub state: &'a RuntimeState,
    /// The instant planned at, in `cfg.tz`.
    pub now: DateTime<Tz>,
    /// `priority::collect_candidates` over the same tree and replay.
    pub cands: &'a [Candidate],
}

/// **A configured double as the exact decimal pair the wire carries** (D17):
/// its shortest `Display` digits over a power of ten, as digit strings — the
/// shape `kernel_capacity::written_pair` gives a written decimal.
pub fn dec(x: f64) -> Value {
    let t = format!("{x}");
    let (int, frac) = t.split_once('.').unwrap_or((t.as_str(), ""));
    json!({"num": format!("{int}{frac}"), "den": format!("1{}", "0".repeat(frac.len()))})
}

/// The same pair as JSON naturals (`kernel_capacity::nat_pair_of`), for every
/// section whose reader is `natAt` rather than a digit string.
pub fn decn(x: f64) -> Value {
    let v = dec(x);
    json!({"num": v["num"].as_str().unwrap_or("0").parse::<u64>().unwrap_or(0),
           "den": v["den"].as_str().unwrap_or("1").parse::<u64>().unwrap_or(1)})
}

/// **The order the candidates are sent in**: `kernel_capacity::send_order`,
/// the fork's `(effective_due, own_order, index)`.
pub fn send_order(cands: &[Candidate]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..cands.len()).collect();
    order.sort_by(|&a, &b| {
        let (ca, cb) = (&cands[a], &cands[b]);
        (ca.effective_due.is_none(), ca.effective_due, ca.own_order, a)
            .cmp(&(cb.effective_due.is_none(), cb.effective_due, cb.own_order, b))
    });
    order
}

/// One candidate record: `kernel_capacity::cand_json` and `plan_json`.
fn cand_json(w: &World<'_>, c: &Candidate) -> Value {
    let date = planwire::plan_date(w.state, w.now);
    let root_prio = w.tree.get(&w.tree.root(&c.id)).and_then(|r| r.priority);
    let floor = c.floor.as_ref().map(|r| {
        json!({"left": r.amount.as_minutes().saturating_sub(c.floor_done_min),
               "until": priority::period_range(r.per, date).1.to_string()})
    });
    json!({
        "id": c.id.as_str(), "ci": c.ci, "rootPrio": root_prio,
        "remaining": c.remaining_min,
        "due": c.effective_due.map(|d| d.date_naive().to_string()),
        "window": c.window.is_some(), "wall": c.is_wall,
        "optional": c.is_optional, "overdue": c.overdue,
        "mandatory": c.mandatory, "hot": c.hot,
        "yesterday": Option::<u8>::None,
        "floor": floor,
        "plan": {"plannedMin": c.planned_min,
                 "multiplier": decn(c.multiplier),
                 "loc": c.loc.as_str(), "splittable": c.splittable,
                 "cap": c.cap.as_ref().map(|r| json!({
                     "capMin": r.amount.as_minutes(), "doneMin": c.cap_done_min})),
                 "state": c.state.glyph().to_string(),
                 "blockedBy": c.blocked_by.iter().map(ToString::to_string).collect::<Vec<String>>(),
                 "wallToday": c.wall_today}})
}

/// **The capacity section**, read off the tree's `Config`.
fn capacity(w: &World<'_>, order: &[usize]) -> Value {
    let cfg = w.cfg;
    let date = planwire::plan_date(w.state, w.now);
    let week = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
    let wds = [chrono::Weekday::Mon, chrono::Weekday::Tue, chrono::Weekday::Wed,
               chrono::Weekday::Thu, chrono::Weekday::Fri, chrono::Weekday::Sat,
               chrono::Weekday::Sun];
    let p_config: Map<String, Value> =
        week.iter().zip(wds).map(|(k, wd)| ((*k).to_string(), dec(*cfg.expected.p_lounge.get(wd)))).collect();
    let arrival: Map<String, Value> =
        week.iter().zip(wds).map(|(k, wd)| ((*k).to_string(), json!(hhmm(*cfg.expected.arrival.get(wd))))).collect();
    let prior: Map<String, Value> = cfg
        .energy
        .prior
        .iter()
        .map(|(loc, steps)| {
            let s: Vec<Value> = steps
                .0
                .iter()
                .map(|s| json!({"from": decn(s.from), "to": s.to.map(decn), "level": s.level}))
                .collect();
            (loc.clone(), Value::Array(s))
        })
        .collect();
    let d = &cfg.day;
    let shift = cfg.energy.sleep_debt.shift;
    let mut shift_pair = decn(shift.abs());
    shift_pair["neg"] = json!(shift < 0.0);
    let mut section = json!({
        "wake": match w.state.wake {
            Some(t) => json!({"sec": t.num_seconds_from_midnight(), "ns": t.nanosecond()}),
            None => json!("log"),
        },
        "pLounge": {"config": p_config},
        "arrival": {"config": arrival},
        "prior": prior,
        "homeMaxCi": cfg.location.home_max_ci,
        "day": {"breakMin": d.break_min, "breakAfterBlocks": d.break_after_blocks,
                "minLastBlockMin": d.min_last_block_min,
                "windowHours": decn(d.window_hours), "windowCap": hhmm(d.window_cap),
                "budgetRatio": decn(d.budget_ratio),
                "windDown": hhmm(d.wind_down), "bed": hhmm(d.bed)},
        "priority": {"bins": cfg.priority.bins.iter().map(|b| decn(*b)).collect::<Vec<_>>(),
                     "safety": decn(cfg.priority.safety),
                     "defaultPriority": cfg.priority.default_priority},
        "days": priority::lookahead_days(w.cands, date),
        "at": w.now.to_rfc3339(),
        "state": {
            "date": w.state.date.map(|x| x.to_string()),
            "window": w.state.window.map(|(f, t)| json!({"from": hhmm(f), "to": hhmm(t)})),
            "budget": w.state.budget,
            "arrival": w.state.arrival.map(hhmm),
            "loc": w.state.loc,
            "allowHome": false},
        "posterior": {"fullHours": decn(cfg.energy.posterior_full_hours),
                      "zeroHours": decn(cfg.energy.posterior_zero_hours)},
        "sleep": {"shiftModel": null, "shiftConfig": shift_pair,
                  "underHours": decn(cfg.energy.sleep_debt.under_hours)},
        "candidates": {"hysteresis": cfg.priority.hysteresis,
                       "items": order.iter().map(|&i| cand_json(w, &w.cands[i])).collect::<Vec<_>>()},
    });
    // The one key the planner section needs from the capacity section, written
    // by the host codec and not here.
    planwire::add_batch_max_min(&mut section, cfg);
    section
}

/// **The whole request**, with `overtime` in the planner section when given.
/// Returns the request and the order the candidates were sent in.
pub fn request(w: &World<'_>, overtime: Option<Value>) -> (Value, Vec<usize>) {
    let order = send_order(w.cands);
    let tz = w.cfg.tz;
    let date = planwire::plan_date(w.state, w.now);
    let routines: Vec<RoutineInst> = planwire::routine_instances(w.cands, w.tree, w.now, date, tz);
    let req = json!({
        "docs": w.docs.iter()
            .map(|(p, t)| json!({"path": p, "lines": t.lines().collect::<Vec<_>>()}))
            .collect::<Vec<_>>(),
        "now": date.to_string(),
        "blockMin": w.cfg.block_min(),
        "tz": tz_table::wire_for(None, tz),
        "log": {"ckpt": null, "from": 1,
                "lines": w.log.lines().collect::<Vec<_>>(),
                "terminated": true, "reseal": null,
                "want": {"facts": true, "headersFrom": null, "render": []},
                "sealed": null},
        "capacity": capacity(w, &order),
        "planner": planwire::planner_json(w.state, w.now, tz, &routines, overtime),
    });
    (req, order)
}

/// **A tree's plan documents** as `(path, text)`: `Store::list_files` over the
/// directory, which is the set the shipped request sends
/// (`kernel_capacity::request`).
pub fn docs_of_dir(dir: &std::path::Path) -> Vec<(String, String)> {
    let store = MemStore::from_dir(dir).expect("the tree is readable");
    store
        .list_files()
        .expect("the tree lists")
        .into_iter()
        .map(|rel| {
            let text = store.read_text(&rel).expect("a plan file is text");
            (rel, text)
        })
        .collect()
}

/// The kernel's raw response to a request.
pub fn call(req: &Value) -> Value {
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("the kernel call returns");
    serde_json::from_str(&raw).unwrap_or_else(|e| panic!("the response is JSON: {e}\n{raw}"))
}

/// **The kernel's day, read by the host's codec**: the grants into [`Prio`]s
/// (`planwire::read_capacity_answer`, the binary's reading) and the `plan`
/// object into a `DayPlan` (`planwire::read_plan`). `Err` carries the refusal
/// or the defect, by name.
///
/// [`Prio`]: tm_core::priority::Prio
pub fn kernel_day(w: &World<'_>, overtime: Option<Value>) -> Result<(KernelDay, CapacityAnswer), String> {
    let (req, order) = request(w, overtime);
    let resp = call(&req);
    kernel_day_of(&resp, w, &order)
}

/// [`kernel_day`] over a response already in hand — the seam a plant corrupts.
pub fn kernel_day_of(resp: &Value, w: &World<'_>, order: &[usize]) -> Result<(KernelDay, CapacityAnswer), String> {
    if let Some(r) = planwire::planner_refusal(resp) {
        return Err(format!("the kernel refused the planner section: {r}"));
    }
    if resp.get("ok").is_none() {
        return Err(format!("the kernel refused the request: {resp}"));
    }
    let ans = planwire::read_capacity_answer(resp, order, true).map_err(|e| format!("capacity: {e}"))?;
    let ctx = DayCtx { tz: w.cfg.tz, cands: w.cands, prios: &ans.prios };
    let day = planwire::read_plan(&resp["ok"]["plan"], &ctx).map_err(|e| format!("plan: {e}"))?;
    Ok((day, ans))
}

/// The id of a running block, as the what-if names it.
pub fn running(state: &RuntimeState) -> Option<Id> {
    state.active.as_ref().map(|a| a.id.clone())
}
