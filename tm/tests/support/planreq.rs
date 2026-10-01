//! **A whole planning request, built from a tree the test holds** — the
//! documents, the log, the capacity section and the `planner` section — and the
//! kernel's day read back through the host's own codec
//! (`tm_core::planwire`). Stage 6 W-35, track R (README gaps 2720, 2722).
//!
//! # Whose spelling this is
//!
//! **No section is spelled here** (W-40 track E, README gap 2875). The
//! `planner` section and the reading of the answer are `tm_core::planwire`'s,
//! the one host codec R3 swaps into the binary, and since W-40 so is the
//! capacity section: `planwire::capacity_json` is the pure half that
//! `tm/src/cli/kernel_capacity.rs`'s `request` calls, moved into `tm-core` so a
//! test can link it. Until then this file spelled the section a third time
//! (`cand_json`, `plan_json`, `send_order` and the `[day]`, `[priority]`,
//! `[energy]` and `[expected]` tables), and the two drifted: the binary sent no
//! `priority.batchMaxMin`, this file sent no `pLounge.model`, its candidates'
//! floors and its lookahead were dated by `state.date` where the binary's are
//! dated by `now`, and its lookahead was not clamped (gaps 2875 and 3720). What
//! is still this file's is the request AROUND the sections — the documents with
//! no region, the whole log from line 1, the zone table with no cache — and
//! `tm/tests/planner_request_keys.rs` diffs its key set against the binary's.
//!
//! # What it deliberately leaves out
//!
//! * The learned model: every caller here plans with `Model::default()`, whose
//!   tables are empty, so the codec writes `pLounge.model`, `arrival.model` and
//!   `energy` empty and the kernel falls back to `config` exactly as it does for
//!   a plan with no `.tm/model.json` (README gap 3901).
//! * The files' literals: `Written::default()`, so every configured decimal is
//!   sent as its double's shortest text — the codec's own fallback for a key no
//!   file writes.
//! * `yesterday` on every candidate record is `null`: the callers' states carry
//!   no `priorities_yesterday`, so the fork reads an empty map too.

#![allow(dead_code)]

#[path = "../../src/cli/tz_table.rs"]
pub mod tz_table;

use std::collections::BTreeMap;

use chrono::DateTime;
use chrono_tz::Tz;
use serde_json::{json, Value};

use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::Replay;
use tm_core::model::Id;
use tm_core::planwire::{self, CapacityAnswer, CapacityIn, DayCtx, KernelDay, Ranked, RoutineInst, Written};
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
    /// The replay of `log` the candidates were collected over: the planner
    /// section reads the running records' logged starts from it
    /// (`planwire::LoggedStarts`, README gap 3943).
    pub replay: &'a Replay,
}

/// **The order the candidates are sent in** — `planwire::send_order`, the order
/// the binary's own request sends them in (README gap 2875).
pub use tm_core::planwire::send_order;

/// **The capacity section** — the binary's own encoder, `planwire::capacity_json`
/// (README gap 2875), over this world: the tree's `Config`, an empty model, no
/// file literals, `now`'s own date as the request's today (`Ctx::today`), the
/// world's replay for the location the encoder reads (`planwire::planned_loc`), and the lookahead
/// `kernel_capacity::rank` asks for (`planwire::horizon` over
/// `priority::lookahead_days`).
fn capacity(w: &World<'_>, order: &[usize]) -> Value {
    let today = w.now.date_naive();
    let (model, written, yesterday) = (Model::default(), Written::default(), BTreeMap::new());
    let input = CapacityIn {
        cfg: w.cfg,
        model: &model,
        written: &written,
        tree: w.tree,
        state: w.state,
        now: w.now,
        // The location is the encoder's own reading, `planwire::planned_loc` over the
        // state and this replay's day record — the binary's (D81, parity P76; until W-41
        // this file read `Ctx::loc`'s lounge itself, README gap 3083).
        replay: w.replay,
        allow_home: false,
        days: planwire::horizon(today, priority::lookahead_days(w.cands, today)).0,
    };
    let section = planwire::capacity_json(&input, Some(&Ranked { cands: w.cands, yesterday: &yesterday }))
        .unwrap_or_else(|e| panic!("the world's configuration is one the codec carries: {e}"));
    // `request` hands `order` back to read the grants with, so it must be the order the encoder
    // wrote the candidates in -- or every grant is read as another candidate's.
    assert_eq!(order, planwire::send_order(w.cands).as_slice(), "the candidates' order is the encoder's");
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
        // `ctx.today` — `now`'s own local date — as the shipped encoder sends
        // it. This sent the PLANNED date (`state.date` first) until W-36 track
        // H, so a stale `state.date` made the kernel refuse `nowDisagrees at`
        // for a request the binary builds with the two in step (README gap
        // 3083, gap 2875's drift).
        "now": w.now.date_naive().to_string(),
        "blockMin": w.cfg.block_min(),
        "tz": tz_table::wire_for(None, tz),
        "log": {"ckpt": null, "from": 1,
                "lines": w.log.lines().collect::<Vec<_>>(),
                "terminated": true, "reseal": null,
                "want": {"facts": true, "headersFrom": null, "render": []},
                "sealed": null},
        "capacity": capacity(w, &order),
        "planner": planwire::planner_json(w.state, w.replay, w.now, tz, &routines, overtime),
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
