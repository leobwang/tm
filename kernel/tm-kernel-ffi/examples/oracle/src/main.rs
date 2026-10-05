//! **The fork-point half of the differential oracle.**
//!
//! The fork point `4748911` carries `tm-core/src/grammar.rs` — 1,246 lines of
//! hand-written tokenizer, parser and byte-faithful serializer — and
//! `tm-core/src/log.rs`'s reader, and that is the code that shipped. (It used
//! to be built from `main`, which was DISCARDED on 2026-09-12; AGENTS §7.3
//! recorded the script as broken and owed until this retarget.) This binary
//! makes that code *observable*: it reads candidate item lines, or whole logs,
//! and prints, as JSONL, exactly what the Rust says about each one. The Lean
//! side (`kernel/tm-kernel-ffi/examples/oracle-compare.rs`, and `tm`'s T5)
//! asks the kernel the same questions and reports every disagreement.
//!
//! Modes:
//!
//! * `gen <n> <seed>` — generate `n` random item lines from the **same module
//!   the two proptests draw from**, `tm-core/tests/grammar_common/mod.rs`
//!   (`build-oracle.sh` copies it in), so the corpus is not a claim about two
//!   files but a fact about one. Deterministic in `seed`.
//! * `parse` — read one JSON string per line from stdin and report on each.
//! * `parse-entry` — read one **log line** per line of stdin and report what
//!   the fork's `log::Log::parse_bytes` says about that single segment:
//!   accepted (with the entry in a stable form), refused (with serde's or
//!   chrono's own message), or blank. This is **T1-T3's oracle at the switch**
//!   (design §12 deletes `Log::parse_bytes`, `LogEntry::parse` and
//!   `parse_timestamp`, which are the only comparand those three tests have
//!   today; README gap 148, owner decision **D23**). A segment that is not
//!   UTF-8 cannot be a JSON string, so it may be given as a JSON array of byte
//!   values instead.
//! * `fit <tz> <today>` — the same input, run through the fork's
//!   `energy::fit_replay` at the default configuration, printing the fitted
//!   `Model` as JSON. This is design §14.6's T12 against the fork point: the
//!   kernel's half fits the observations **the kernel** derived.
//! * `replay <tz>` — read one JSON string per line from stdin, each the whole
//!   text of a `.tm/log.jsonl`, and print what the fork's `log::replay` derives
//!   from it, as JSON. This is **T5's oracle** at the switch (design §14.6
//!   item 4): the in-tree Rust reader is deleted there, so the fork point
//!   becomes the only other implementation to compare against.
//! * `plan` — **the fork's PLANNER, out of the tree** (the owner's D72, stage 6
//!   W-39; README gap 3533): one JSON request per line of stdin, one answer per
//!   line of stdout, so a caller keeps the process and asks it many days. R3
//!   deletes `tm-core/src/planner.rs`, and with it the one differential that
//!   explores fresh draws (`planner_invariants`' arms); this is what those draws
//!   meet after it — D23's shape, for the planner. Two ops:
//!
//!   ```text
//!   {"op":"plan", "world":{docs,log,state,now,mult,ratio}, "state":{..}, "now":"..",
//!    "log_line":null|"..", "order":null|{id:[[r,r],[o,o]]}, "prios":[grant..],
//!    "extend":null|[id,minutes], "runs":false|true}
//!     -> {"day":<DayPlan>, "hash":<DayPlan::hash>, "ranked":[id..], "cands":[id..]}
//!   {"op":"diff", "old":[segment..], "new":[segment..]}
//!     -> {"diff":<planner::diff>}
//!   {"op":"worked", "world":{..}, "state":{..}, "now":"..", "log_line":null|".."}
//!     -> {"worked": n|null, "read_by": "planner::active_worked"}
//!   ```
//!
//!   `worked` (W-43 track C, README gap 4460) is the running block's worked minutes as the
//!   fork reads them — `active_run`'s reading over its own replay — which the comparand
//!   needs before it plans (P55 and P46 move the estimate by the FORK's reading). Since W-44
//!   track C (README gap 4507) it is read by the fork's own lines, which `worked-seam.patch`
//!   moves out of `active_run` into a method both call; until then this file re-typed them.
//!
//!   The world is read as the FORK reads it — its own parser, its own
//!   `log::replay` over the same bytes (and `log_line` appended for the day
//!   planned), its own `priority::collect_candidates` at the world's `now` —
//!   and ranked by the grants the request carries, which is how the shipped
//!   binary runs its fork (D53): fork 4748911's `planner::plan` takes NO ranking,
//!   so `build-oracle.sh` grafts `09d38fa`'s two edits onto it
//!   (`plan-seam.patch`, whose header says which). `order` is D60's key, the
//!   two order fields rewritten by id; `extend` is §9.1's what-if
//!   (`PlanOverrides::extending`); `runs` is D74's split of a batch into its runs (parity P64,
//!   `p64-runs.patch`, the W-40 land step), the comparand's departure for P64. A request the fork cannot answer is answered
//!   `{"error": ...}`, by name, and the process keeps reading.
//! * `capacity` — **the fork's §7 pass and §8.4 lookahead, out of the tree** (stage 6
//!   W-46 track C; README gap 4752 restated as a class): R3 leaves tm-core's in-tree
//!   `capacity::lookahead`, `cut_slots`, `energize`, `priority::compute`, `batches` and the
//!   rest of that class with no shipped caller and deletes them, so every comparison that
//!   read them reads the fork's answers from here (D72's shape). Ops `today`, `lookahead`,
//!   `cut`, `rank`, `batches`, `cand`, `sort_key`, `wall_minutes`; `capacity_one`'s doc gives
//!   the wire.
//! * `review` — **the fork's WEEK GRID, out of the tree** (stage 6 W-40 track H,
//!   README gap 3718; D23's shape, as `plan` is for the planner): one JSON request
//!   per line of stdin, one answer per line of stdout. Until W-40 every test of the
//!   week grid compared the kernel's cut of a Pause (`GridCut.segSpans`) with the
//!   day plan's (`Planner.pastSpans`, after R3) — the kernel with itself through
//!   two surfaces. This is fork 4748911's own drawing of the same world, for a
//!   comparand that outlives R3:
//!
//!   ```text
//!   {"op":"week", "world":{docs, log, config}, "date":"YYYY-MM-DD"|"YYYY-Www"}
//!     -> {"week":"YYYY-Www", "heat":[<DayHeat> x7], "pauses":[[date, start, end, id]..]}
//!   ```
//!
//!   The world is read as the FORK reads it — its own parser (`Tree::from_texts`
//!   over the documents, `config.toml`'s text through `Config::parse`, the default
//!   configuration when the world carries none), its own `log::replay(None, tz)`
//!   over the same bytes, as fork `Ctx::load` replays the whole log — and the grid
//!   is fork `review::week_review`'s `heat`, the seven `DayHeat` rows its
//!   `heat_of` draws (seven styles, every Pause whole as `pause`). `pauses` is every
//!   `Pause` segment of the week's day records, in record order, with the day whose
//!   record holds it: what a comparand needs to apply a registered departure that
//!   moves a Pause's minutes (parity P63) by its property.
//!
//! One JSON object per line, on stdout:
//!
//! ```text
//! {"in": <the line>,
//!  "item": <parse_line returned Ok>,
//!  "id": <item.id, "" when the line carries none>,
//!  "roundtrip": <item.line_text() == in>,
//!  "out": <item.line_text()>,
//!  "problems": [<tm check's diagnostics for this line>],
//!  "est_edit": <the line after set_token("est","45m"), or null>}
//! ```
//!
//! and for `replay`, one object per input log:
//!
//! ```text
//! {"replay": <tm_core::log::Replay, serialised>,
//!  "warningLines": [<1-based physical line of every line the reader refused>],
//!  "entries": <surviving + cancelled entries the reader read>}
//! ```
//!
//! and for `parse-entry`, one object per input segment:
//!
//! ```text
//! {"v": "entry", "json": <LogEntry::to_json>, "tag": <ev>, "id": <primary id>,
//!  "t": <fmt_timestamp>, "display": <tm log's column>,
//!  "epoch": <seconds>, "nanos": <subsec, >= 1e9 on a leap second>,
//!  "offset": <written offset in seconds east>}
//! {"v": "warn", "error": <serde's or chrono's own text>}
//! {"v": "blank"}
//! ```
//!
//! The fork's `Replay` and this branch's differ by exactly two serialised
//! fields — this branch adds `seams` and `last_effective_t` (step R1–R4), and
//! its `rows`/`line_count` are `#[serde(skip)]` — and every nested record
//! struct has the identical field list, on the same `chrono`/`chrono-tz`
//! versions. So the two `serde_json` values are comparable key for key once
//! those two added keys are set aside, which is what makes this a whole-
//! `Replay` comparison rather than a hand-listed one.

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::io::{BufRead, Write};

use tm_core::grammar::{parse_line, ItemLine, ParseCtx};
use tm_core::log::{fmt_timestamp, Log};

// ---------------------------------------------------------------------------
// The generator: ONE definition, shared with the two proptests.
//
// It was 186 lines COPIED here from `tm-core/tests/grammar_proptest.rs`, and
// W-25 moved the originals to `tm-core/tests/grammar_common/mod.rs` and left
// this copy behind with two comments pointing at a file that no longer holds a
// single strategy.  Byte-for-byte identical at that moment, with no mechanism
// that would have made a divergence visible -- AGENTS §5.3's own defect, in the
// one place where "the kernel sees what the fork's proptest sees" is the whole
// claim being made.
//
// `build-oracle.sh` copies the module into this crate's `src/` before it
// builds, and FAILS if it is not there, because the fork-point checkout this
// binary is compiled in does not carry it.  The code under test stays the fork
// point's; only the SAMPLER is shared, which is what makes the three readers
// comparable at all.
// ---------------------------------------------------------------------------

// `ctx_for` and `without_src` belong to the proptests that share this module
// and are not called here; a copy would have dropped them silently.
#[allow(dead_code)]
#[path = "grammar_common.rs"]
mod grammar_common;

use grammar_common::line;

// ---------------------------------------------------------------------------
// What the Rust says about one line
// ---------------------------------------------------------------------------

/// The path both halves of the oracle use. A week file has no §4.3 shape rule
/// on either side, so neither the Rust's horizon defaults nor the kernel's
/// `shapeWfFor` colours the answer.
const FILE: &str = "week/2026-W37.md";

fn observe(text: &str) -> Value {
    let ctx = ParseCtx::new(FILE, 60);
    match parse_line(text, &ctx) {
        Err(_) => json!({ "in": text, "item": false }),
        Ok(item) => {
            let out = item.line_text();
            let est_edit = ItemLine::parse(text).ok().map(|mut l| {
                l.set_token("est", "45m");
                l.to_string()
            });
            json!({
                "in": text,
                "item": true,
                "id": item.id.as_str(),
                "roundtrip": out == text,
                "out": out,
                "problems": item.problems,
                "est_edit": est_edit,
            })
        }
    }
}

/// What the fork's reader derives from one whole log's text, in `tz`.
///
/// `replay(None, tz)` is exactly what `Ctx::replay_of` called on this branch
/// before the switch: the whole log, every day, no range.
fn observe_log(text: &str, tz: chrono_tz::Tz) -> Value {
    let log = Log::parse(text);
    json!({
        "replay": log.replay(None, tz),
        "warningLines": log.warnings.iter().map(|w| w.line as u64).collect::<Vec<u64>>(),
        "entries": log.entries.len(),
    })
}

/// **What the fork's reader says about ONE physical log line** (owner decision
/// **D23**; README gap 148).
///
/// This is `Log::parse_bytes`'s own loop body over a single `\n`-separated
/// segment — exactly the call `tm/tests/kernel_log_grammar.rs`'s `fork_read`
/// made against the **in-tree** copy of this reader until design §12 deleted
/// it. It gives the three verdicts that reader can give (blank, entry,
/// warning) and, for an entry, everything T1 and T3 compare:
///
/// * `json` — `LogEntry::to_json`, serde's own bytes for the entry just read.
///   That is the parse-*then*-write round trip T1's byte-identity arm needs.
///   The writer alone (`to_json`, `fmt_timestamp`, `Event`) is **kept** by §12
///   and so needs no oracle; it is the *parse* that has to come from here.
/// * `tag`, `id` — `Event::name` and `Event::primary_id`: the kernel's header.
/// * `t`, `display` — `fmt_timestamp` and `tm log`'s column.
/// * `epoch`, `nanos`, `offset` — the instant exactly as chrono read it. `json`
///   keeps only whole seconds, so a leap second (`nanos >= 1e9`) and the
///   *written* offset would otherwise not survive the round trip, and both are
///   what T3 is about.
///
/// A refusal carries serde's or chrono's message **verbatim**. The kernel's
/// warning classes are named constructors and the fork's are free text (parity
/// **P15**), so the class is read off this text on the kernel's side, by the
/// same `fork_class` the test has always used.
fn observe_entry(seg: &[u8]) -> Value {
    let log = Log::parse_bytes(seg);
    match (log.entries.first(), log.warnings.first()) {
        (Some(e), None) => json!({
            "v": "entry",
            "json": e.to_json().expect("serde writes back the entry it just read"),
            "tag": e.ev.name(),
            "id": e.ev.primary_id(),
            "t": fmt_timestamp(&e.t),
            "display": e.t.format("%Y-%m-%d %H:%M").to_string(),
            "epoch": e.t.timestamp(),
            "nanos": e.t.timestamp_subsec_nanos(),
            "offset": e.t.offset().local_minus_utc(),
        }),
        (None, Some(w)) => json!({ "v": "warn", "error": w.error }),
        (None, None) => json!({ "v": "blank" }),
        (Some(_), Some(_)) => panic!("one segment gave both an entry and a warning"),
    }
}

/// What the fork's `tm model --fit` makes of one whole log, in `tz`, as of
/// `today`: fork `energy::fit_replay` over the fork's own replay, at the
/// default configuration — both halves of the comparison must use the same
/// one, and the corpus logs carry no config of their own.
///
/// This is design §14.6's **T12** asked of the fork point rather than of a
/// saved `model.json`: on this branch `fit_replay` is gone (phase F1,
/// `983a8be`), and the fit reads the three observation lists. So the kernel's
/// half runs `energy::fit_observations` over the observations **the kernel
/// derived**, and the two `Model`s must be equal field for field.
fn observe_fit(text: &str, tz: chrono_tz::Tz, today: chrono::NaiveDate) -> Value {
    let replay = Log::parse(text).replay(None, tz);
    let cfg = tm_core::config::Config::default();
    json!({ "model": tm_core::energy::fit_replay(&cfg, &replay, today) })
}

// ---------------------------------------------------------------------------
// `plan`: the fork's planner, ranked as the shipped binary ranks it (D72)
// ---------------------------------------------------------------------------

/// A §7 grant as the request carries it — fork 4748911's `Prio`, field by field,
/// with the graft's `shortfall_positive` (`plan-seam.patch`). `u` is the double's
/// shortest text (`inf` for a zero capacity: JSON has no infinity).
fn prio_of(v: &Value) -> Result<tm_core::priority::Prio, String> {
    use tm_core::priority::PrioClass;
    let small = |k: &str| -> Result<u8, String> {
        v[k].as_u64().and_then(|n| u8::try_from(n).ok()).ok_or_else(|| format!("a grant's `{k}`: {}", v[k]))
    };
    let minutes = |k: &str| -> Result<u32, String> {
        v[k].as_u64().and_then(|n| u32::try_from(n).ok()).ok_or_else(|| format!("a grant's `{k}`: {}", v[k]))
    };
    let class = match v["class"].as_str() {
        Some("wall") => PrioClass::Wall,
        Some("hot") => PrioClass::Hot,
        Some("impossible") => PrioClass::Impossible,
        Some("overdue") => PrioClass::Overdue,
        Some("mandatory") => PrioClass::Mandatory,
        Some("hotflag") => PrioClass::HotFlag,
        Some("dated") => PrioClass::Dated,
        Some("floor") => PrioClass::Floor,
        Some("rank") => PrioClass::Rank,
        Some("optional") => PrioClass::Optional,
        other => return Err(format!("a grant's class {other:?}")),
    };
    Ok(tm_core::priority::Prio {
        id: tm_core::model::Id::new(v["id"].as_str().ok_or("a grant with no id")?),
        p: small("p")?,
        class,
        k: small("k")?,
        u: match &v["u"] {
            Value::Null => None,
            Value::String(t) => Some(t.parse::<f64>().map_err(|e| format!("a grant's `u` {t:?}: {e}"))?),
            other => return Err(format!("a grant's `u` is {other}, not a double's text")),
        },
        bin: match &v["bin"] {
            Value::Null => None,
            _ => Some(small("bin")?),
        },
        need_min: minutes("need_min")?,
        avail_min: minutes("avail_min")?,
        allocation_min: minutes("allocation_min")?,
        shortfall_min: minutes("shortfall_min")?,
        until: match v["until"].as_str() {
            None => None,
            Some(d) => Some(chrono::NaiveDate::parse_from_str(d, "%Y-%m-%d").map_err(|e| format!("a grant's `until`: {e}"))?),
        },
        hysteresis_applied: v["hysteresis_applied"].as_bool().ok_or("a grant's `hysteresis_applied`")?,
        raw_p: small("raw_p")?,
        shortfall_positive: v["shortfall_positive"].as_bool().ok_or("a grant's `shortfall_positive`")?,
    })
}

/// An instant as the request spells it, in the configuration's zone.
fn instant(v: &Value, tz: chrono_tz::Tz, what: &str) -> Result<chrono::DateTime<chrono_tz::Tz>, String> {
    let t = v.as_str().ok_or_else(|| format!("`{what}` is {v}, not an instant"))?;
    chrono::DateTime::parse_from_rfc3339(t).map(|d| d.with_timezone(&tz)).map_err(|e| format!("`{what}` {t:?}: {e}"))
}

/// **A world as the FORK reads it** — its own parser over the documents
/// (`Tree::from_texts`), the default configuration with the world's budget ratio, the
/// duration model the world names, its stored state and instant, and the log's bytes, which
/// [`ForkWorld::log_with`] hands the fork's own `log::replay`. The ONE reading of a request's
/// `world`, shared by the `plan` and `worked` ops (W-44 track C, README gap 4507), so the two
/// ops read one world one way.
struct ForkWorld {
    cfg: tm_core::config::Config,
    tree: tm_core::tree::Tree,
    log_text: String,
    model: tm_core::energy::Model,
    state: tm_core::store::RuntimeState,
    now: chrono::DateTime<chrono_tz::Tz>,
}

impl ForkWorld {
    /// The request's `world`, read as the fork reads it — or why not, by name.
    fn read(world: &Value) -> Result<ForkWorld, String> {
        let mut cfg = tm_core::config::Config::default();
        if let Some(r) = world["ratio"].as_str() {
            cfg.day.budget_ratio = r.parse().map_err(|e| format!("world.ratio {r:?}: {e}"))?;
        }
        let docs: Vec<(String, String)> = world["docs"]
            .as_array()
            .ok_or("world.docs is not an array")?
            .iter()
            .map(|d| match (d[0].as_str(), d[1].as_str()) {
                (Some(p), Some(t)) => Ok((p.to_string(), t.to_string())),
                _ => Err(format!("world.docs holds {d}")),
            })
            .collect::<Result<_, _>>()?;
        let files: Vec<(&str, &str)> = docs.iter().map(|(p, t)| (p.as_str(), t.as_str())).collect();
        let tree = tm_core::tree::Tree::from_texts(&files, &cfg);
        let log_text = world["log"].as_str().ok_or("world.log is not a string")?.to_string();
        let mut model = tm_core::energy::Model::default();
        if let Some(m) = world["mult"].as_str() {
            let m: f64 = m.parse().map_err(|e| format!("world.mult {m:?}: {e}"))?;
            model.duration.insert(tm_core::energy::DEFAULT_TAG.to_string(), m);
        }
        let state: tm_core::store::RuntimeState =
            serde_json::from_value(world["state"].clone()).map_err(|e| format!("world.state: {e}"))?;
        let now = instant(&world["now"], cfg.tz, "world.now")?;
        Ok(ForkWorld { cfg, tree, log_text, model, state, now })
    }

    /// The fork's own log and replay of the world's bytes, with `line` appended when the
    /// request carries one (the day a comparand plans after a line it logs).
    fn log_with(&self, line: Option<&str>) -> (Log, tm_core::log::Replay) {
        let log = match line {
            Some(l) => Log::parse(&format!("{}{l}", self.log_text)),
            None => Log::parse(&self.log_text),
        };
        let replay = log.replay(None, self.cfg.tz);
        (log, replay)
    }
}

/// **One `plan` op**: the world read as the fork reads it, its candidates collected at the
/// world's `now` and ranked by the request's grants, the day planned at the request's own
/// `now` and state (a comparand's), over the log with `log_line` appended when there is one.
fn plan_one(req: &Value) -> Result<Value, String> {
    use tm_core::planner::{self, PlanInput, PlanOverrides};
    use tm_core::priority;
    let world = ForkWorld::read(&req["world"])?;
    let (cfg, tree, model) = (&world.cfg, &world.tree, &world.model);
    let tz = cfg.tz;
    let (world_log, world_replay) = world.log_with(None);
    let date = world.state.date.unwrap_or_else(|| world.now.date_naive());
    let mut cands = priority::collect_candidates(tree, &world_replay, cfg, model, date, world.now);
    if let Some(order) = req["order"].as_object() {
        for c in cands.iter_mut() {
            if let Some(o) = order.get(c.id.as_str()) {
                let pair = |x: &Value| -> Result<(usize, usize), String> {
                    match (x[0].as_u64(), x[1].as_u64()) {
                        (Some(a), Some(b)) => Ok((a as usize, b as usize)),
                        _ => Err(format!("an order pair {x}")),
                    }
                };
                c.root_order = pair(&o[0])?;
                c.own_order = pair(&o[1])?;
            }
        }
    }
    let mut given: BTreeMap<String, tm_core::priority::Prio> = BTreeMap::new();
    for v in req["prios"].as_array().ok_or("`prios` is not an array")? {
        let p = prio_of(v)?;
        given.insert(p.id.as_str().to_string(), p);
    }
    let prios: Vec<tm_core::priority::Prio> = cands
        .iter()
        .map(|c| given.get(c.id.as_str()).cloned().ok_or_else(|| format!("no grant for the fork's candidate {}", c.id.as_str())))
        .collect::<Result<_, _>>()?;
    let state: tm_core::store::RuntimeState =
        serde_json::from_value(req["state"].clone()).map_err(|e| format!("state: {e}"))?;
    let now = instant(&req["now"], tz, "now")?;
    let (log, replay) = match req["log_line"].as_str() {
        Some(l) => world.log_with(Some(l)),
        None => (world_log, world_replay),
    };
    let ov = match req["extend"].as_array() {
        Some(e) => {
            let id = e.first().and_then(Value::as_str).ok_or("`extend`'s id")?;
            let m = e.get(1).and_then(Value::as_u64).and_then(|m| u32::try_from(m).ok()).ok_or("`extend`'s minutes")?;
            Some(PlanOverrides::new().extending(&tm_core::model::Id::new(id), m))
        }
        None => None,
    };
    // `runs`: D74's split into runs (parity P64, `p64-runs.patch`), the comparand's.
    let runs = req["runs"].as_bool().unwrap_or(false);
    let mut input =
        PlanInput::new(tree, &log, &replay, cfg, model, &state, now).with_ranking(&cands, &prios).with_runs(runs);
    if let Some(ov) = ov.as_ref() {
        input = input.with_overrides(ov);
    }
    let day = planner::plan(&input);
    let ranked: Vec<&str> = priority::sorted_candidates(&prios, &cands).iter().map(|c| c.id.as_str()).collect();
    Ok(json!({
        "day": day,
        "hash": day.hash(),
        "ranked": ranked,
        "cands": cands.iter().map(|c| c.id.as_str()).collect::<Vec<_>>(),
    }))
}

/// **One `diff` op**: fork `planner::diff` of two days' rows — each row's start, end,
/// kind (a batch's members with it) and item, which is all `diff` reads.
fn diff_one(req: &Value) -> Result<Value, String> {
    use tm_core::planner::{self, DayPlan, SegFlags, SegKind, Segment};
    let tz = tm_core::config::Config::default().tz;
    let day_of = |v: &Value| -> Result<DayPlan, String> {
        let segs = v.as_array().ok_or("a day's rows are not an array")?;
        let epoch = instant(&json!("1970-01-01T00:00:00Z"), tz, "epoch")?;
        let date = chrono::NaiveDate::from_ymd_opt(1970, 1, 1).ok_or("a date")?;
        let mut day = DayPlan::empty(date, (epoch, epoch), 0);
        for s in segs {
            let kind = match &s["kind"] {
                Value::String(k) => match k.as_str() {
                    "block" => SegKind::Block,
                    "break" => SegKind::Break,
                    "routine" => SegKind::Routine,
                    "wall" => SegKind::Wall,
                    "rest" => SegKind::Rest,
                    "optional" => SegKind::Optional,
                    "winddown" => SegKind::WindDown,
                    "sleep" => SegKind::Sleep,
                    "lost" => SegKind::Lost,
                    other => return Err(format!("a row of kind `{other}`")),
                },
                k => SegKind::Batch(
                    k["batch"]
                        .as_array()
                        .ok_or_else(|| format!("a row of kind {k}"))?
                        .iter()
                        .filter_map(Value::as_str)
                        .map(tm_core::model::Id::new)
                        .collect(),
                ),
            };
            day.segments.push(Segment {
                start: instant(&s["start"], tz, "a row's start")?,
                end: instant(&s["end"], tz, "a row's end")?,
                kind,
                energy: None,
                item: s["item"].as_str().map(tm_core::model::Id::new),
                instance: None,
                flags: SegFlags::default(),
            });
        }
        Ok(day)
    };
    let (old, new) = (day_of(&req["old"])?, day_of(&req["new"])?);
    Ok(json!({ "diff": planner::diff(&old, &new) }))
}

// ---------------------------------------------------------------------------
// `review`: the fork's week grid (README gap 3718)
// ---------------------------------------------------------------------------

/// **One `week` op**: fork `review::week_review`'s heat grid for the ISO week holding
/// `date`, over the world read as the fork reads it, and every Pause segment of the
/// week's day records with the day that holds it. A date is read as fork `IsoWeek::
/// from_date` reads it; `YYYY-Www` as fork `IsoWeek::parse` does.
fn week_one(req: &Value) -> Result<Value, String> {
    use tm_core::log::SegmentKind;
    use tm_core::model::IsoWeek;
    let world = &req["world"];
    let cfg = match &world["config"] {
        Value::Null => tm_core::config::Config::default(),
        Value::String(t) => tm_core::config::Config::parse(t).map_err(|e| format!("world.config: {e}"))?,
        other => return Err(format!("world.config is {other}, not a config.toml's text")),
    };
    let tz = cfg.tz;
    let docs: Vec<(String, String)> = world["docs"]
        .as_array()
        .ok_or("world.docs is not an array")?
        .iter()
        .map(|d| match (d[0].as_str(), d[1].as_str()) {
            (Some(p), Some(t)) => Ok((p.to_string(), t.to_string())),
            _ => Err(format!("world.docs holds {d}")),
        })
        .collect::<Result<_, _>>()?;
    let files: Vec<(&str, &str)> = docs.iter().map(|(p, t)| (p.as_str(), t.as_str())).collect();
    let tree = tm_core::tree::Tree::from_texts(&files, &cfg);
    let log_text = world["log"].as_str().ok_or("world.log is not a string")?;
    let replay = Log::parse(log_text).replay(None, tz);
    let model = tm_core::energy::Model::default();
    let spelled = req["date"].as_str().ok_or("`date` is not a string")?;
    let week = match chrono::NaiveDate::parse_from_str(spelled, "%Y-%m-%d") {
        Ok(d) => IsoWeek::from_date(d),
        Err(_) => IsoWeek::parse(spelled).map_err(|e| format!("`date` {spelled:?}: {e}"))?,
    };
    let review = tm_core::review::week_review(
        &tree,
        &replay,
        &cfg,
        &model,
        week,
        tz,
        &tm_core::review::WeekExtras::default(),
    );
    let mut pauses: Vec<Value> = Vec::new();
    for date in week.dates() {
        for seg in replay.day(date).map(|d| d.segments.as_slice()).unwrap_or_default() {
            if let SegmentKind::Pause { id } = &seg.kind {
                pauses.push(json!([date.to_string(), seg.start.to_rfc3339(), seg.end.to_rfc3339(), id]));
            }
        }
    }
    Ok(json!({ "week": week.to_string(), "heat": review.heat, "pauses": pauses }))
}

/// A `review` request, answered — or refused `{"error": …}` by name.
fn observe_review(req: &Value) -> Value {
    let answer = match req["op"].as_str() {
        Some("week") => week_one(req),
        other => Err(format!("unknown op {other:?}")),
    };
    answer.unwrap_or_else(|e| json!({ "error": e }))
}

/// **One `worked` op** (stage 6 W-43 track C, README gap 4460): the running block's worked
/// minutes as fork 4748911 READS them at the request's `now` — over the fork's own replay of
/// the world's log (with `log_line` appended, as `plan` reads it): the log's open block when it
/// is the state's running item (`OpenBlock::worked_min_at`), the clock since `started` on the
/// planned date otherwise; `null` when the state runs no block.
///
/// **Since W-44 track C (README gap 4507) it is the fork's OWN lines that read it.** Until then
/// this function RE-TYPED fork `active_run`'s selection, because the reading is a local of that
/// private method, so a frozen comparand was partly computed by code this repository owns.
/// `worked-seam.patch` (applied by `build-oracle.sh` after the two grafts) MOVES those lines,
/// unchanged, into a method `active_run` itself calls, and adds one public entry that builds
/// the fork's own `Planner` for a `PlanInput`; this op builds the `PlanInput` `plan` builds for
/// the same request, less the ranking (which the reading does not read), and asks it. The
/// answer names the entry that read it, `read_by`, and the harness refuses an answer without
/// it — an oracle built before W-44 is STALE (README gap 196's rule: provenance is not freshness).
///
/// The comparand needs it BEFORE it plans — P55 moves the running estimate by the difference
/// between the host's reading and the FORK's, and P46 asks whether the FORK's reading is past
/// the estimate — and the kernel's replay is not the fork's reading wherever a registered number
/// nets a break the log holds (parity P81, the owner's D87; and D92's break run into a block's
/// start). Until W-43 the comparand read the kernel's replay as the fork's (README gap 4247), so
/// on such a world it asked the oracle with the wrong estimate.
///
/// ```text
/// {"op":"worked", "world":{docs,log,state,now,mult,ratio}, "state":{..}, "now":"..",
///  "log_line":null|".."}  ->  {"worked": n|null, "read_by": "planner::active_worked"}
/// ```
fn worked_one(req: &Value) -> Result<Value, String> {
    use tm_core::planner::{self, PlanInput};
    let world = ForkWorld::read(&req["world"])?;
    let (log, replay) = world.log_with(req["log_line"].as_str());
    let state: tm_core::store::RuntimeState =
        serde_json::from_value(req["state"].clone()).map_err(|e| format!("state: {e}"))?;
    let now = instant(&req["now"], world.cfg.tz, "now")?;
    let input = PlanInput::new(&world.tree, &log, &replay, &world.cfg, &world.model, &state, now);
    Ok(json!({ "worked": planner::active_worked(&input), "read_by": "planner::active_worked" }))
}

// ---------------------------------------------------------------------------
// `capacity`: the fork's §7 pass and §8.4 lookahead, out of the tree (W-46 track C)
// ---------------------------------------------------------------------------
//
// R3 leaves tm-core's in-tree copies of these functions with no shipped caller (README
// gap 4752, restated as a CLASS by W-46 track C), and the switch deletes them.  Every
// comparison that read them in-tree reads fork 4748911's own answers from here instead
// (D72's shape): frozen by value in `tm/tests/fixtures/`, re-blessed through this mode,
// and asked live under `TM_ORACLE`.  Each op calls the EXTRACTED fork's own function and
// nothing re-types its body: `today` is `cut_slots` + `EnergyCtx` + `energize` (and
// `DayCapacity::from_slots`), `lookahead` is `capacity::lookahead`, `cut` is `cut_slots`
// (and `Cut::slot_minutes`, `Cut::break_minutes`), `rank` is `priority::compute` (and, per
// grant, `utilization` and `bin_of` over its need and availability), `batches` is
// `priority::batches`, `cand` is `Candidate::cap_left_min` and `Candidate::floor_need_min`,
// `sort_key` is `priority::sort_key`, `wall_minutes` is `capacity::wall_minutes`.
//
// A double crosses as its shortest TEXT and is read by `str::parse` (exact): this
// build's serde_json is the fork's, without `float_roundtrip` (parity P25), so a JSON
// number of seventeen significant digits could come back one ULP away.  The config
// crosses as `config.toml` TEXT for the same reason — `Config::parse`, the fork's own
// reader of it.

/// A `config.toml` text, read by the fork's own `Config::parse`.
fn cap_config(v: &Value) -> Result<tm_core::config::Config, String> {
    let text = v.as_str().ok_or_else(|| format!("`config` is {v}, not a config.toml's text"))?;
    tm_core::config::Config::parse(text).map_err(|e| format!("config: {e}"))
}

/// A weekday as the wire names it (`Mon` .. `Sun`).
fn cap_weekday(k: &str) -> Result<chrono::Weekday, String> {
    use chrono::Weekday::*;
    Ok(match k {
        "Mon" => Mon,
        "Tue" => Tue,
        "Wed" => Wed,
        "Thu" => Thu,
        "Fri" => Fri,
        "Sat" => Sat,
        "Sun" => Sun,
        other => return Err(format!("a weekday {other:?}")),
    })
}

/// A model: the default one with its learned `energy` curves, `p_lounge` (each weight a
/// double's text) and `expected_arrival` (`HH:MM`) set — the three a capacity reads.
fn cap_model(v: &Value) -> Result<tm_core::energy::Model, String> {
    let mut m = tm_core::energy::Model::default();
    if let Some(e) = v.get("energy").filter(|e| !e.is_null()) {
        m.energy = serde_json::from_value(e.clone()).map_err(|e| format!("model.energy: {e}"))?;
    }
    for (k, x) in v["p_lounge"].as_object().into_iter().flatten() {
        let t = x.as_str().ok_or_else(|| format!("model.p_lounge.{k} is {x}, not a double's text"))?;
        m.p_lounge.set(cap_weekday(k)?, t.parse::<f64>().map_err(|e| format!("model.p_lounge.{k} {t:?}: {e}"))?);
    }
    for (k, x) in v["expected_arrival"].as_object().into_iter().flatten() {
        let t = x.as_str().ok_or_else(|| format!("model.expected_arrival.{k} is {x}"))?;
        let at = chrono::NaiveTime::parse_from_str(t, "%H:%M").map_err(|e| format!("model.expected_arrival.{k} {t:?}: {e}"))?;
        m.expected_arrival.set(cap_weekday(k)?, tm_core::energy::Hhmm(at));
    }
    Ok(m)
}

/// `[[start, end], …]` — walls as instants, in the configuration's zone.
fn cap_walls(v: &Value, tz: chrono_tz::Tz, what: &str) -> Result<Vec<tm_core::capacity::Wall>, String> {
    v.as_array()
        .ok_or_else(|| format!("`{what}` is not an array"))?
        .iter()
        .map(|w| Ok((instant(&w[0], tz, what)?, instant(&w[1], tz, what)?)))
        .collect()
}

/// A slot as the wire spells it: `[start, end, energy, "block"|"short"]`.
fn cap_slot_json(s: &tm_core::capacity::Slot) -> Value {
    use tm_core::capacity::SlotKind;
    let kind = match s.kind {
        SlotKind::Block => "block",
        SlotKind::ShortBlock => "short",
    };
    json!([s.start.to_rfc3339(), s.end.to_rfc3339(), s.energy, kind])
}

fn cap_slots(v: &Value, tz: chrono_tz::Tz) -> Result<Vec<tm_core::capacity::Slot>, String> {
    use tm_core::capacity::{Slot, SlotKind};
    v.as_array()
        .ok_or("`slots` is not an array")?
        .iter()
        .map(|s| {
            Ok(Slot {
                start: instant(&s[0], tz, "a slot's start")?,
                end: instant(&s[1], tz, "a slot's end")?,
                energy: s[2].as_u64().and_then(|e| u8::try_from(e).ok()).ok_or_else(|| format!("a slot's energy {}", s[2]))?,
                kind: match s[3].as_str() {
                    Some("block") => SlotKind::Block,
                    Some("short") => SlotKind::ShortBlock,
                    other => return Err(format!("a slot's kind {other:?}")),
                },
            })
        })
        .collect()
}

/// A day of capacity: `[date, [m0 .. m5]]`.
fn cap_day_json(d: &tm_core::capacity::DayCapacity) -> Value {
    json!([d.date.to_string(), d.minutes_at_level])
}

fn cap_days(v: &Value) -> Result<Vec<tm_core::capacity::DayCapacity>, String> {
    v.as_array()
        .ok_or("`caps` is not an array")?
        .iter()
        .map(|d| {
            Ok(tm_core::capacity::DayCapacity {
                date: chrono::NaiveDate::parse_from_str(d[0].as_str().ok_or("a day's date")?, "%Y-%m-%d").map_err(|e| e.to_string())?,
                minutes_at_level: serde_json::from_value(d[1].clone()).map_err(|e| format!("a day's minutes: {e}"))?,
            })
        })
        .collect()
}

fn cap_date(v: &Value, what: &str) -> Result<chrono::NaiveDate, String> {
    let t = v.as_str().ok_or_else(|| format!("`{what}` is {v}, not a date"))?;
    chrono::NaiveDate::parse_from_str(t, "%Y-%m-%d").map_err(|e| format!("`{what}` {t:?}: {e}"))
}

/// **A candidate, field by field** — fork 4748911's `Candidate` (`priority.rs`), which
/// derives no `Deserialize`: the in-tree struct's own `Serialize` output, its `multiplier`
/// as the double's text; each leaf type through its own `Deserialize`, an instant into the
/// configuration's zone.
fn cap_cand(v: &Value, tz: chrono_tz::Tz) -> Result<tm_core::priority::Candidate, String> {
    let leaf = |k: &str| v.get(k).cloned().ok_or_else(|| format!("a candidate with no `{k}`"));
    macro_rules! field {
        ($k:literal) => {
            serde_json::from_value(leaf($k)?).map_err(|e| format!("a candidate's `{}`: {e}", $k))?
        };
    }
    let opt_instant = |k: &str| -> Result<Option<chrono::DateTime<chrono_tz::Tz>>, String> {
        match leaf(k)? {
            Value::Null => Ok(None),
            x => Ok(Some(instant(&x, tz, k)?)),
        }
    };
    let window = match leaf("window")? {
        Value::Null => None,
        w => Some((instant(&w[0], tz, "window")?, instant(&w[1], tz, "window")?)),
    };
    let mult = leaf("multiplier")?;
    let mult = mult.as_str().ok_or_else(|| format!("a candidate's `multiplier` is {mult}, not a double's text"))?;
    Ok(tm_core::priority::Candidate {
        id: tm_core::model::Id::new(v["id"].as_str().ok_or("a candidate with no id")?),
        title: field!("title"),
        ci: field!("ci"),
        k: field!("k"),
        remaining_min: field!("remaining_min"),
        planned_min: field!("planned_min"),
        need_min: field!("need_min"),
        multiplier: mult.parse::<f64>().map_err(|e| format!("a candidate's `multiplier` {mult:?}: {e}"))?,
        effective_due: opt_instant("effective_due")?,
        window,
        scope: field!("scope"),
        floor: field!("floor"),
        floor_done_min: field!("floor_done_min"),
        cap: field!("cap"),
        cap_done_min: field!("cap_done_min"),
        state: field!("state"),
        blocked_by: field!("blocked_by"),
        waiting: field!("waiting"),
        loc: field!("loc"),
        splittable: field!("splittable"),
        hot: field!("hot"),
        overdue: field!("overdue"),
        mandatory: field!("mandatory"),
        is_optional: field!("is_optional"),
        is_wall: field!("is_wall"),
        wall_today: field!("wall_today"),
        instance: field!("instance"),
        root_order: field!("root_order"),
        own_order: field!("own_order"),
        tags: field!("tags"),
    })
}

/// A grant as fork `compute` returns it, with `u` as the double's shortest text (`inf`,
/// `null` when the pass gave none): JSON has no infinity, and serde would write `null`.
fn cap_prio_json(p: &tm_core::priority::Prio) -> Value {
    let class = serde_json::to_value(p.class).unwrap_or(Value::Null);
    json!({
        "id": p.id.as_str(), "p": p.p, "class": class, "k": p.k,
        "u": p.u.map(|u| u.to_string()), "bin": p.bin,
        "need_min": p.need_min, "avail_min": p.avail_min, "allocation_min": p.allocation_min,
        "shortfall_min": p.shortfall_min, "shortfall_positive": p.shortfall_positive,
        "until": p.until.map(|d| d.to_string()), "hysteresis_applied": p.hysteresis_applied, "raw_p": p.raw_p,
    })
}

/// **One `capacity` op** (W-46 track C):
///
/// ```text
/// {"op":"today", "config":<toml>, "model":{..}, "from":t, "end":t, "walls":[[a,b]..],
///  "reports":[[t,pred,rep]..], "wake":t, "loc":"lounge", "slept":n|null, "blocks_done":n,
///  "allow_home":bool, "date":"YYYY-MM-DD"}
///   -> {"slots":[[start,end,energy,kind]..], "day0":[6]}        cut_slots, EnergyCtx, energize, DayCapacity::from_slots
/// {"op":"lookahead", "config":<toml>, "model":{..}, "walls":{date:[[a,b]..]}, "slots":[..],
///  "from":"YYYY-MM-DD", "days":n, "wake":"HH:MM:SS[.f]"}
///   -> {"days":[[date,[6]]..]}                                  capacity::lookahead
/// {"op":"cut", "config":<toml>, "from":t, "end":t, "walls":[[a,b]..]}
///   -> {"slots":[..], "breaks":[[a,b]..], "slot_minutes":n, "break_minutes":n}
///                                                                cut_slots, Cut::slot_minutes, Cut::break_minutes
/// {"op":"rank", "config":<toml>, "cands":[..], "caps":[[date,[6]]..], "yesterday":{id:p}, "today":"YYYY-MM-DD"}
///   -> {"prios":[..], "pass":[[u, bin]..]}                       priority::compute; utilization, bin_of
/// {"op":"batches", "config":<toml>, "ranked":[cand..]}
///   -> {"batches":[{ids,ci,total_min,total_remaining_min}..]}    priority::batches
/// {"op":"cand", "config":<toml>, "cands":[cand..]}
///   -> {"cands":[{"cap_left_min":n|null,"floor_need_min":n|null}..]}
///                                                                Candidate::cap_left_min, Candidate::floor_need_min
/// {"op":"sort_key", "config":<toml>, "cand":cand, "prio":grant}
///   -> {"key":[p,[r,r],[o,o]]}                                   priority::sort_key
/// {"op":"wall_minutes", "config":<toml>, "from":t, "to":t, "walls":[[a,b]..]}
///   -> {"minutes":n}                                             capacity::wall_minutes (§8.1's Σ walls inside)
/// ```
fn capacity_one(req: &Value) -> Result<Value, String> {
    use tm_core::capacity;
    use tm_core::priority;
    let cfg = cap_config(&req["config"])?;
    let tz = cfg.tz;
    match req["op"].as_str() {
        Some("today") => {
            let model = cap_model(&req["model"])?;
            let from = instant(&req["from"], tz, "from")?;
            let end = instant(&req["end"], tz, "end")?;
            let walls = cap_walls(&req["walls"], tz, "walls")?;
            let reports: Vec<(chrono::DateTime<chrono_tz::Tz>, u8, u8)> = req["reports"]
                .as_array()
                .ok_or("`reports` is not an array")?
                .iter()
                .map(|r| {
                    let small = |x: &Value| x.as_u64().and_then(|n| u8::try_from(n).ok()).ok_or_else(|| format!("a report's level {x}"));
                    Ok((instant(&r[0], tz, "a report")?, small(&r[1])?, small(&r[2])?))
                })
                .collect::<Result<_, String>>()?;
            let posterior = tm_core::energy::Posterior::from_reports(&reports, &cfg);
            let wake = instant(&req["wake"], tz, "wake")?;
            let loc_text = req["loc"].as_str().ok_or("`loc` is not a string")?;
            let loc = tm_core::model::Loc::parse(loc_text).map_err(|e| format!("loc {loc_text:?}: {e}"))?;
            let slept = match &req["slept"] {
                Value::Null => None,
                x => Some(x.as_u64().and_then(|n| u32::try_from(n).ok()).ok_or_else(|| format!("`slept` {x}"))?),
            };
            let blocks_done = req["blocks_done"].as_u64().and_then(|n| u32::try_from(n).ok()).ok_or("`blocks_done`")?;
            let allow_home = req["allow_home"].as_bool().ok_or("`allow_home`")?;
            let date = cap_date(&req["date"], "date")?;
            let cut = capacity::cut_slots(from, end, &walls, &cfg);
            let ectx = capacity::EnergyCtx::new(&model, &cfg, &posterior, wake, loc)
                .with_slept(slept)
                .with_blocks_done(blocks_done)
                .with_allow_home(allow_home);
            let slots = capacity::energize(&cut.slots, &ectx);
            let day0 = capacity::DayCapacity::from_slots(date, &slots);
            Ok(json!({ "slots": slots.iter().map(cap_slot_json).collect::<Vec<_>>(), "day0": day0.minutes_at_level }))
        }
        Some("lookahead") => {
            let model = cap_model(&req["model"])?;
            let mut walls = capacity::WallsByDate::new();
            for (d, ws) in req["walls"].as_object().ok_or("`walls` is not an object")? {
                walls.insert(cap_date(&json!(d), "a walls date")?, cap_walls(ws, tz, "walls")?);
            }
            let slots = cap_slots(&req["slots"], tz)?;
            let from = cap_date(&req["from"], "from")?;
            let days = req["days"].as_u64().and_then(|n| u32::try_from(n).ok()).ok_or("`days`")?;
            let wake_text = req["wake"].as_str().ok_or("`wake` is not a clock")?;
            let wake = chrono::NaiveTime::parse_from_str(wake_text, "%H:%M:%S%.f").map_err(|e| format!("wake {wake_text:?}: {e}"))?;
            let caps = capacity::lookahead(&walls, &cfg, &model, &slots, from, days, wake);
            Ok(json!({ "days": caps.iter().map(cap_day_json).collect::<Vec<_>>() }))
        }
        Some("cut") => {
            let from = instant(&req["from"], tz, "from")?;
            let end = instant(&req["end"], tz, "end")?;
            let walls = cap_walls(&req["walls"], tz, "walls")?;
            let cut = capacity::cut_slots(from, end, &walls, &cfg);
            let breaks: Vec<Value> = cut.breaks.iter().map(|b| json!([b.start.to_rfc3339(), b.end.to_rfc3339()])).collect();
            Ok(json!({
                "slots": cut.slots.iter().map(cap_slot_json).collect::<Vec<_>>(), "breaks": breaks,
                "slot_minutes": cut.slot_minutes(), "break_minutes": cut.break_minutes(),
            }))
        }
        Some("rank") => {
            let cands: Vec<priority::Candidate> = req["cands"]
                .as_array()
                .ok_or("`cands` is not an array")?
                .iter()
                .map(|c| cap_cand(c, tz))
                .collect::<Result<_, _>>()?;
            let caps = cap_days(&req["caps"])?;
            let mut yesterday: BTreeMap<tm_core::model::Id, u8> = BTreeMap::new();
            for (id, p) in req["yesterday"].as_object().ok_or("`yesterday` is not an object")? {
                yesterday.insert(tm_core::model::Id::new(id), p.as_u64().and_then(|n| u8::try_from(n).ok()).ok_or("a yesterday's p")?);
            }
            let today = cap_date(&req["today"], "today")?;
            let prios = priority::compute(&cands, &caps, &yesterday, &cfg, today);
            let pass: Vec<Value> = prios
                .iter()
                .map(|p| {
                    let u = priority::utilization(p.need_min, p.avail_min);
                    json!([u.to_string(), priority::bin_of(u, &cfg.priority.bins)])
                })
                .collect();
            Ok(json!({ "prios": prios.iter().map(cap_prio_json).collect::<Vec<_>>(), "pass": pass }))
        }
        Some("batches") => {
            let ranked: Vec<priority::Candidate> = req["ranked"]
                .as_array()
                .ok_or("`ranked` is not an array")?
                .iter()
                .map(|c| cap_cand(c, tz))
                .collect::<Result<_, _>>()?;
            let refs: Vec<&priority::Candidate> = ranked.iter().collect();
            let batches = priority::batches(&refs, &cfg);
            Ok(json!({ "batches": serde_json::to_value(&batches).map_err(|e| e.to_string())? }))
        }
        Some("cand") => {
            let cands: Vec<Value> = req["cands"]
                .as_array()
                .ok_or("`cands` is not an array")?
                .iter()
                .map(|c| {
                    let c = cap_cand(c, tz)?;
                    Ok(json!({ "cap_left_min": c.cap_left_min(), "floor_need_min": c.floor_need_min(&cfg) }))
                })
                .collect::<Result<_, String>>()?;
            Ok(json!({ "cands": cands }))
        }
        Some("wall_minutes") => {
            let from = instant(&req["from"], tz, "from")?;
            let to = instant(&req["to"], tz, "to")?;
            let walls = cap_walls(&req["walls"], tz, "walls")?;
            Ok(json!({ "minutes": capacity::wall_minutes(from, to, &walls) }))
        }
        Some("sort_key") => {
            let cand = cap_cand(&req["cand"], tz)?;
            let prio = prio_of(&req["prio"])?;
            let (p, root, own) = priority::sort_key(&prio, &cand);
            Ok(json!({ "key": [p, [root.0, root.1], [own.0, own.1]] }))
        }
        other => Err(format!("unknown op {other:?}")),
    }
}

/// A `capacity` request, answered — or refused `{"error": …}` by name.
fn observe_capacity(req: &Value) -> Value {
    capacity_one(req).unwrap_or_else(|e| json!({ "error": e }))
}

/// A request, answered — or refused `{"error": …}` by name, so the caller sees why.
fn observe_plan(req: &Value) -> Value {
    let answer = match req["op"].as_str() {
        Some("plan") => plan_one(req),
        Some("diff") => diff_one(req),
        Some("worked") => worked_one(req),
        other => Err(format!("unknown op {other:?}")),
    };
    answer.unwrap_or_else(|e| json!({ "error": e }))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let stdout = std::io::stdout();
    let mut w = std::io::BufWriter::new(stdout.lock());

    match args.get(1).map(String::as_str) {
        Some("gen") => {
            let n: usize = args[2].parse().expect("gen <n> <seed>");
            let seed: u64 = args[3].parse().expect("gen <n> <seed>");
            let mut bytes = [0u8; 32];
            bytes[..8].copy_from_slice(&seed.to_le_bytes());
            let rng = TestRng::from_seed(RngAlgorithm::ChaCha, &bytes);
            let mut runner = TestRunner::new_with_rng(Config::default(), rng);
            let strategy = line();
            for _ in 0..n {
                let (text, _stateful) = strategy.new_tree(&mut runner).unwrap().current();
                writeln!(w, "{}", observe(&text)).unwrap();
            }
        }
        Some("parse") => {
            for l in std::io::stdin().lock().lines() {
                let l = l.unwrap();
                if l.trim().is_empty() {
                    continue;
                }
                let text: String = serde_json::from_str(&l)
                    .unwrap_or_else(|e| panic!("stdin must be one JSON string per line: {e} in {l:?}"));
                writeln!(w, "{}", observe(&text)).unwrap();
            }
        }
        Some("parse-entry") => {
            for l in std::io::stdin().lock().lines() {
                let l = l.unwrap();
                if l.trim().is_empty() {
                    continue;
                }
                // One physical log line per input line. A UTF-8 segment arrives
                // as a JSON string, like every other mode. A segment that is
                // NOT UTF-8 (a torn write; the crafted set's `\xff`) cannot be
                // a JSON string at all, so it arrives as a JSON array of byte
                // values. Either way the reader is handed the raw bytes of one
                // segment, which is what `Log::parse_bytes` splits out.
                let v: Value = serde_json::from_str(&l).unwrap_or_else(|e| {
                    panic!("stdin must be a JSON string or byte array per line: {e} in {l:?}")
                });
                let seg: Vec<u8> = match v {
                    Value::String(s) => s.into_bytes(),
                    Value::Array(bytes) => bytes
                        .iter()
                        .map(|b| {
                            let n = b.as_u64().unwrap_or_else(|| panic!("a byte array holds numbers: {b} in {l:?}"));
                            u8::try_from(n).unwrap_or_else(|_| panic!("a byte is 0..=255, not {n}, in {l:?}"))
                        })
                        .collect(),
                    other => panic!("stdin must be a JSON string or byte array per line, not {other} in {l:?}"),
                };
                writeln!(w, "{}", observe_entry(&seg)).unwrap();
            }
        }
        Some("replay") => {
            let tz: chrono_tz::Tz = args
                .get(2)
                .expect("replay <tz>  (e.g. America/Chicago)")
                .parse()
                .expect("a tz database name");
            for l in std::io::stdin().lock().lines() {
                let l = l.unwrap();
                if l.trim().is_empty() {
                    continue;
                }
                let text: String = serde_json::from_str(&l)
                    .unwrap_or_else(|e| panic!("stdin must be one JSON string per line: {e} in {l:?}"));
                writeln!(w, "{}", observe_log(&text, tz)).unwrap();
            }
        }
        Some("plan") => {
            // One request, one answer, FLUSHED: the caller keeps this process and
            // waits for each answer before it asks again.
            for l in std::io::stdin().lock().lines() {
                let l = l.unwrap();
                if l.trim().is_empty() {
                    continue;
                }
                let answer = match serde_json::from_str::<Value>(&l) {
                    Ok(req) => observe_plan(&req),
                    Err(e) => json!({ "error": format!("a request is one JSON object per line: {e}") }),
                };
                writeln!(w, "{answer}").unwrap();
                w.flush().unwrap();
            }
        }
        Some("review") => {
            // `plan`'s protocol: one request, one answer, FLUSHED.
            for l in std::io::stdin().lock().lines() {
                let l = l.unwrap();
                if l.trim().is_empty() {
                    continue;
                }
                let answer = match serde_json::from_str::<Value>(&l) {
                    Ok(req) => observe_review(&req),
                    Err(e) => json!({ "error": format!("a request is one JSON object per line: {e}") }),
                };
                writeln!(w, "{answer}").unwrap();
                w.flush().unwrap();
            }
        }
        Some("capacity") => {
            // `plan`'s protocol: one request, one answer, FLUSHED (W-46 track C).
            for l in std::io::stdin().lock().lines() {
                let l = l.unwrap();
                if l.trim().is_empty() {
                    continue;
                }
                let answer = match serde_json::from_str::<Value>(&l) {
                    Ok(req) => observe_capacity(&req),
                    Err(e) => json!({ "error": format!("a request is one JSON object per line: {e}") }),
                };
                writeln!(w, "{answer}").unwrap();
                w.flush().unwrap();
            }
        }
        Some("fit") => {
            let tz: chrono_tz::Tz = args
                .get(2)
                .expect("fit <tz> <today>  (e.g. America/Chicago 2026-09-15)")
                .parse()
                .expect("a tz database name");
            let today = chrono::NaiveDate::parse_from_str(
                args.get(3).expect("fit <tz> <today>"),
                "%Y-%m-%d",
            )
            .expect("today as YYYY-MM-DD");
            for l in std::io::stdin().lock().lines() {
                let l = l.unwrap();
                if l.trim().is_empty() {
                    continue;
                }
                let text: String = serde_json::from_str(&l)
                    .unwrap_or_else(|e| panic!("stdin must be one JSON string per line: {e} in {l:?}"));
                writeln!(w, "{}", observe_fit(&text, tz, today)).unwrap();
            }
        }
        _ => {
            eprintln!(
                "usage: tm-oracle gen <n> <seed>   |   tm-oracle parse  (JSON strings on stdin)\n\
                 \x20      tm-oracle parse-entry  (ONE log line per line: a JSON string, or a JSON array of bytes)\n\
                 \x20      tm-oracle replay <tz>  (whole log texts, one JSON string per line)\n\
                 \x20      tm-oracle fit <tz> <today>  (the same, fitted: `tm model --fit`)\n\
                 \x20      tm-oracle plan  (one planning request per line: the fork's planner, ranked as the binary ranks it;\n\
                 \x20                       ops plan, diff, worked)\n\
                 \x20      tm-oracle review  (one week-grid request per line: the fork's review::week_review heat over a world)\n\
                 \x20      tm-oracle capacity  (one request per line: the fork's lookahead, day-0 slots, slot cut, §7 pass and\n\
                 \x20                           §7.5 batches; ops today, lookahead, cut, rank, batches, cand, sort_key,\n\
                 \x20                           wall_minutes)"
            );
            std::process::exit(2);
        }
    }
}
