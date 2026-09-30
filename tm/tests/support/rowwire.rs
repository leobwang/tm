//! **The `plan` section's wire, in one place** — how a fork `DayPlan` becomes
//! the kernel's request, and how the two sides' cells are compared.
//!
//! This was `tm/tests/kernel_row_cells.rs`'s own until stage 6 **W-25 (step
//! R2)**, when `tm/tests/planner_invariants.rs` began sending **its** generated
//! days through the same wire. A copy would have made "the invariants' days go
//! through the wire `kernel_row_cells` tests" a claim about two encoders that
//! drift (AGENTS §5.3); this module makes it a fact about one.
//!
//! Nothing here asserts, and nothing here decides which differences are
//! allowed: `differences` reports every cell that differs and each caller
//! declares its own holes.

#[path = "../../src/cli/tz_table.rs"]
pub mod tz_table;

use std::collections::HashMap;

use chrono::Timelike;
use serde_json::{json, Value};

use tm_core::config::Config;
use tm_core::emit::{self, RowCells};
use tm_core::model::Id;
use tm_core::dayplan::{self, DayPlan, SegKind, Segment};
use tm_core::tree::Tree;

/// The kernel's epoch and a `chrono` instant as its absolute second — the host
/// codec's (`tm_core::planwire`, W-35), not a copy of it. Not every crate that
/// includes this module reads both.
#[allow(unused_imports)]
pub use tm_core::planwire::{kernel_sec, EPOCH_FROM_CE};

// ---------------------------------------------------------------------------
// The request
// ---------------------------------------------------------------------------

/// An exact decimal as the wire's `{num, den}` pair.
///
/// The fork's multiplier is an `f64` and this kernel has no float (AGENTS §4),
/// so the test does the conversion the host will do at R3: six places, which is
/// `energy::fmt_multiplier`'s two with room to spare, over `10^6` — inside
/// `CapWire.maxPairDen`. An `f64` that is not a six-place decimal would be
/// rounded here, and the fixture's 1.6 is not one of those.
pub fn decimal_pair(x: f64) -> Value {
    let scaled = (x * 1_000_000.0).round() as u64;
    json!({"num": scaled, "den": 1_000_000u64})
}

/// One segment, as the `plan` section carries it.
///
/// `instance` is not sent: no cell reads it (`Emit.rowOf` takes a `Seg` and
/// never looks at `inst`). `flags.ghost` is not sent either — the kernel makes
/// the ghost row a *kind* and the fork makes it a flag, and the fixture has no
/// ghost row.
pub fn seg_json(seg: &Segment) -> Value {
    let mut o = json!({
        "start": kernel_sec(seg.start),
        "stop": kernel_sec(seg.end),
        "kind": dayplan::kind_label(&seg.kind),
        "energy": seg.energy,
        "item": seg.item.as_ref().map(|i| i.to_string()),
        "planned": seg.flags.planned_min,
        "flags": {
            "done": seg.flags.done,
            "current": seg.flags.current,
            "underused": seg.flags.underused,
            "hot": seg.flags.hot,
            "mandatory": seg.flags.mandatory,
            "deferred": seg.flags.deferred,
            "open": seg.flags.open,
        },
        // **Null but for one row** (see the module header): the fork's planner
        // wrote this column as prose and the kernel's `Note` is a name, so there
        // is nothing to send and the kernel derives what it can. The exception is
        // a replayed `tm pause` ([`Segment::is_pause`]), whose note IS a name the
        // two sides share (`PAUSED_NOTE`, `EmitWire.readNote`'s `paused`) and
        // which D68 draws from (`paused <dur>`, parity P59): sent null, the
        // kernel drew it `lost` and the host `paused`, an UNDECLARED `title`
        // difference waiting for the first generated day with a typed pause
        // (W-38 land step, README gap 3436).
        "note": if seg.is_pause() { json!({"name": "paused"}) } else { Value::Null },
    });
    if let SegKind::Batch(ids) = &seg.kind {
        o["batch"] = json!(ids.iter().map(|i| i.to_string()).collect::<Vec<_>>());
    }
    if let Some(m) = seg.flags.multiplier {
        o["mult"] = decimal_pair(m);
    }
    o
}

/// **The whole request**: the caller's documents, the zone, the clock, and the
/// `plan` section's rows.
///
/// `docs` is the caller's because the two callers hold their trees differently
/// — `kernel_row_cells.rs` reads the fixture off disk and
/// `planner_invariants.rs` generates its four files in memory — and **the docs
/// are the whole point**: the kernel reads the title, `ci`, estimate and parent
/// out of its own parse of these bytes, and is told none of them.
pub fn request(docs: Vec<Value>, plan: &DayPlan, cfg: &Config) -> Value {
    let prios: Vec<Value> = plan
        .priorities
        .iter()
        .map(|(id, p)| json!({"id": id.to_string(), "p": p.p}))
        .collect();
    json!({
        "docs": docs,
        "now": plan.date.to_string(),
        "blockMin": cfg.block_min(),
        "tz": tz_table::wire_for(None, cfg.tz),
        "plan": {
            "bed": format!("{:02}:{:02}", cfg.day.bed.hour(), cfg.day.bed.minute()),
            "priorities": prios,
            "segments": plan.segments.iter().map(seg_json).collect::<Vec<_>>(),
        }
    })
}

/// The kernel's rows for a day, as [`RowCells`].
pub fn kernel_cells(docs: Vec<Value>, plan: &DayPlan, cfg: &Config) -> Vec<RowCells> {
    match kernel_rows(docs, plan, cfg) {
        Ok(cells) => cells,
        Err(raw) => panic!("no plan.rows in the response:\n{raw}"),
    }
}

/// The same, with a **refusal returned rather than a panic**: the fuzz in
/// `planner_invariants.rs` asserts that no day the fork's planner produces is
/// refused by the wire, which it cannot do if a refusal aborts the case.
pub fn kernel_rows(docs: Vec<Value>, plan: &DayPlan, cfg: &Config) -> Result<Vec<RowCells>, String> {
    let req = request(docs, plan, cfg);
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("the response is json");
    let Some(rows) = resp["ok"]["plan"]["rows"].as_array() else {
        return Err(raw);
    };
    Ok(rows
        .iter()
        .map(|r| {
            let s = |k: &str| r[k].as_str().unwrap_or_else(|| panic!("{k} in {r}")).to_string();
            RowCells {
                time: s("time"),
                ci: s("ci"),
                p: s("p"),
                mark: s("mark"),
                title: s("title"),
                parent: s("parent"),
                est: s("est"),
                actual: s("actual"),
                note: s("note"),
                batch_names: r["batchNames"].as_array().and_then(|xs| {
                    if xs.is_empty() {
                        None
                    } else {
                        Some(xs.iter().map(|x| x.as_str().unwrap_or_default().to_string()).collect())
                    }
                }),
            }
        })
        .collect())
}

/// The fork's cells for the same day.
pub fn fork_cells(plan: &DayPlan, tree: &Tree, cfg: &Config) -> Vec<RowCells> {
    let prios: HashMap<&Id, u8> = plan.priorities.iter().map(|(id, p)| (id, p.p)).collect();
    plan.segments
        .iter()
        .map(|seg| emit::row_cells(seg, plan, tree, cfg, &prios))
        .collect()
}

/// `(cell name, fork, kernel)` for every cell of a row that differs.
///
/// The nine cells **and** `batchNames`, which is not a cell but is carried
/// beside them and would otherwise be compared only by the batch test.
pub fn differences(a: &RowCells, b: &RowCells) -> Vec<(&'static str, String, String)> {
    const NAMES: [&str; 9] = [
        "time", "ci", "p", "mark", "title", "parent", "est", "actual", "note",
    ];
    let mut out: Vec<(&'static str, String, String)> = NAMES
        .iter()
        .zip(a.cells().iter().zip(b.cells()))
        .filter(|(_, (x, y))| *x != y)
        .map(|(n, (x, y))| (*n, (*x).to_string(), y.to_string()))
        .collect();
    if a.batch_names != b.batch_names {
        out.push((
            "batchNames",
            format!("{:?}", a.batch_names),
            format!("{:?}", b.batch_names),
        ));
    }
    out
}