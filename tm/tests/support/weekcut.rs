//! **The kernel's cut of a week's Pauses, asked as the binary asks it** (stage 6 W-40 track H,
//! README gap 3721): the `emit` section's walls form with a `week` — `tm/src/cli/day.rs`'
//! `call_the_walls`, the request behind `day::week_cut`, which the CLI's `tm review week` and the
//! TUI's Review screen both draw the heat grid from (README gaps 3432 and 3528, parity P63) — and
//! its `ok.emit.cut` read back as `day::read_week_cut` reads it.
//!
//! # Whose spelling this is
//!
//! The binary's walls request lives in a `[[bin]]` no test can link (README gap 3717), so it is
//! spelled here a second time, as `support/planreq.rs` spells the capacity section. It is kept in
//! its own file rather than in `planreq.rs`, which another track rewrites this run (W-40 track E,
//! README gap 2875), so the two do not meet in one hunk at the merge.
//!
//! # What it leaves out, and why that is safe where it is used
//!
//! * **The running break.** The binary sends `break` from `.tm/state.json`'s running break;
//!   this sends `null`. [`walls_week_request`] is asked only about worlds with no running break
//!   (its caller asserts it), where the two are the same request.
//! * **The sealed day records.** The binary's `log` section is `kernel_log::week_log_section`
//!   (the week's sealed day records when its replay cache sealed it); this sends the whole log
//!   from line 1 with no checkpoint ([`log_section`]), which the kernel answers from its own
//!   genesis. That the two give one cut is not argued here but measured: the caller holds the
//!   grid drawn from this cut to the binary's own `tm review week` on the same world, cell for
//!   cell.
//! * **The documents' regions** (`kernel_bridge::region_of`), which orient a demotion pair only
//!   where both lines are `[-]`.

#![allow(dead_code)]

use chrono::DateTime;
use chrono_tz::Tz;
use serde_json::{json, Value};

use tm_core::config::Config;
use tm_core::planwire;
use tm_core::review::PauseCut;

use crate::planreq::tz_table;

/// **A genesis `log` section**: the whole log from line 1, no checkpoint, the facts asked — what
/// the binary sends for a tree with no replay cache (`kernel_log::capacity_log_section`'s
/// genesis).
pub fn log_section(log: &str) -> Value {
    json!({"ckpt": null, "from": 1,
           "lines": log.lines().collect::<Vec<_>>(),
           "terminated": true, "reseal": null,
           "want": {"facts": true, "headersFrom": null, "render": []},
           "sealed": null})
}

/// **The walls form, asked with a week**: the documents, the request clock, the zone, a genesis
/// `log` section, and `emit.walls` with `at` (`now`), no running break, and `week` (its Monday).
pub fn walls_week_request(docs: &[(String, String)], log: &str, cfg: &Config, now: DateTime<Tz>, monday: chrono::NaiveDate) -> Value {
    json!({
        "log": log_section(log),
        "docs": docs.iter()
            .map(|(p, t)| json!({"path": p, "lines": t.lines().collect::<Vec<_>>()}))
            .collect::<Vec<_>>(),
        "now": now.date_naive().to_string(),
        "blockMin": cfg.block_min(),
        "tz": tz_table::wire_for(None, cfg.tz),
        // The binary's own encoder of the walls object (README gap 3955).
        "emit": {"walls": planwire::walls_json(now.fixed_offset(), None, Some(monday))},
    })
}

/// **The kernel's cut of a week's Pauses**, read off [`walls_week_request`]'s answer —
/// the binary's own decoder, `planwire::read_week_cut` (README gap 3955; until the W-40
/// repair this file decoded `ok.emit.cut` a second time).
pub fn read_week_cut(resp: &Value, tz: Tz) -> Result<PauseCut, String> {
    planwire::read_week_cut(resp, tz)
}
