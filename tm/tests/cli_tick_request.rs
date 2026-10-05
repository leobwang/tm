//! **The planner request's read, held** — stage 6 W-45, track Q (README gap 4662).
//!
//! `kernel_capacity::planner_request` is two halves since this step: `kernel_capacity::tick_inputs` reads, once,
//! everything the request carries that a context does not hold in memory, and `kernel_capacity::planner_ask_from`
//! builds the request from that read and the context alone — the call the TUI's minute tick makes after R3 (the
//! owner's D103), with the read its last reload took.  One of the things the read holds is not a file the request
//! carries verbatim: the HYSTERESIS INPUT, `Ctx::hysteresis_input` — `.tm/last_plan.json`'s priorities before the
//! day's first plan — which every ranked candidate carries as `yesterday` (§7.4).  Nothing pinned it: replacing it
//! with an empty map left every suite green (W-45 track Q's plant P6).  This file pins it, through the binary, on the
//! request the binary sends.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

/// The planner request `tm check` sends, read off the FFI's request trace (as `cli_latency.rs`' T18 reads it).
fn planner_request(tm: &Tm, now: &str) -> Value {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_tm"))
        .arg("--dir")
        .arg(&tm.plan)
        .arg("--now")
        .arg(now)
        .arg("check")
        .env(tm_kernel_ffi::TRACE_CALLS_ENV, "1")
        .env(tm_kernel_ffi::TRACE_REQUESTS_ENV, "1")
        .output()
        .expect("spawn tm");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "`tm check`: {err:.400}");
    let mut planners = err.lines().filter_map(|l| l.strip_prefix("kernel request: ")).filter(|r| r.contains("\"planner\":{"));
    let request = planners.next().unwrap_or_else(|| panic!("`tm check` traced no planner request: {err:.400}"));
    assert!(planners.next().is_none(), "`tm check` traced two planner requests");
    serde_json::from_str(request).expect("the traced request parses")
}

/// **The day after a plan, the planner request ranks against that plan's priorities** (§7.4's hysteresis): Monday's
/// `tm plan` stores every candidate's `p` in `.tm/last_plan.json`; Tuesday's request, before Tuesday's first plan,
/// carries each one as that candidate's `yesterday`.
#[test]
fn the_planner_request_carries_the_stored_plans_priorities_as_yesterday() {
    let tm = Tm::empty();
    tm.ok_at("2026-09-07T06:00:00-05:00", &["init", "--example"]);
    tm.ok_at("2026-09-07T07:00:00-05:00", &["wake", "07:00"]);
    tm.ok_at("2026-09-07T09:00:00-05:00", &["plan"]);
    let stored: Value =
        serde_json::from_str(&std::fs::read_to_string(tm.plan.join(".tm/last_plan.json")).expect("the stored plan")).expect("json");
    assert_eq!(stored["date"], "2026-09-07", "{stored}");
    let monday = stored["priorities"].as_object().expect("the stored priorities").clone();
    assert!(!monday.is_empty(), "Monday's plan stored no priorities: {stored}");
    let req = planner_request(&tm, "2026-09-08T09:00:00-05:00");
    let items = req["capacity"]["candidates"]["items"].as_array().expect("the ranked candidates");
    let mut compared = 0;
    for item in items {
        let id = item["id"].as_str().expect("an id");
        if let Some(p) = monday.get(id) {
            assert_eq!(&item["yesterday"], p, "`^{id}` is ranked against Monday's p: {item}");
            compared += 1;
        }
    }
    assert!(compared > 0, "no candidate of Tuesday's request was ranked on Monday: {items:?}");
    eprintln!("cli_tick_request: {compared} of {} candidates carry Monday's p as yesterday", items.len());
}
