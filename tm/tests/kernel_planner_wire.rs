//! **The planner's inputs, through the FFI** — stage 6 W-27, step R2, D48.
//!
//! `kernel/TmKernel/TmKernel/PlanWire.lean` decodes the four values
//! `Planner.PlanReq` needed and no section carried: `state` (§9's `RuntimeIn`),
//! `routines`, `overrides` and `prio.batchMaxMin` (§16's `[priority]
//! batch_max_min`, README gap 801). Every bound it puts on them is one this
//! wire already carried — `CapWire.maxCandId`, `CapWire.maxRemaining` (the fork
//! `u32`), `Cal.Instant.wf`, `Look.maxDayMin` and `Planner.maxCands` — reached
//! through the constructor that already owns it.
//!
//! **This file is what makes those bounds more than definitions.** The Lean
//! side proves each refusal; this side shows a host reaches it: the same bytes
//! a caller would send, through `tm_kernel_call`, with the refusal read back
//! off the response. A decoder whose refusals no caller can reach is the defect
//! `Emit.lean`'s own header records from W-22 (README gap 1331).
//!
//! **And since W-28 the call ANSWERS** (D48's response half, README gap 1667):
//! a `planner` section that decodes puts `Planner.dayPlan`'s seven keys into
//! the same `plan` object `EmitWire.withPlan` writes `rows` into, so the
//! refusals below are now refusals to build a request the kernel would
//! otherwise have planned.

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

use serde_json::{json, Value};

/// The day every request in this file plans, and the instant it plans at.
///
/// The instant §9's three runtime records are `wf` against is the **capacity
/// section's `at`** (`CapWire.readAt`, the one reader of that key), not the
/// request's top-level `now`: `Boundary.parseClock` reads that one as a `Day`
/// through `Field.parseDate`, and a day number standing in for an instant is a
/// unit error the types do not catch — both are `Nat`. So `NOW` below is the
/// absolute second `AT` names, and the two must agree or the guards under test
/// are being asked about the wrong instant.
const TODAY: &str = "2026-09-07";
const AT: &str = "2026-09-07T07:00:00+00:00";
/// `AT` as the kernel's absolute second: unix 1,788,764,400 plus the CE offset
/// `tm/tests/support/rowwire.rs` spells, 62,135,596,800.
const NOW: i64 = 63_924_361_200;

/// The `log` section every capacity request carries since step L9: genesis in
/// one call over an empty log, asking for the facts the seam hands the capacity
/// reader. Copied in shape from `tm/tests/kernel_unit_reserve.rs`, which is
/// where the capacity request below comes from too — a capacity section is a
/// large object and this file is about the section BESIDE it.
const LOG_SECTION: &str = r#"{"ckpt":null,"from":1,"lines":[],"terminated":true,"reseal":null,"want":{"facts":true,"headersFrom":null,"render":[]},"sealed":null}"#;

/// A capacity section the kernel accepts, with §16's `[priority]` table
/// carrying `batchMaxMin` — the fourth key of the object `CapWire.readPriority`
/// already reads three of (§16's own home for the value, README gap 801).
///
/// `at` is what the planner section reads as `now`; `batch` is the value under
/// test, and `null` leaves the key out so the absent case is reachable.
fn capacity(batch: Option<Value>, with_at: bool) -> Value {
    let week = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
    let p_config: serde_json::Map<String, Value> = week
        .iter()
        .map(|k| (k.to_string(), json!({"num": "1000000", "den": "1000000"})))
        .collect();
    let arrival: serde_json::Map<String, Value> =
        week.iter().map(|k| (k.to_string(), json!("07:00"))).collect();
    let step = |from: u64, to: Option<u64>, level: u8| {
        json!({"from": {"num": from, "den": 1},
               "to": to.map(|t| json!({"num": t, "den": 1})), "level": level})
    };
    let mut priority = json!({
        "bins": [{"num": 1, "den": 2}, {"num": 1, "den": 4}, {"num": 1, "den": 10}],
        "safety": {"num": 13, "den": 10}, "defaultPriority": 3});
    if let Some(b) = batch {
        priority["batchMaxMin"] = b;
    }
    let mut cap = json!({
        "pLounge": {"config": p_config},
        "arrival": {"config": arrival},
        "prior": {
            "lounge": [step(0, Some(4), 5), step(4, Some(8), 3), step(8, None, 1)],
            "home": [step(0, Some(6), 3), step(6, None, 2)]},
        "homeMaxCi": 3,
        "day": {"breakMin": 20, "breakAfterBlocks": 2, "minLastBlockMin": 30,
                "windowHours": {"num": 8, "den": 1}, "windowCap": "19:00",
                "budgetRatio": {"num": 3, "den": 4}, "windDown": "21:30", "bed": "22:00"},
        "priority": priority,
        "days": 7,
        "state": {"date": TODAY, "window": {"from": "07:00", "to": "15:00"},
                  "budget": 6, "arrival": null, "loc": "lounge", "allowHome": false},
        "posterior": {"fullHours": {"num": 3, "den": 1}, "zeroHours": {"num": 6, "den": 1}},
        "sleep": {"shiftModel": null, "shiftConfig": {"neg": false, "num": 1, "den": 1},
                  "underHours": {"num": 7, "den": 1}},
        "candidates": {"hysteresis": false, "items": []}});
    if with_at {
        cap["at"] = json!(AT);
    }
    cap
}

/// The whole request: the `log` section spliced as text beside the rest, as
/// `kernel_unit_reserve.rs` splices it (the checkpoint's keys are read in build
/// order, so nothing about that section may go through `serde_json::Value`).
fn request_with(planner: Option<Value>, cap: Option<Value>) -> String {
    request_with_docs(planner, cap, json!([]))
}

/// The same, over documents the kernel parses itself — what a request needs
/// before `Planner.mkRoutines?` can accept a window instance, since
/// `Planner.mkRoutine?` refuses an id the plan does not hold and an item that
/// declares no window (README gap 285).
fn request_with_docs(planner: Option<Value>, cap: Option<Value>, docs: Value) -> String {
    let mut body = json!({
        "docs": docs, "now": TODAY, "blockMin": 60,
        "tz": tz_table::probe(chrono_tz::UTC).to_wire()});
    if let Some(c) = cap {
        body["capacity"] = c;
    }
    if let Some(p) = planner {
        body["planner"] = p;
    }
    let body = body.to_string();
    format!(r#"{{"log":{LOG_SECTION},{}"#, &body[1..])
}

/// The everyday request: a valid capacity section with §16's shipped 20.
fn request(planner: Option<Value>) -> String {
    request_with(planner, Some(capacity(Some(json!(20)), true)))
}

/// The response, parsed.
fn call(req: &str) -> Value {
    let raw = tm_kernel_ffi::call(req).expect("kernel call");
    serde_json::from_str(&raw).unwrap_or_else(|e| panic!("the response is json: {e}\n{raw}"))
}

/// `{"err":{"planner":"<text>"}}`, or `None` when the call was answered.
fn planner_err(resp: &Value) -> Option<String> {
    resp["err"]["planner"].as_str().map(str::to_string)
}

/// Two routine items the plan holds, each declaring a window (§4.3).
fn routine_docs() -> Value {
    json!([{"path": "routines.md",
            "lines": ["- lunch      win:11:30-13:30 dur:30m  every:day",
                      "- shower     win:07:00-23:00 dur:20m  every:day"]}])
}

/// A `state` section wrapped as the whole planner section.
fn state(v: Value) -> Option<Value> {
    Some(json!({"state": v}))
}

// ---------------------------------------------------------------------------
// The section is optional, and absent it changes nothing
// ---------------------------------------------------------------------------

/// **A request with no `planner` section is answered exactly as before** —
/// `PlanWire.callPlanner_without_a_planner_section_is_callRows`, driven.
#[test]
fn a_request_without_a_planner_section_is_answered_as_before() {
    let raw = tm_kernel_ffi::call(&request(None)).expect("call");
    let again = tm_kernel_ffi::call(&request(None)).expect("call");
    assert_eq!(raw, again, "the same bytes twice were two answers");
    assert!(
        raw.contains("\"lookahead\""),
        "the capacity section was not answered, so nothing below is about the planner: {raw}"
    );
    assert!(
        !raw.contains("\"planner\""),
        "a request with no planner section got a planner answer: {raw}"
    );
}

/// **A readable section ANSWERS THE DAY** — D48's response half, README gap
/// **1667**, landed at W-28.
///
/// This replaces a_readable_planner_section_changes_no_byte, which W-27 wrote
/// as the shape of the debt rather than of the feature and said in its own
/// doc comment that the step building the response would be the step changing
/// it. Both names are written without backticks because neither exists.
#[test]
fn a_readable_planner_section_answers_the_day() {
    let bare = call(&request(None));
    let with_section = call(&request(Some(json!({}))));
    assert!(
        bare["ok"]["plan"].is_null(),
        "a request with no planner section answered a plan object: {bare}"
    );
    let plan = &with_section["ok"]["plan"];
    assert!(
        !plan.is_null(),
        "a readable planner section answered no plan: {with_section}"
    );
    for k in [
        "day",
        "window",
        "budgetBlocks",
        "segments",
        "diagnostics",
        "priorities",
        "hash",
    ] {
        assert!(!plan[k].is_null(), "no plan.{k} in {with_section}");
    }
    assert_eq!(plan["day"].as_str(), Some(TODAY), "{with_section}");
    assert_eq!(
        plan["hash"].as_str().map(str::len),
        Some(16),
        "the hash is not sixteen hex digits: {with_section}"
    );
    assert!(
        plan["window"]["lo"].as_i64().unwrap_or(0) < plan["window"]["hi"].as_i64().unwrap_or(0),
        "the window does not run forwards: {with_section}"
    );
}

/// **The two writers of the `plan` key share one object** — `rows` is
/// `EmitWire.withPlan`'s and the seven above are `PlanWire.planJson`'s, and
/// `PlanWire.the_plan_objects_keys_are_disjoint` says they cannot collide.
/// Driven here because a Lean theorem cannot see which object the linked
/// archive actually writes into.
#[test]
fn the_rows_and_the_day_share_one_plan_object() {
    let mut body: Value =
        serde_json::from_str(&request(Some(json!({})))).expect("the request is json");
    body["plan"] = json!({"bed": "22:00", "priorities": [], "segments": []});
    let resp = call(&body.to_string());
    let plan = &resp["ok"]["plan"];
    assert!(plan["rows"].is_array(), "no plan.rows beside the day: {resp}");
    assert!(!plan["day"].is_null(), "no plan.day beside the rows: {resp}");
    assert_eq!(
        plan["rows"].as_array().map(Vec::len),
        Some(0),
        "an empty `plan` section rendered rows: {resp}"
    );
}

// ---------------------------------------------------------------------------
// Every refusal, reached from a host
// ---------------------------------------------------------------------------

/// **The capacity section is answered FIRST, so the planner section never sees
/// a request the capacity reader refused.**
///
/// `EmitWire.runRows` answers before this section is read, and `runCap` inside
/// it decodes `capacity.at` through the same `CapWire.readAt` the planner
/// section uses. So a request with no readable `at` comes back under the
/// CAPACITY section's name even when the planner section also carries a fault —
/// which is why `PlanWire` declares no `nowAbsent` of its own: it would be a
/// constructor no host could reach (AGENTS §9.2). The branch that survives in
/// Lean keeps `CapWire.refusalJson`'s shape and is recorded unreachable as
/// README gap **1672**.
#[test]
fn a_capacity_section_without_an_at_is_refused_before_the_planner_section() {
    // The planner section ALSO carries a fault; the capacity one still wins.
    let resp = call(&request_with(
        Some(json!({"state": {"active": {"id": "x".repeat(1025), "started": 0, "estMin": 0}}})),
        Some(capacity(Some(json!(20)), false)),
    ));
    assert_eq!(planner_err(&resp), None, "the planner section answered: {resp}");
    assert_eq!(
        resp["err"]["capacity"].as_str(),
        Some("badAt at"),
        "{resp}"
    );
}

/// **And the `capacity` section**: `PlanReq.look` is `Look.mkInput?`'s answer
/// for it and `prio`'s five values are its `priority` object's.
#[test]
fn a_planner_section_without_a_capacity_section_is_refused_by_name() {
    let resp = call(&request_with(Some(json!({})), None));
    assert_eq!(
        planner_err(&resp).as_deref(),
        Some("capacityAbsent"),
        "{resp}"
    );
}

/// **README gap 801, reachable.** §16's `batch_max_min` is a fork `u32`
/// (`config.rs:361`) and the guard is `EmitWire.u32Within`, which is
/// `CapWire.maxRemaining` is `Look.maxPlanMinutes` is that width — one
/// function, one number, no third name.
#[test]
fn a_batch_max_min_past_the_forks_u32_is_refused() {
    let over = call(&request_with(
        Some(json!({})),
        Some(capacity(Some(json!(4_294_967_296u64)), true)),
    ));
    assert_eq!(
        planner_err(&over).as_deref(),
        Some("badBatchMaxMin"),
        "{over}"
    );
    // And the width itself reads, so the bound is where `config.rs` puts it and
    // not one step either side.
    let at = call(&request_with(
        Some(json!({})),
        Some(capacity(Some(json!(4_294_967_295u64)), true)),
    ));
    assert_eq!(planner_err(&at), None, "the fork's own u32 was refused: {at}");
}

/// **An absent `batchMaxMin` is refused, never defaulted to §16's 20.**
/// A default written in the kernel would be a second copy of `config.rs:371`.
#[test]
fn an_absent_batch_max_min_is_refused_not_defaulted() {
    let resp = call(&request_with(Some(json!({})), Some(capacity(None, true))));
    assert_eq!(
        planner_err(&resp).as_deref(),
        Some("badBatchMaxMin"),
        "{resp}"
    );
}

/// **`CapWire.maxCandId` on the running block's id**, reached from a host: 1,024
/// characters is what the candidate section already puts on a candidate's own
/// id, and `state.active.id` now takes the same one.
#[test]
fn a_long_active_id_is_refused_at_the_wires_own_id_bound() {
    let long = "x".repeat(1025);
    let resp = call(&request(state(
        json!({"active": {"id": long, "started": NOW - 60, "estMin": 60}}),
    )));
    assert_eq!(planner_err(&resp).as_deref(), Some("badActive id"), "{resp}");
    // And 1,024 is inside it, so the guard is where it says it is.
    let at = call(&request(state(
        json!({"active": {"id": "x".repeat(1024), "started": NOW - 60, "estMin": 60}}),
    )));
    assert_eq!(planner_err(&at), None, "an id at the bound was refused: {at}");
}

/// **A running block that started after `now`** is not one the planner could
/// hold — `Planner.ActiveBlock.wf`, through `Planner.mkActive?`.
#[test]
fn a_running_block_that_started_after_now_is_refused() {
    let resp = call(&request(state(
        json!({"active": {"id": "m2", "started": NOW + 60, "estMin": 60}}),
    )));
    assert_eq!(planner_err(&resp).as_deref(), Some("badActive wf"), "{resp}");
}

/// **An estimate past the day** is refused by the same constructor —
/// `Look.maxDayMin` is the day's own bound and `PlanWire` writes no second one.
#[test]
fn an_active_estimate_past_the_day_is_refused() {
    let resp = call(&request(state(
        json!({"active": {"id": "m2", "started": NOW - 60, "estMin": 1441}}),
    )));
    assert_eq!(planner_err(&resp).as_deref(), Some("badActive wf"), "{resp}");
}

/// **A break longer than a day**, through `Planner.mkBreak?`.
#[test]
fn a_break_longer_than_a_day_is_refused() {
    let resp = call(&request(state(json!({"break": {"plannedMin": 1441}}))));
    assert_eq!(planner_err(&resp).as_deref(), Some("badBreak wf"), "{resp}");
}

/// **An unknown `place` word**, never defaulted to a seat (AGENTS §5.7).
#[test]
fn an_unknown_break_place_is_refused_by_name() {
    let resp = call(&request(state(
        json!({"break": {"plannedMin": 10, "place": "hammock"}}),
    )));
    assert_eq!(
        planner_err(&resp).as_deref(),
        Some("badBreak place"),
        "{resp}"
    );
}

/// **A `lastHash` that is not sixteen hex digits**, through `Planner.mkHash?` —
/// the kernel's one hex reader.
#[test]
fn a_short_last_plan_hash_is_refused() {
    let resp = call(&request(state(json!({"lastHash": "00ff"}))));
    assert_eq!(planner_err(&resp).as_deref(), Some("badHash"), "{resp}");
}

/// **A stored priority past seven**, through `Planner.mkYesterday?` — the one
/// reader of a stored `p` (§7.4).
#[test]
fn a_stored_priority_past_seven_is_refused() {
    let resp = call(&request(state(
        json!({"yesterday": [{"id": "m1", "p": 8}]}),
    )));
    assert_eq!(
        planner_err(&resp).as_deref(),
        Some("badYesterdayList"),
        "{resp}"
    );
}

/// **A routine window past the calendar**, at its position, through
/// `Cal.mkInstant?`.
#[test]
fn a_routine_window_past_the_calendar_is_refused_at_its_position() {
    let resp = call(&request(Some(json!({"routines": [
        {"id": "lunch", "winLo": NOW, "winHi": NOW + 60, "durMin": 30},
        {"id": "shower", "winLo": 315_537_897_600u64, "winHi": 0, "durMin": 20}
    ]}))));
    assert_eq!(
        planner_err(&resp).as_deref(),
        Some("badRoutine 1 winLo"),
        "{resp}"
    );
}

/// **A routine duration past the fork's `u32`**, through `EmitWire.u32Within`.
#[test]
fn a_routine_duration_past_the_forks_u32_is_refused() {
    let resp = call(&request(Some(json!({"routines": [
        {"id": "lunch", "winLo": NOW, "winHi": NOW + 60, "durMin": 4_294_967_296u64}
    ]}))));
    assert_eq!(
        planner_err(&resp).as_deref(),
        Some("badRoutine 0 durMin"),
        "{resp}"
    );
}

/// **A `drop` override that is not an id** is refused by name, never skipped.
#[test]
fn a_drop_override_that_is_not_an_id_is_refused() {
    let resp = call(&request(Some(json!({"overrides": {"drop": [3]}}))));
    assert_eq!(
        planner_err(&resp).as_deref(),
        Some("badOverride drop"),
        "{resp}"
    );
}

/// **An override's minutes past the fork's `u32`.**
#[test]
fn an_override_estimate_past_the_forks_u32_is_refused() {
    let resp = call(&request(Some(
        json!({"overrides": {"est": [{"id": "m1", "min": 4_294_967_296u64}]}}),
    )));
    assert_eq!(
        planner_err(&resp).as_deref(),
        Some("badOverride est"),
        "{resp}"
    );
}

// ---------------------------------------------------------------------------
// And the other direction (AGENTS §5.8): a real day reads
// ---------------------------------------------------------------------------

/// **A day with everything running is accepted.**
///
/// Every refusal above is a refusal of something a host actually sent, and this
/// is the sentence that keeps them from being a check no input can pass: the
/// same section, with every record inside its bound, is answered.
#[test]
fn a_day_with_everything_running_is_accepted() {
    let resp = call(&request_with_docs(Some(json!({
        "state": {
            "active": {"id": "m2", "started": NOW - 900, "estMin": 60, "paused": false},
            "break": {"started": NOW - 300, "plannedMin": 10, "place": "walk"},
            "interrupt": {"started": NOW - 120, "id": "m1"},
            "lastHash": "00000000000000ff",
            "yesterday": [{"id": "m1", "p": 3}, {"id": "m2", "p": 0}]
        },
        "routines": [
            {"id": "lunch", "winLo": NOW, "winHi": NOW + 7200, "durMin": 30},
            {"id": "shower", "winLo": NOW, "winHi": NOW + 3600, "durMin": 20,
             "mandatory": true}
        ],
        "overrides": {
            "est": [{"id": "m1", "min": 90}],
            "extra": [{"id": "m2", "min": 30}],
            "drop": ["m3"]
        }
    })), Some(capacity(Some(json!(20)), true)), routine_docs()));
    assert_eq!(
        planner_err(&resp),
        None,
        "a day inside every bound was refused: {resp}"
    );
    // **And the day it answers is a day, not an empty one.** Without this the
    // test above is satisfied by any response at all (AGENTS §9.2's "a check no
    // input can fail"): §8.2 step 2 places the mandatory instance and step 1
    // replays the open interruption, so both rows are here by name.
    let segs = resp["ok"]["plan"]["segments"]
        .as_array()
        .unwrap_or_else(|| panic!("no plan.segments: {resp}"));
    let kinds: Vec<&str> = segs.iter().filter_map(|s| s["kind"].as_str()).collect();
    assert!(
        kinds.contains(&"routine"),
        "the mandatory window instance was not placed: {kinds:?}"
    );
    assert!(
        kinds.contains(&"lost"),
        "§9's running interruption did not reach the day: {kinds:?}"
    );
    assert!(
        segs.iter()
            .any(|s| s["kind"] == "routine" && s["item"] == "shower" && s["planned"] == 20),
        "the routine row is not the instance the request sent: {resp}"
    );
}

/// **A window instance the plan does not hold is refused BY ITS ID.**
///
/// The request half decoded `routines` without a plan; the response half
/// assembles `Planner.PlanReq`, so `Planner.mkRoutine?`'s own rules — an
/// unknown item, and README gap 285's "declares no window" — are now reachable
/// from a host, with the id in the text so the caller can tell which of the
/// instances it sent was refused.
#[test]
fn a_routine_the_plan_does_not_hold_is_refused_by_its_id() {
    let resp = call(&request_with_docs(
        Some(json!({"routines": [{"id": "lunch", "winLo": NOW, "winHi": NOW + 3600,
                                  "durMin": 30}]})),
        Some(capacity(Some(json!(20)), true)),
        json!([]),
    ));
    assert_eq!(
        planner_err(&resp).as_deref(),
        Some("routineRefused unknownItem lunch"),
        "{resp}"
    );
}

/// **The seam's replay is the CAPACITY section's demand first** — so
/// `PlannerRefusal.runAbsent` is a branch no host reaches today, and this test
/// asserts the ordering that makes it unreachable rather than a refusal
/// nothing can produce (AGENTS §9.2; the shape README gap 1672 established and
/// W-28 reuses for the same reason one field along).
///
/// `Planner.PlanReq.run` is this call's own replay (D9, D24) and the seam
/// carries a `Seal.Run` on exactly the requests it carries facts for
/// (`Boundary.LogReq.seamRun`, and
/// `PlanWire.the_seam_carries_its_run_exactly_when_it_carries_its_facts`). A
/// request that asks for no facts never gets past `CapWire.Section.today0`,
/// which refuses `day0WithoutLog` before the planner section is read. README
/// gap **1783**.
#[test]
fn the_seams_replay_is_demanded_by_the_capacity_section_first() {
    let body = request_with_docs(Some(json!({})), Some(capacity(Some(json!(20)), true)), json!([]));
    let no_facts = body.replace(r#""facts":true"#, r#""facts":false"#);
    assert_ne!(body, no_facts, "the log section's `facts` key moved");
    let resp = call(&no_facts);
    assert_eq!(planner_err(&resp), None, "the planner section answered: {resp}");
    assert_eq!(
        resp["err"]["capacity"].as_str(),
        Some("day0WithoutLog"),
        "{resp}"
    );
}
