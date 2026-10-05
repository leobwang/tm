//! **Every refusal the `planner` section can answer, and why the binary's request never meets it on a tree the
//! fork planned — or the gap that says where it can** (README gap 4751; stage 6 W-46 track H).
//!
//! R3 swaps the shipped planner for the kernel's, and the kernel can REFUSE a request where fork 4748911's planner
//! was total. Two refusals are licensed by a standing decision (the owner's D80: `eveningPastTheCalendar`, P71, and
//! `ciDisagrees`, P72); the W-45 switch measured that no driven or generated world reached another, which is a
//! sample (gap 4751). This file turns it into a CLASS, held three ways:
//!
//! * **the class itself** ([`every_planner_refusal_is_classified`]): every constructor of `PlanWire.PlannerRefusal`
//!   and every key a definition of `PlanWire.lean` throws it with — read off the source, so a new refusal, or a new
//!   key of an old one, fails here until it is classified — and every `Planner.RoutineErr` `routineRefused` carries;
//! * **the binary's encoder** ([`the_encoder_writes_only_the_keys_the_class_admits`],
//!   [`every_value_the_host_types_hold_is_answered`], [`every_routine_instance_is_a_candidate_the_request_sends`]):
//!   the keys `tm_core::planwire`'s encoder writes, over arbitrary host values; the kernel's answer to a request
//!   carrying each host type at its extremes; and the one hypothesis a proof below is stated under;
//! * **the binary itself** ([`an_id_past_the_bound_is_refused_by_the_capacity_section_first`],
//!   [`a_routine_word_the_two_readers_key_apart_is_p72s_refusal_by_name`],
//!   [`the_calendars_last_day_reaches_the_planner_section_by_p71s_name`]).
//!
//! Two refusals of the class were an R3 BLOCKER until the W-46 repair (README gap 4793, the W-46 switch's gap 4843): an
//! evening routine on the calendar's last local day was refused by the section's reader, `badRoutine <i> winLo|winHi`,
//! where P71's row names that day's refusal `eveningPastTheCalendar`. A section refusal now yields to D80 (a), asked of
//! the capacity section's parts (`PlanWire.eveningFirst`, `Why::YieldsToTheEvening`), and the last test pins it.
//!
//! Four refusals no request at all reaches — `runAbsent`, `candsPastCap`, `wallsDisagree` and `routineRefused
//! pastTheHorizon` — are PROVED unreachable (`PlanWire.planReqOf_never_refuses_what_the_capacity_section_excludes`,
//! `PlanWire.planReqOf_never_refuses_past_the_horizon`), and a fifth, `routineRefused unknownItem`, on every request whose
//! routines each name a candidate it carries, which the encoder pays by construction
//! (`PlanWire.planReqOf_never_refuses_an_item_a_candidate_names`: since W-46 the assembler asks D80 first, so such a
//! request is P72's `ciDisagrees … plan none` by name — README gap 4795). The class table says each by name.

mod cli_common;

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[path = "support/planreq.rs"]
#[allow(dead_code)]
mod planreq;

#[path = "support/plangen.rs"]
#[allow(dead_code)]
mod plangen;

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use cli_common::Tm;
use proptest::prelude::*;
use serde_json::{json, Value};
use tm_core::model::{Id, InstanceKey};
use tm_core::planwire::{self, Grown, RoutineInst};
use tm_core::priority;
use tm_core::store::{ActiveBlock, BreakState, InterruptState, RuntimeState};

/// Why a refusal is never met on a tree the fork planned — or where it is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Why {
    /// No definition of `PlanWire.lean` throws it.
    ThrownNowhere,
    /// The binary's encoder never writes the key it is about.
    NotSent,
    /// The encoder builds the container as JSON with unique keys (`serde_json::Map`), so its shape never fails.
    Shape,
    /// Read from a host type every value of which the reader accepts (the fork's `u32` is `Look.maxPlanMinutes`).
    HostType,
    /// The encoder never sends such a record: it filters it or builds the request around it.
    Filtered,
    /// No request reaches it: proved, by the theorem the row's evidence names.
    Excluded,
    /// No request whose routines each name a candidate it carries reaches it — proved under that hypothesis, which the
    /// binary's encoder pays by construction (`planwire::routine_instances` reads the instances off the candidates
    /// `planwire::capacity_json` sends) and [`every_routine_instance_is_a_candidate_the_request_sends`] holds.
    ExcludedOnTheEncodersRequests,
    /// The capacity section, read before this one, refuses the same tree first — on the binary's own trees.
    Shadowed,
    /// Licensed by a standing decision: D80, P71 and P72.
    Licensed,
    /// Reachable only from bytes the binary never writes, typed by hand: named in a README gap.
    HandEdited,
    /// **Yields to D80 (a)** (README gap 4793, the W-46 repair): a section refusal on a day whose evening runs past the
    /// calendar is answered by P71's name (`PlanWire.eveningFirst`,
    /// `runPlanner_names_an_evening_past_the_calendar_over_a_section_refusal`); a window past the calendar on a day
    /// whose evening is inside crosses midnight, and the capacity section refuses that routine's `due` first on both
    /// binaries (driven over four zones, the README's W-46 repair block).
    YieldsToTheEvening,
}

/// **The class, classified.** `(constructor, key, why, the evidence)`: a `None` key covers every key the
/// constructor is thrown with (a family the encoder never sends, or one whose key is a variable).
const CLASS: &[(&str, Option<&str>, Why, &str)] = &[
    ("shape", None, Why::ThrownNowhere, "no definition throws it (README gap 4791: a dead constructor)"),
    ("badState", Some("state"), Why::Shape, "planwire::planner_json writes `state` as an object"),
    ("badState", Some("active"), Why::Shape, "planwire::state_json writes `active` as an object of a `Map`"),
    ("badState", Some("brk"), Why::Shape, "planwire::state_json writes `break` as an object of a `Map`"),
    ("badState", Some("interrupt"), Why::Shape, "planwire::state_json writes `interrupt` as an object of a `Map`"),
    ("badState", Some("lastHash"), Why::NotSent, "planwire::state_json writes no `lastHash`"),
    ("badState", Some("yesterday"), Why::NotSent, "planwire::state_json writes no `yesterday`"),
    ("badActive", Some("id"), Why::Shadowed, "a running item's id is a candidate's, bounded by `CapWire.maxCandId` first; past it only by hand (gap 4792)"),
    ("badActive", Some("started"), Why::HandEdited, "an instant outside the calendar: the kernel's `emit` refuses a start stamped past it (`badAt`, driven), so only a hand-edited log or `.tm/state.json` (gap 4793)"),
    ("badActive", Some("estMin"), Why::HostType, "`ActiveBlock::est_min: u32`"),
    ("badActive", Some("paused"), Why::HostType, "`ActiveBlock::paused: bool`"),
    ("badActive", Some("wf"), Why::HostType, "`ActiveBlock.wf` is `estMin ≤ Look.maxPlanMinutes`, the `u32`'s width"),
    ("badActive", Some("workedMin"), Why::HostType, "`planwire::add_worked_min(_, u32)`, `Planner.workedOf?` at the `u32`'s width"),
    ("badBreak", Some("started"), Why::HostType, "`BreakState::started_at` is an instant at or before `now`"),
    ("badBreak", Some("plannedMin"), Why::HostType, "`BreakState::planned_min: u32`"),
    ("badBreak", Some("place"), Why::HandEdited, "`.tm/state.json`'s `where` is a String; `tm break` writes BreakPlace's four words (gap 4794)"),
    ("badBreak", Some("wf"), Why::HostType, "`BreakState.wf`: started at or before `now`, planned within the `u32`'s width"),
    ("badInterrupt", Some("started"), Why::HandEdited, "an instant outside the calendar: the kernel's `emit` refuses an interruption stamped past it (`badAt`, driven), so only a hand edit (gap 4793)"),
    ("badInterrupt", Some("id"), Why::Shadowed, "the interrupted item's id, a candidate's; past `maxCandId` only by hand (gap 4792)"),
    ("badHash", None, Why::NotSent, "planwire::state_json writes no `lastHash`"),
    ("badYesterday", None, Why::NotSent, "planwire::state_json writes no `yesterday`"),
    ("badYesterdayList", None, Why::NotSent, "planwire::state_json writes no `yesterday`"),
    ("badRoutine", Some("routines"), Why::Shape, "planwire::routines_json writes an array"),
    ("badRoutine", Some("id"), Why::Shadowed, "an instance's id is its candidate's, bounded by `CapWire.maxCandId` first (gap 4792)"),
    ("badRoutine", Some("inst"), Why::HostType, "`InstanceKey`'s Display: a date or `#n`"),
    ("badRoutine", Some("winLo"), Why::YieldsToTheEvening, "an evening routine on the calendar's last local day west of UTC: P71's `eveningPastTheCalendar` first (gap 4793, the_calendars_last_day_reaches_the_planner_section_by_p71s_name)"),
    ("badRoutine", Some("winHi"), Why::YieldsToTheEvening, "as `winLo`; a window past the calendar on a day whose evening is inside crosses midnight, and the capacity section's `badCandidate <i> due` comes first (gap 4793)"),
    ("badRoutine", Some("durMin"), Why::HostType, "`RoutineInst::dur_min: u32`"),
    ("badRoutine", Some("mandatory"), Why::HostType, "`RoutineInst::mandatory: bool`"),
    ("badOverride", None, Why::NotSent, "planwire::planner_json writes no `overrides`"),
    ("tooManyOverrides", None, Why::NotSent, "planwire::planner_json writes no `overrides`"),
    ("badBatchMaxMin", None, Why::HostType, "`PriorityCfg::batch_max_min: u32`, written by planwire::capacity_json"),
    ("capacityAbsent", None, Why::Filtered, "the planner request is the capacity request with the section spliced in (planwire::with_planner)"),
    ("runAbsent", None, Why::Excluded, "PlanWire.planReqOf_never_refuses_what_the_capacity_section_excludes"),
    ("wallsDisagree", None, Why::Excluded, "PlanWire.planReqOf_never_refuses_what_the_capacity_section_excludes"),
    ("candsPastCap", None, Why::Excluded, "PlanWire.planReqOf_never_refuses_what_the_capacity_section_excludes"),
    ("routineRefused", Some("unknownItem"), Why::ExcludedOnTheEncodersRequests, "PlanWire.planReqOf_never_refuses_an_item_a_candidate_names: D80 is asked first since W-46, so the request is P72's `ciDisagrees <id> wire <w> plan none` by name (gap 4795)"),
    ("routineRefused", Some("undeclaredWindow"), Why::HandEdited, "a window the host reads and the kernel does not; a routines.md line with neither is refused at load (gap 4795)"),
    ("routineRefused", Some("emptyWindow"), Why::Filtered, "planwire::routine_instances drops an instance with nothing left of its span (W-37, gap 3201)"),
    ("routineRefused", Some("pastTheHorizon"), Why::Excluded, "PlanWire.planReqOf_never_refuses_past_the_horizon: the reader bounds `winHi` by `secWithin`, mkRoutine?'s own bound (gap 4793)"),
    ("routineRefused", Some("noMinutes"), Why::Filtered, "planwire::routine_instances drops an instance with no minutes left"),
    ("routineRefused", Some("tooManyRoutines"), Why::Shadowed, "the instances are candidates, capped by `CapWire.readCands` at the same number"),
    ("badOvertime", Some("overtime"), Why::Shape, "planwire::overtime_json writes an object"),
    ("badOvertime", Some("id"), Why::Shadowed, "the running item's id, a candidate's (gap 4792)"),
    ("badOvertime", Some("blocks"), Why::HostType, "planwire::overtime_json's `blocks: u32`"),
    ("badOvertime", Some("grown"), Why::HostType, "`Grown`'s fields are `u32`, `Planner.GrownFacts.wf` their width"),
    ("badOvertime", Some("remaining"), Why::HostType, "`Grown::remaining_min: u32`"),
    ("badOvertime", Some("plannedMin"), Why::HostType, "`Grown::planned_min: u32`"),
    ("eveningPastTheCalendar", None, Why::Licensed, "the owner's D80 (a), parity P71"),
    ("ciDisagrees", None, Why::Licensed, "the owner's D80 (b), parity P72"),
];

/// `text` with its Lean comments cut away (`--` to the end of the line, `/- … -/` nested), its strings kept.
fn lean_code(text: &str) -> String {
    let b = text.as_bytes();
    let (mut out, mut i) = (String::new(), 0usize);
    while i < b.len() {
        if b[i..].starts_with(b"/-") {
            let mut depth = 1;
            i += 2;
            while i < b.len() && depth > 0 {
                if b[i..].starts_with(b"/-") {
                    depth += 1;
                    i += 2;
                } else if b[i..].starts_with(b"-/") {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
        } else if b[i..].starts_with(b"--") {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
        } else if b[i] == b'"' {
            let start = i;
            i += 1;
            while i < b.len() && b[i] != b'"' {
                i += if b[i] == b'\\' { 2 } else { 1 };
            }
            i = (i + 1).min(b.len());
            out.push_str(&String::from_utf8_lossy(&b[start..i]));
        } else {
            let c = text[i..].chars().next().expect("a char");
            out.push(c);
            i += c.len_utf8();
        }
    }
    out
}

/// The constructors of `inductive <name>` in a Lean source, in order.
fn constructors(code: &str, name: &str) -> Vec<String> {
    let head = format!("inductive {name}");
    let at = code.find(&head).unwrap_or_else(|| panic!("no `{head}`"));
    let mut out = Vec::new();
    for line in code[at + head.len()..].lines().skip(1) {
        let t = line.trim_start();
        if t.starts_with("deriving") || (!line.starts_with(' ') && !t.is_empty()) {
            break;
        }
        if let Some(rest) = t.strip_prefix("| ") {
            out.push(rest.split(|c: char| !c.is_alphanumeric()).next().expect("a name").to_string());
        }
    }
    out
}

/// The top-level `def` bodies of a Lean source (comments cut), each to the next declaration.
fn def_bodies(code: &str) -> Vec<String> {
    let starts = ["def ", "theorem ", "structure ", "inductive ", "abbrev ", "instance ", "end ", "namespace ", "open ", "@[", "private def "];
    let mut out: Vec<String> = Vec::new();
    let mut cur: Option<String> = None;
    for line in code.lines() {
        if starts.iter().any(|s| line.starts_with(s)) {
            if let Some(c) = cur.take() {
                out.push(c);
            }
            if line.starts_with("def ") || line.starts_with("private def ") || line.starts_with("@[export") {
                cur = Some(String::new());
            }
        }
        if let Some(c) = cur.as_mut() {
            c.push_str(line);
            c.push('\n');
        }
    }
    out.extend(cur);
    out
}

/// **What the section's definitions throw**: every `PlannerRefusal.<ctor>` inside a `def` of `PlanWire.lean`, with
/// the `PlanKey` it is thrown with when the site names one (`None` when the key is a variable or there is none).
fn thrown(code: &str, ctors: &[String]) -> BTreeSet<(String, Option<String>)> {
    let mut out = BTreeSet::new();
    for body in def_bodies(code) {
        let mut rest = body.as_str();
        while let Some(at) = rest.find("PlannerRefusal.") {
            let after = &rest[at + "PlannerRefusal.".len()..];
            let name: String = after.chars().take_while(|c| c.is_alphanumeric()).collect();
            let len = name.len();
            if ctors.contains(&name) {
                // The arguments up to the closing parenthesis or the end of the line.
                let args: String = after[len..].chars().take_while(|&c| c != ')' && c != '\n' && c != ',').collect();
                let key = args
                    .split_whitespace()
                    .find_map(|w| w.strip_prefix("PlanKey."))
                    .map(|k| k.chars().take_while(|c| c.is_alphanumeric()).collect::<String>());
                out.insert((name, key));
            }
            rest = &after[len..];
        }
    }
    out
}

fn root() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// **The class, held** (README gap 4751): every constructor of `PlannerRefusal` is classified; every
/// `(constructor, key)` a definition of `PlanWire.lean` throws is covered by a row — its own, or its constructor's
/// `None` row; no row names a pair nothing throws (a stale row FAILS, W-27's shape); `routineRefused` has one row
/// for each `Planner.RoutineErr`; and the table is printed for the README block.
#[test]
fn every_planner_refusal_is_classified() {
    let plan_wire = lean_code(&std::fs::read_to_string(root().join("kernel/TmKernel/TmKernel/PlanWire.lean")).expect("PlanWire.lean"));
    let planner = lean_code(&std::fs::read_to_string(root().join("kernel/TmKernel/TmKernel/Planner.lean")).expect("Planner.lean"));
    let ctors = constructors(&plan_wire, "PlannerRefusal");
    let errs = constructors(&planner, "RoutineErr");
    assert!(ctors.len() >= 20 && ctors.contains(&"shape".to_string()) && ctors.contains(&"ciDisagrees".to_string()), "{ctors:?}");
    assert_eq!(errs.len(), 6, "{errs:?}");
    let thrown = thrown(&plan_wire, &ctors);
    assert!(thrown.len() > 40, "the scan reached {} pairs", thrown.len());
    let mut problems = Vec::new();
    for c in &ctors {
        if !CLASS.iter().any(|(n, _, _, _)| n == c) {
            problems.push(format!("`{c}` is a constructor no row classifies"));
        }
    }
    for (c, k) in &thrown {
        let own = CLASS.iter().any(|(n, kk, _, _)| n == c && kk.map(str::to_string) == *k);
        let family = CLASS.iter().any(|(n, kk, _, _)| n == c && kk.is_none());
        if !own && !family && c != "routineRefused" {
            problems.push(format!("`{c} {}` is thrown and no row classifies it", k.as_deref().unwrap_or("-")));
        }
    }
    for (n, k, why, _) in CLASS {
        if *n == "routineRefused" {
            if !k.is_some_and(|k| errs.iter().any(|e| e == k)) {
                problems.push(format!("`routineRefused {}` names no `RoutineErr`", k.unwrap_or("-")));
            }
            continue;
        }
        let throws = thrown.iter().any(|(c, kk)| c == n && (k.is_none() || kk.as_deref() == *k));
        if *why == Why::ThrownNowhere {
            if throws {
                problems.push(format!("`{n}` is classified as thrown nowhere and a definition throws it"));
            }
        } else if !throws {
            problems.push(format!("`{n} {}` is classified and nothing throws it: a stale row", k.unwrap_or("-")));
        }
    }
    for e in &errs {
        if !CLASS.iter().any(|(n, k, _, _)| *n == "routineRefused" && *k == Some(e.as_str())) {
            problems.push(format!("`routineRefused {e}` is not classified"));
        }
    }
    let mut by: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (n, k, why, _) in CLASS {
        by.entry(format!("{why:?}")).or_default().push(match k {
            Some(k) => format!("{n} {k}"),
            None => (*n).to_string(),
        });
    }
    for (why, names) in &by {
        eprintln!("gap 4751 class: {why} ({}): {}", names.len(), names.join(", "));
    }
    eprintln!("gap 4751 class: {} constructors, {} thrown (constructor, key) pairs, {} rows", ctors.len(), thrown.len(), CLASS.len());
    assert!(problems.is_empty(), "the planner refusals are not classified:\n  {}", problems.join("\n  "));
}

/// Every key path a JSON value carries, arrays read element-wise (`routines[].id`).
fn key_paths(v: &Value, at: &str, out: &mut BTreeSet<String>) {
    match v {
        Value::Object(m) => {
            for (k, x) in m {
                let p = if at.is_empty() { k.clone() } else { format!("{at}.{k}") };
                out.insert(p.clone());
                key_paths(x, &p, out);
            }
        }
        Value::Array(xs) => {
            for x in xs {
                key_paths(x, &format!("{at}[]"), out);
            }
        }
        _ => {}
    }
}

/// The key paths the class lets the encoder write: none of `lastHash`, `yesterday` or `overrides`.
const ADMITTED: &[&str] = &[
    "state", "state.active", "state.active.id", "state.active.started", "state.active.estMin", "state.active.paused",
    "state.active.workedMin", "state.break", "state.break.started", "state.break.plannedMin", "state.break.place",
    "state.interrupt", "state.interrupt.started", "state.interrupt.id", "routines", "routines[].id",
    "routines[].inst", "routines[].winLo", "routines[].winHi", "routines[].durMin", "routines[].mandatory",
    "overtime", "overtime.id", "overtime.blocks", "overtime.grown", "overtime.grown.remaining",
    "overtime.grown.plannedMin",
];

fn hhmm() -> impl Strategy<Value = chrono::NaiveTime> {
    (0u32..24, 0u32..60).prop_map(|(h, m)| chrono::NaiveTime::from_hms_opt(h, m, 0).expect("a clock"))
}

fn runtime_state() -> impl Strategy<Value = RuntimeState> {
    let active = proptest::option::of((hhmm(), any::<u32>(), any::<bool>()));
    let brk = proptest::option::of((proptest::option::of(hhmm()), any::<u32>(), proptest::option::of("[a-z]{1,8}")));
    let intr = proptest::option::of((proptest::option::of(hhmm()), any::<bool>()));
    let yesterday = proptest::collection::btree_map("[a-z][0-9]", 0u8..8, 0..4);
    let hash = proptest::option::of("[0-9a-f]{16}");
    (active, brk, intr, yesterday, hash).prop_map(|(a, b, i, y, h)| {
        let mut s = RuntimeState::default();
        s.active = a.map(|(started, est_min, paused)| ActiveBlock { id: Id::new("t3"), started, est_min, paused });
        s.break_ = b.map(|(started, planned_min, place)| BreakState { started, planned_min, place });
        s.interrupt = i.map(|(started, with)| InterruptState { started, id: with.then(|| Id::new("t3")) });
        s.priorities_yesterday = y.into_iter().map(|(k, v)| (Id::new(&k), v)).collect();
        s.last_plan_hash = h;
        s
    })
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(256),
        ..ProptestConfig::default()
    })]

    /// **The encoder writes only the keys the class admits** (gap 4751's NotSent and Shape rows): over
    /// arbitrary host values — a running block, a break, an interruption, stored priorities and a stored hash, any
    /// `u32` — `planwire::planner_json`, with `add_worked_min` and a what-if (`overtime_json`), writes `state` and
    /// its three records as objects, `routines` as an array of records, and never `lastHash`, `yesterday` or
    /// `overrides` — though the state it is handed holds the first two.
    #[test]
    fn the_encoder_writes_only_the_keys_the_class_admits(
        state in runtime_state(),
        worked in any::<u32>(),
        blocks in any::<u32>(),
        grown in proptest::option::of((any::<u32>(), any::<u32>())),
        dur in any::<u32>(),
        inst in proptest::option::of(any::<u32>()),
    ) {
        let tz = chrono_tz::America::Chicago;
        let now = plangen::at(tz, 10, 0);
        let replay = chokepoint::replay_of_text("", tz);
        let routines = [RoutineInst {
            id: Id::new("lunch"),
            inst: inst.map(InstanceKey::Nth),
            from: plangen::at(tz, 11, 0),
            to: plangen::at(tz, 13, 0),
            dur_min: dur,
            mandatory: inst.is_some(),
        }];
        let g = grown.map(|(r, p)| Grown { remaining_min: r, planned_min: p, need_min: 0 });
        let mut planner = planwire::planner_json(&state, &replay, now, tz, &routines, Some(planwire::overtime_json(&Id::new("t3"), blocks, g.as_ref())));
        planwire::add_worked_min(&mut planner, worked);
        let mut paths = BTreeSet::new();
        key_paths(&planner, "", &mut paths);
        let extra: Vec<&String> = paths.iter().filter(|p| !ADMITTED.contains(&p.as_str())).collect();
        prop_assert!(extra.is_empty(), "the encoder wrote a key the class does not admit: {:?}", extra);
        prop_assert!(planner["state"].is_object());
        for k in ["active", "break", "interrupt"] {
            prop_assert!(planner["state"].get(k).is_none_or(Value::is_object), "{}", k);
        }
        prop_assert!(planner["routines"].is_array());
        prop_assert!(planner["overtime"].is_object());
    }

    /// **Every value the host types hold is answered** (gap 4751's HostType rows): on every day the planner
    /// generator draws, the binary's encoder's request (`support/planreq.rs`, `tm_core::planwire`'s functions)
    /// with each host type at its extreme — the running estimate, the worked minutes, a break's planned minutes,
    /// every routine instance's duration, a what-if's blocks and grown facts and §16's `batch_max_min` at
    /// `u32::MAX`, every mark flipped — is a planned day, or a refusal the owner licensed (`eveningPastTheCalendar`,
    /// `ciDisagrees`); never another refusal of the section.
    #[test]
    fn every_value_the_host_types_hold_is_answered(case in plangen::case_strategy(), paused in any::<bool>()) {
        let w = plangen::build(&case);
        let tz = w.cfg.tz;
        let mut st = w.state.clone();
        if let Some(a) = st.active.as_mut() {
            a.est_min = u32::MAX;
            a.paused = paused;
        }
        st.break_ = Some(BreakState { started: None, planned_min: u32::MAX, place: Some("phone".into()) });
        let cands = priority::collect_candidates(&w.tree, &w.replay, &w.cfg, &w.model, plangen::date(), w.now);
        let world = planreq::World { docs: &w.docs, log: &w.log, tree: &w.tree, cfg: &w.cfg, state: &st, now: w.now, cands: &cands, replay: &w.replay };
        let running = planreq::running(&st).unwrap_or_else(|| Id::new("t1"));
        let grown = Grown { remaining_min: u32::MAX, planned_min: u32::MAX, need_min: 0 };
        let (mut req, _) = planreq::request(&world, Some(planwire::overtime_json(&running, u32::MAX, Some(&grown))));
        planwire::add_worked_min(&mut req["planner"], u32::MAX);
        if let Some(rs) = req["planner"]["routines"].as_array_mut() {
            for r in rs {
                r["durMin"] = json!(u32::MAX);
                r["mandatory"] = json!(!r["mandatory"].as_bool().unwrap_or(false));
            }
        }
        if let Some(p) = req["capacity"]["priority"].as_object_mut() {
            p.insert("batchMaxMin".into(), json!(u32::MAX));
        }
        let resp = planreq::call(&req);
        let _ = tz;
        match planwire::planner_refusal(&resp) {
            None => prop_assert!(resp.get("ok").is_some(), "neither a day nor a planner refusal: {}", resp),
            Some(r) => prop_assert!(
                r.starts_with("eveningPastTheCalendar") || r.starts_with("ciDisagrees"),
                "the kernel refused a host-typed value by a name no decision licenses: {}", r
            ),
        }
    }
}

/// The request the binary's encoder builds for a generated day (`support/planreq.rs`, which `planner_request_keys`'
/// `the_binarys_planner_request_and_the_harnesss_agree_in_value` holds to the binary's own by value).
fn generated_request(case: &plangen::Case) -> Value {
    let w = plangen::build(case);
    let cands = priority::collect_candidates(&w.tree, &w.replay, &w.cfg, &w.model, plangen::date(), w.now);
    let world = planreq::World { docs: &w.docs, log: &w.log, tree: &w.tree, cfg: &w.cfg, state: &w.state, now: w.now, cands: &cands, replay: &w.replay };
    planreq::request(&world, None).0
}

/// `(the routine instances the request sends, the ids among them no candidate of the same request carries)`.
fn routines_no_candidate_names(req: &Value) -> (usize, Vec<String>) {
    let cands: BTreeSet<&str> = req["capacity"]["candidates"]["items"]
        .as_array()
        .map(|xs| xs.iter().filter_map(|c| c["id"].as_str()).collect())
        .unwrap_or_default();
    let routines = req["planner"]["routines"].as_array().cloned().unwrap_or_default();
    let orphans = routines.iter().filter_map(|r| r["id"].as_str()).filter(|id| !cands.contains(id)).map(str::to_string).collect();
    (routines.len(), orphans)
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(256),
        ..ProptestConfig::default()
    })]

    /// **Every routine instance the binary's encoder sends names a candidate the same request sends** (README gap
    /// 4795): the hypothesis `PlanWire.planReqOf_never_refuses_an_item_a_candidate_names` is stated under. It holds by
    /// construction — `planwire::routine_instances` reads the instances off the candidates and `planwire::capacity_json`
    /// sends every one of them — and this holds it over the planner generator's days, so a change that sent an
    /// instance its candidate did not accompany fails here, and not as a refusal named `unknownItem` after R3.
    #[test]
    fn every_routine_instance_is_a_candidate_the_request_sends(case in plangen::case_strategy()) {
        let (_, orphans) = routines_no_candidate_names(&generated_request(&case));
        prop_assert!(orphans.is_empty(), "routine instances no candidate of the request names: {:?}", orphans);
    }
}

/// **And the property is not vacuous**: over the first 64 days a deterministic runner draws, most send routine
/// instances, and every instance names a candidate.
#[test]
fn the_routine_instance_property_meets_instances() {
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;

    let mut runner = TestRunner::deterministic();
    let strategy = plangen::case_strategy();
    let (mut days_with, mut instances) = (0usize, 0usize);
    for _ in 0..64 {
        let case = strategy.new_tree(&mut runner).expect("a generated day").current();
        let (n, orphans) = routines_no_candidate_names(&generated_request(&case));
        assert!(orphans.is_empty(), "routine instances no candidate of the request names: {orphans:?}");
        days_with += usize::from(n > 0);
        instances += n;
    }
    eprintln!("gap 4795: {days_with} of 64 generated days send routine instances, {instances} in all, each a candidate's");
    assert!(days_with >= 16 && instances >= 32, "{days_with} days, {instances} instances");
}

/// A long run of one letter: past `CapWire.maxCandId`'s 1,024 characters.
fn long(c: char) -> String {
    std::iter::repeat_n(c, 1_100).collect()
}

/// **An id past the bound is refused by the capacity section first** (gap 4751's Shadowed rows for `id`): a
/// routine whose title — its key since D31 — runs to 1,100 characters, and an item whose `^id` does, each on §4.3's
/// tree. `tm check` names the CAPACITY section's `badCandidate <i> id` for both, never the planner section's, and
/// `tm plan` is refused by the same name today — so the binary never sends the planner section such an id on a tree
/// the fork planned.
#[test]
fn an_id_past_the_bound_is_refused_by_the_capacity_section_first() {
    let now = "2026-09-07T08:00:00-05:00";
    for (file, edit) in [
        ("routines.md", None),
        ("week/2026-W37.md", Some("^t3")),
    ] {
        let tm = Tm::empty();
        tm.ok_at("2026-09-07T06:00:00-05:00", &["init", "--example"]);
        let path = tm.plan.join(file);
        let text = std::fs::read_to_string(&path).expect("the file");
        let text = match edit {
            None => format!("{text}- {}  win:09:00-21:00 dur:30m  every:day\n", long('x')),
            Some(id) => {
                assert_eq!(text.matches(id).count(), 1, "{id} once in {file}");
                text.replace(id, &format!("^{}", long('y')))
            }
        };
        std::fs::write(&path, text).expect("the edit");
        let check = tm.run_at(now, &["check"]);
        assert!(check.stdout.contains("badCandidate") && check.stdout.contains(" id "), "{file}: {}", check.stdout);
        assert!(!check.stdout.contains("badRoutine") && !check.stdout.contains("badActive"), "{file}: {}", check.stdout);
        let plan = tm.run_at(now, &["plan"]);
        assert_ne!(plan.code, 0, "{file}: `tm plan` planned a tree the capacity section refuses: {}", plan.stdout);
        assert!(plan.stderr.contains("badCandidate"), "{file}: {}", plan.stderr);
    }
}

/// **A routine word the two readers key apart is P72's refusal, by P72's name** (README gap 4795): a routine line
/// whose `^` word the host reads as title text and the kernel as an id — `- stretch ^é1  win:07:00-21:00 dur:10m
/// every:day` on §4.3's tree. The host keys the routine `stretch ^é1`, the kernel `é1`, so the request carries a
/// candidate the kernel's plan does not hold: P72's `ciDisagrees <id> wire <w> plan none`, the owner's D80 (b). Until
/// W-46 the assembler read the routines first and named it `routineRefused unknownItem stretch ^é1` — one
/// disagreement, two names, and the second no register row gives; since W-46 it asks D80 first. `tm check` names it
/// as the task twin is named (P78, exit 2), and `tm plan`, on fork 4748911's planner until R3, plans the routine (exit
/// 0) — at R3 `tm plan` meets P72's refusal, which P72's row licenses by this very text.
#[test]
fn a_routine_word_the_two_readers_key_apart_is_p72s_refusal_by_name() {
    let tm = Tm::empty();
    tm.ok_at("2026-09-07T06:00:00-05:00", &["init", "--example"]);
    let path = tm.plan.join("routines.md");
    let text = std::fs::read_to_string(&path).expect("routines.md");
    std::fs::write(&path, format!("{text}- stretch ^é1  win:07:00-21:00 dur:10m  every:day\n")).expect("the edit");
    let now = "2026-09-07T10:00:00-05:00";
    let check = tm.run_at(now, &["check"]);
    assert_eq!(check.code, 2, "{}{}", check.stdout, check.stderr);
    assert!(check.stdout.contains("ciDisagrees stretch ^é1 wire 1 plan none"), "{}", check.stdout);
    assert!(!check.stdout.contains("routineRefused"), "the routine's own refusal named first: {}", check.stdout);
    let plan = tm.run_at(now, &["plan"]);
    assert_eq!(plan.code, 0, "{}{}", plan.stdout, plan.stderr);
    assert!(plan.stdout.contains("stretch ^é1"), "{}", plan.stdout);

    // The task-side twin: the same `^` word on a task is P72's, by name.
    let twin = Tm::empty();
    twin.ok_at("2026-09-07T06:00:00-05:00", &["init", "--example"]);
    let week = twin.plan.join("week/2026-W37.md");
    let text = std::fs::read_to_string(&week).expect("the week");
    let at = text.find("- [ ] 3 1b Review the drafts").expect("^t5's line");
    let end = at + text[at..].find('\n').expect("its end") + 1;
    std::fs::write(&week, format!("{}- [ ] 2 30m Sketch the plan ^é9\n{}", &text[..end], &text[end..])).expect("the edit");
    let check = twin.run_at(now, &["check"]);
    assert!(check.stdout.contains("ciDisagrees Sketch the plan ^é9 wire 2 plan none"), "{}", check.stdout);
}

/// **The calendar's last day reaches the planner section by P71's name** (README gap 4793, the W-46 switch's R3
/// BLOCKER gap 4843, closed by the W-46 repair): on 9999-12-31 in Chicago the calendar's last second is 17:59:59
/// local, so the day's evening runs past it — the day the owner's D80 (a) refuses, which P71's row names
/// `eveningPastTheCalendar`. A tree with no routine instance meets that name, and so does a tree with an evening
/// routine: its instance's window opens past the calendar and the section's reader refuses it (`badRoutine 0 winLo`),
/// and that refusal yields to D80 (a) (`PlanWire.eveningFirst`; until the repair it reached the host under its own
/// name). A routine whose window crosses midnight past the calendar is refused by the capacity section first, on fork
/// 4748911's binary as on the kernel's. Today `tm check` names each (P78) and `tm plan`, on fork 4748911's planner,
/// plans the first two; at R3 `tm plan` meets both under P71's name. And the binary cannot log a running block past
/// the calendar — the kernel's `emit` refuses the line (`badAt`) — which is why `badActive started` is a hand edit's.
#[test]
fn the_calendars_last_day_reaches_the_planner_section_by_p71s_name() {
    let now = "9999-12-31T12:00:00-06:00";
    let tree = |routine: Option<&str>| {
        let tm = Tm::empty();
        tm.ok_at("2026-09-07T06:00:00-05:00", &["init"]);
        let cfg = tm.plan.join("config.toml");
        let text = std::fs::read_to_string(&cfg).expect("config.toml");
        let text: String = text
            .lines()
            .map(|l| if l.starts_with("tz = ") { "tz = \"America/Chicago\"".to_string() } else { l.to_string() })
            .collect::<Vec<_>>()
            .join("\n");
        std::fs::write(&cfg, format!("{text}\n")).expect("the zone");
        if let Some(r) = routine {
            let path = tm.plan.join("routines.md");
            let text = std::fs::read_to_string(&path).expect("routines.md");
            std::fs::write(&path, format!("{text}{r}\n")).expect("the routine");
        }
        tm
    };

    let plain = tree(None);
    let check = plain.run_at(now, &["check"]);
    assert_eq!(check.code, 2, "{}{}", check.stdout, check.stderr);
    assert!(check.stdout.contains("eveningPastTheCalendar"), "{}", check.stdout);
    assert_eq!(plain.run_at(now, &["plan"]).code, 0, "fork 4748911's planner plans the calendar's last day");

    let evening = tree(Some("- wind  win:20:00-23:00 dur:30m  every:day"));
    let check = evening.run_at(now, &["check"]);
    assert_eq!(check.code, 2, "{}{}", check.stdout, check.stderr);
    assert!(check.stdout.contains("eveningPastTheCalendar"), "{}", check.stdout);
    assert!(!check.stdout.contains("badRoutine"), "{}", check.stdout);
    let plan = evening.run_at(now, &["plan"]);
    assert_eq!(plan.code, 0, "fork 4748911's planner plans it: {}{}", plan.stdout, plan.stderr);

    let night = tree(Some("- sleep  win:22:00-08:00 dur:8h  every:day"));
    let check = night.run_at(now, &["check"]);
    assert_eq!(check.code, 2, "{}{}", check.stdout, check.stderr);
    assert!(check.stdout.contains("badCandidate 0 due"), "{}", check.stdout);
    assert!(!check.stdout.contains("badRoutine"), "{}", check.stdout);
    let plan = night.run_at(now, &["plan"]);
    assert_eq!(plan.code, 1, "the capacity section refuses the night's routine on both binaries: {}", plan.stdout);
    assert!(plan.stderr.contains("badCandidate 0 due"), "{}", plan.stderr);

    let path = plain.plan.join("backlog.md");
    let text = std::fs::read_to_string(&path).expect("backlog.md");
    std::fs::write(&path, format!("{text}- [ ] 2 1h Write it ^w1\n")).expect("a task");
    let start = plain.run_at("9999-12-31T18:30:00-06:00", &["start", "^w1"]);
    assert_ne!(start.code, 0, "a start past the calendar was logged: {}", start.stdout);
    assert!(start.stderr.contains("badAt"), "{}", start.stderr);
}
