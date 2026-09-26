//! **The host's planner codec, through the FFI** — stage 6 W-35, track R
//! (README gap 2720).
//!
//! `tm_core::planwire` is the encoder of the request's `planner` section and
//! the decoder of the kernel's `plan` answer that R3 swaps into the binary. Its
//! own unit tests read hand-built JSON; this file is what makes it more than a
//! reading of JSON someone wrote down: the same bytes a host would send, through
//! `tm_kernel_call`, and the kernel's answer read back whole.
//!
//! * The four fixture days `planner_fixtures.rs` plans are answered, and every
//!   one decodes with its **hash check passing** — the decoded day's own
//!   `DayPlan::hash` is the digest the kernel wrote, so no digested field of any
//!   row was bent on the way back.
//! * A running block crosses as `state.active` and comes back as the fork draws
//!   it: the worked stretch (`open`, "30m so far") and the reservation (`▶`,
//!   "running · 90m left").
//! * §9.1's what-if crosses as `overtime` and comes back as a `PlanDiff`.
//! * The encoder mints no bound: a start after `now`, an unknown break place and
//!   an id one character past `CapWire.maxCandId` are sent as the host holds
//!   them and refused BY THE KERNEL, by name.
//!
//! What it does not do is compare the kernel's day with the fork's — that is
//! the frozen comparand's job (`planner_fixtures.rs`, README gap 2722).

mod planner_common;

#[allow(dead_code)]
#[path = "support/planreq.rs"]
mod planreq;

use chrono::{DateTime, NaiveTime};
use chrono_tz::Tz;
use planner_common::{at, basic_state, date, fixture_path, load, load_with_log, Fixture, BASIC_LOG};
use serde_json::{json, Value};
use tm_core::dayplan::SegKind;
use tm_core::model::Id;
use tm_core::planwire::{self, KernelDay};
use tm_core::priority::{self, Candidate};
use tm_core::store::{ActiveBlock, BreakState, RuntimeState};

/// A fixture tree, its log, the state and the instant it is planned at.
struct Case {
    docs: Vec<(String, String)>,
    log: String,
    fx: Fixture,
    state: RuntimeState,
    now: DateTime<Tz>,
    cands: Vec<Candidate>,
}

impl Case {
    fn new(fixture: &str, log: Option<&str>, state: Option<RuntimeState>, h: u32, m: u32) -> Case {
        let fx = match log {
            Some(l) => load_with_log(fixture, Some(l)),
            None => load(fixture),
        };
        let log = match log {
            Some(l) => l.to_string(),
            None => std::fs::read_to_string(format!("{}/.tm/log.jsonl", fixture_path(fixture))).unwrap_or_default(),
        };
        let state = state.unwrap_or_else(|| fx.state.clone());
        let now = at("2026-09-07", h, m);
        let cands = priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, date("2026-09-07"), now);
        let docs = planreq::docs_of_dir(std::path::Path::new(&fixture_path(fixture)));
        Case { docs, log, fx, state, now, cands }
    }

    fn world(&self) -> planreq::World<'_> {
        planreq::World {
            docs: &self.docs,
            log: &self.log,
            tree: &self.fx.tree,
            cfg: &self.fx.cfg,
            state: &self.state,
            now: self.now,
            cands: &self.cands,
        }
    }

    fn day(&self, overtime: Option<Value>) -> KernelDay {
        planreq::kernel_day(&self.world(), overtime).unwrap_or_else(|e| panic!("{e}")).0
    }

    /// The raw response to this case with its planner section rewritten.
    fn raw(&self, edit: impl FnOnce(&mut Value)) -> Value {
        let (mut req, _) = planreq::request(&self.world(), None);
        edit(&mut req["planner"]);
        planreq::call(&req)
    }
}

fn late_state() -> RuntimeState {
    RuntimeState {
        date: Some(date("2026-09-07")),
        wake: Some(NaiveTime::from_hms_opt(9, 0, 0).expect("time")),
        arrival: Some(NaiveTime::from_hms_opt(10, 30, 0).expect("time")),
        loc: Some("lounge".to_string()),
        ..RuntimeState::default()
    }
}

/// **The four fixture days, answered and read back whole** — the hash check
/// is `planwire::read_plan`'s own, so a day that decodes is a day whose every
/// digested field came back as the kernel digested it.
#[test]
fn the_kernel_answers_the_encoders_request_and_the_decoder_reads_the_day_whole() {
    let cases = [
        ("plan-basic 07:00", Case::new("plan-basic", Some(BASIC_LOG), Some(basic_state()), 7, 0)),
        ("plan-basic 10:30", Case::new("plan-basic", Some(BASIC_LOG), Some(late_state()), 10, 30)),
        ("plan-home-day 09:00", Case::new("plan-home-day", None, None, 9, 0)),
        ("plan-travel-day 07:00", Case::new("plan-travel-day", None, None, 7, 0)),
    ];
    let mut rows = 0;
    let mut routines = 0;
    for (name, c) in &cases {
        let k = c.day(None);
        assert_eq!(k.hash, k.day.hash(), "{name}");
        assert_eq!(k.day.date, date("2026-09-07"), "{name}");
        assert!(!k.day.segments.is_empty(), "{name}: the kernel planned nothing");
        // Every host candidate is in the day's priorities, in the host's order.
        assert_eq!(
            k.day.priorities.iter().map(|(i, _)| i.clone()).collect::<Vec<Id>>(),
            c.cands.iter().map(|c| c.id.clone()).collect::<Vec<Id>>(),
            "{name}"
        );
        rows += k.day.segments.len();
        routines += k.day.segments.iter().filter(|s| s.kind == SegKind::Routine).count();
        // The routines the encoder collected crossed and were placed: every
        // mandatory instance the host sent has a row.
        let sent = planwire::routine_instances(&c.cands, &c.fx.tree, c.now, date("2026-09-07"), c.fx.cfg.tz);
        for r in sent.iter().filter(|r| r.mandatory) {
            assert!(
                k.day.segments.iter().any(|s| s.item.as_ref() == Some(&r.id)),
                "{name}: the mandatory `{}` the encoder sent has no row",
                r.id.as_str()
            );
        }
    }
    // Not vacuous: four whole days, with their routines.
    assert!(rows >= 60 && routines >= 20, "{rows} rows, {routines} routine rows");
    // The travel day's two notes came back as the fork's sentences.
    let travel = cases[3].1.day(None);
    assert!(
        travel.day.segments.iter().any(|s| s.flags.note.as_deref() == Some("travel day")),
        "the flight carries `travel day`"
    );
    assert!(
        travel.day.segments.iter().any(|s| s.flags.note.as_deref().is_some_and(|n| n.starts_with("buffer before "))),
        "the buffer carries its wall's title"
    );
    assert_eq!(
        travel.day.diagnostics.notes,
        vec!["travel day: no blocks planned (`travel-day` wall today)".to_string()]
    );
}

/// The `start` a running block leaves in the log (`ev: start`), at 09:30.
const START_M4: &str = r#"{"t":"2026-09-07T09:30:00-05:00","ev":"start","id":"m4","pred":4,"rep":4,"hsw":3.42,"slept_min":490,"loc":"lounge","blocks_done":0,"since_break_min":0}"#;

fn running_case() -> Case {
    let log = format!("{BASIC_LOG}{START_M4}\n");
    let state = RuntimeState {
        active: Some(ActiveBlock {
            id: Id::new("m4"),
            started: NaiveTime::from_hms_opt(9, 30, 0).expect("time"),
            est_min: 120,
            paused: false,
        }),
        ..basic_state()
    };
    Case::new("plan-basic", Some(&log), Some(state), 10, 0)
}

/// **A running block crosses as `state.active`** and comes back the way the
/// fork draws it (`planner_dynamics.rs`' `the_active_block_keeps_the_slot_containing_now`
/// is the same day on the fork): the stretch already worked, open and noted
/// "30m so far", and the block it is in, reserved and current, "running · 90m
/// left".
#[test]
fn a_running_block_crosses_and_comes_back_as_its_two_rows() {
    let c = running_case();
    let k = c.day(None);
    let current = k.day.current_segment().expect("a block is running");
    assert_eq!(current.item.as_ref().map(Id::as_str), Some("m4"));
    assert_eq!((current.start, current.end), (at("2026-09-07", 10, 0), at("2026-09-07", 10, 30)));
    assert_eq!(current.flags.planned_min, Some(90));
    assert_eq!(current.flags.note.as_deref(), Some("running · 90m left"));
    let open: Vec<_> = k.day.segments.iter().filter(|s| s.flags.open).collect();
    assert_eq!(open.len(), 1, "one open stretch");
    assert_eq!((open[0].start, open[0].end), (at("2026-09-07", 9, 30), at("2026-09-07", 10, 0)));
    assert_eq!(open[0].flags.note.as_deref(), Some("30m so far"));
}

/// **§9.1's what-if crosses as `overtime`** and comes back as a `PlanDiff`.
/// With D58's `grown` key the request is still answered: the kernel's reader
/// does not know the key yet (README gap 2873), so it is carried and read by
/// nothing — which is why this asserts acceptance and not an answer.
#[test]
fn the_what_if_crosses_and_comes_back_as_a_diff() {
    let c = running_case();
    let m4 = Id::new("m4");
    let k = c.day(Some(planwire::overtime_json(&m4, 1, None)));
    let d = k.overtime.expect("the what-if was answered");
    // A dropped item is one the base day had assigned.
    let assigned = k.day.assigned();
    assert!(d.removed.iter().all(|i| assigned.contains(i)), "{d:?}");

    let cand = c.cands.iter().find(|x| x.id == m4).expect("m4 is a candidate");
    let grown = planwire::grown(cand, None, c.fx.cfg.block_min(), &c.fx.cfg).expect("an extension grows");
    assert_eq!(grown.remaining_min, cand.remaining_min + 60);
    let with = c.day(Some(planwire::overtime_json(&m4, 1, Some(&grown))));
    assert!(with.overtime.is_some(), "the kernel answered the what-if carrying `grown`");
}

/// **The encoder mints no bound** — the kernel refuses, by name, what the host
/// holds and cannot be planned.
#[test]
fn what_the_kernel_cannot_plan_is_refused_by_the_kernel_by_name() {
    let c = Case::new("plan-basic", Some(BASIC_LOG), Some(basic_state()), 7, 0);
    let after_now = planwire::kernel_sec(at("2026-09-07", 7, 5));
    let resp = c.raw(|p| {
        p["state"]["active"] = json!({"id": "m4", "started": after_now, "estMin": 60, "paused": false});
    });
    assert_eq!(planwire::planner_refusal(&resp), Some("badActive wf"), "{resp}");

    // An unknown break place is the kernel's to refuse, and it does.
    let mut state = basic_state();
    state.break_ = Some(BreakState { started: None, planned_min: 20, place: Some("couch".to_string()) });
    let enc = planwire::state_json(&state, date("2026-09-07"), c.fx.cfg.tz);
    let resp = c.raw(|p| p["state"] = enc.clone());
    assert_eq!(planwire::planner_refusal(&resp), Some("badBreak place"), "{resp}");

    // `CapWire.maxCandId` is 1,024: one past it is refused, and at it is not.
    for (len, refused) in [(1025usize, true), (1024, false)] {
        let mut state = basic_state();
        state.active = Some(ActiveBlock {
            id: Id::new("x".repeat(len)),
            started: NaiveTime::from_hms_opt(6, 0, 0).expect("time"),
            est_min: 60,
            paused: false,
        });
        let enc = planwire::state_json(&state, date("2026-09-07"), c.fx.cfg.tz);
        let resp = c.raw(|p| p["state"] = enc.clone());
        let got = planwire::planner_refusal(&resp);
        if refused {
            assert_eq!(got, Some("badActive id"), "{len}: {resp}");
        } else {
            assert_eq!(got, None, "{len}: {resp}");
        }
    }
}
