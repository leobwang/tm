//! **The binary's planner request and the harness's carry one key set** —
//! stage 6 W-40 track E (README gaps 3720 and 2875).
//!
//! Every suite that asks the kernel for a day — the classes, the seeded batch,
//! the fixtures, the W-37/38/39 rows, the codec — builds its request with
//! `tm/tests/support/planreq.rs`. They prove the kernel plans right **given the
//! harness's request**, and gap 3720 is that they stay green whatever the
//! binary's encoder sends after R3's swap. This file ties the two: on each
//! world it reads **the request the binary sends** and the one the harness
//! builds, and fails by name on any key path one carries and the other does
//! not.
//!
//! # Whose request is "the binary's"
//!
//! The capacity request the shipped `tm plan` sends, **read off the binary
//! itself**: `tm` is a `[[bin]]`, so it is run on a temp copy of a fixture with
//! `TM_TRACE_CAPACITY_REQUEST` set and its stderr line is parsed — the
//! documents with their regions, the zone table from its cache, the log section
//! from its checkpoint, and the capacity section from `planwire::capacity_json`.
//! The binary sends no `planner` section yet (R3 is the body swap, D48), so that
//! section is built the way the swap will build it — `planwire::planner_json`
//! over the same world — and **R3's own additions are applied by name**
//! ([`SWAP`]): today that is `planwire::add_worked_min` (README gap 3043). When
//! the binary starts sending its own `planner` section the captured one is used
//! and nothing is synthesised.
//!
//! The binary's request, so completed, is also **sent to the kernel**, and the
//! kernel must answer it with a planned day: before W-40 the capacity section
//! the binary sends had no `priority.batchMaxMin` (gap 2875), and a `planner`
//! section beside it was refused `badBatchMaxMin` — the swap would have shipped
//! a request no green test had ever sent.
//!
//! # What may differ, and only by name
//!
//! [`NAMED`] lists every difference the worlds below show, each with the side
//! that carries it and the gap that answers it. A differing key path no entry
//! names FAILS, and an entry no world shows FAILS as STALE — the list may only
//! shrink, W-27's shape. Arrays are read element-wise: `docs[].grain` is a key
//! some element of `docs` carries, and an array of scalars is `p[]` whatever its
//! length, so a log of a different length is not a key difference.
//!
//! # What it cannot see
//!
//! Values: a key both requests send with different values is not a finding here
//! (that is what the classes and the batch compare, against the fork). The
//! learned model's tables are seen on one world only ([`model_world`]); a world
//! that sends a section neither request here builds — the `plan` rows, the
//! `emit` walls — is check 13's (`kernel/fields.py`), not this file's.

mod cli_common;
mod planner_common;

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use chrono::DateTime;
use chrono_tz::Tz;
use cli_common::Tm;
use serde_json::Value;
use tm_core::energy::Model;
use tm_core::log::Replay;
use tm_core::planwire;
use tm_core::priority;
use tm_core::store::{MemStore, RuntimeState, Store};
use tm_core::tree::Tree;

use planner_common::planreq;

/// `tm/src/cli/kernel_capacity.rs`'s `TRACE_REQUEST_ENV` and its line's prefix,
/// spelled out rather than imported: `tm` is a binary-only package, so a test
/// cannot name anything inside it (the shape `kernel_call_counts.rs` takes for
/// `TRACE_SCOPE_ENV`). A rename there makes the capture empty, and
/// [`binary_request`] fails on an empty capture by name — never a vacuous pass.
const TRACE_REQUEST_ENV: &str = "TM_TRACE_CAPACITY_REQUEST";
const TRACE_REQUEST_PREFIX: &str = "capacity request: ";

/// Which request carries a difference.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Side {
    /// The binary's request (as the swap will send it).
    Binary,
    /// `support/planreq.rs`'s.
    Harness,
}

/// **One difference the worlds show, named.** `path` is a key path, or a
/// prefix ending in `.` that names every path under it.
struct Named {
    path: &'static str,
    side: Side,
    gap: u32,
    why: &'static str,
}

/// **Every difference allowed, each with the gap that answers it.**
const NAMED: &[Named] = &[
    Named {
        path: "planner.state.active.workedMin",
        side: Side::Binary,
        gap: 3043,
        why: "R3 calls `planwire::add_worked_min` beside `planner_json` ([`SWAP`]); `planreq` \
              does not, so every suite built on it plans a running block from the log's \
              open-block reading — the reading gap 2920 says counts a break inside the block as \
              worked",
    },
    Named {
        path: "log.ckpt.",
        side: Side::Binary,
        gap: 3583,
        why: "the binary's run resumes from its process checkpoint (`kernel_log::\
              capacity_log_section`) and sends the tail since its cut; the harness sends \
              `ckpt: null` and the whole log from line 1. R3 must send a run whose replay holds \
              today's day record whole",
    },
    Named {
        path: "docs[].grain",
        side: Side::Binary,
        gap: 3900,
        why: "the binary declares each regioned document's horizon (`kernel_bridge::doc_json`, \
              `region_of`); `planreq` sends `{path, lines}` and the kernel loads every harness \
              document with no region",
    },
    Named {
        path: "docs[].ix",
        side: Side::Binary,
        gap: 3900,
        why: "the region's index, beside `grain` (the same gap)",
    },
    Named {
        path: "capacity.pLounge.model.",
        side: Side::Binary,
        gap: 3901,
        why: "the learned model's lounge weights: `planreq` plans with `Model::default()`, whose \
              tables are empty",
    },
    Named {
        path: "capacity.arrival.model.",
        side: Side::Binary,
        gap: 3901,
        why: "the learned model's expected arrivals (the same gap)",
    },
    Named {
        path: "capacity.energy.",
        side: Side::Binary,
        gap: 3901,
        why: "the learned energy curves (the same gap)",
    },
    Named {
        path: "capacity.sleep.shiftModel.",
        side: Side::Binary,
        gap: 3901,
        why: "the model's fitted sleep-debt shift (the same gap)",
    },
];

/// **R3's own additions to the `planner` section**, applied to the binary's side
/// only while the binary sends none of its own: `(the key path it adds, the gap
/// that owes it)`. Each is a call R3 must make; [`NAMED`] holds the difference it
/// leaves against the harness.
const SWAP: &[(&str, u32)] = &[("planner.state.active.workedMin", 3043)];

/// Does `entry` name `path`?
fn names(entry: &Named, path: &str, side: Side) -> bool {
    entry.side == side
        && if entry.path.ends_with('.') { path.starts_with(entry.path) } else { path == entry.path }
}

/// **Every key path of a JSON value**: `a.b` for an object member, `a[]` for an
/// array (whatever its length), and an array's element paths unioned.
fn paths(v: &Value) -> BTreeSet<String> {
    fn walk(v: &Value, at: &str, out: &mut BTreeSet<String>) {
        match v {
            Value::Object(m) => {
                for (k, x) in m {
                    let p = if at.is_empty() { k.clone() } else { format!("{at}.{k}") };
                    out.insert(p.clone());
                    walk(x, &p, out);
                }
            }
            Value::Array(xs) => {
                let p = format!("{at}[]");
                out.insert(p.clone());
                for x in xs {
                    walk(x, &p, out);
                }
            }
            _ => {}
        }
    }
    let mut out = BTreeSet::new();
    walk(v, "", &mut out);
    out
}

/// **The request the binary sent**, off its stderr: the ranked capacity request
/// (the one carrying `capacity.candidates`), as text — its `log` section is in
/// build order and a `serde_json::Value` would sort it.
fn binary_request(stderr: &str, world: &str) -> String {
    let sent: Vec<&str> = stderr.lines().filter_map(|l| l.strip_prefix(TRACE_REQUEST_PREFIX)).collect();
    assert!(
        !sent.is_empty(),
        "{world}: the binary printed no `{TRACE_REQUEST_PREFIX}` line under {TRACE_REQUEST_ENV} — \
         the trace is dead (renamed in kernel_capacity.rs?), so nothing below would compare"
    );
    sent.iter()
        .rev()
        .find(|t| {
            serde_json::from_str::<Value>(t)
                .map(|v| v["capacity"].get("candidates").is_some())
                .unwrap_or(false)
        })
        .unwrap_or_else(|| panic!("{world}: no ranked capacity request among {} sent", sent.len()))
        .to_string()
}

/// One world, driven: the plan directory after the binary's verbs, the instant
/// it was planned at, and the binary's request.
struct World {
    name: &'static str,
    dir: std::path::PathBuf,
    now: &'static str,
    request: String,
    _tm: Tm,
}

/// Run `verbs` (each at its own instant), then `tm plan` at `now` with the trace
/// on, and keep the request it sent.
fn drive(name: &'static str, tm: Tm, verbs: &[(&str, &[&str])], now: &'static str) -> World {
    for (at, args) in verbs {
        tm.ok_at(at, args);
    }
    let out = tm.run_env_at(now, &[(TRACE_REQUEST_ENV, "1")], &["plan"]);
    assert_eq!(out.code, 0, "{name}: `tm plan` failed:\n{}{}", out.stdout, out.stderr);
    let request = binary_request(&out.stderr, name);
    World { name, dir: tm.plan.clone(), now, request, _tm: tm }
}

/// A fixture tree other than `plan-basic`, copied into a temp directory.
fn fixture(name: &str) -> Tm {
    let tm = Tm::empty();
    copy_dir(Path::new(&planner_common::fixture_path(name)), &tm.plan);
    tm
}

fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).expect("create dir");
    for entry in std::fs::read_dir(from).expect("read fixture") {
        let entry = entry.expect("dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            std::fs::copy(entry.path(), &target).expect("copy file");
        }
    }
}

/// `plan-basic` with the fixture model (`tm-core/tests/fixtures/model.json`)
/// as its `.tm/model.json`: the one world whose capacity section carries the
/// learned tables.
fn model_world() -> Tm {
    let tm = Tm::new();
    std::fs::create_dir_all(tm.plan.join(".tm")).expect(".tm");
    std::fs::copy(planner_common::fixture_path("model.json"), tm.plan.join(".tm/model.json")).expect("model");
    tm
}

/// **The worlds**: a fresh tree, a running block, a running break, a learned
/// model, and the two fixture days that carry their own state and log.
fn worlds() -> Vec<World> {
    vec![
        drive("plan-basic", Tm::new(), &[], cli_common::NOW),
        drive(
            "plan-basic, ^t4 running",
            Tm::new(),
            &[("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"])],
            "2026-09-07T09:40:00-05:00",
        ),
        drive(
            "plan-basic, a break running",
            Tm::new(),
            &[("2026-09-07T09:00:00-05:00", &["break", "20m", "--where", "walk"])],
            "2026-09-07T09:10:00-05:00",
        ),
        // README gap 2874: a block whose stored start is after `now` (a `--now` before it, or a
        // synced machine's clock ahead of this one) -- the fork plans it as nothing worked yet.
        drive(
            "plan-basic, ^t4 started after now",
            Tm::new(),
            &[("2026-09-07T10:00:00-05:00", &["start", "^t4", "--energy", "4"])],
            "2026-09-07T09:55:00-05:00",
        ),
        drive("plan-basic with a learned model", model_world(), &[], cli_common::NOW),
        drive("plan-home-day", fixture("plan-home-day"), &[], "2026-09-07T10:00:00-05:00"),
        drive("plan-travel-day", fixture("plan-travel-day"), &[], "2026-09-07T10:00:00-05:00"),
    ]
}

/// The world's files, read as `planner_common` reads a fixture.
struct Read {
    tree: Tree,
    cfg: tm_core::config::Config,
    replay: Replay,
    state: RuntimeState,
    docs: Vec<(String, String)>,
    log: String,
    now: DateTime<Tz>,
}

fn read(w: &World) -> Read {
    let store = MemStore::from_dir(&w.dir).expect("the tree reads");
    let plan = store.read_tree().expect("the tree parses");
    let tree = Tree::build(&plan.files, &plan.config);
    let log = std::fs::read_to_string(w.dir.join(".tm/log.jsonl")).unwrap_or_default();
    let replay = planner_common::chokepoint::replay_of_text(&log, plan.config.tz);
    let state = store.load_state().expect("state.json parses");
    let docs = planreq::docs_of_dir(&w.dir);
    let now = DateTime::parse_from_rfc3339(w.now).expect("an instant").with_timezone(&plan.config.tz);
    Read { tree, cfg: plan.config, replay, state, docs, log, now }
}

/// **The harness's request** on the world: `planreq::request`, the builder every
/// planning suite calls, over the candidates `planner_common::Fixture` collects.
fn harness_request(r: &Read) -> Value {
    let date = planwire::plan_date(&r.state, r.now);
    let cands = priority::collect_candidates(&r.tree, &r.replay, &r.cfg, &Model::default(), date, r.now);
    let w = planreq::World {
        docs: &r.docs,
        log: &r.log,
        tree: &r.tree,
        cfg: &r.cfg,
        state: &r.state,
        now: r.now,
        cands: &cands,
    };
    planreq::request(&w, None).0
}

/// **The `planner` section the swap will send** beside the binary's capacity
/// request: `planwire::planner_json` over the world (the encoder R3 calls), with
/// [`SWAP`]'s additions — the running block's worked minutes as
/// `Replay::active_worked_min` reads them, the reading `day::worked_min` is.
fn swap_planner(r: &Read) -> Value {
    let today = r.now.date_naive();
    let tz = r.cfg.tz;
    let cands = priority::collect_candidates(&r.tree, &r.replay, &r.cfg, &Model::default(), today, r.now);
    let date = planwire::plan_date(&r.state, r.now);
    let routines = planwire::routine_instances(&cands, &r.tree, r.now, date, tz);
    let mut planner = planwire::planner_json(&r.state, r.now, tz, &routines, None);
    for (path, _gap) in SWAP {
        match *path {
            "planner.state.active.workedMin" => {
                if let Some(a) = &r.state.active {
                    let started = tm_core::capacity::local_dt(tz, date, a.started).fixed_offset();
                    let worked = r.replay.active_worked_min(date, started, r.now.fixed_offset(), None);
                    planwire::add_worked_min(&mut planner, worked);
                }
            }
            other => panic!("SWAP names `{other}`, which this file does not know how to add"),
        }
    }
    planner
}

/// The binary's request text with its `planner` section, spliced as text so the
/// log section keeps its build order (`kernel_capacity::request`'s own rule).
fn with_planner(request: &str, planner: &Value) -> String {
    let body = request.trim_end();
    assert!(body.ends_with('}'), "a request is an object");
    format!("{},\"planner\":{}}}", &body[..body.len() - 1], planner)
}

/// **Gap 3720.** On every world the binary's planner request and the harness's
/// differ only where [`NAMED`] says, and every entry of [`NAMED`] is shown by
/// some world.
#[test]
fn the_binarys_planner_request_and_the_harnesss_differ_only_by_name() {
    let mut seen: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    let mut unnamed = Vec::new();
    for w in worlds() {
        let r = read(&w);
        let mut binary: Value = serde_json::from_str(&w.request).expect("the binary's request is JSON");
        if binary.get("planner").is_none() {
            binary["planner"] = swap_planner(&r);
        }
        let harness = harness_request(&r);
        let (b, h) = (paths(&binary), paths(&harness));
        for (side, path) in b.difference(&h).map(|p| (Side::Binary, p)).chain(h.difference(&b).map(|p| (Side::Harness, p))) {
            match NAMED.iter().position(|e| names(e, path, side)) {
                Some(i) => seen.entry(i).or_default().push(format!("{}: {path}", w.name)),
                None => unnamed.push(format!("{}: `{path}` is sent by the {side:?} request only", w.name)),
            }
        }
    }
    assert!(
        unnamed.is_empty(),
        "UNNAMED differences between the binary's planner request and the harness's (README gap 3720) \
         — make the two send the same keys, or name the difference in NAMED with its gap:\n  {}",
        unnamed.join("\n  ")
    );
    for (i, e) in NAMED.iter().enumerate() {
        let shown = seen.get(&i).map_or(0, Vec::len);
        eprintln!("named {:?}-only `{}` (gap {}): {shown} key path(s) over the worlds", e.side, e.path, e.gap);
    }
    let stale: Vec<String> = NAMED
        .iter()
        .enumerate()
        .filter(|(i, _)| !seen.contains_key(i))
        .map(|(_, e)| format!("`{}` ({:?}, gap {}): {}", e.path, e.side, e.gap, e.why))
        .collect();
    assert!(
        stale.is_empty(),
        "STALE: no world shows these named differences any more — delete them (the list only \
         shrinks), or say which world stopped reaching them:\n  {}",
        stale.join("\n  ")
    );
}

/// **Gap 2875, at the kernel.** The binary's capacity request, with the `planner`
/// section the swap adds, is a request the kernel PLANS, on every world, and the
/// day it answers is one the host's codec reads (`planwire::read_capacity_answer`,
/// `planwire::read_plan` over the binary's own candidates) — so
/// `priority.batchMaxMin` reaches the reader that refuses a planner section
/// without it (`PlanWire.readBatchMaxMin`), and the swap's request is not one
/// only the harness has ever sent.
#[test]
fn the_binarys_request_with_the_swaps_planner_section_is_planned() {
    for w in worlds() {
        let r = read(&w);
        let sent: Value = serde_json::from_str(&w.request).expect("JSON");
        assert!(
            sent["capacity"]["priority"]["batchMaxMin"].is_u64(),
            "{}: the binary's capacity section carries §16's batch_max_min (README gap 2875): {}",
            w.name,
            sent["capacity"]["priority"]
        );
        let req = with_planner(&w.request, &swap_planner(&r));
        let raw = tm_kernel_ffi::call(&req).expect("the kernel call returns");
        let resp: Value = serde_json::from_str(&raw).expect("the response is JSON");
        assert!(
            planwire::planner_refusal(&resp).is_none() && resp["ok"]["plan"]["day"].is_string(),
            "{}: the kernel did not plan the binary's request with the swap's planner section: {}",
            w.name,
            &raw[..raw.len().min(400)]
        );
        // The binary's own candidates (`Ctx::priorities`: its model, `now`'s date), in the order
        // its request sent them, and the day read back by the decoder R3 swaps in.
        let model: Model = std::fs::read_to_string(w.dir.join(".tm/model.json"))
            .ok()
            .map(|t| serde_json::from_str(&t).expect("the model parses"))
            .unwrap_or_default();
        let cands = priority::collect_candidates(&r.tree, &r.replay, &r.cfg, &model, r.now.date_naive(), r.now);
        let order = planwire::send_order(&cands);
        let ans = planwire::read_capacity_answer(&resp, &order, true)
            .unwrap_or_else(|e| panic!("{}: the grants do not read back: {e}", w.name));
        let ctx = planwire::DayCtx { tz: r.cfg.tz, cands: &cands, prios: &ans.prios };
        let day = planwire::read_plan(&resp["ok"]["plan"], &ctx)
            .unwrap_or_else(|e| panic!("{}: the kernel's day does not read back: {e}", w.name));
        assert!(!day.day.segments.is_empty(), "{}: a day with no rows", w.name);
    }
}

/// **What R3's request is REFUSED on, today, on worlds the binary's own verbs build**
/// (README gaps 3902 and 3903, the remainder of gap 2874). The shipped `tm plan` — the
/// fork until R3 — plans each; the swap's request, as the codec builds it, is refused by
/// name. This pins the refusals so R3 cannot swap past them unseen: when the kernel's
/// bound or the verb's validation changes, this test fails and is rewritten to the new
/// answer, with its behaviour row.
///
/// * `tm start` then `tm extend 24h`: the running block's estimate passes the day
///   (`Look.maxDayMin`), and `Planner.ActiveBlock.wf` refuses it — `badActive wf`.
///   The fork's width is `u32` (gap 3902).
/// * `tm break 25h`: a break planned past the day — `Planner.BreakState.wf` bounds
///   `plannedMin` by the same `Look.maxDayMin` — `badBreak wf` (gap 3902; gap 2874
///   listed four inputs and this is a fifth).
/// * `tm break 20m --where hammock`: the verb stores any word, and `PlanWire.placeOf?`
///   knows four — `badBreak place` (gap 3903).
#[test]
fn the_swaps_request_is_refused_on_three_worlds_the_binary_builds() {
    let cases: [(World, &str); 3] = [
        (
            drive(
                "plan-basic, ^t4 extended past a day",
                Tm::new(),
                &[
                    ("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]),
                    ("2026-09-07T09:10:00-05:00", &["extend", "24h"]),
                ],
                "2026-09-07T09:20:00-05:00",
            ),
            "badActive wf",
        ),
        (
            drive(
                "plan-basic, a break of 25h",
                Tm::new(),
                &[("2026-09-07T09:00:00-05:00", &["break", "25h"])],
                "2026-09-07T09:05:00-05:00",
            ),
            "badBreak wf",
        ),
        (
            drive(
                "plan-basic, a break --where hammock",
                Tm::new(),
                &[("2026-09-07T09:00:00-05:00", &["break", "20m", "--where", "hammock"])],
                "2026-09-07T09:05:00-05:00",
            ),
            "badBreak place",
        ),
    ];
    for (w, want) in cases {
        let r = read(&w);
        let req = with_planner(&w.request, &swap_planner(&r));
        let raw = tm_kernel_ffi::call(&req).expect("the kernel call returns");
        let resp: Value = serde_json::from_str(&raw).expect("the response is JSON");
        assert_eq!(
            planwire::planner_refusal(&resp),
            Some(want),
            "{}: R3's request on this world (README gaps 3902-3903): {}",
            w.name,
            &raw[..raw.len().min(300)]
        );
    }
}

/// **The clamp's residue, both sides of it, on one world** (README gaps 2874 and 3905).
/// `tm start ^m1` at 10:00 (a six-block item) and `tm plan` at 09:55 — a `--now` before
/// the stored start, which is what a synced machine's clock ahead of this one leaves.
/// The codec sends the start as `now` (`planwire::state_json`), so the kernel PLANS the
/// day where it refused the raw start (`badActive wf`): the running row starts at
/// `now`, as the fork's does. It ENDS at `now + block_min` (10:55), where fork
/// `current_block_end` ends it at `started + block_min` (11:00) — the residue the Land
/// step numbers. The fork's half is read off the shipped binary, which plans with
/// `planner::plan` until R3: at the swap that half fails, and is rewritten with the
/// divergence's parity number rather than re-blessed.
#[test]
fn a_running_block_started_after_now_is_planned_from_now_and_its_row_ends_a_block_later() {
    let w = drive(
        "plan-basic, ^m1 started after now",
        Tm::new(),
        &[("2026-09-07T10:00:00-05:00", &["start", "^m1", "--energy", "4"])],
        "2026-09-07T09:55:00-05:00",
    );
    let r = read(&w);
    let req = with_planner(&w.request, &swap_planner(&r));
    let raw = tm_kernel_ffi::call(&req).expect("the kernel call returns");
    let resp: Value = serde_json::from_str(&raw).expect("the response is JSON");
    assert!(planwire::planner_refusal(&resp).is_none(), "the clamped start is planned: {}", &raw[..raw.len().min(300)]);
    let model = Model::default();
    let cands = priority::collect_candidates(&r.tree, &r.replay, &r.cfg, &model, r.now.date_naive(), r.now);
    let order = planwire::send_order(&cands);
    let ans = planwire::read_capacity_answer(&resp, &order, true).expect("the grants read back");
    let ctx = planwire::DayCtx { tz: r.cfg.tz, cands: &cands, prios: &ans.prios };
    let day = planwire::read_plan(&resp["ok"]["plan"], &ctx).expect("the day reads back");
    let running = day.day.segments.iter().find(|s| s.flags.current).expect("a running row");
    let hm = |t: chrono::DateTime<Tz>| t.format("%H:%M").to_string();
    assert_eq!(running.item.as_ref().map(|i| i.as_str()), Some("m1"));
    assert_eq!((hm(running.start), hm(running.end)), ("09:55".to_string(), "10:55".to_string()), "the kernel's row");
    // The fork's, today: the shipped binary.
    let fork = w._tm.json_at(w.now, &["plan"]);
    let row = fork["segments"].as_array().expect("segments").iter()
        .find(|s| s["item"] == "m1" && s["kind"] == "block").expect("the fork's running row");
    assert_eq!((row["start"].as_str(), row["end"].as_str()), (Some("09:55"), Some("11:00")), "the fork's row: {row}");
}
