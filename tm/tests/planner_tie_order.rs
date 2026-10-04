//! **Two rows of one start and one end are drawn in fork `emit_segments`' push order** — stage 6
//! W-45 track D, README gap **4623**: the running block's reservation before the Sleep row it ties
//! with, as the KERNEL's day reaches the host through the codec R3 swaps in (`planwire::read_plan`).
//!
//! Found by driving the swapped binary's TUI across midnight: a block left running past bed, planned in
//! the last minutes of the day, is reserved from `now` to midnight — the end of the `block_min` block it
//! is in and of the day — and the Sleep row runs from `max(bed, now)` to the same midnight. Fork 4748911
//! pushes the reservation first and the Sleep row LAST, and its stable `(start, end)` sort keeps them so;
//! the kernel's `Planner.dayRows` put the evening beside the routines, ahead of the reservation, so `tm
//! plan`, `tm now` and the TUI would have shown `23:59 · sleep` above `23:59 ▶` the block after R3, and
//! the day's hash would have moved with them. Re-driving every frozen week grid's steps found the same
//! tie on 8 of their 56 differing planning steps (README gap 4623's census).
//!
//! The world is the shipped binary's own: `plan-basic`, `tm wake`, `tm arrive`, `^p1` done at 22:00 and
//! `^t3` started at 23:30 — the TUI's midnight world (`tui::tests`' `midnight_world`) — read back whole and
//! planned at 23:59:35 through the harness's request (`support/planreq.rs`, the binary's own encoders).
//! It does not name the fork planner, so it outlives R3.

mod cli_common;

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[path = "support/planreq.rs"]
#[allow(dead_code)]
mod planreq;

use chrono::DateTime;
use cli_common::Tm;
use tm_core::dayplan::SegKind;
use tm_core::energy::Model;
use tm_core::priority;
use tm_core::store::{MemStore, Store};
use tm_core::tree::Tree;

/// The instant planned: 25 seconds before midnight, a block running since 23:30.
const NOW: &str = "2026-09-07T23:59:35-05:00";

/// The TUI's midnight world, built by the shipped binary's verbs.
fn world() -> Tm {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]);
    tm.ok_at("2026-09-07T22:00:00-05:00", &["done", "^p1"]);
    tm.ok_at("2026-09-07T23:30:00-05:00", &["start", "^t3", "--energy", "3"]);
    tm
}

#[test]
fn the_reservation_of_a_block_running_to_midnight_precedes_its_sleep_row() {
    let tm = world();
    let store = MemStore::from_dir(&tm.plan).expect("the tree reads");
    let plan = store.read_tree().expect("the tree parses");
    let cfg = plan.config.clone();
    let tree = Tree::build(&plan.files, &cfg);
    let log = std::fs::read_to_string(tm.plan.join(".tm/log.jsonl")).expect("the log");
    let replay = chokepoint::replay_of_text(&log, cfg.tz);
    let state = store.load_state().expect("state.json parses");
    let docs = planreq::docs_of_dir(&tm.plan);
    let now = DateTime::parse_from_rfc3339(NOW).expect("an instant").with_timezone(&cfg.tz);
    let cands = priority::collect_candidates(&tree, &replay, &cfg, &Model::default(), now.date_naive(), now);
    let w = planreq::World { docs: &docs, log: &log, tree: &tree, cfg: &cfg, state: &state, now, cands: &cands, replay: &replay };
    let (k, _) = planreq::kernel_day(&w, None).unwrap_or_else(|e| panic!("the kernel plans the world: {e}"));
    let segs = &k.day.segments;
    let reserved = segs
        .iter()
        .position(|s| s.kind == SegKind::Block && s.flags.current && s.item.as_ref().is_some_and(|i| i.as_str() == "t3"))
        .unwrap_or_else(|| panic!("`^t3` is reserved: {segs:#?}"));
    let sleep = segs.iter().position(|s| s.kind == SegKind::Sleep).unwrap_or_else(|| panic!("a Sleep row: {segs:#?}"));
    // The tie is real (AGENTS §5.2): both rows run from `now` to midnight.
    assert_eq!(
        (segs[reserved].start, segs[reserved].end),
        (segs[sleep].start, segs[sleep].end),
        "the reservation and the Sleep row tie on start and end"
    );
    assert_eq!(segs[sleep].start, now, "both from `now`");
    assert!(
        reserved < sleep,
        "the reservation is drawn before the Sleep row it ties with, as fork `emit_segments` pushes them: {segs:#?}"
    );
    // ...and that is the day the binary plans on this world (the fork's until R3, the kernel's after).
    let shipped = tm.json_at(NOW, &["plan"]);
    let kinds: Vec<(&str, Option<&str>)> = shipped["segments"]
        .as_array()
        .expect("segments")
        .iter()
        .filter(|s| s["start"] == "23:59")
        .map(|s| (s["kind"].as_str().unwrap_or_default(), s["item"].as_str()))
        .collect();
    assert_eq!(kinds, [("block", Some("t3")), ("sleep", Some("sleep"))], "`tm plan --json` at 23:59: {shipped}");
}
