//! **P68's and P69's worlds: the shipped fork's day frozen by value, flagged by its number** —
//! stage 6 W-41 track H (README gap 3964, gap 3912 restated).
//!
//! Two parity numbers are about a running record's START, and until W-41 neither had a frozen
//! comparand: `planner_request_keys.rs`' P68 test read fork 4748911's `09:55–11:00` row off the
//! SHIPPED BINARY live — which after R3 plans with the kernel, so that half would read the kernel
//! — and its P69 test read no fork day at all. After R3 both divergences would have been held by
//! their register rows alone.
//!
//! # What is frozen
//!
//! `tests/fixtures/fork-4748911-planner-starts.jsonl`, one line per [`STARTS`] entry: the world
//! AS THE SHIPPED BINARY WROTE IT — `plan-basic` (`cli_common::Tm::new`'s tree), the entry's verbs
//! each at its own instant, the last a `tm plan` at the instant planned, read back with
//! `support/forkgrid.rs`' reader — the verbs with their exit codes, and **fork 4748911's day on it
//! by value** (`shipped`), taken from `tm-oracle plan` over the grants the shipped binary ranks by
//! (`forkplan::capacity_grants`: the capacity request alone, `kernel_capacity::rank`'s), each line
//! carrying its number's flag in its own home (`p68: {"p68": true}`, `p69: {"p69": true}`).
//!
//! **Both worlds hold no location** (no `tm arrive` runs), so they are days the owner's D81 rules
//! on: before `tm arrive` the day is planned on the home curve, location `any`, and day 0's
//! capacity follows that one reading (README gap 3861; track E builds it this run as parity `P76`).
//! The frozen day is ranked by THAT reading, measured to matter: on both worlds the grants sent
//! `any` are not the grants sent the lounge, and the fork's day carries them (its `priorities`;
//! its rows did not move on either world). Track H pre-computed it with an override while track
//! E was being built; since W-41's land step the binary's encoder sends `any` itself (P76), the
//! override is gone (README gap 4086), and the kernel here is asked as the binary asks.
//!
//! # What each line is held to, outside every region (outlives R3)
//!
//! * **P68** — a running block whose logged start is after `now` (`tm start ^m1` at 10:00, `tm plan`
//!   at 09:55: a `--now` before the stored start, or a synced machine's clock ahead). Fork 4748911
//!   plans the block from `now` — `active_run`'s `.max(0)`, nothing worked — its row ending at
//!   `started + block_min`, and the frozen day says so by value. The kernel's answer is read by
//!   [`P68_READING`]: until W-41's land step the W-40 repair's P68, a refusal by name (`badActive
//!   wf`); since it composed track K, the owner's D78 — the kernel plans it from `now` as fork
//!   4748911 plans it, and `P68Reading::AsTheFork` holds the kernel's whole day to the frozen one by
//!   the class lines' day comparison ([`p68s_two_readings_are_told_apart`] refuses the other).
//! * **P69** — a block begun before local midnight (`tm start ^t4` Monday 23:00, `tm plan` Tuesday
//!   00:40, whose housekeeping rolls `.tm/state.json`'s date). Fork 4748911 put the cache's `23:00`
//!   on the plan's date — TONIGHT, after `now`. The kernel is held to P69's property: the request
//!   sends the instant of the block's own `start` line, the kernel plans the frozen day's date,
//!   window, budget and fixed frame (walls, wind-down, sleep) by value, its running row is the
//!   block's from `now` to the first block boundary of the LOGGED start after `now`, and the frozen
//!   fork day holds no such row — so the departure is real on this world. **And since the owner's
//!   D89 (W-42 track C, README gaps 4133 and 4282) the line also carries the COMPARAND** — fork
//!   4748911 asked with a start on the plan's date at one of the logged start's boundaries
//!   (`forkplan::p69_state`: `00:00`, whose first boundary after `00:40` is the logged start's
//!   `01:00`), P46's reservation composed (the block is in overtime by the log's 100 minutes) — and
//!   the kernel's whole day and what-if are held to it by the class lines' comparison: all
//!   seventeen rows, the fourteen after the running one among them.
//!
//! # What it does not compare, said out loud
//!
//! Until D89, P69's step-5 rows, optionals and deferred routines — fork 4748911 could not be ASKED
//! with the logged start (its `started` is a bare `HH:MM` on the plan's date), so no comparand day
//! carried P69, and a bent row after the running one passed (the W-41 verifier's `work` and `swap`,
//! README gap 4133). Now: a world P69's transformation cannot reach — a logged start with seconds,
//! no boundary of it on the plan's date at or before `now` — would be held by the property alone,
//! and no frozen world is one (`forkplan::p69_state`'s header).

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[allow(dead_code)]
#[path = "support/planreq.rs"]
mod planreq;

#[allow(dead_code)]
#[path = "support/forkday.rs"]
mod forkday;

#[allow(dead_code)]
#[path = "support/forkclass.rs"]
mod forkclass;

#[allow(dead_code)]
#[path = "support/plangen.rs"]
mod plangen;

#[allow(dead_code)]
#[path = "support/forkplan.rs"]
mod forkplan;

#[allow(dead_code)]
#[path = "support/forkgrid.rs"]
mod forkgrid;

/// The committed history a bless holds its lines against (README gap 4151).
#[allow(dead_code)]
#[path = "support/frozenhist.rs"]
mod frozenhist;

use std::collections::BTreeSet;

use chrono::{DateTime, Duration};
use chrono_tz::Tz;
use serde_json::{json, Value};

use tm_core::planwire::{self, KernelDay};

use forkclass::{Built, ClassWorld};

fn tz() -> Tz {
    tm_core::config::Config::default().tz
}

// ---------------------------------------------------------------------------
// The worlds
// ---------------------------------------------------------------------------

/// **One world whose running record's start is the departure**: the verbs the shipped binary runs
/// over `plan-basic`, each at its instant (the last a `tm plan` at [`Start::now`]), and the parity
/// number its line is flagged by.
struct Start {
    name: &'static str,
    flag: u32,
    verbs: &'static [(&'static str, &'static [&'static str])],
    now: &'static str,
}

/// **The two worlds** — the verbs of `planner_request_keys.rs`' P68 and P69 tests
/// (`a_running_block_started_after_now_is_refused_by_name_where_the_fork_plans_it`, its
/// `midnight_world`), each ending in the `tm plan` those tests run.
const STARTS: [Start; 2] = [
    Start {
        name: "p68 a block started after now",
        flag: 68,
        verbs: &[
            ("2026-09-07T10:00:00-05:00", &["start", "^m1", "--energy", "4"]),
            ("2026-09-07T09:55:00-05:00", &["plan"]),
        ],
        now: "2026-09-07T09:55:00-05:00",
    },
    Start {
        name: "p69 a block begun before midnight",
        flag: 69,
        verbs: &[
            ("2026-09-07T23:00:00-05:00", &["start", "^t4", "--energy", "4"]),
            ("2026-09-08T00:40:00-05:00", &["plan"]),
        ],
        now: "2026-09-08T00:40:00-05:00",
    },
];

/// An entry's verbs as `forkgrid`'s steps.
fn steps_of(s: &Start) -> Vec<forkgrid::Step> {
    s.verbs.iter().map(|(at, args)| forkgrid::Step::run(at, args)).collect()
}

/// **Run an entry's verbs with the shipped binary over `plan-basic`, and read the world back** —
/// its documents, its log and `.tm/state.json`, planned at [`Start::now`] — with the verbs and the
/// exit code each gave.
fn build(s: &Start) -> Result<(ClassWorld, Vec<forkgrid::Step>), String> {
    let tmp = tempfile::TempDir::new().map_err(|e| e.to_string())?;
    let dir = tmp.path().join("plan");
    let ran = forkgrid::run_steps(&dir, &steps_of(s));
    let g = forkgrid::GridWorld::read(&dir);
    let state = serde_json::from_str(g.file(".tm/state.json").ok_or("no .tm/state.json")?).map_err(|e| format!(".tm/state.json: {e}"))?;
    let now = DateTime::parse_from_rfc3339(s.now).map_err(|e| format!("{}: {e}", s.now))?.with_timezone(&tz());
    Ok((ClassWorld { docs: g.docs(), log: g.log().to_string(), state, now, mult: None, ratio: None }, ran))
}

/// **A start line**: the entry's name, its flag in its own home, the verbs with their exit codes,
/// the instant, the world's class, the world, and fork 4748911's day on it with its digest.
fn start_line(s: &Start, b: &Built, ran: &[forkgrid::Step], shipped: &Value) -> Value {
    let flag = format!("p{}", s.flag);
    let mut line = json!({
        "name": s.name,
        "steps": ran.iter().map(forkgrid::Step::to_json).collect::<Vec<_>>(),
        "now": s.now,
        "class": forkclass::class_of(b).key(),
        "world": b.world.to_json(),
        "shipped": forkplan::frozen_day_json(shipped),
    });
    line[flag.as_str()] = json!({flag.as_str(): true});
    line
}

// ---------------------------------------------------------------------------
// The frozen file
// ---------------------------------------------------------------------------

/// The frozen start days.
const FROZEN_STARTS: &str = "fork-4748911-planner-starts.jsonl";

/// Where they live.
fn starts_path() -> std::path::PathBuf {
    forkday::frozen_path().with_file_name(FROZEN_STARTS)
}

/// The frozen start lines, in file order.
fn starts_lines() -> Vec<Value> {
    starts_lines_of(&std::fs::read_to_string(starts_path()).unwrap_or_else(|e| panic!("{}: {e}", starts_path().display())))
}

/// [`starts_lines`] over a file's text; a name carried twice FAILS.
fn starts_lines_of(text: &str) -> Vec<Value> {
    let mut seen = BTreeSet::new();
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Value = serde_json::from_str(l).expect("a frozen start line is JSON");
            let name = v["name"].as_str().expect("a frozen start line names its world").to_string();
            assert!(seen.insert(name.clone()), "two frozen start lines for {name}");
            v
        })
        .collect()
}

/// The entry a line names.
fn start_named(name: &str) -> Option<&'static Start> {
    STARTS.iter().find(|s| s.name == name)
}

/// A line's world, rebuilt.
fn built(line: &Value) -> Built {
    Built::of(ClassWorld::of_json(&line["world"], tz()).unwrap_or_else(|e| panic!("{}: {e}", line["name"])))
}

/// **The kernel's answer on a world, asked as R3's host asks it under D81** — the request of
/// `forkclass::kernel_answer_with_grants`, whose location is the encoder's own (P76).
fn kernel_of(b: &Built) -> Result<KernelDay, String> {
    let (req, order) = forkplan::request_with_loc(b, None);
    planreq::kernel_day_of(&planreq::call(&req), &b.request_world(), &order).map(|(k, _)| k)
}

/// **The shipped fork's day on a world, over `fp`**: fork 4748911's own drawing, its candidates
/// ranked by the shipped binary's grants under D81, no departure applied.
fn shipped_day(b: &Built, fp: &dyn forkplan::ForkPlan) -> Result<Value, String> {
    let prios = forkplan::capacity_grants(b, None)?;
    let ask = forkplan::ForkAsk { state: &b.world.state, now: b.world.now, d60: false, p64: false, prios: &prios, extend: None, log_line: None };
    Ok(fp.plan(b, &ask)?.fork_day)
}

/// A serialised row's start and end.
fn span(row: &Value) -> (Option<DateTime<chrono::FixedOffset>>, Option<DateTime<chrono::FixedOffset>>) {
    (forkplan::at(&row["start"]), forkplan::at(&row["end"]))
}

/// The rows of a serialised day.
fn rows(day: &Value) -> &[Value] {
    day["segments"].as_array().map(Vec::as_slice).unwrap_or_default()
}

// ---------------------------------------------------------------------------
// P68 and P69, each by its property
// ---------------------------------------------------------------------------

/// **P68's two readings of a start after `now`.**
#[derive(Clone, Copy, Debug, PartialEq)]
enum P68Reading {
    /// The W-40 repair's P68: the kernel REFUSES the request by name, `badActive wf`.
    Refused,
    /// The owner's D78 (track K, this run): the kernel plans the block from `now` with no minutes
    /// worked, as fork 4748911 plans it — its whole day the frozen fork day's, by the class lines'
    /// day comparison (`forkday::compare_day_with_fork`).
    AsTheFork,
}

/// **The reading this tree holds the kernel to.** `P68Reading::AsTheFork` since W-41's land step
/// composed track K's D78 (README gap 4084): the kernel plans the frozen world's day, the
/// fork's, and [`p68s_two_readings_are_told_apart`] refuses the W-40 repair's refusal on it.
const P68_READING: P68Reading = P68Reading::AsTheFork;

/// **P68 on a line, by its property**: the frozen fork day plans the running block from `now` to
/// `started + block_min` (`active_run` with nothing worked: `current_block_end`'s first block),
/// noting the whole estimate left; and the kernel answers by `reading`. Empty when it holds.
fn p68_unmet(line: &Value, b: &Built, reading: P68Reading) -> Vec<String> {
    let who = line["name"].as_str().unwrap_or("?");
    let mut out = Vec::new();
    let Some(a) = b.world.state.active.as_ref() else { return vec![format!("{who}: no running block")] };
    let started = tm_core::capacity::local_dt(b.cfg.tz, b.date(), a.started);
    if started <= b.world.now {
        out.push(format!("{who}: the stored start {started} is not after now {}", b.world.now));
    }
    let fork = &line["shipped"]["day"];
    let row = rows(fork).iter().find(|r| r["kind"] == "block" && r["item"] == a.id.as_str() && r["flags"]["current"] == true);
    let want_end = started + Duration::minutes(i64::from(b.cfg.block_min()));
    let want_note = format!("running · {}m left", a.est_min);
    match row {
        Some(r) if span(r) == (Some(b.world.now.fixed_offset()), Some(want_end.fixed_offset())) && r["flags"]["note"] == want_note.as_str() => {}
        other => out.push(format!(
            "{who}: fork 4748911's day does not plan the block from now to started + block_min ({} – {want_end}, `{want_note}`): {other:?}",
            b.world.now
        )),
    }
    match (reading, kernel_of(b)) {
        (P68Reading::Refused, Err(e)) if e.ends_with("badActive wf") => {}
        (P68Reading::Refused, other) => out.push(format!("{who}: P68 says the kernel refuses `badActive wf`, and it answered {:?}", other.map(|k| k.hash))),
        (P68Reading::AsTheFork, Ok(k)) => {
            let mut t = forkday::DayTally::default();
            out.extend(forkday::compare_day_with_fork(who, &k, &line["shipped"], b.world.now, &mut t));
        }
        (P68Reading::AsTheFork, Err(e)) => out.push(format!("{who}: D78 plans the block from now, and the kernel did not plan the world: {e}")),
    }
    out
}

/// **P69 on a line, by its property** (see the module's header): the request half, and
/// `forkplan::p69_day_unmet` over the kernel's day against the frozen fork day. Empty when it holds.
fn p69_unmet(line: &Value, b: &Built) -> Vec<String> {
    let who = line["name"].as_str().unwrap_or("?");
    let tz = b.cfg.tz;
    let now = b.world.now;
    let Some(a) = b.world.state.active.as_ref() else { return vec![format!("{who}: no running block")] };
    // The request half: the log's own `start` instant, where the cache's clock on the plan's date
    // is tonight's.
    let Some(logged) = forkplan::logged_start(b) else {
        return vec![format!("{who}: the log holds no open block for the cache's {}", a.id.as_str())];
    };
    let cache = tm_core::capacity::local_dt(tz, b.date(), a.started);
    let mut out = Vec::new();
    if !(logged < now && now < cache) {
        out.push(format!("{who}: P69's world has its logged start {logged} before now {now} and the cache's clock {cache} after it"));
    }
    let (req, _) = forkplan::request_with_loc(b, None);
    if req["planner"]["state"]["active"]["started"] != json!(planwire::kernel_sec(logged)) {
        out.push(format!("{who}: the request sends the start {}, not the log's {logged}", req["planner"]["state"]["active"]["started"]));
    }
    match kernel_of(b) {
        Ok(k) => out.extend(forkplan::p69_day_unmet(who, &line["shipped"]["day"], b, logged, &k)),
        Err(e) => out.push(format!("{who}: the kernel did not plan the world: {e}")),
    }
    out
}

/// **A start line against the kernel, by its flag's property — and, where the line carries the
/// comparand, by the comparand whole** (the owner's D89, README gap 4133): P69's transformation
/// (`forkplan::p69_state`) reaches a world exactly when the line carries the comparand's answers,
/// and those are held to the kernel's day and what-if by the frozen lines' one comparison
/// (`forkclass::compare_line`) — every row, so P69's fourteen rows after the running one are
/// compared by value after R3, not by the property alone.
fn start_unmet(line: &Value) -> Vec<String> {
    let b = built(line);
    let who = line["name"].as_str().unwrap_or("?");
    let mut out = match (line["p68"]["p68"] == true, line["p69"]["p69"] == true) {
        (true, false) => p68_unmet(line, &b, P68_READING),
        (false, true) => p69_unmet(line, &b),
        _ => vec![format!("{who}: a start line carries exactly one of P68's and P69's flags")],
    };
    match (forkplan::p69_state(&b, &b.world.state).is_some(), line["day"].is_null()) {
        (true, true) => out.push(format!("{who}: P69's transformation reaches this world and the line carries no comparand (D89)")),
        (false, false) => out.push(format!("{who}: the line carries a comparand on a world P69's transformation does not reach")),
        (true, false) => out.extend(forkclass::compare_line(line, &mut forkclass::ClassTally::default())),
        (false, true) => {}
    }
    out
}

// ---------------------------------------------------------------------------
// Outside every region: what outlives R3
// ---------------------------------------------------------------------------

/// **The kernel departs from every frozen start day by its number, and by its number alone** —
/// README gap 3964: P68's line by [`P68_READING`], P69's by its property, each against fork
/// 4748911's day frozen by value — and since the owner's D89 P69's by its comparand whole as well;
/// every flag a registered number, and the line's own number's flag SET. (Until D89 every flag a
/// start line carried was its own number's; the comparand carries the class lines' flags beside
/// it, `d57` and `d60`, each set where its rule departs and `false` where it was asked and does
/// not — W-42 track C, README gap 4282.)
#[test]
fn the_kernel_departs_from_every_frozen_start_day_by_its_number_alone() {
    let lines = starts_lines();
    let registered = forkclass::registered_parity();
    let mut unmet = Vec::new();
    for l in &lines {
        let own = start_named(l["name"].as_str().unwrap_or_default()).map(|s| s.flag);
        for (n, set, _) in forkclass::flag_homes(l) {
            if !registered.contains(&n) || (Some(n) == own && !set) {
                unmet.push(format!("{}: the flag P{n} is {set} and registered {}", l["name"], registered.contains(&n)));
            }
        }
        unmet.extend(start_unmet(l));
    }
    println!("frozen start days: {} line(s) compared, P68 read as {P68_READING:?}; {} unmet", lines.len(), unmet.len());
    assert!(unmet.is_empty(), "{}", unmet.join("\n  "));
    assert_eq!(lines.len(), STARTS.len(), "every start world is frozen");
}

/// **Every frozen start world is the shipped binary's own output** (AGENTS §5.4): the file holds a
/// line for every [`STARTS`] entry and no other, in order, each world byte for byte what the
/// binary writes when its verbs are run again over `plan-basic`, every verb's exit code the one
/// recorded, and its class the world's own.
#[test]
fn every_frozen_start_world_is_the_binarys_own_output() {
    let lines = starts_lines();
    let names: Vec<&str> = lines.iter().map(|l| l["name"].as_str().unwrap_or_default()).collect();
    assert_eq!(names, STARTS.iter().map(|s| s.name).collect::<Vec<_>>(), "the frozen start lines are STARTS, in order");
    let mut bad = Vec::new();
    for l in &lines {
        let s = start_named(l["name"].as_str().unwrap_or_default()).expect("named above");
        let (world, ran) = build(s).unwrap_or_else(|e| panic!("{}: {e}", s.name));
        if world.to_json() != l["world"] {
            bad.push(format!("{}: the verbs write another world now ({})", s.name, forkplan::first_difference("world", &l["world"], &world.to_json()).unwrap_or_default()));
        }
        let steps: Vec<Value> = ran.iter().map(forkgrid::Step::to_json).collect();
        if Value::Array(steps.clone()) != l["steps"] {
            bad.push(format!("{}: the verbs ran {steps:?}, the line records {}", s.name, l["steps"]));
        }
        if forkclass::class_of(&built(l)).key() != l["class"] {
            bad.push(format!("{}: the world classifies as `{}`, the line says {}", s.name, forkclass::class_of(&built(l)).key(), l["class"]));
        }
        // The line the bless writes from its own day is the committed line, byte for byte — its
        // comparand's answers, where it carries them, taken from the line (the bless asks them of
        // the oracle, `add_comparand`; the oracle arm below asks them again).
        let mut again = start_line(s, &built(l), &ran, &l["shipped"]["day"]);
        if let Some(why) = l.get("d64b") {
            again["d64b"] = why.clone();
        }
        if !l["day"].is_null() {
            for key in forkclass::ANSWERS.iter().filter(|k| **k != "shipped") {
                forkclass::set_answer(&mut again, key, l[*key].clone());
            }
        }
        if again != *l {
            bad.push(format!("{}: the bless would write another line ({})", s.name, forkplan::first_difference("line", l, &again).unwrap_or_default()));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n  "));
}

/// **Every frozen start world is one the shipped binary holds** (the owner's D64(b),
/// `forkclass::binary_holds`): the cache is what the binary rebuilds from the log, and the world is
/// at rest — so the day frozen is the day the binary plans on it.
#[test]
fn the_frozen_start_worlds_are_held_by_the_binary() {
    for l in starts_lines() {
        if let Err(e) = forkclass::binary_holds(&built(&l)) {
            panic!("{}: not a world the binary holds: {}", l["name"], e.join("; "));
        }
    }
}

/// **P68's two readings are told apart on this tree** (AGENTS §5.8, neither reading inert): the
/// reading the tree holds ([`P68_READING`]) holds on the frozen P68 line and the other does not —
/// so when track K's D78 makes the kernel plan the block from `now`, this fails by name and the
/// land step sets the reading, and until then `P68Reading::AsTheFork` cannot pass on a kernel that refuses.
#[test]
fn p68s_two_readings_are_told_apart() {
    let line = starts_lines().into_iter().find(|l| l["p68"]["p68"] == true).expect("the P68 line");
    let b = built(&line);
    let held = p68_unmet(&line, &b, P68_READING);
    assert!(held.is_empty(), "P68 read as {P68_READING:?} does not hold — if track K's D78 has landed, set P68_READING: {held:?}");
    let other = if P68_READING == P68Reading::Refused { P68Reading::AsTheFork } else { P68Reading::Refused };
    let unheld = p68_unmet(&line, &b, other);
    assert!(!unheld.is_empty(), "P68 read as {other:?} holds too — the two readings are not told apart");
    println!("P68 as {other:?}: {unheld:?}");
}

/// **Each start comparison bites a bent line** (AGENTS §5.8): P68's frozen row a minute longer,
/// P69's frozen date moved, P69's frozen day given the kernel's own running row, and a line
/// carrying both flags — each refused by name.
#[test]
fn the_start_comparisons_bite_a_bent_line() {
    let lines = starts_lines();
    let p68 = lines.iter().find(|l| l["p68"]["p68"] == true).expect("the P68 line").clone();
    let p69 = lines.iter().find(|l| l["p69"]["p69"] == true).expect("the P69 line").clone();
    assert!(start_unmet(&p68).is_empty() && start_unmet(&p69).is_empty(), "the unbent lines hold");
    let mut longer = p68.clone();
    let segs = longer["shipped"]["day"]["segments"].as_array_mut().expect("rows");
    let r = segs.iter_mut().find(|r| r["flags"]["current"] == true).expect("the running row");
    r["end"] = json!("2026-09-07T11:01:00-05:00");
    assert!(start_unmet(&longer).iter().any(|f| f.contains("started + block_min")), "a bent P68 row passed");
    let mut moved = p69.clone();
    moved["shipped"]["day"]["date"] = json!("2026-09-07");
    assert!(start_unmet(&moved).iter().any(|f| f.contains("date: kernel")), "a moved P69 date passed");
    let b = built(&p69);
    let k = kernel_of(&b).expect("the kernel plans P69's world");
    let mut agreeing = p69.clone();
    agreeing["shipped"]["day"]["segments"] = serde_json::to_value(&k.day).expect("a day")["segments"].clone();
    assert!(start_unmet(&agreeing).iter().any(|f| f.contains("departs nowhere")), "a P69 line whose fork day holds the kernel's row passed");
    let mut both = p69.clone();
    both["p68"] = json!({"p68": true});
    assert!(start_unmet(&both).iter().any(|f| f.contains("exactly one")), "a line carrying both flags passed");
    // The fork's fixed frame moved (its sleep a minute later) — refused.
    let mut late = p69.clone();
    let sleep = late["shipped"]["day"]["segments"].as_array_mut().expect("rows").iter_mut().find(|r| r["kind"] == "sleep").expect("a sleep row");
    sleep["start"] = json!("2026-09-08T22:01:00-05:00");
    assert!(start_unmet(&late).iter().any(|f| f.contains("the fixed frame")), "a moved frame passed");
    // The kernel's own running row a minute long, and its grants another day's — each refused.
    let logged = forkplan::logged_start(&b).expect("the logged start");
    let fork = &p69["shipped"]["day"];
    let who = p69["name"].as_str().unwrap_or("?");
    assert!(forkplan::p69_day_unmet(who, fork, &b, logged, &k).is_empty(), "the kernel's own day holds");
    let mut bent = k.clone();
    let r = bent.day.segments.iter_mut().find(|r| r.flags.current).expect("the running row");
    r.end += Duration::minutes(1);
    assert!(forkplan::p69_day_unmet(who, fork, &b, logged, &bent).iter().any(|f| f.contains("the logged start's boundary")), "a bent running row passed");
    let mut reranked = k.clone();
    if let Some(p) = reranked.day.priorities.iter_mut().next() {
        p.1.p = p.1.p.wrapping_add(1);
    }
    assert!(forkplan::p69_day_unmet(who, fork, &b, logged, &reranked).iter().any(|f| f.contains("priorities: kernel")), "another ranking passed");
    // — and since the owner's D89, P69's comparand WHOLE (README gap 4133): a step-5 row a minute
    // longer (`work`) and two step-5 rows' items swapped (`swap`) in the frozen comparand — the
    // W-41 verifier's two bends, which P69's property alone let through — refused by name.
    let step5 = |r: &Value| r["kind"] == "block" && r["flags"]["current"] != true;
    let mut work = p69.clone();
    let rows = work["day"]["day"]["segments"].as_array_mut().expect("P69's comparand rows (D89)");
    let r = rows.iter_mut().find(|r| step5(r)).expect("a step-5 row on P69's day");
    r["end"] = json!((forkplan::at(&r["end"]).expect("an end") + Duration::minutes(1)).to_rfc3339());
    assert!(start_unmet(&work).iter().any(|f| f.starts_with(who) && f.contains("the rows differ at")), "a step-5 row bent a minute passed: {:?}", start_unmet(&work));
    let mut swap = p69.clone();
    let rows = swap["day"]["day"]["segments"].as_array_mut().expect("P69's comparand rows (D89)");
    let i = rows.iter().position(|r| step5(r)).expect("a step-5 row");
    let j = rows.iter().position(|r| step5(r) && r["item"] != rows[i]["item"]).expect("a second step-5 item");
    let (a, z) = (rows[i]["item"].clone(), rows[j]["item"].clone());
    rows[i]["item"] = z;
    rows[j]["item"] = a;
    assert!(start_unmet(&swap).iter().any(|f| f.starts_with(who) && f.contains("the rows differ at")), "two step-5 rows swapped passed: {:?}", start_unmet(&swap));
    // A line that drops its comparand on a world P69's transformation reaches is refused too.
    let mut bare = p69.clone();
    for key in forkclass::ANSWERS.iter().filter(|k| **k != "shipped" && **k != "p69") {
        bare.as_object_mut().expect("a line").remove(*key);
    }
    assert!(start_unmet(&bare).iter().any(|f| f.contains("carries no comparand (D89)")), "a P69 line without its comparand passed");
    // P68's refusal, asked of a world the kernel PLANS (P69's), is refused by name.
    assert!(
        p68_unmet(&p69, &b, P68Reading::Refused).iter().any(|f| f.contains("P68 says the kernel refuses")),
        "a planned world passed as P68's refusal"
    );
}

/// **The start lines' gate admits D89's comparand and nothing else** (W-42 track C, README gap 4282;
/// AGENTS §5.8): the frozen P69 line with its comparand stripped GAINS it under D70 when P69 — the
/// number whose flag it carries — is named, and is refused with no number, with a number it carries
/// no flag of, or when anything it already carries moves beside the gain; a line with a comparand is
/// then held to `forkclass::d64_allows`; and a line with none that gains none may change nothing.
#[test]
fn the_start_gate_admits_d89s_comparand_and_nothing_else() {
    let registered = forkclass::registered_parity();
    let p69 = starts_lines().into_iter().find(|l| l["p69"]["p69"] == true).expect("the P69 line");
    assert!(!p69["day"].is_null(), "the P69 line carries its comparand (D89)");
    let shipped = p69["shipped"]["day"].clone();
    let mut bare = p69.clone();
    for key in forkclass::ANSWERS.iter().filter(|k| **k != "shipped" && **k != "p69") {
        bare.as_object_mut().expect("a line").remove(*key);
    }
    let gained = starts_gate(&bare, &p69, &shipped, &[69], None, &registered).expect("D89's introduction was refused");
    assert_eq!(gained, vec!["d57", "d60", "day", "whatif"]);
    assert!(starts_gate(&bare, &p69, &shipped, &[], None, &registered).is_err_and(|e| e.contains("names no registered number")));
    assert!(starts_gate(&bare, &p69, &shipped, &[68], None, &registered).is_err(), "P68, whose flag the line does not carry, introduced P69's comparand");
    let mut moved_now = p69.clone();
    moved_now["now"] = json!("2026-09-08T00:41:00-05:00");
    assert!(starts_gate(&bare, &moved_now, &shipped, &[69], None, &registered).is_err_and(|e| e.contains("`now` moved")), "a gain that moved the line passed");
    let mut bent = p69.clone();
    bent["day"]["hash"] = json!("bent");
    assert!(starts_gate(&p69, &bent, &shipped, &[], None, &registered).is_err(), "a comparand bent with no reason passed");
    assert_eq!(starts_gate(&p69, &bent, &shipped, &[69], None, &registered), Ok(vec!["day".to_string()]), "P69 may move its own comparand's day (D64(a))");
    let p68 = starts_lines().into_iter().find(|l| l["p68"]["p68"] == true).expect("the P68 line");
    let mut p68_moved = p68.clone();
    p68_moved["class"] = json!("idle/elsewhere");
    assert!(starts_gate(&p68, &p68_moved, &p68["shipped"]["day"], &[68], None, &registered).is_err_and(|e| e.contains("no comparand")));
    assert_eq!(starts_gate(&p68, &p68, &p68["shipped"]["day"], &[], None, &registered), Ok(Vec::new()));
}

/// **A bless's reasons are read strictly** (AGENTS §5.8, `forkclass::because_of` and
/// `forkclass::is_d64b_reason`): a token that is not a parity number is refused rather than
/// skipped, and a re-draw's reason is dated and names D64(b).
#[test]
fn a_bless_reason_is_read_strictly() {
    assert!(forkclass::is_d64b_reason("2026-10-01 D64(b): the TUI's constructor changed"));
    assert!(!forkclass::is_d64b_reason("D64(b): undated"));
    assert!(!forkclass::is_d64b_reason("2026-10-01 because"));
    assert_eq!(forkclass::because_of("TM_W41_H_BECAUSE_UNSET_PROBE"), Vec::<u32>::new());
    std::env::set_var("TM_W41_H_BECAUSE_PROBE", "P45, P67");
    assert_eq!(forkclass::because_of("TM_W41_H_BECAUSE_PROBE"), vec![45, 67]);
    std::env::set_var("TM_W41_H_BECAUSE_BAD_PROBE", "P45,sixty-seven");
    let bad = std::panic::catch_unwind(|| forkclass::because_of("TM_W41_H_BECAUSE_BAD_PROBE"));
    assert!(bad.is_err(), "a reason that is not a parity number was skipped");
}

/// **A frozen start name carried twice is refused** (AGENTS §5.8).
#[test]
#[should_panic(expected = "two frozen start lines for")]
fn a_frozen_start_name_carried_twice_is_refused() {
    let one = serde_json::to_string(&starts_lines()[0]).expect("a line");
    starts_lines_of(&format!("{one}\n{one}\n"));
}

/// **D81's location on these worlds is the request's own** (README gaps 3861 and 4086): on both
/// worlds the stored state holds no location, and since W-41's land step composed track E's
/// `P76` the binary's encoder sends the planner's reading of such a day, `any`, itself — so
/// the override `forkplan::d81_loc` that pre-computed it while track E was being built is
/// deleted, and the frozen day (ranked by `any`) is the day this request plans.
#[test]
fn d81s_location_is_the_requests_own() {
    for l in starts_lines() {
        let b = built(&l);
        assert_eq!(b.world.state.loc, None, "{}: a day no `tm arrive` located", l["name"]);
        let own = forkplan::request_with_loc(&b, None).0;
        assert_eq!(own["capacity"]["state"]["loc"], "any", "{}: the request sends D81's `any` itself (P76)", l["name"]);
    }
}

/// The oracle at `TM_ORACLE`, when set (D23's shape).
fn the_oracle() -> Option<forkplan::Oracle> {
    forkplan::oracle_path().map(forkplan::Oracle::new)
}

/// **The frozen start days are fork 4748911's answer today, out of the tree** (`TM_ORACLE`;
/// outlives R3): each line's `shipped` day, asked again of `tm-oracle plan` over the shipped
/// binary's grants under D81, by value.
#[test]
#[ignore]
fn the_frozen_start_days_are_the_forks_oracle_answer_today() {
    let Some(oracle) = the_oracle() else { return };
    for l in starts_lines() {
        let b = built(&l);
        let day = shipped_day(&b, &oracle).unwrap_or_else(|e| panic!("{}: {e}", l["name"]));
        assert_eq!(day, l["shipped"]["day"], "{}: the fork oracle does not plan the frozen day ({:?})", l["name"], forkplan::first_difference("day", &l["shipped"]["day"], &day));
        comparand_is_the_frozen_one(&l, &b, &oracle);
    }
    println!("tm-oracle plan asked {} time(s)", *oracle.asked.lock().expect("census"));
}

/// **A line's comparand is `fp`'s answer today** (the owner's D89): where the line carries the
/// comparand's answers, `forkplan::comparand_answers` over the shipped binary's grants answers
/// every one of them, key for key — so the frozen P69 comparand is fork 4748911's (the oracle
/// arm) and, while it is here, the in-tree fork's.
fn comparand_is_the_frozen_one(l: &Value, b: &Built, fp: &dyn forkplan::ForkPlan) {
    if l["day"].is_null() {
        return;
    }
    let prios = forkplan::capacity_grants(b, None).unwrap_or_else(|e| panic!("{}: {e}", l["name"]));
    let answers = forkplan::comparand_answers(b, &prios, fp).unwrap_or_else(|e| panic!("{}: {e}", l["name"]));
    for key in forkclass::ANSWERS {
        assert_eq!(answers[key], l[key], "{}: `{key}` is not the comparand's ({:?})", l["name"], forkplan::first_difference(key, &l[key], &answers[key]));
    }
}

/// **Freeze the start days** — inert without `TM_STARTS_BLESS`, and it asks `TM_ORACLE`. Every
/// [`STARTS`] entry is driven with the shipped binary and written with fork 4748911's day — and,
/// on a world P69's transformation reaches (`forkplan::p69_state`, the owner's D89), with the
/// comparand's answers over the same grants (`forkplan::comparand_answers`), so P69's day is
/// compared by value after R3. A line the file holds may not move but by the owner's D64: its
/// world moving is a re-draw, allowed only with D64(b)'s reason in `TM_STARTS_BLESS_REDRAW`
/// (dated, naming `D64(b)`), which the line then carries as `d64b`; its fork day moving over the
/// same world is the SHIPPED fork's day moving, which no comparand number moves (D64, clause 2) —
/// refused by name; and its answers moving is [`starts_gate`]'s to allow. A line HEAD holds that no
/// entry builds is refused. `TM_STARTS_BLESS_OUT` writes elsewhere, for a dry run.
///
/// **What a line is held against is the file's COMMITTED history** (W-42 track C, README gap 4151;
/// `frozenhist::held`): its latest version at HEAD or at any first-parent commit since
/// `kernel/ratchet.py`'s base — never the working copy, so deleting the file is not a fresh freeze.
#[test]
#[ignore]
fn the_frozen_start_days_are_blessed() {
    if std::env::var_os("TM_STARTS_BLESS").is_none() {
        eprintln!("inert: set TM_STARTS_BLESS=1 (with TM_ORACLE) to write {FROZEN_STARTS}");
        return;
    }
    let oracle = the_oracle().expect("TM_STARTS_BLESS asks the fork: set TM_ORACLE");
    let redraw = std::env::var("TM_STARTS_BLESS_REDRAW").ok();
    let because = forkclass::because_of("TM_STARTS_BLESS_BECAUSE");
    let harness = forkclass::harness_of("TM_STARTS_BLESS_HARNESS");
    let registered = forkclass::registered_parity();
    let held = frozenhist::held(&starts_path(), frozenhist::key_of("name")).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", held.census(FROZEN_STARTS));
    let (mut out, mut refused, mut changed, mut added) = (String::new(), Vec::new(), Vec::new(), 0usize);
    for s in &STARTS {
        let (world, ran) = build(s).unwrap_or_else(|e| panic!("{}: {e}", s.name));
        let b = Built::of(world);
        let shipped = shipped_day(&b, &oracle).unwrap_or_else(|e| panic!("{}: {e}", s.name));
        let mut line = start_line(s, &b, &ran, &shipped);
        if let Err(e) = add_comparand(&mut line, &b, &oracle) {
            refused.push(format!("{}: {e}", s.name));
        }
        match held.get(s.name) {
            None => added += 1,
            Some(old) if old["world"] != line["world"] || old["steps"] != line["steps"] => match redraw.as_deref() {
                Some(why) if forkclass::is_d64b_reason(why) => {
                    line["d64b"] = json!(why);
                    changed.push(format!("{} re-drawn", s.name));
                }
                _ => refused.push(format!("{}: the verbs write another world now — a re-draw, which needs D64(b)'s reason in TM_STARTS_BLESS_REDRAW", s.name)),
            },
            Some(old) if old["shipped"] != line["shipped"] => refused.push(format!(
                "{}: the SHIPPED fork's day moved over the same world, and no comparand parity number moves it (D64, clause 2)",
                s.name
            )),
            Some(old) => {
                if let Some(why) = old.get("d64b") {
                    line["d64b"] = why.clone();
                }
                match starts_gate(old, &line, &shipped, &because, harness.as_deref(), &registered) {
                    Err(e) => refused.push(e),
                    Ok(keys) if !keys.is_empty() => changed.push(format!("{} `{}`", s.name, keys.join("`, `"))),
                    Ok(_) => {}
                }
            }
        }
        out.push_str(&serde_json::to_string(&line).expect("a line serialises"));
        out.push('\n');
    }
    for name in &held.head {
        if start_named(name).is_none() {
            refused.push(format!("{name}: a frozen line no entry builds any more"));
        }
    }
    eprintln!("start days: {added} line(s) added, {} changed ({}), {} refused", changed.len(), changed.join("; "), refused.len());
    assert!(refused.is_empty(), "the start re-bless is refused and wrote nothing:\n  {}", refused.join("\n  "));
    let path = std::env::var_os("TM_STARTS_BLESS_OUT").map(std::path::PathBuf::from).unwrap_or_else(starts_path);
    std::fs::write(path, out).expect("the frozen start days are written");
}

/// **The comparand's answers on a start line, where P69's transformation reaches its world** (the
/// owner's D89; README gap 4133): `forkplan::comparand_answers` over the grants the shipped binary
/// ranks the fork's candidates by (`forkplan::capacity_grants`, the line's own `shipped` day's), each
/// written as the class lines write theirs. The comparand's `shipped` IS the line's — fork 4748911's
/// day over the same grants — and anything else is refused. A world P69's transformation does not
/// reach (P68's) gains nothing.
fn add_comparand(line: &mut Value, b: &Built, fp: &dyn forkplan::ForkPlan) -> Result<(), String> {
    if forkplan::p69_state(b, &b.world.state).is_none() {
        return Ok(());
    }
    let prios = forkplan::capacity_grants(b, None)?;
    let answers = forkplan::comparand_answers(b, &prios, fp)?;
    if forkclass::bytes(&answers["shipped"]) != forkclass::bytes(&line["shipped"]) {
        return Err(format!(
            "the comparand's shipped day is not the line's ({})",
            forkplan::first_difference("shipped", &line["shipped"], &answers["shipped"]).unwrap_or_default()
        ));
    }
    for key in forkclass::ANSWERS {
        forkclass::set_answer(line, key, answers[key].clone());
    }
    Ok(())
}

/// **What a start line's re-bless may change** (the owner's D64, as the start lines carry it; W-42
/// track C). The caller has held the world and the shipped fork's day by value. What is left:
///
/// * **a line frozen with no comparand GAINS one** — the owner's D89, under D70: every key that
///   moved is a comparand answer (`forkclass::ANSWERS`) the committed line does not carry
///   (adds-only: nothing it carries moves), and the re-bless names a registered number whose flag
///   the committed line carries SET — the number whose comparand did not exist when it was frozen
///   (P69's, since its transformation landed);
/// * **a line with a comparand** is held to `forkclass::d64_allows` — (a), the introduction, and
///   since the owner's D85 a corrected harness reading, (c) — as every class line is;
/// * **a line with none that gains none** may change nothing.
///
/// `Ok` names what changed.
fn starts_gate(
    old: &Value,
    new: &Value,
    shipped: &Value,
    because: &[u32],
    harness: Option<&str>,
    registered: &BTreeSet<u32>,
) -> Result<Vec<String>, String> {
    let who = old["name"].as_str().unwrap_or("?");
    let keys: BTreeSet<&String> = old.as_object().into_iter().flatten().chain(new.as_object().into_iter().flatten()).map(|(k, _)| k).collect();
    let moved: Vec<String> = keys.into_iter().filter(|k| forkclass::bytes(&old[k.as_str()]) != forkclass::bytes(&new[k.as_str()])).cloned().collect();
    if moved.is_empty() {
        return Ok(moved);
    }
    if !old["day"].is_null() {
        return forkclass::d64_allows(old, new, shipped, because, harness, registered);
    }
    if new["day"].is_null() {
        return Err(format!("{who}: `{}` moved on a line with no comparand, which nothing licenses", moved.join("`, `")));
    }
    if let Some(k) = moved.iter().find(|k| old.get(k.as_str()).is_some() || !forkclass::ANSWERS.contains(&k.as_str())) {
        return Err(format!("{who}: `{k}` moved — a line gaining its comparand (D70) may only ADD the comparand's answers"));
    }
    let licensed = forkclass::flag_homes(old).into_iter().any(|(n, set, _)| set && because.contains(&n) && registered.contains(&n));
    if !licensed {
        return Err(format!(
            "{who}: the line gains a comparand and the re-bless names no registered number whose flag the line carries \
             (TM_STARTS_BLESS_BECAUSE; D70)"
        ));
    }
    Ok(moved)
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gap 3964)

/// **The frozen start days are the in-tree fork's answer today** — while the fork is here, the
/// in-tree fork (what the shipped binary plans with until R3) draws each frozen day by value over
/// the same grants, so the frozen days the plain arm reads after R3 are the shipped fork's as well
/// as the oracle's.
#[test]
fn the_frozen_start_days_are_the_in_tree_forks_answer_today() {
    for l in starts_lines() {
        let b = built(&l);
        let day = shipped_day(&b, &forkplan::InTree).unwrap_or_else(|e| panic!("{}: {e}", l["name"]));
        assert_eq!(day, l["shipped"]["day"], "{}: the in-tree fork does not plan the frozen day ({:?})", l["name"], forkplan::first_difference("day", &l["shipped"]["day"], &day));
        comparand_is_the_frozen_one(&l, &b, &forkplan::InTree);
        // The line the bless writes, comparand and all (`add_comparand`, the owner's D89), from the
        // in-tree fork, is the committed line.
        let s = start_named(l["name"].as_str().unwrap_or_default()).expect("a STARTS entry");
        let ran: Vec<forkgrid::Step> = l["steps"].as_array().map(Vec::as_slice).unwrap_or_default().iter().map(|v| forkgrid::Step::of_json(v).expect("a step")).collect();
        let mut again = start_line(s, &b, &ran, &day);
        add_comparand(&mut again, &b, &forkplan::InTree).unwrap_or_else(|e| panic!("{}: {e}", l["name"]));
        if let Some(why) = l.get("d64b") {
            again["d64b"] = why.clone();
        }
        assert_eq!(again, l, "{}: the bless would write another line ({:?})", l["name"], forkplan::first_difference("line", &l, &again));
    }
}

/// **A comparand that is not the fork's is caught** (AGENTS §5.8, the arm above bites): the frozen
/// P69 line with a step-5 row a minute longer is not the in-tree fork's comparand.
#[test]
#[should_panic(expected = "is not the comparand's")]
fn a_comparand_that_is_not_the_forks_is_caught() {
    let mut l = starts_lines().into_iter().find(|l| l["p69"]["p69"] == true).expect("the P69 line");
    let rows = l["day"]["day"]["segments"].as_array_mut().expect("the comparand's rows");
    let r = rows.iter_mut().find(|r| r["kind"] == "block" && r["flags"]["current"] != true).expect("a step-5 row");
    r["end"] = json!((forkplan::at(&r["end"]).expect("an end") + Duration::minutes(1)).to_rfc3339());
    comparand_is_the_frozen_one(&l, &built(&l), &forkplan::InTree);
}
// END THE FORK PLANNER
