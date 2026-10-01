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
//!   fork day holds no such row — so the departure is real on this world.
//!
//! # What it does not compare, said out loud
//!
//! P69's step-5 rows, optionals and deferred routines: they move with P46's reservation (the block
//! is in overtime by the log's 100 minutes), P69's boundary, the harness's worked minutes (README
//! gap 3941, track E's this run) and the location's reading (D81) — and fork 4748911 cannot be
//! ASKED with the logged start (its `started` is a bare `HH:MM` on the plan's date), so no
//! comparand day carries P69 by its property. P68's day is compared whole only once D78 lands.

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

/// **A start line against the kernel, by its flag's property.**
fn start_unmet(line: &Value) -> Vec<String> {
    let b = built(line);
    match (line["p68"]["p68"] == true, line["p69"]["p69"] == true) {
        (true, false) => p68_unmet(line, &b, P68_READING),
        (false, true) => p69_unmet(line, &b),
        _ => vec![format!("{}: a start line carries exactly one of P68's and P69's flags", line["name"])],
    }
}

// ---------------------------------------------------------------------------
// Outside every region: what outlives R3
// ---------------------------------------------------------------------------

/// **The kernel departs from every frozen start day by its number, and by its number alone** —
/// README gap 3964: P68's line by [`P68_READING`], P69's by its property, each against fork
/// 4748911's day frozen by value; and every flag a registered number.
#[test]
fn the_kernel_departs_from_every_frozen_start_day_by_its_number_alone() {
    let lines = starts_lines();
    let registered = forkclass::registered_parity();
    let mut unmet = Vec::new();
    for l in &lines {
        for (n, set, _) in forkclass::flag_homes(l) {
            if !set || !registered.contains(&n) {
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
        // The line the bless writes from its own day is the committed line, byte for byte.
        let mut again = start_line(s, &built(l), &ran, &l["shipped"]["day"]);
        if let Some(why) = l.get("d64b") {
            again["d64b"] = why.clone();
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
    // P68's refusal, asked of a world the kernel PLANS (P69's), is refused by name.
    assert!(
        p68_unmet(&p69, &b, P68Reading::Refused).iter().any(|f| f.contains("P68 says the kernel refuses")),
        "a planned world passed as P68's refusal"
    );
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
    }
    println!("tm-oracle plan asked {} time(s)", *oracle.asked.lock().expect("census"));
}

/// **Freeze the start days** — inert without `TM_STARTS_BLESS`, and it asks `TM_ORACLE`. Every
/// [`STARTS`] entry is driven with the shipped binary and written with fork 4748911's day. A line
/// the file holds may not move: its world moving is a re-draw, allowed only with D64(b)'s reason in
/// `TM_STARTS_BLESS_REDRAW` (dated, naming `D64(b)`), which the line then carries as `d64b`; its
/// fork day moving over the same world is the SHIPPED fork's day moving, which no comparand number
/// moves (the owner's D64, clause 2) — refused by name. A held line no entry builds is refused.
/// `TM_STARTS_BLESS_OUT` writes elsewhere, for a dry run.
#[test]
#[ignore]
fn the_frozen_start_days_are_blessed() {
    if std::env::var_os("TM_STARTS_BLESS").is_none() {
        eprintln!("inert: set TM_STARTS_BLESS=1 (with TM_ORACLE) to write {FROZEN_STARTS}");
        return;
    }
    let oracle = the_oracle().expect("TM_STARTS_BLESS asks the fork: set TM_ORACLE");
    let redraw = std::env::var("TM_STARTS_BLESS_REDRAW").ok();
    let held = if starts_path().exists() { starts_lines() } else { Vec::new() };
    let (mut out, mut refused, mut changed, mut added) = (String::new(), Vec::new(), Vec::new(), 0usize);
    for s in &STARTS {
        let (world, ran) = build(s).unwrap_or_else(|e| panic!("{}: {e}", s.name));
        let b = Built::of(world);
        let shipped = shipped_day(&b, &oracle).unwrap_or_else(|e| panic!("{}: {e}", s.name));
        let mut line = start_line(s, &b, &ran, &shipped);
        match held.iter().find(|o| o["name"] == s.name) {
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
            }
        }
        out.push_str(&serde_json::to_string(&line).expect("a line serialises"));
        out.push('\n');
    }
    for o in &held {
        if start_named(o["name"].as_str().unwrap_or_default()).is_none() {
            refused.push(format!("{}: a frozen line no entry builds any more", o["name"]));
        }
    }
    eprintln!("start days: {added} line(s) added, {} changed ({}), {} refused", changed.len(), changed.join("; "), refused.len());
    assert!(refused.is_empty(), "the start re-bless is refused and wrote nothing:\n  {}", refused.join("\n  "));
    let path = std::env::var_os("TM_STARTS_BLESS_OUT").map(std::path::PathBuf::from).unwrap_or_else(starts_path);
    std::fs::write(path, out).expect("the frozen start days are written");
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
    }
}
// END THE FORK PLANNER
