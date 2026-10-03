//! **P85's planner half, frozen out of the tree** — the W-43 repair (README gap 4367).
//!
//! The owner's D92 (parity P85, W-43 track K): a block's clock that starts — at a `start`, or an
//! `unpause` — inside the span of the last `break` the replay stepped starts at that break's end, so
//! the planner draws the running block from the break's end and reads its worked minutes net of the
//! overlap. Track K held the replay's half to fork 4748911 asked the D92 day (`p85::as_asked_log`,
//! T5's arms) and the planner's half to written values only (`PlannerWit` section 32, and
//! `cli_break_into_block.rs`' `tm plan` row): **no frozen planner world held such a log**, so after
//! R3 nothing would have compared the planner's rows on it with the fork (README gap 4367).
//!
//! # What is frozen
//!
//! `tests/fixtures/fork-4748911-planner-p85.jsonl`, one line per [`WORLDS`] entry, each the world
//! AS THE SHIPPED BINARY WROTE IT — `plan-basic`, the entry's verbs each at its own instant, a
//! `--now` that moves back across a break the binary has just logged being how the binary writes a
//! clock start inside a logged break (gap 4361's mechanism, which D92's own shape needs: `tm start`
//! ends a RUNNING break first), the last a `tm plan` at the instant planned — and **two fork days by
//! value**, both asked of a freshly built `tm-oracle plan` over the grants the shipped binary ranks
//! by (`forkplan::capacity_grants`, D53):
//!
//! * `shipped` — fork 4748911's day on the world as given, which credits and draws the block across
//!   the break's tail (what the departure departs FROM);
//! * `p85` — fork 4748911 **asked the D92 day** (`forkplan::p85_after`): each start P85 moves followed
//!   by a `pause` of its block where the clock started and an `unpause` at the break's end, which
//!   fork 4748911's own machine nets as the kernel's `Replay.restartAt` does, the `paused` row over
//!   that stretch taken off (the break's own row draws it) and the day re-digested. Introduced on a
//!   new file of new worlds, each flagged `{"p85": true}` in its own home — the owner's D70 shape: a
//!   comparand GAINED for a registered number, never a shipped day changed.
//!
//! # What each line is held to, outside every region (outlives R3)
//!
//! * [`the_kernel_plans_every_frozen_p85_day_as_the_fork_asked_the_d92_day`] — the kernel's day,
//!   asked as R3's host asks it, against the frozen `p85` day by the class lines' comparator
//!   (`forkday::compare_day_with_fork`: every row in order, the date, the window, the budget, the
//!   diagnostics, the priorities, the hash).
//! * [`the_departure_is_real_on_every_frozen_p85_world`] — the shipped day is not the `p85` day: the
//!   fork's own drawing starts the block where the log's line does.
//! * [`every_frozen_p85_world_is_the_binarys`] — each world rebuilt now by running its verbs over the
//!   fixture and compared by value, and one the shipped binary holds.
//!
//! The bless and the oracle arm ask fork 4748911 out of the tree; the in-tree fork is asked only in
//! the one region below, which R3 deletes.

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
use std::path::PathBuf;

use chrono::DateTime;
use chrono_tz::Tz;
use serde_json::{json, Value};

use tm_core::planwire::KernelDay;

use forkclass::{Built, ClassWorld};

fn tz() -> Tz {
    tm_core::config::Config::default().tz
}

/// **One world whose running block's clock starts inside a logged break.**
struct World {
    name: &'static str,
    verbs: &'static [(&'static str, &'static [&'static str])],
    now: &'static str,
}

/// **The two worlds** — one per kind of clock start P85 moves.
const WORLDS: [World; 2] = [
    // A twenty-five-minute break 09:00-09:25, logged when it ended; `tm start ^t4` at `--now` 09:10,
    // fifteen minutes back inside it; `tm plan` at 10:00. The kernel's clock starts at 09:25.
    World {
        name: "p85 a start inside a logged break",
        verbs: &[
            ("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]),
            ("2026-09-07T09:00:00-05:00", &["break", "25m"]),
            ("2026-09-07T09:25:00-05:00", &["break"]),
            ("2026-09-07T09:10:00-05:00", &["start", "^t4", "--energy", "4"]),
            ("2026-09-07T10:00:00-05:00", &["plan"]),
        ],
        now: "2026-09-07T10:00:00-05:00",
    },
    // `^t4` from 08:30, paused at 08:50; a break 09:00-09:25 taken while it was paused; `tm pause`
    // (which resumes it) at `--now` 09:10, back inside the break; `tm plan` at 10:00. The kernel's
    // clock restarts at 09:25.
    World {
        name: "p85 an unpause inside a logged break",
        verbs: &[
            ("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]),
            ("2026-09-07T08:30:00-05:00", &["start", "^t4", "--energy", "4"]),
            ("2026-09-07T08:50:00-05:00", &["pause"]),
            ("2026-09-07T09:00:00-05:00", &["break", "25m"]),
            ("2026-09-07T09:25:00-05:00", &["break"]),
            ("2026-09-07T09:10:00-05:00", &["pause"]),
            ("2026-09-07T10:00:00-05:00", &["plan"]),
        ],
        now: "2026-09-07T10:00:00-05:00",
    },
];

/// The frozen file's name, under `tm/tests/fixtures`.
const FROZEN_P85: &str = "fork-4748911-planner-p85.jsonl";

fn frozen_path() -> PathBuf {
    frozenhist::fixtures_dir().join(FROZEN_P85)
}

fn steps_of(w: &World) -> Vec<forkgrid::Step> {
    w.verbs.iter().map(|(at, args)| forkgrid::Step::run(at, args)).collect()
}

/// **Run a world's verbs with the shipped binary over `plan-basic`, and read the world back** — its
/// documents, its log and `.tm/state.json`, planned at [`World::now`] — with the verbs and the exit
/// code each gave.
fn build(w: &World) -> Result<(ClassWorld, Vec<forkgrid::Step>), String> {
    let tmp = tempfile::TempDir::new().map_err(|e| e.to_string())?;
    let dir = tmp.path().join("plan");
    let ran = forkgrid::run_steps(&dir, &steps_of(w));
    let g = forkgrid::GridWorld::read(&dir);
    let state = serde_json::from_str(g.file(".tm/state.json").ok_or("no .tm/state.json")?).map_err(|e| format!(".tm/state.json: {e}"))?;
    let now = DateTime::parse_from_rfc3339(w.now).map_err(|e| format!("{}: {e}", w.now))?.with_timezone(&tz());
    Ok((ClassWorld { docs: g.docs(), log: g.log().to_string(), state, now, mult: None, ratio: None }, ran))
}

/// The frozen lines in file order; a name carried twice FAILS.
fn lines_of(text: &str) -> Vec<Value> {
    let mut names = BTreeSet::new();
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Value = serde_json::from_str(l).expect("a frozen P85 line is JSON");
            let name = v["name"].as_str().expect("a frozen P85 line names its world").to_string();
            assert!(names.insert(name.clone()), "two frozen P85 lines for `{name}`");
            v
        })
        .collect()
}

fn frozen() -> Vec<Value> {
    let path = frozen_path();
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e} — bless it (`the_frozen_p85_days_are_blessed`)", path.display()));
    lines_of(&text)
}

/// A frozen line's world, rebuilt into what both planners read.
fn built(line: &Value) -> Built {
    Built::of(ClassWorld::of_json(&line["world"], tz()).expect("a stored world"))
}

/// **The kernel's day on a world, asked as R3's host asks it** (`forkplan::request_with_loc`).
fn kernel_of(b: &Built) -> Result<KernelDay, String> {
    let (req, order) = forkplan::request_with_loc(b, None);
    planreq::kernel_day_of(&planreq::call(&req), &b.request_world(), &order).map(|(k, _)| k)
}

/// **The fork's two days on a world, over `fp`**: the shipped day (fork 4748911's own drawing of the
/// world as given, `{hash, day}`) and the D92 day (`forkplan::p85_after`), both over the grants the
/// shipped binary ranks by (D53).
fn fork_days(b: &Built, fp: &dyn forkplan::ForkPlan) -> Result<(Value, Value), String> {
    let prios = forkplan::capacity_grants(b, None)?;
    let ask = forkplan::ForkAsk { state: &b.world.state, now: b.world.now, d60: false, p64: false, prios: &prios, extend: None, log_line: None };
    let shipped = forkplan::frozen_day_json(&fp.plan(b, &ask)?.fork_day);
    let p85 = forkplan::p85_after(b, &prios, fp, true)?.ok_or("P85 moves no clock start on this world")?;
    Ok((shipped, p85))
}

/// One frozen line: the world's name, its verbs with their exit codes, the instant, the world, and
/// the two fork days.
fn line_of(w: &World, ran: &[forkgrid::Step], world: &ClassWorld, shipped: &Value, p85: &Value) -> Value {
    json!({
        "name": w.name,
        "steps": ran.iter().map(forkgrid::Step::to_json).collect::<Vec<_>>(),
        "now": w.now,
        "world": world.to_json(),
        "shipped": shipped,
        "p85": p85,
    })
}

/// **The kernel plans every frozen P85 day as fork 4748911 asked the D92 day plans it**, by value —
/// the comparison that outlives R3 (README gap 4367).
#[test]
fn the_kernel_plans_every_frozen_p85_day_as_the_fork_asked_the_d92_day() {
    let lines = frozen();
    let names: Vec<&str> = lines.iter().map(|l| l["name"].as_str().unwrap_or_default()).collect();
    assert_eq!(names, WORLDS.iter().map(|w| w.name).collect::<Vec<_>>(), "the frozen P85 lines are WORLDS, in order");
    let mut t = forkday::DayTally::default();
    let mut findings = Vec::new();
    for l in &lines {
        let name = l["name"].as_str().unwrap_or("?");
        assert_eq!(l["p85"]["p85"], true, "{name}: the line carries P85's flag in its own home");
        let b = built(l);
        match kernel_of(&b) {
            Ok(k) => findings.extend(forkday::compare_day_with_fork(name, &k, &l["p85"], b.world.now, &mut t)),
            Err(e) => findings.push(format!("{name}: the kernel refused the day: {e}")),
        }
    }
    println!("{}", t.line("the frozen P85 days", findings.len()));
    forkday::no_disagreement(&findings);
    assert_eq!(t.days, WORLDS.len(), "every frozen P85 day was compared: {t:?}");
    assert_eq!(t.hashes_equal, t.days, "every P85 day hashes as the fork's asked the D92 day: {t:?}");
}

/// **The departure is real on every frozen world**: fork 4748911's day on the world as given is not
/// its day asked the D92 day — the running block is drawn from where its clock started in the log,
/// across the break's tail — so holding the kernel to the `p85` day holds P85, not a world it does
/// not reach.
#[test]
fn the_departure_is_real_on_every_frozen_p85_world() {
    for l in frozen() {
        let name = l["name"].as_str().unwrap_or("?");
        assert_ne!(l["shipped"], l["p85"]["day"], "{name}");
        assert_ne!(l["shipped"]["hash"], l["p85"]["hash"], "{name}: the two fork days hash alike");
    }
}

/// **Every frozen world is the binary's**: its verbs run again now over `plan-basic` give the world
/// by value (so a change to the fixture or to [`WORLDS`] fails by name instead of leaving a frozen
/// day that describes no world the suite builds), every verb exited 0 as frozen, and the world is
/// one the shipped binary holds (`forkclass::binary_holds`).
#[test]
fn every_frozen_p85_world_is_the_binarys() {
    let lines = frozen();
    let mut bad = Vec::new();
    for (w, l) in WORLDS.iter().zip(&lines) {
        let (world, ran) = build(w).unwrap_or_else(|e| panic!("{}: {e}", w.name));
        if world.to_json() != l["world"] {
            bad.push(format!("{}: the verbs build another world now ({})", w.name, forkplan::first_difference("world", &l["world"], &world.to_json()).unwrap_or_default()));
        }
        let steps: Vec<Value> = ran.iter().map(forkgrid::Step::to_json).collect();
        if json!(steps) != l["steps"] || steps.iter().any(|s| s["code"] != 0) {
            bad.push(format!("{}: the verbs ran otherwise: {steps:?}", w.name));
        }
        if let Err(e) = forkclass::binary_holds(&built(l)) {
            bad.push(format!("{}: not a world the binary holds: {}", w.name, e.join("; ")));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n  "));
}

/// **The comparison bites a bent day** (AGENTS §5.8): the frozen D92 day with its running block's
/// row started at the log's line again (the shipped drawing), and with one row a minute longer, is
/// each refused by name — and the unbent lines compare clean.
#[test]
fn the_p85_comparison_bites_a_bent_day() {
    let compare = |l: &Value| -> Vec<String> {
        let b = built(l);
        let k = kernel_of(&b).expect("the kernel plans the day");
        let mut t = forkday::DayTally::default();
        forkday::compare_day_with_fork(l["name"].as_str().unwrap_or("?"), &k, &l["p85"], b.world.now, &mut t)
    };
    for l in frozen() {
        assert!(compare(&l).is_empty(), "{}: the unbent line differs", l["name"]);
        let mut shipped = l.clone();
        shipped["p85"] = json!({"p85": true, "hash": l["shipped"]["hash"], "day": l["shipped"]["day"]});
        assert!(!compare(&shipped).is_empty(), "{}: the shipped drawing passed as the D92 day", l["name"]);
        let mut longer = l.clone();
        let rows = longer["p85"]["day"]["segments"].as_array_mut().expect("rows");
        let r = rows.iter_mut().rfind(|r| r["kind"] == "block").expect("a block row");
        let end = forkplan::at(&r["end"]).expect("an end") + chrono::Duration::minutes(1);
        r["end"] = json!(end.to_rfc3339());
        assert!(compare(&longer).iter().any(|f| f.contains("rows differ")), "{}: a row a minute longer passed: {:?}", l["name"], compare(&longer));
    }
}

/// **A frozen P85 name carried twice is refused** (AGENTS §5.8).
#[test]
#[should_panic(expected = "two frozen P85 lines for")]
fn a_frozen_p85_name_carried_twice_is_refused() {
    let one = serde_json::to_string(&frozen()[0]).expect("a line");
    lines_of(&format!("{one}\n{one}\n"));
}

/// The oracle at `TM_ORACLE`, when set (D23's shape).
fn the_oracle() -> Option<forkplan::Oracle> {
    forkplan::oracle_path().map(forkplan::Oracle::new)
}

/// **The frozen P85 days are fork 4748911's answers today, out of the tree** (`TM_ORACLE`; outlives
/// R3): each line's `shipped` and `p85` days asked again of `tm-oracle plan`, by value.
#[test]
#[ignore]
fn the_frozen_p85_days_are_the_forks_oracle_answer_today() {
    let Some(oracle) = the_oracle() else {
        eprintln!("inert: set TM_ORACLE to an oracle built by kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh");
        return;
    };
    for l in frozen() {
        let name = l["name"].as_str().unwrap_or("?");
        let (shipped, p85) = fork_days(&built(&l), &oracle).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(shipped, l["shipped"], "{name}: the oracle plans another shipped day ({:?})", forkplan::first_difference("shipped", &l["shipped"], &shipped));
        assert_eq!(p85, l["p85"], "{name}: the oracle plans another D92 day ({:?})", forkplan::first_difference("p85", &l["p85"], &p85));
    }
    println!("tm-oracle plan asked {} time(s)", *oracle.asked.lock().expect("census"));
}

/// **Freeze the P85 days** — inert without `TM_P85_BLESS`; it asks `TM_ORACLE`, fork 4748911 out of
/// the tree, so it outlives R3. Every [`WORLDS`] entry is run ([`build`]) and written with the two
/// fork days on it ([`fork_days`]). **What a line is held against is the file's COMMITTED history**
/// (README gap 4151; `frozenhist::held`): a committed line may not move — its world moving is a
/// re-draw (D64(b)'s, decided elsewhere), and its shipped day moving over the same world is the
/// SHIPPED fork's day moving (D64, clause 2). A line HEAD holds that no world builds is refused.
/// `TM_P85_BLESS_OUT` writes elsewhere, for a dry run.
#[test]
#[ignore]
fn the_frozen_p85_days_are_blessed() {
    if std::env::var_os("TM_P85_BLESS").is_none() {
        eprintln!("inert: set TM_P85_BLESS=1 (with TM_ORACLE) to write {FROZEN_P85}");
        return;
    }
    let oracle = the_oracle().expect("TM_P85_BLESS asks fork 4748911: set TM_ORACLE");
    let path = frozen_path();
    let held = frozenhist::held(&path, frozenhist::key_of("name")).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", held.census(FROZEN_P85));
    let (mut out, mut refused, mut added) = (String::new(), Vec::new(), 0usize);
    for w in &WORLDS {
        let (world, ran) = build(w).unwrap_or_else(|e| panic!("{}: {e}", w.name));
        assert!(ran.iter().all(|s| s.to_json()["code"] == 0), "{}: a verb failed: {:?}", w.name, ran.iter().map(forkgrid::Step::to_json).collect::<Vec<_>>());
        let (shipped, p85) = fork_days(&Built::of(world.clone()), &oracle).unwrap_or_else(|e| panic!("{}: {e}", w.name));
        let l = line_of(w, &ran, &world, &shipped, &p85);
        match held.get(w.name) {
            None => added += 1,
            Some(old) if old["world"] != l["world"] || old["steps"] != l["steps"] => {
                refused.push(format!("{}: the verbs build another world now — a re-draw, which D64(b) must decide", w.name))
            }
            Some(old) if old["shipped"] != l["shipped"] => refused.push(format!(
                "{}: the SHIPPED fork's day moved over the same world ({}), and no comparand parity number moves it (D64, clause 2)",
                w.name,
                forkplan::first_difference("shipped", &old["shipped"], &l["shipped"]).unwrap_or_default()
            )),
            Some(old) if old["p85"] != l["p85"] => refused.push(format!(
                "{}: the fork's D92 day moved over the same world ({}) — fork 4748911 does not move, so the ASKING did, which is a decision",
                w.name,
                forkplan::first_difference("p85", &old["p85"], &l["p85"]).unwrap_or_default()
            )),
            Some(_) => {}
        }
        out.push_str(&serde_json::to_string(&l).expect("a line serialises"));
        out.push('\n');
    }
    for k in &held.head {
        if !WORLDS.iter().any(|w| w.name == k) {
            refused.push(format!("{k}: a frozen line no world builds any more"));
        }
    }
    eprintln!("P85 days: {added} line(s) added, {} refused", refused.len());
    assert!(refused.is_empty(), "the P85 bless is refused and wrote nothing:\n  {}", refused.join("\n  "));
    let out_path = std::env::var_os("TM_P85_BLESS_OUT").map(PathBuf::from).unwrap_or(path);
    std::fs::write(out_path, out).expect("the frozen P85 days are written");
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gap 4367)
/// **The frozen P85 days are the in-tree fork's answers today** — while the in-tree fork stands, it
/// plans each frozen world's two days exactly as frozen. Deleted with the region.
#[test]
fn the_frozen_p85_days_are_the_in_tree_forks_answer_today() {
    for l in frozen() {
        let name = l["name"].as_str().unwrap_or("?");
        let (shipped, p85) = fork_days(&built(&l), &forkplan::InTree).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(p85, l["p85"], "{name}: the in-tree fork plans another D92 day ({:?})", forkplan::first_difference("p85", &l["p85"], &p85));
        let _ = shipped;
    }
}
// END THE FORK PLANNER
