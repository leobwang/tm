//! **The week grid against fork 4748911's, by value — the comparand that survives R3**
//! (stage 6 W-40 track H, README gap 3718).
//!
//! `cli_week_grid.rs` and `cli_week_cut.rs` hold the grid (`tm review week`'s `heat`) to the
//! day plan's cut of the same Pause. After R3 the day plan's cut is the kernel's
//! (`Planner.pastSpans`) and so is the grid's (`GridCut.segSpans`) — one definition through two
//! surfaces — so those tests compare the kernel with itself. Here the grid is held to fork
//! 4748911's OWN grid of the same world, frozen by value through `tm-oracle review`, with the
//! one registered departure that moves a cell (parity P63) applied by its property and its
//! cells named on the line. `support/forkgrid.rs` says what is frozen and why.
//!
//! **Plain `cargo test`, outside any fork region.** The comparison runs the shipped binary and
//! reads bytes on disk; no test process here reaches the fork's planner or computes the fork's
//! grid in-tree. The oracle arms — the frozen lines still the fork's answer, fresh weeks against
//! the fork, and the bless — are inert without `TM_ORACLE` (D23's shape, as `tm-oracle plan` is
//! for the planner).

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

/// `tm-oracle`'s process client (`Oracle::with_mode`), reached here for its `review` mode only.
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

use proptest::prelude::*;
use serde_json::{json, Value};

use forkgrid::{GridWorld, P63Reading, Step, P63_READING};

/// The registered parity numbers (`kernel/parity.txt`).
fn registered() -> BTreeSet<u32> {
    forkclass::registered_parity()
}

/// The comparison's census: `[lines, cells compared, named cells, minutes moved pause → wall,
/// minutes not drawn]`.
fn census(lines: &[Value]) -> [i64; 5] {
    let mut c = [0i64; 5];
    for l in lines {
        c[0] += 1;
        c[1] += l["fork"]["heat"].as_array().map_or(0, |d| d.len() as i64) * 24 * 8;
        for (_, _, p, w) in forkgrid::cells_of(&l["p63"]).unwrap_or_default() {
            c[2] += 1;
            c[3] += w;
            c[4] += -p - w;
        }
    }
    c
}

/// Whether a line's fork pauses hold one that runs past local midnight of its record's day.
fn has_midnight_pause(line: &Value) -> bool {
    line["fork"]["pauses"].as_array().into_iter().flatten().any(|p| {
        let (Some(d), Some(e)) = (p[0].as_str(), p[2].as_str()) else { return false };
        e.get(..10).is_some_and(|ed| ed > d)
    })
}

/// **The binary draws every frozen week as fork 4748911 drew it, P63's named cells apart** —
/// cell by cell, eight styles a cell, `blocks_done` and `block_min` too, and the log the binary
/// read is the log the fork read. The floors (AGENTS §9.2): every grid test's world, every
/// generated draw, a named cell, a pause past local midnight, a sealed and an unsealed week,
/// each compared at least once.
#[test]
fn the_binary_draws_every_frozen_week_as_the_fork_drew_it() {
    let lines = forkgrid::frozen_lines();
    let mut findings = Vec::new();
    for l in &lines {
        findings.extend(forkgrid::compare_line(l, P63_READING));
    }
    let [n, cells, named, moved, dropped] = census(&lines);
    println!(
        "week grids: {n} line(s), {cells} cells compared with fork 4748911's grid; P63 names {named} cell(s), \
         {moved} minute(s) moved from `pause` to `wall`, {dropped} not drawn"
    );
    assert!(findings.is_empty(), "{} disagreement(s) with fork 4748911's week grid:\n  {}", findings.len(), findings.join("\n  "));
    let names: BTreeSet<&str> = lines.iter().filter_map(|l| l["name"].as_str()).collect();
    for w in forkgrid::cli_worlds() {
        assert!(names.contains(w.name), "the grid test's world `{}` ({}) is frozen nowhere", w.name, w.from);
    }
    let generated = lines.iter().filter(|l| l["from"]["midnight"] == false).count();
    let late = lines.iter().filter(|l| l["from"]["midnight"] == true).count();
    assert_eq!((generated, late), (forkgrid::WEEK_DRAWS, forkgrid::MIDNIGHT_DRAWS), "every generated draw is a frozen line");
    assert!(named > 0 && moved > 0, "no cell P63 names was compared");
    assert!(lines.iter().any(has_midnight_pause), "no pause past local midnight was compared");
    assert!(lines.iter().any(|l| l["sealed"] == true), "no sealed week was compared");
    assert!(lines.iter().any(|l| l["sealed"] == false), "no unsealed week was compared");
}

/// **The grid tests' worlds draw what the grid tests assert** — the frozen `cli/*` worlds are
/// `cli_week_grid.rs`' and `cli_week_cut.rs`' own: the binary's grid on each holds the cells
/// those tests pin (the meeting's hour `wall` 10 + 50, the straddle's `pause` 10 + 10 around
/// it, the plain pause's 20, Tuesday's interruption 15, the midnight call's `wall` 30 before
/// midnight and `pause` 30 after), so a step that drifts from the test it names fails here.
#[test]
fn the_cli_worlds_draw_what_the_grid_tests_assert() {
    let lines = forkgrid::frozen_lines();
    let heat = |name: &str| -> Value {
        let l = lines.iter().find(|l| l["name"] == name).unwrap_or_else(|| panic!("no line {name}"));
        let w = GridWorld::of_json(&l["world"]).expect("a stored world");
        forkgrid::review(&w, l["date"].as_str().unwrap_or_default(), l["at"].as_str().unwrap_or_default())
            .unwrap_or_else(|e| panic!("{name}: {e}"))
            .heat
    };
    let cell = |heat: &Value, date: &str, hour: usize, style: usize| -> u64 {
        let row = heat.as_array().into_iter().flatten().find(|d| d["date"] == date).cloned().unwrap_or(Value::Null);
        row["hours"][hour][style].as_u64().unwrap_or_default()
    };
    let (pause, wall, interrupt) = (4, 7, 3);
    let m = heat("cli/meeting");
    assert_eq!((cell(&m, "2026-09-07", 12, wall), cell(&m, "2026-09-07", 13, wall)), (10, 50));
    assert_eq!(cell(&m, "2026-09-07", 12, pause) + cell(&m, "2026-09-07", 13, pause), 0);
    let s = heat("cli/straddle");
    assert_eq!((cell(&s, "2026-09-07", 12, pause), cell(&s, "2026-09-07", 12, wall)), (10, 10));
    assert_eq!((cell(&s, "2026-09-07", 13, pause), cell(&s, "2026-09-07", 13, wall)), (10, 50));
    assert_eq!(cell(&heat("cli/plain"), "2026-09-07", 9, pause), 20);
    for name in ["cli/week", "cli/week-sealed"] {
        let w = heat(name);
        assert_eq!((cell(&w, "2026-09-07", 12, wall), cell(&w, "2026-09-07", 13, wall)), (10, 50), "{name}");
        assert_eq!(cell(&w, "2026-09-08", 10, interrupt), 15, "{name}");
    }
    let n = heat("cli/midnight");
    assert_eq!((cell(&n, "2026-09-08", 23, wall), cell(&n, "2026-09-08", 23, pause)), (30, 0));
    // D77 (P63 restated, the W-40 land step): after midnight Wednesday's own wall covers the
    // call, so hour 00 of Tuesday's record row is the wall, as `cli_week_cut.rs` pins.
    assert_eq!((cell(&n, "2026-09-08", 0, wall), cell(&n, "2026-09-08", 0, pause)), (30, 0));
}

/// **Every frozen world is the world its steps build** — re-derived through the shipped binary
/// from `plan-basic`: a grid test's world by the verbs the line records (and the step list is
/// [`forkgrid::cli_worlds`]' own), a generated week by its draw (`forkgrid::week_draws`'
/// index, re-run), each verb's exit code as recorded, and the world byte for byte. So "this
/// line is draw 7" and "this line is the midnight test's world" are checked facts; a change to
/// what the binary writes that moves a frozen world fails here by name, and whether that is a
/// re-draw under the owner's D64(b) is the next step's to decide.
#[test]
fn every_frozen_week_is_the_world_its_steps_build() {
    let lines = forkgrid::frozen_lines();
    let cli = forkgrid::cli_worlds();
    let draws: Vec<forkgrid::WeekDraw> = forkgrid::week_draws(forkgrid::WEEK_SEED, false).take(forkgrid::WEEK_DRAWS).collect();
    let late: Vec<forkgrid::WeekDraw> = forkgrid::week_draws(forkgrid::MIDNIGHT_SEED, true).take(forkgrid::MIDNIGHT_DRAWS).collect();
    let check = |l: &Value| -> Vec<String> {
        let who = l["name"].as_str().unwrap_or("<unnamed>").to_string();
        let recorded: Vec<Step> = match l["steps"].as_array() {
            Some(s) => match s.iter().map(Step::of_json).collect::<Result<Vec<_>, _>>() {
                Ok(s) => s,
                Err(e) => return vec![format!("{who}: {e}")],
            },
            None => return vec![format!("{who}: no steps")],
        };
        let mut out = Vec::new();
        let want: Vec<Step> = match l["from"]["seed"].as_str() {
            Some(seed) => {
                let i = l["from"]["draw"].as_u64().unwrap_or(u64::MAX) as usize;
                let pool = match (seed, l["from"]["midnight"].as_bool()) {
                    (forkgrid::WEEK_SEED, Some(false)) => &draws,
                    (forkgrid::MIDNIGHT_SEED, Some(true)) => &late,
                    _ => return vec![format!("{who}: seed {seed:?} is not one this file freezes")],
                };
                match pool.get(i) {
                    Some(d) => forkgrid::week_steps(d),
                    None => return vec![format!("{who}: draw {i} of seed {seed:?} is not one this file freezes")],
                }
            }
            None => match cli.iter().find(|w| l["name"] == w.name) {
                Some(w) => w.steps.clone(),
                None => return vec![format!("{who}: neither a grid test's world nor a draw")],
            },
        };
        let strip = |s: &[Step]| -> Vec<Step> {
            s.iter()
                .map(|x| match x {
                    Step::Run { at, args, .. } => Step::Run { at: at.clone(), args: args.clone(), code: 0 },
                    other => other.clone(),
                })
                .collect()
        };
        if strip(&recorded) != strip(&want) {
            out.push(format!("{who}: the recorded steps are not its source's"));
            return out;
        }
        match forkgrid::build(&recorded, l["date"].as_str().unwrap_or_default(), l["at"].as_str().unwrap_or_default()) {
            Err(e) => out.push(format!("{who}: {e}")),
            Ok((world, ran)) => {
                if ran != recorded {
                    let first = ran.iter().zip(&recorded).position(|(a, b)| a != b);
                    out.push(format!("{who}: a verb's exit code moved (step {first:?})"));
                }
                let stored = GridWorld::of_json(&l["world"]).expect("a stored world");
                if world != stored {
                    let path = world
                        .files
                        .iter()
                        .zip(&stored.files)
                        .find(|(a, b)| a != b)
                        .map_or_else(|| "the file list".to_string(), |(a, _)| a.0.clone());
                    out.push(format!("{who}: the steps build another world (first difference: {path})"));
                }
            }
        }
        out
    };
    let findings: Vec<String> = std::thread::scope(|s| {
        let chunks: Vec<&[Value]> = lines.chunks(lines.len().div_ceil(8).max(1)).collect();
        let handles: Vec<_> = chunks.into_iter().map(|c| s.spawn(move || c.iter().flat_map(&check).collect::<Vec<_>>())).collect();
        handles.into_iter().flat_map(|h| h.join().expect("a worker")).collect()
    });
    println!("week grids re-derived: {} line(s)", lines.len());
    assert!(findings.is_empty(), "{} frozen world(s) are not what their steps build:\n  {}", findings.len(), findings.join("\n  "));
}

/// **D77's reading moves exactly the cells past local midnight** (the campaign's call on README
/// gap 3620, which another track builds this run): on every frozen line, the cells P63 names
/// under `P63Reading::EachDay` differ from `P63Reading::RecordDay`'s only in the clock hours a
/// Pause reaches PAST local
/// midnight of its record's day — so the flip of `forkgrid::P63_READING` the land step makes
/// when D77 lands moves those cells and no other, and the midnight test's world is among them.
#[test]
fn d77s_reading_moves_only_the_cells_past_midnight() {
    let lines = forkgrid::frozen_lines();
    let mut moved_lines = Vec::new();
    for l in &lines {
        let w = GridWorld::of_json(&l["world"]).expect("a stored world");
        let tz = w.cfg().tz;
        let at = forkgrid::line_at(l, tz).expect("an instant");
        let a = forkgrid::p63_cells(&w, &l["fork"]["pauses"], at, P63Reading::RecordDay).expect("the rule");
        let b = forkgrid::p63_cells(&w, &l["fork"]["pauses"], at, P63Reading::EachDay).expect("the rule");
        if a == b {
            continue;
        }
        moved_lines.push(l["name"].as_str().unwrap_or("?").to_string());
        // The cells a Pause reaches past local midnight of its record's day.
        let mut past: BTreeSet<(String, usize)> = BTreeSet::new();
        for p in l["fork"]["pauses"].as_array().into_iter().flatten() {
            let d = chrono::NaiveDate::parse_from_str(p[0].as_str().unwrap_or_default(), "%Y-%m-%d").expect("a date");
            let t = |k: usize| chrono::DateTime::parse_from_rfc3339(p[k].as_str().unwrap_or_default()).expect("an instant").with_timezone(&tz);
            let next = tm_core::capacity::local_dt(tz, d + chrono::Duration::days(1), chrono::NaiveTime::MIN);
            if t(2) > next {
                for (h, _) in forkgrid::hour_minutes(next, t(2)) {
                    past.insert((d.to_string(), h));
                }
            }
        }
        for (d, h, _, _) in b.iter().filter(|c| !a.contains(c)).chain(a.iter().filter(|c| !b.contains(c))) {
            assert!(past.contains(&(d.clone(), *h)), "{}: D77's reading moved {d} hour {h}, which no pause reaches past midnight", l["name"]);
        }
    }
    println!("D77's reading would move {} line(s): {}", moved_lines.len(), moved_lines.join(", "));
    assert!(moved_lines.iter().any(|n| n == "cli/midnight"), "the midnight test's world is not among the lines D77 moves");
}

/// **The grid's re-bless gate bites, and admits what D64 allows** (AGENTS §5.8): a fork grid
/// that moves over an unchanged world is refused; named cells that move without a registered
/// P63 named are refused, and admitted with it; a world that moves is a re-draw, refused
/// without D64(b)'s reason and admitted with one; an unchanged line changes nothing.
#[test]
fn the_grid_rebless_gate_holds_d64() {
    let reg = registered();
    let old = json!({"name": "x", "from": {}, "steps": [], "date": "2026-09-07", "at": "a", "sealed": false,
                     "world": [["a.md", "x"]], "fork": {"heat": [1]}, "p63": [["2026-09-07", 12, -10, 10]]});
    assert_eq!(forkgrid::rebless_allows(&old, &old, &[], None, None, &reg), Ok(Vec::new()));
    let mut fork = old.clone();
    fork["fork"]["heat"] = json!([2]);
    assert!(forkgrid::rebless_allows(&old, &fork, &[63], None, None, &reg).is_err(), "the fork's grid moved over one world");
    let mut cells = old.clone();
    cells["p63"] = json!([["2026-09-07", 12, -20, 20]]);
    assert!(forkgrid::rebless_allows(&old, &cells, &[], None, None, &reg).is_err(), "cells moved with no number named");
    assert!(forkgrid::rebless_allows(&old, &cells, &[62], None, None, &reg).is_err(), "cells moved with another number named");
    assert_eq!(forkgrid::rebless_allows(&old, &cells, &[63], None, None, &reg), Ok(vec!["p63".to_string()]));
    let mut world = old.clone();
    world["world"] = json!([["a.md", "y"]]);
    world["fork"]["heat"] = json!([3]);
    assert!(forkgrid::rebless_allows(&old, &world, &[63], None, None, &reg).is_err(), "a re-draw with no reason");
    assert!(forkgrid::rebless_allows(&old, &world, &[], Some("D64(b): the binary no longer writes it"), None, &reg).is_ok());
    // The owner's D85, D64(c) (W-42 track C, README gap 4281): a corrected harness reading moves the
    // named cells with no number named, and nothing else — not the fork's grid, not the world.
    let why = Some("2026-10-02 D64(c): P63's reading corrected (gap 4281)");
    assert_eq!(forkgrid::rebless_allows(&old, &cells, &[], None, why, &reg), Ok(vec!["p63".to_string()]), "a corrected reading of the cells was refused");
    let mut cells_and_fork = cells.clone();
    cells_and_fork["fork"]["heat"] = json!([2]);
    assert!(forkgrid::rebless_allows(&old, &cells_and_fork, &[], None, why, &reg).is_err(), "the fork's grid moved under (c)");
    let mut cells_and_world = cells.clone();
    cells_and_world["world"] = json!([["a.md", "y"]]);
    assert!(forkgrid::rebless_allows(&old, &cells_and_world, &[], None, why, &reg).is_err(), "a world moved under (c)");
}

/// **A line cannot be shadowed** (AGENTS §5.8): a frozen grid file carrying one name twice is
/// refused by name when it is read, so no second line of a name can stand beside the one the
/// comparison holds the binary to — and the file as frozen reads clean.
#[test]
#[should_panic(expected = "two frozen grid lines named `cli/meeting`")]
fn a_frozen_grid_name_carried_twice_is_refused() {
    let lines = forkgrid::frozen_lines();
    let one = serde_json::to_string(lines.iter().find(|l| l["name"] == "cli/meeting").expect("the meeting world")).expect("a line");
    let _ = forkgrid::lines_of(&format!("{one}\n{one}\n"));
}

/// **The comparison bites** (AGENTS §5.8, the other direction from the green run): on the
/// meeting world, a fork cell bent by one minute is named by its day, hour and style; named
/// cells that are not P63's rule are named as such; and a seal flag the binary does not
/// reproduce is named. Each through the very functions the frozen comparison runs
/// (`forkgrid::compare_line`, and `forkgrid::compare_heat` under it).
#[test]
fn the_week_comparison_bites_a_bent_line() {
    let lines = forkgrid::frozen_lines();
    let line = lines.iter().find(|l| l["name"] == "cli/meeting").expect("the meeting world");
    assert!(forkgrid::compare_line(line, P63_READING).is_empty(), "the line itself compares clean");
    let mut cell = line.clone();
    let c = cell["fork"]["heat"][0]["hours"][12][0].as_i64().expect("a cell");
    cell["fork"]["heat"][0]["hours"][12][0] = json!(c + 1);
    let f = forkgrid::compare_line(&cell, P63_READING);
    assert!(f.iter().any(|x| x.contains("2026-09-07 hour 12 `block`")), "a bent fork cell is named: {f:?}");
    let mut named = line.clone();
    named["p63"] = json!([["2026-09-07", 12, -9, 9], ["2026-09-07", 13, -50, 50]]);
    let f = forkgrid::compare_line(&named, P63_READING);
    assert!(f.iter().any(|x| x.contains("not P63's rule")), "a named cell off the rule is named: {f:?}");
    assert!(f.iter().any(|x| x.contains("hour 12 `wall`")), "and the cell it moves: {f:?}");
    let mut sealed = line.clone();
    sealed["sealed"] = json!(true);
    let f = forkgrid::compare_line(&sealed, P63_READING);
    assert!(f.iter().any(|x| x.contains("sealed")), "a seal the binary does not make is named: {f:?}");
}

/// **P63's rule, on a hand-sized world** (non-vacuity, AGENTS §5.2): the meeting world's pause
/// 12:50–13:50 under `^g1` (12:50–13:50) moves 10 minutes of hour 12 and 50 of hour 13 from
/// `pause` to `wall`; a pause a wall does not touch moves nothing; and a pause clipped by `now`
/// loses the minutes past it, drawn as nothing.
#[test]
fn p63s_rule_moves_the_minutes_a_wall_covers() {
    let lines = forkgrid::frozen_lines();
    let w = |name: &str| GridWorld::of_json(&lines.iter().find(|l| l["name"] == name).expect("a line")["world"]).expect("a world");
    let meeting = w("cli/meeting");
    let tz = meeting.cfg().tz;
    let at = |s: &str| chrono::DateTime::parse_from_rfc3339(s).expect("an instant").with_timezone(&tz);
    let pauses = json!([["2026-09-07", "2026-09-07T12:50:00-05:00", "2026-09-07T13:50:00-05:00", "t4"]]);
    let cells = forkgrid::p63_cells(&meeting, &pauses, at("2026-09-07T14:20:00-05:00"), P63Reading::RecordDay).expect("the rule");
    assert_eq!(cells, vec![("2026-09-07".to_string(), 12, -10, 10), ("2026-09-07".to_string(), 13, -50, 50)]);
    let free = json!([["2026-09-07", "2026-09-07T09:10:00-05:00", "2026-09-07T09:30:00-05:00", "t4"]]);
    assert!(forkgrid::p63_cells(&meeting, &free, at("2026-09-07T14:20:00-05:00"), P63Reading::RecordDay).expect("the rule").is_empty());
    let clipped = forkgrid::p63_cells(&meeting, &free, at("2026-09-07T09:20:00-05:00"), P63Reading::RecordDay).expect("the rule");
    assert_eq!(clipped, vec![("2026-09-07".to_string(), 9, -10, 0)], "the ten minutes past `now` are not drawn");
}

// ---------------------------------------------------------------------------
// The oracle arms: inert without TM_ORACLE (D23's shape)
// ---------------------------------------------------------------------------

/// `tm-oracle review` at `TM_ORACLE`, running — `None` without it.
fn the_oracle() -> Option<&'static forkplan::Oracle> {
    static ORACLE: std::sync::OnceLock<Option<forkplan::Oracle>> = std::sync::OnceLock::new();
    ORACLE.get_or_init(|| forkplan::oracle_path().map(|b| forkplan::Oracle::with_mode(b, "review"))).as_ref()
}

/// Fork 4748911's grid of a world, asked of the oracle.
fn fork_grid(oracle: &forkplan::Oracle, world: &GridWorld, date: &str) -> Result<Value, String> {
    oracle.ask(&json!({"op": "week", "world": world.oracle_world(), "date": date}))
}

/// **Every frozen grid is fork 4748911's answer today** — the oracle asked again about every
/// line's world answers its `fork` exactly. The assertion bytes on disk cannot make about
/// themselves; after R3 the oracle is the only fork left to ask. Inert without `TM_ORACLE`.
#[test]
#[ignore]
fn the_frozen_week_grids_are_the_forks_oracle_answer_today() {
    let Some(oracle) = the_oracle() else {
        eprintln!("inert: set TM_ORACLE to an oracle built by kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh");
        return;
    };
    let lines = forkgrid::frozen_lines();
    let mut stale = Vec::new();
    for l in &lines {
        let w = GridWorld::of_json(&l["world"]).expect("a stored world");
        match fork_grid(oracle, &w, l["date"].as_str().unwrap_or_default()) {
            Err(e) => stale.push(format!("{}: {e}", l["name"])),
            Ok(a) if a != l["fork"] => stale.push(format!("{}: the oracle's grid is not the frozen one", l["name"])),
            Ok(_) => {}
        }
    }
    println!("frozen week grids the fork oracle answers as frozen: {} of {}", lines.len() - stale.len(), lines.len());
    assert!(stale.is_empty(), "the fork oracle does not answer the frozen grids as frozen:\n  {}", stale.join("\n  "));
}

/// The fresh arm's census: `[weeks, compared, named cells, minutes moved to wall]`.
static FRESH: std::sync::Mutex<[i64; 4]> = std::sync::Mutex::new([0; 4]);

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(16),
        max_shrink_iters: 0,
        ..ProptestConfig::default()
    })]

    /// **The binary draws every fresh week as fork 4748911 draws it** — the exploring half
    /// (D46: a fixed list finds nothing in a world no line holds): draw 0 of
    /// `forkgrid::week_draws` from a fresh seed, built through the binary, its grid held to
    /// the oracle's with P63's cells applied by the rule, exactly as a frozen line is. Inert
    /// without `TM_ORACLE`; a failure names the seed, so the week can be drawn again.
    #[test]
    #[ignore]
    fn the_binary_draws_every_fresh_week_as_the_forks_oracle_draws_it(bytes in any::<[u8; 12]>(), midnight in any::<bool>()) {
        let Some(oracle) = the_oracle() else { return Ok(()) };
        let seed: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
        let draw = forkgrid::week_draws(&seed, midnight).next().expect("a draw");
        let steps = forkgrid::week_steps(&draw);
        let (world, ran) = forkgrid::build(&steps, forkgrid::WEEK_DAYS[0], forkgrid::WEEK_AT)
            .map_err(|e| TestCaseError::fail(format!("seed {seed}: {e}")))?;
        let fork = fork_grid(oracle, &world, forkgrid::WEEK_DAYS[0])
            .map_err(|e| TestCaseError::fail(format!("seed {seed}: the oracle: {e}")))?;
        let tz = world.cfg().tz;
        let at = chrono::DateTime::parse_from_rfc3339(forkgrid::WEEK_AT).expect("an instant").with_timezone(&tz);
        let cells = forkgrid::p63_cells(&world, &fork["pauses"], at, P63_READING).map_err(TestCaseError::fail)?;
        let r = forkgrid::review(&world, forkgrid::WEEK_DAYS[0], forkgrid::WEEK_AT).map_err(TestCaseError::fail)?;
        let line = forkgrid::line_of(&format!("fresh {seed}"), json!({"seed": seed, "draw": 0, "midnight": midnight}), &ran, &world,
            forkgrid::WEEK_DAYS[0], forkgrid::WEEK_AT, r.sealed, &fork, &cells);
        let findings = forkgrid::compare_line(&line, P63_READING);
        prop_assert!(findings.is_empty(), "seed {} (midnight {}): {} disagreement(s) with fork 4748911's grid:\n  {}", seed, midnight, findings.len(), findings.join("\n  "));
        let [weeks, compared, named, moved] = {
            let mut c = FRESH.lock().expect("census");
            c[0] += 1;
            c[1] += 1;
            c[2] += cells.len() as i64;
            c[3] += cells.iter().map(|x| x.3).sum::<i64>();
            *c
        };
        eprintln!("fork_week_grid fresh census: {weeks} week(s), {compared} compared with fork 4748911's grid; {named} named cell(s), {moved} minute(s) moved to `wall`");
    }
}

/// **Freeze the week grids** — inert without `TM_GRID_BLESS`. `TM_GRID_BLESS=1` draws every line
/// again — the grid tests' worlds (`forkgrid::cli_worlds`), `forkgrid::WEEK_DRAWS` draws of
/// `forkgrid::WEEK_SEED` and `forkgrid::MIDNIGHT_DRAWS` of `forkgrid::MIDNIGHT_SEED` — and asks
/// `TM_ORACLE` for the fork's grid; `TM_GRID_BLESS=p63`
/// recomputes only the named cells by `forkgrid::P63_READING`, over each line's own world and
/// the fork pauses it holds (no oracle: the land step's re-bless when D77 restates P63). Every
/// line it already holds is held to the owner's D64 (`forkgrid::rebless_allows`):
/// `TM_GRID_BLESS_BECAUSE` names the parity numbers (`63`), `TM_GRID_BLESS_REDRAW` D64(b)'s
/// reason for a re-draw, and since the owner's D85 `TM_GRID_BLESS_HARNESS` a corrected harness
/// reading's (D64(c): the named cells move, nothing else). Each changed line is named; a refusal
/// writes nothing. **What each line is held against is the file's COMMITTED history** (W-42 track
/// C, README gap 4151; `frozenhist::held`) — never the working copy, which stays the INPUT of
/// `TM_GRID_BLESS=p63` only — so deleting the file or a line of it is not a fresh freeze, and a line
/// HEAD holds that the bless no longer draws is refused.
#[test]
#[ignore]
fn the_frozen_week_grids_are_blessed() {
    let Some(mode) = std::env::var("TM_GRID_BLESS").ok() else {
        eprintln!("inert: set TM_GRID_BLESS=1 (with TM_ORACLE) or TM_GRID_BLESS=p63 to write {}", forkgrid::FROZEN_GRID);
        return;
    };
    let because: Vec<u32> = std::env::var("TM_GRID_BLESS_BECAUSE")
        .unwrap_or_default()
        .split(',')
        .filter_map(|s| s.trim().trim_start_matches('P').parse().ok())
        .collect();
    let redraw = std::env::var("TM_GRID_BLESS_REDRAW").ok();
    let harness = forkclass::harness_of("TM_GRID_BLESS_HARNESS");
    let reg = registered();
    let held: Vec<Value> = if forkgrid::frozen_path().exists() { forkgrid::frozen_lines() } else { Vec::new() };
    let committed = frozenhist::held(&forkgrid::frozen_path(), frozenhist::key_of("name")).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", committed.census(forkgrid::FROZEN_GRID));
    let fresh: Vec<Value> = match mode.as_str() {
        "p63" => held
            .iter()
            .map(|l| {
                let w = GridWorld::of_json(&l["world"]).expect("a stored world");
                let at = forkgrid::line_at(l, w.cfg().tz).expect("an instant");
                let cells = forkgrid::p63_cells(&w, &l["fork"]["pauses"], at, P63_READING).expect("the rule");
                let mut n = l.clone();
                n["p63"] = forkgrid::cells_json(&cells);
                n
            })
            .collect(),
        "1" => {
            let oracle = the_oracle().expect("TM_GRID_BLESS=1 asks the fork: set TM_ORACLE");
            let mut out = Vec::new();
            let mut todo: Vec<(String, Value, Vec<Step>, &str, &str)> = forkgrid::cli_worlds()
                .into_iter()
                .map(|w| (w.name.to_string(), json!({"test": w.from}), w.steps, w.date, w.at))
                .collect();
            for (seed, midnight, n, what) in [
                (forkgrid::WEEK_SEED, false, forkgrid::WEEK_DRAWS, "week"),
                (forkgrid::MIDNIGHT_SEED, true, forkgrid::MIDNIGHT_DRAWS, "midnight"),
            ] {
                for d in forkgrid::week_draws(seed, midnight).take(n) {
                    todo.push((
                        format!("{what} draw {}", d.index),
                        json!({"seed": seed, "draw": d.index, "midnight": midnight}),
                        forkgrid::week_steps(&d),
                        forkgrid::WEEK_DAYS[0],
                        forkgrid::WEEK_AT,
                    ));
                }
            }
            for (name, from, steps, date, at) in todo {
                let (world, ran) = forkgrid::build(&steps, date, at).unwrap_or_else(|e| panic!("{name}: {e}"));
                let r = forkgrid::review(&world, date, at).unwrap_or_else(|e| panic!("{name}: {e}"));
                assert_eq!(r.log_after, world.log(), "{name}: the second review appended to the log");
                let fork = fork_grid(oracle, &world, date).unwrap_or_else(|e| panic!("{name}: the oracle: {e}"));
                let tz = world.cfg().tz;
                let t = chrono::DateTime::parse_from_rfc3339(at).expect("an instant").with_timezone(&tz);
                let cells = forkgrid::p63_cells(&world, &fork["pauses"], t, P63_READING).expect("the rule");
                out.push(forkgrid::line_of(&name, from, &ran, &world, date, at, r.sealed, &fork, &cells));
            }
            out
        }
        other => panic!("TM_GRID_BLESS={other}: say 1 or p63"),
    };
    let (mut refused, mut changed, mut added) = (Vec::new(), Vec::new(), 0usize);
    // **A re-draw is RECORDED on its line** (the W-44 repair, README gap 4618's harness half): the plain
    // history check (`fork_rebless_history.rs`, `frozenhist::redrawn`) licenses a moved world only where the
    // newer version carries `d64b`, a dated reason naming D64(b) — the field every other bless that re-draws
    // writes (`planner_w41_starts.rs`, `tui_kernel_answers.rs`). This bless admitted the re-draw and wrote no
    // such field, so its first re-draw since that check landed failed every plain run that followed. A line
    // that keeps its world keeps the reason it was last re-drawn with.
    let drawn = ["name", "from", "steps", "date", "at", "sealed", "world"];
    let mut fresh = fresh;
    for n in &mut fresh {
        match committed.get(n["name"].as_str().unwrap_or_default()) {
            None => added += 1,
            Some(o) => match forkgrid::rebless_allows(o, n, &because, redraw.as_deref(), harness.as_deref(), &reg) {
                Err(e) => refused.push(e),
                Ok(k) => {
                    if k.iter().any(|f| drawn.contains(&f.as_str())) {
                        match redraw.as_deref() {
                            Some(why) if forkclass::is_d64b_reason(why) => n["d64b"] = json!(why),
                            _ => refused.push(format!(
                                "{}: a re-draw records its reason on the line, dated and naming D64(b) (TM_GRID_BLESS_REDRAW)",
                                n["name"]
                            )),
                        }
                    } else if let Some(why) = o.get("d64b") {
                        n["d64b"] = why.clone();
                    }
                    if !k.is_empty() {
                        changed.push(format!("{} `{}`", n["name"], k.join("`, `")));
                    }
                }
            },
        }
    }
    for name in &committed.head {
        if !fresh.iter().any(|n| n["name"] == name.as_str()) {
            refused.push(format!("{name}: a frozen line the bless no longer draws"));
        }
    }
    eprintln!(
        "week grids: {added} line(s) added, {} changed ({}), {} refused",
        changed.len(),
        changed.join("; "),
        refused.len()
    );
    assert!(refused.is_empty(), "the re-bless is refused by the owner's D64 and wrote nothing:\n  {}", refused.join("\n  "));
    let text: String = fresh.iter().map(|l| serde_json::to_string(l).expect("a line serialises") + "\n").collect();
    std::fs::write(forkgrid::frozen_path(), text).expect("the frozen grids are written");
}
