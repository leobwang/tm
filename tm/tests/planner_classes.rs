//! **The kernel plans every generated CLASS the fork planned** — the planner's
//! differential that survives R3 (stage 6 W-36 track H; README gaps 2925, 2871).
//!
//! `support/forkclass.rs` is the specification: what a class is (a function of
//! the world, never a label), the class space (every `(run, shape)` an arm of
//! `planner_invariants.rs` draws), what is frozen for each class and what the
//! kernel's answer is held to — the fork's day as the shipped binary ranks it
//! (D53) with the owner's D57 rule applied by its property (P46, P47), P45's
//! rule on a break day, §9.1's what-if with P44 by its property, and gaps
//! 550/551/435 as the only row classes the day may differ by.
//!
//! **The arm that survives R3** is everything outside the one region below:
//! it reads the frozen lines and the kernel, and nothing of the fork's planner.
//! **The fork's arm** — the re-bless, and the check that the frozen answers are
//! still the fork's on this tree — plans with `planner::plan` and is one region,
//! `BEGIN THE FORK PLANNER` … `END THE FORK PLANNER`, which R3 deletes whole;
//! [`the_fork_half_of_this_suite_is_one_region`] holds this file to that.
//!
//! **Since W-37 track H the file answers to the owner's D64 by a test, not a
//! sentence** (README gaps 3133, 3138, 3123): every world is the shared
//! generator's own draw ([`every_frozen_world_is_the_generators_own_draw`]) and
//! one the shipped binary can hold
//! ([`every_frozen_world_is_one_the_binary_holds`]); the re-bless and the
//! re-draw refuse, by name, a change that is neither D64(a) — a registered
//! parity number whose flag the line carries — nor D64(b) — a world the binary
//! cannot hold, checked; and D61's worlds, the pause the binary logs at a wall's
//! start, are frozen as `d61` lines derived from the primary ones.

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
#[path = "support/srcwalk.rs"]
mod srcwalk;

use std::collections::BTreeSet;

use chrono::{DateTime, Duration};
use chrono_tz::Tz;
use serde_json::Value;
use tm_core::config::Config;
use tm_core::dayplan::SegKind;

use forkclass::{class_of, class_space, compare_line, frozen_lines, Built, ClassTally, ClassWorld, DayShape, Run};

fn tz() -> Tz {
    Config::default().tz
}

/// **The kernel plans every frozen class as the fork planned it**, by value,
/// with the declared classes and nothing else (see `support/forkclass.rs`).
#[test]
fn the_kernel_plans_every_generated_class_the_fork_planned() {
    let mut t = ClassTally::default();
    let mut findings = Vec::new();
    for line in frozen_lines() {
        findings.extend(compare_line(line, &mut t));
    }
    let line = t.line(findings.len());
    println!("{line}");
    assert!(line.starts_with(&format!("frozen fork classes — {} class(es)", class_space().len())), "{line}");
    assert!(
        findings.is_empty(),
        "{} disagreement(s) with the frozen fork classes (each must be one of the declared classes):\n  {}",
        findings.len(),
        findings.join("\n  ")
    );
    // **The floors** (AGENTS §9.2): every declared divergence was compared on
    // at least one day, so none of them is asserted on nothing.
    assert_eq!(t.classes.len(), class_space().len(), "every class was compared: {t:?}");
    assert!(t.p45_running > 0 && t.p45_overrun > 0, "P45 was checked running and overrun: {t:?}");
    assert!(t.p45_shipped_over > 0, "no frozen break day shows the shipped fork planning over the break: {t:?}");
    assert!(t.p46 > 0, "no P46 comparand day: {t:?}");
    assert!(t.p47 > 0, "no P47 comparand day: {t:?}");
    assert!(t.p51 > 0, "no P51 comparand day: D60's order is asserted on no frozen day: {t:?}");
    assert!(t.whatifs > 0 && t.whatif_ids > 0, "no what-if with an id in it was compared: {t:?}");
    assert!(t.day.break_rows_551 > 0, "gap 551's class counted no row: {t:?}");
    assert!(t.day.mult_rows_550 > 0, "gap 550's class counted no row: {t:?}");
    assert!(
        t.day.underused_notes > 0 && t.notes_rendered == t.day.underused_notes,
        "every under-used note left to the renderer is rendered as the fork wrote it: {t:?}"
    );
}

/// **The frozen file holds a day of every class the arms draw, and nothing
/// else** — the property that makes it a comparand keyed by class and not a
/// list of days. Each stored world classifies as its own key (a line may not
/// choose its class; `compare_line` asserts it again at comparison).
#[test]
fn the_frozen_file_holds_every_class_the_arms_draw() {
    let space: BTreeSet<String> = class_space().into_iter().map(|c| c.key()).collect();
    let mut held = BTreeSet::new();
    let mut secondary = Vec::new();
    for line in frozen_lines() {
        let key = line["class"].as_str().expect("a frozen line names its class").to_string();
        let w = ClassWorld::of_json(&line["world"], tz()).unwrap_or_else(|e| panic!("{key}: {e}"));
        let c = class_of(&Built::of(w)).key();
        assert_eq!(c, key, "a frozen line's world classifies as another class");
        // A SECONDARY day is drawn for a floor no class representative reached,
        // and says which; a class has exactly one primary day.
        if let Some(why) = line["secondary"].as_str() {
            assert!(SECONDARY_FLOORS.contains(&why), "{key}: a secondary day for `{why}`, which no floor asks for");
            secondary.push(format!("{key} ({why})"));
            continue;
        }
        assert!(held.insert(key.clone()), "two primary frozen lines for `{key}`");
    }
    let missing: Vec<&String> = space.difference(&held).collect();
    let extra: Vec<&String> = held.difference(&space).collect();
    assert!(missing.is_empty(), "classes an arm draws with no frozen day: {missing:?}");
    assert!(extra.is_empty(), "frozen days of a class no arm draws: {extra:?}");
    println!(
        "frozen fork classes: {} of the {} classes the arms draw, and {} secondary day(s): {}",
        held.len(),
        space.len(),
        secondary.len(),
        secondary.join(", ")
    );
}

/// The floors a SECONDARY frozen day may be drawn for: each is one
/// [`the_frozen_days_cover_what_the_arms_floors_demand`] asserts. `d61` is not
/// drawn but DERIVED (W-37, README gap 3123): the world the binary holds once
/// the owner's D61 has logged a wall's pause, one per instant
/// `forkclass::d61_worlds` answers for a primary line, and
/// [`the_frozen_d61_worlds_are_every_one_d61_derives`] holds the file to
/// exactly that set.
const SECONDARY_FLOORS: [&str; 3] = ["rest_debt", "whatif", "d61"];

/// **What the frozen days cover beyond their class**, counted off the FORK's
/// frozen days (never the kernel's, which is the value under test): each floor
/// is one the differential arms hold their own random draws to, so the frozen
/// set is not narrower than the arms it stands in for at R3.
#[test]
fn the_frozen_days_cover_what_the_arms_floors_demand() {
    let mut kinds = BTreeSet::new();
    let mut n = [0usize; 20];
    for line in frozen_lines() {
        let day = &line["day"]["day"];
        for s in day["segments"].as_array().map(Vec::as_slice).unwrap_or_default() {
            let k = s["kind"].as_str().map(str::to_string).unwrap_or_else(|| {
                // A batch serialises as `{"batch": [..]}`.
                s["kind"].as_object().and_then(|o| o.keys().next().cloned()).unwrap_or_default()
            });
            kinds.insert(k);
            let m = s["flags"]["multiplier"].as_f64();
            n[0] += usize::from(m.is_some_and(|m| m != 1.0));
            n[1] += usize::from(s["flags"]["open"] == true);
        }
        let d = &day["diagnostics"];
        let len = |k: &str| d[k].as_array().map_or(0, Vec::len);
        n[2] += usize::from(d["rest_debt_min"].as_u64().unwrap_or(0) > 0);
        n[3] += len("waiting");
        n[4] += len("blocked");
        n[5] += len("impossible");
        n[6] += len("hot");
        n[7] += len("conflicts");
        n[8] += len("underused");
        n[9] += len("dropped_tail");
        n[10] += len("notes");
        n[11] += usize::from(d["a_capacity_lost"].as_u64().unwrap_or(0) > 0);
        n[12] += len("deferred");
        // The three kinds of step-8 note, by the fork's own prose.
        for note in d["notes"].as_array().map(Vec::as_slice).unwrap_or_default().iter().filter_map(Value::as_str) {
            n[13] += usize::from(note.starts_with("travel day"));
            n[14] += usize::from(note.contains("no free"));
            n[15] += usize::from(note.starts_with("budget spent"));
        }
        // §9.1's what-if: the ids the COMPARED side drops (the estimate's on a
        // parity-P44 day, the TUI's otherwise).
        let w = &line["whatif"];
        if !w.is_null() {
            let side = if w["full"] == w["est"] { &w["full"] } else { &w["est"] };
            n[16] += side["removed"].as_array().map_or(0, Vec::len);
        }
        // D61's world: a running block the log paused at a wall's start (W-37,
        // README gap 3123), read off the world — the stored log's `pause` of
        // the block `.tm/state.json` runs.
        let world = &line["world"];
        let run = world["state"]["active"]["id"].as_str().unwrap_or("<none>");
        n[17] += usize::from(world["log"].as_str().unwrap_or_default().lines().any(|l| {
            serde_json::from_str::<Value>(l).is_ok_and(|e| e["ev"] == "pause" && e["id"] == run)
        }));
        // An interruption the log holds open (README gap 3138), and one over a
        // block it names — `tm interrupt`'s two shapes.
        let log: Vec<Value> = world["log"].as_str().unwrap_or_default().lines().filter_map(|l| serde_json::from_str(l).ok()).collect();
        n[18] += usize::from(log.iter().any(|e| e["ev"] == "interrupt"));
        n[19] += usize::from(log.iter().any(|e| e["ev"] == "interrupt" && e["id"].is_string()));
    }
    println!("frozen fork classes cover row kinds {kinds:?}; counts {n:?}");
    for k in ["block", "batch", "break", "routine", "wall", "rest", "optional", "lost"] {
        assert!(kinds.contains(k), "no frozen day holds a `{k}` row: {kinds:?}");
    }
    let names = [
        "rows at a multiplier other than 1.0", "open rows", "days with rest debt", "waiting ids",
        "blocked ids", "impossible tuples", "hot ids", "conflicts", "underused tuples",
        "dropped-tail ids", "notes", "days losing A-capacity", "deferred ids", "travel-day notes",
        "no-position notes", "budget-spent notes", "what-if drops",
        "days whose running block a wall's logged pause stopped (D61)", "days with a logged open interruption",
        "days whose logged interruption names the block it paused",
    ];
    for (i, name) in names.iter().enumerate() {
        assert!(n[i] > 0, "the frozen days hold no {name}: {n:?}");
    }
    // A what-if that drops one id is one comparison of a list; the secondary
    // `whatif` day is drawn so the list is compared at two.
    assert!(n[16] >= 2, "the frozen what-ifs drop {} id(s) on the compared side", n[16]);
}

/// **The class enumerations are derived, and the space is the rule's**: eight
/// run states and five shapes by their exhaustive chains, the words distinct,
/// and the only pairs left out the ones no arm draws — a running break on a
/// travel or spent day.
#[test]
fn the_class_space_is_the_product_less_what_no_arm_draws() {
    let runs = Run::all();
    let shapes = DayShape::all();
    assert_eq!((runs.len(), shapes.len()), (8, 5));
    let words: BTreeSet<&str> = runs.iter().map(|r| r.word()).chain(shapes.iter().map(|s| s.word())).collect();
    assert_eq!(words.len(), 13, "two coordinates share a word");
    let space = class_space();
    let left_out: Vec<String> = runs
        .iter()
        .flat_map(|r| shapes.iter().map(move |s| forkclass::Class { run: *r, shape: *s }))
        .filter(|c| !space.contains(c))
        .map(|c| c.key())
        .collect();
    assert_eq!(
        left_out,
        ["break/travel", "break/spent", "break-block/travel", "break-block/spent"],
        "the space leaves out exactly the pairs no arm draws"
    );
}

/// **P45's rule bites, and does not over-bite** (AGENTS §5.8): on every
/// frozen break day the kernel's own day passes it, and each of four
/// perturbations of that day — the Break row moved, its `open` mark flipped, a
/// block laid over it, a step-5 row pulled back before its end — fails it by
/// name.
#[test]
fn the_p45_rule_accepts_the_kernel_and_bites_a_perturbation() {
    let (mut checked, mut running, mut early_checked) = (0, 0, 0);
    for line in frozen_lines() {
        let w = ClassWorld::of_json(&line["world"], tz()).expect("a stored world");
        let Some(brk) = w.state.break_.clone().filter(|b| b.started.is_some()) else { continue };
        let b = Built::of(w);
        let k = forkclass::kernel_answer(&b).expect("the kernel plans a break day");
        let now = b.world.now;
        let started = tm_core::capacity::local_dt(b.cfg.tz, b.date(), brk.started.expect("filtered"));
        let rule = |day: &tm_core::dayplan::DayPlan| {
            forkclass::p45_rule(day, started, brk.planned_min, brk.place.as_deref(), now, b.day_bounds())
        };
        let (lo, hi, open) = rule(&k.day).unwrap_or_else(|e| panic!("{}: {e}", line["class"]));
        let at = k.day.segments.iter().position(|s| s.kind == SegKind::Break).expect("the Break row");
        let mut moved = k.day.clone();
        moved.segments[at].end = hi + Duration::minutes(1);
        assert!(rule(&moved).is_err(), "a moved Break row passed");
        let mut flipped = k.day.clone();
        flipped.segments[at].flags.open = !flipped.segments[at].flags.open;
        assert!(rule(&flipped).is_err(), "a flipped `open` passed");
        checked += 1;
        // An OVERRUN break ends at `now` and nothing is placed before `now`, so
        // the two perturbations below are about a break that is still running.
        if open {
            continue;
        }
        let mut over = k.day.clone();
        let mut blk = over.segments[at].clone();
        blk.kind = SegKind::Block;
        blk.start = now.max(lo);
        blk.end = hi;
        blk.energy = Some(3);
        over.segments.push(blk);
        assert!(rule(&over).is_err(), "a block over the break passed");
        if let Some(i) = k.day.segments.iter().position(|s| s.kind.is_work() && s.energy.is_some() && s.start >= hi) {
            let mut early = k.day.clone();
            let d = early.segments[i].end - early.segments[i].start;
            early.segments[i].start = now.max(hi - Duration::minutes(1));
            early.segments[i].end = early.segments[i].start + d;
            assert!(rule(&early).is_err(), "a step-5 row before the break's end passed");
            early_checked += 1;
        }
        running += 1;
    }
    assert!(checked >= 2 && running >= 1, "{checked} frozen break day(s), {running} of them running");
    assert!(early_checked >= 1, "no running break day had a step-5 row after it to pull back");
}

/// **R3's deletion is mechanical here**, as `planner_fixtures.rs`' is: every
/// line that reaches the fork's planner sits inside this file's one region.
#[test]
fn the_fork_half_of_this_suite_is_one_region() {
    let here = env!("CARGO_MANIFEST_DIR");
    for file in ["tests/planner_classes.rs", "tests/support/forkclass.rs"] {
        let text = std::fs::read_to_string(format!("{here}/{file}")).expect("the source reads");
        let scan = forkday::fork_scan(&text);
        assert!(scan.escapes.is_empty(), "{file}: the fork reached outside its region:\n  {}", scan.escapes.join("\n  "));
    }
}

/// **The files a test may reach the fork's planner from OUTSIDE one region**:
/// W-27's shape, an enumeration you join to be EXEMPT and never to be covered,
/// each line dated with its EXIT. A file listed here that has become clean
/// FAILS as STALE, so the list only shrinks. **Empty since W-37 track H**: its
/// one line, `tm/tests/planner_invariants.rs` (README gap 3084), went STALE when
/// that file's arms moved into one region and its §8.3 arm was asked of the
/// kernel — so it was deleted, and every test file is held to one region.
const OUTSIDE_A_REGION: [(&str, &str); 0] = [];

/// **Every test that reaches the fork's planner keeps it in ONE region** —
/// the property `planner_fixtures.rs` holds of two files, held of EVERY `.rs`
/// file under a `tests/` directory of the repository (`srcwalk`'s walk, its
/// prune rule): R3 deletes the regions, and nothing else of the fork's may be
/// left to find by reading (README gap 2872). A file with no region may name
/// the fork nowhere in code, which after R3 is the assertion that every
/// comparand moved.
#[test]
fn every_test_that_reaches_the_fork_keeps_it_in_one_region() {
    let mut bad = Vec::new();
    let mut regions = Vec::new();
    let mut exempt_seen = BTreeSet::new();
    for (label, text) in srcwalk::every_rust_file() {
        if !label.split('/').any(|seg| seg == "tests") {
            continue;
        }
        let scan = forkday::fork_scan(&text);
        if !scan.deleted {
            regions.push(label.clone());
        }
        if let Some((_, why)) = OUTSIDE_A_REGION.iter().find(|(f, _)| *f == label) {
            exempt_seen.insert(label.clone());
            assert!(why.contains("EXIT") && why.starts_with("20"), "{label}: an exemption needs a date and an EXIT");
            if scan.escapes.is_empty() {
                bad.push(format!("STALE: {label} reaches the fork from no line outside a region — delete its exemption"));
            }
            continue;
        }
        if !scan.escapes.is_empty() {
            bad.push(format!("{label}: the fork reached outside one region:\n    {}", scan.escapes.join("\n    ")));
        }
    }
    for (f, _) in OUTSIDE_A_REGION {
        if !exempt_seen.contains(f) {
            bad.push(format!("STALE: {f} is exempt and is not a test file of this tree"));
        }
    }
    println!("files with one fork region: {}", regions.join(", "));
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    // While the fork is here the scan must SEE its regions (a guard that reads
    // no banner is reading nothing); once R3 deletes `planner.rs`, a region left
    // behind is dead code and none may remain.
    let fork_here = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-core/src/planner.rs").exists();
    if fork_here {
        assert!(regions.len() >= 7, "the walk found {} fork regions: {regions:?}", regions.len());
    } else {
        assert!(regions.is_empty(), "the fork is gone and regions remain: {regions:?}");
    }
}

/// **A stored world reads back as the bytes it was written from** — the frozen
/// file is its own input, so `ClassWorld`'s two directions are one another's
/// inverse on every line of it.
#[test]
fn every_frozen_world_round_trips_through_its_json() {
    for line in frozen_lines() {
        let w = ClassWorld::of_json(&line["world"], tz()).expect("a stored world");
        assert_eq!(w.to_json(), line["world"], "{}: the world does not round-trip", line["class"]);
    }
}

/// **Every frozen day says which draw it came from**: the generator's `Case`,
/// the arm whose widenings were applied, the ChaCha seed's text and the draw's
/// index — what the harness README gap 3080 names needs to draw it again (the
/// 35 primary days were re-drawn from those, byte for byte, before this
/// landed).
#[test]
fn every_frozen_day_says_which_draw_it_came_from() {
    for line in frozen_lines() {
        let case = line["case"].as_str().unwrap_or_default();
        assert!(case.starts_with("Case {"), "{}: no generator draw recorded: {case:?}", line["class"]);
        assert!(
            ["base", "hash", "w35", "step8"].contains(&line["arm"].as_str().unwrap_or_default()),
            "{}: no arm recorded",
            line["class"]
        );
        assert!(line["seed"].as_str().is_some_and(|s| s.starts_with("W-36 track H")), "{}: no seed", line["class"]);
        assert!(line["draw"].as_u64().is_some(), "{}: no draw index", line["class"]);
    }
}

/// **Every frozen world is the shared generator's own draw** (README gap 3080):
/// each line's world is RE-DRAWN at its recorded seed, index and arm
/// (`forkclass::draws_of_line`, over `support/plangen.rs`), and a derived D61
/// world is re-derived from its re-drawn parent — and must be the stored world
/// byte for byte. Until W-37 the provenance was four fields this suite checked
/// for presence (`every_frozen_day_says_which_draw_it_came_from`); now it is a
/// fact, and a change to the generator that moves a frozen world fails here by
/// name, where the next step must decide it under the owner's D64.
#[test]
fn every_frozen_world_is_the_generators_own_draw() {
    let tz = tz();
    let mut bad = Vec::new();
    let (mut drawn, mut derived) = (0usize, 0usize);
    for line in frozen_lines() {
        let key = line["class"].as_str().unwrap_or("<no class>");
        let draws = forkclass::draws_of_line(line);
        if draws.is_empty() {
            bad.push(format!("{key}: no draw at seed {} index {} reproduces arm {}", line["seed"], line["draw"], line["arm"]));
            continue;
        }
        let at = line["derived"]["now"]
            .as_str()
            .and_then(|t| DateTime::parse_from_rfc3339(t).ok())
            .map(|t| t.with_timezone(&tz));
        // The world each candidate draw builds — re-derived through D61 for a derived line.
        let worlds: Vec<ClassWorld> = draws
            .iter()
            .map(forkclass::world_of)
            .filter_map(|w| match at {
                None => Some(w),
                Some(at) => forkclass::d61_worlds(&w).into_iter().find(|(d, _)| d.now == at).map(|(d, _)| d),
            })
            .collect();
        if at.is_some() {
            derived += 1;
        } else {
            drawn += 1;
        }
        let stored = ClassWorld::of_json(&line["world"], tz).unwrap_or_else(|e| panic!("{key}: {e}"));
        if !worlds.contains(&stored) {
            let Some(world) = worlds.into_iter().next() else {
                bad.push(format!("{key}: D61 derives no world at {:?} from its parent draw", line["derived"]["now"]));
                continue;
            };
            let why = if world.log != stored.log {
                "the log"
            } else if world.state != stored.state {
                "`.tm/state.json`"
            } else if world.docs != stored.docs {
                "the documents"
            } else {
                "`now` or the multiplier"
            };
            bad.push(format!("{key}{}: the re-draw differs in {why}", line["secondary"].as_str().map(|s| format!(" ({s})")).unwrap_or_default()));
        }
    }
    println!("frozen worlds re-drawn from the tree: {drawn} drawn and {derived} derived, {} differ", bad.len());
    assert!(bad.is_empty(), "frozen worlds that are not the generator's draw:\n  {}", bad.join("\n  "));
}

/// **Every frozen world is one the shipped binary can hold** (owner D64(b),
/// README gap 3138): `forkclass::binary_holds` on every line — the cache and
/// the log agree on what is open, a running break began after the last
/// `start`/`done`/`stop`, a paused block has a reason the binary pauses one
/// for. Twelve lines failed it until W-37 (the ten interruptions in
/// `.tm/state.json` alone and two breaks begun before the block under them);
/// each was re-drawn and carries `d64b`.
#[test]
fn every_frozen_world_is_one_the_binary_holds() {
    let mut bad = Vec::new();
    for line in frozen_lines() {
        let key = line["class"].as_str().unwrap_or("<no class>");
        let w = ClassWorld::of_json(&line["world"], tz()).unwrap_or_else(|e| panic!("{key}: {e}"));
        if let Err(e) = forkclass::binary_holds(&Built::of(w)) {
            bad.push(format!("{key}{}: {}", line["secondary"].as_str().map(|s| format!(" ({s})")).unwrap_or_default(), e.join("; ")));
        }
    }
    println!("frozen worlds the binary can hold: {} of {}", frozen_lines().len() - bad.len(), frozen_lines().len());
    assert!(bad.is_empty(), "frozen worlds the shipped binary cannot hold (owner D64(b)):\n  {}", bad.join("\n  "));
}

/// **A world's running state is read off its LOG, as the binary reads it** (owner D64(b),
/// README gap 3138; `forkclass::running`): an interrupted world whose `interrupt` line is taken
/// out of the log — the pre-W-37 shape, `.tm/state.json` alone saying interrupted — is NOT an
/// interrupted world, and the same world with the line kept and the state's interruption taken
/// out still is; a running block the log holds open runs whatever the cache says, and one only
/// the cache names does not. Until W-37 `class_of` read the cache, and nothing here could tell.
#[test]
fn a_worlds_run_state_is_read_off_its_log() {
    let tz = tz();
    let world = |class: &str| {
        let line = frozen_lines().iter().find(|l| l["class"] == class && l["secondary"].is_null()).expect("a primary line");
        ClassWorld::of_json(&line["world"], tz).expect("a stored world")
    };
    let run = |w: &ClassWorld| class_of(&Built::of(w.clone())).run;
    let w = world("interrupted/lounge");
    assert_eq!(run(&w), Run::Interrupted);
    let mut unlogged = w.clone();
    unlogged.log = w.log.lines().filter(|l| !l.contains("\"ev\":\"interrupt\"")).map(|l| format!("{l}\n")).collect();
    assert_ne!(unlogged.log, w.log, "the world logs its interruption");
    assert_eq!(run(&unlogged), Run::Idle, "an interruption in .tm/state.json alone classified as interrupted");
    let mut uncached = w.clone();
    uncached.state.interrupt = None;
    assert_eq!(run(&uncached), Run::Interrupted, "an interruption the log holds open was not read");
    let r = world("running/lounge");
    let mut cacheless = r.clone();
    cacheless.state.active = None;
    assert_eq!(run(&cacheless), Run::Running, "a block the log holds open was not read");
    let mut logless = r.clone();
    logless.log = r.log.lines().filter(|l| !l.contains(&format!("\"ev\":\"start\",\"id\":\"{}\"", r.state.active.as_ref().expect("a block").id))).map(|l| format!("{l}\n")).collect();
    assert_eq!(run(&logless), Run::Idle, "a block only .tm/state.json names classified as running");
}

/// **`binary_holds` bites, clause by clause, and does not over-bite** (AGENTS
/// §5.8): each of the six clauses fails, by its number, on a frozen world
/// bent into a state the binary cannot hold — the pre-W-37 shape among them —
/// and the unbent worlds pass (the test above).
#[test]
fn every_clause_of_binary_holds_bites() {
    let tz = tz();
    let world = |class: &str| {
        let line = frozen_lines().iter().find(|l| l["class"] == class && l["secondary"].is_null()).expect("a primary line");
        ClassWorld::of_json(&line["world"], tz).expect("a stored world")
    };
    let fails = |w: &ClassWorld, clause: &str| {
        let e = forkclass::binary_holds(&Built::of(w.clone())).err().unwrap_or_default();
        assert!(e.iter().any(|m| m.starts_with(clause)), "clause {clause} did not bite: {e:?}");
    };
    // 1: the cache runs no block while the log holds one open.
    let mut w = world("running/lounge");
    w.state.active = None;
    fails(&w, "1:");
    // 2: the interruption in `.tm/state.json` alone — the shape gap 3138 found.
    let mut w = world("interrupted/lounge");
    w.log = w.log.lines().filter(|l| !l.contains("\"ev\":\"interrupt\"")).map(|l| format!("{l}\n")).collect();
    fails(&w, "2:");
    // 3: a running break begun before the block under it.
    let mut w = world("break-block/lounge");
    let started = w.state.active.as_ref().expect("a block").started;
    if let Some(b) = w.state.break_.as_mut() {
        b.started = Some(started - Duration::minutes(5));
    }
    fails(&w, "3:");
    // 4: an interrupted block left running, and a running block paused for nothing.
    let mut w = world("interrupted-block/lounge");
    assert!(w.state.interrupt.as_ref().is_some_and(|i| i.id.is_some()), "interrupted-block/lounge's interruption names its block");
    if let Some(a) = w.state.active.as_mut() {
        a.paused = false;
    }
    fails(&w, "4:");
    let mut w = world("running/lounge");
    if let Some(a) = w.state.active.as_mut() {
        a.paused = true;
    }
    fails(&w, "4:");
    // 5: a cache the log does not rebuild — the stored window moved an hour off the one
    // `tm arrive` logged (the W-37 auditor's shape), and the location flipped.
    let mut w = world("idle/lounge");
    if let Some((from, to)) = w.state.window {
        w.state.window = Some((from, to + Duration::hours(1)));
    }
    fails(&w, "5:");
    let mut w = world("idle/lounge");
    w.state.loc = Some("home".to_string());
    fails(&w, "5:");
    // 6: a world not at rest — a meeting's pause taken out of the log, which the
    // binary's housekeeping then writes.
    let mut w = world("wall-on-now/lounge");
    let before = w.log.clone();
    w.log = w.log.lines().filter(|l| !l.contains("\"ev\":\"pause\"")).map(|l| format!("{l}\n")).collect();
    assert_ne!(w.log, before, "wall-on-now/lounge logs its meeting's pause");
    fails(&w, "6:");
}

/// **Every parity flag a frozen line carries names a REGISTERED number** (the
/// owner's D64(a)): the comparand's flags are named by their number
/// (`d57.p46`, `d57.p47`, `d60.p51`, and whatever flag a later step adds), and
/// `forkclass::parity_flags` reads every key spelled `p<n>` on a line, so a
/// flag for a number `kernel/parity.txt` does not register fails here by name —
/// a property of the keys, not a list of three.
#[test]
fn every_parity_flag_names_a_registered_number() {
    let registered = forkclass::registered_parity();
    let mut seen = BTreeSet::new();
    let mut bad = Vec::new();
    for line in frozen_lines() {
        for (n, _) in forkclass::parity_flags(line) {
            seen.insert(n);
            if !registered.contains(&n) {
                bad.push(format!("{}: a flag for P{n}, which kernel/parity.txt does not register", line["class"]));
            }
        }
    }
    println!("parity flags on the frozen lines: {:?}", seen.iter().map(|n| format!("P{n}")).collect::<Vec<_>>());
    assert!(seen.len() >= 3, "the frozen lines carry the flags of {seen:?}, not the comparand's three");
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// **Every re-drawn world says why, and the why is a checked fact** (the
/// owner's D64(b)): a line carrying `d64b` names the step's dated reason, which
/// names D64(b), and the clauses of `forkclass::binary_holds` its OLD world
/// failed — the re-draw ([`the_frozen_class_worlds_are_redrawn`]) refuses a
/// world that failed none — and its new world holds (the test above).
#[test]
fn every_redrawn_world_says_why() {
    let mut n = 0;
    for line in frozen_lines().iter().filter(|l| !l["d64b"].is_null()) {
        let key = line["class"].as_str().unwrap_or("<no class>");
        let why = line["d64b"]["why"].as_str().unwrap_or_default();
        assert!(why.starts_with("20") && why.contains("D64(b)"), "{key}: `d64b.why` is not dated or does not name D64(b): {why:?}");
        let held = line["d64b"]["held"].as_array().map(Vec::as_slice).unwrap_or_default();
        assert!(!held.is_empty(), "{key}: a re-drawn world names no clause its old world failed");
        for c in held {
            let c = c.as_str().unwrap_or_default();
            // A clause is `<n>:` — a property of the text, so a clause a later step adds is
            // one without an edit here (it listed "1:".."4:" until the W-37 repair).
            let n: String = c.chars().take_while(char::is_ascii_digit).collect();
            assert!(!n.is_empty() && c[n.len()..].starts_with(':'), "{key}: `{c}` is not a clause of binary_holds");
        }
        n += 1;
    }
    println!("re-drawn frozen worlds: {n}");
    assert!(n >= 12, "the twelve worlds W-37 re-drew under D64(b) carry `d64b`: {n}");
}

/// **The frozen D61 worlds are exactly the worlds D61 derives** (README gap
/// 3123): for every PRIMARY line, `forkclass::d61_worlds` of its world — the
/// pause the binary logs at a wall's start, at `now` and twenty minutes into
/// the meeting — is a `d61` secondary line of the same class carrying that
/// world, and no `d61` line is anything else. A property of the file, so a
/// primary re-drawn later cannot leave its D61 lines stale or missing.
#[test]
fn the_frozen_d61_worlds_are_every_one_d61_derives() {
    let tz = tz();
    let mut want = BTreeSet::new();
    for line in frozen_lines().iter().filter(|l| l["secondary"].is_null()) {
        let w = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        for (d, pause) in forkclass::d61_worlds(&w) {
            want.insert((line["class"].as_str().unwrap_or_default().to_string(), pause.to_rfc3339(), d.to_json().to_string()));
        }
    }
    let have: BTreeSet<(String, String, String)> = frozen_lines()
        .iter()
        .filter(|l| l["secondary"] == "d61")
        .map(|l| {
            assert_eq!(l["derived"]["from"], l["class"], "a d61 line is derived from a line of its own class");
            (l["class"].as_str().unwrap_or_default().to_string(), l["derived"]["pause"].as_str().unwrap_or_default().to_string(), l["world"].to_string())
        })
        .collect();
    let missing: Vec<String> = want.difference(&have).map(|w| format!("{} at pause {}", w.0, w.1)).collect();
    let extra: Vec<String> = have.difference(&want).map(|w| format!("{} at pause {}", w.0, w.1)).collect();
    println!("frozen D61 worlds: {} derived, {} held", want.len(), have.len());
    assert!(missing.is_empty() && extra.is_empty(), "D61 worlds missing {missing:?}, held and not derived {extra:?}");
    assert!(!want.is_empty(), "no primary line's world is one D61 pauses");
}

/// **D61's derivation logs every wall the running block ran into, in order** —
/// `stop_the_timer_at_walls`' loop, not only the meeting covering `now`: on the frozen
/// `wall-on-now/lounge` world (the block from 09:22, the meeting from 10:00) with a ten-minute
/// wall added at 09:30, the derived log gains `pause` 09:30, `unpause` 09:40 and `pause`
/// 10:00, in that order, and the block is paused. No primary world holds an earlier wall
/// today, so this is the only thing that asks the loop's `unpause` branch.
#[test]
fn d61_logs_every_wall_the_block_ran_into() {
    let line = frozen_lines().iter().find(|l| l["class"] == "wall-on-now/lounge" && l["secondary"].is_null()).expect("the primary line");
    // The stored world is at rest (README gap 3340): the derivation starts from it as it
    // stood before the housekeeping logged its meeting.
    let mut w = forkclass::before_housekeeping(&ClassWorld::of_json(&line["world"], tz()).expect("a stored world"));
    let cal = w.docs.iter_mut().find(|(p, _)| p.starts_with("calendar/")).expect("a calendar document");
    cal.1.push_str("- [ ] 3 Coffee at:2026-09-07T09:30/09:40 ^wxa\n");
    let derived = forkclass::d61_worlds(&w);
    let (d, pause) = derived.first().expect("D61 derives the world");
    assert_eq!(pause.format("%H:%M").to_string(), "10:00");
    let added: Vec<(String, String)> = d.log[w.log.len()..]
        .lines()
        .map(|l| {
            let v: Value = serde_json::from_str(l).expect("a log line");
            (v["ev"].as_str().unwrap_or_default().to_string(), v["t"].as_str().unwrap_or_default()[11..16].to_string())
        })
        .collect();
    let want: Vec<(String, String)> = [("pause", "09:30"), ("unpause", "09:40"), ("pause", "10:00")]
        .iter()
        .map(|(e, t)| ((*e).to_string(), (*t).to_string()))
        .collect();
    assert_eq!(added, want);
    assert!(d.state.active.as_ref().is_some_and(|a| a.paused), "the block is paused");
}

/// **D61's pause reaches the kernel's day** — the non-vacuity the W-36 land
/// step's fork-region test asserted, kept when its worlds were frozen into
/// `d61` lines (README gap 3123): the kernel's day for a D61 world differs
/// from its day for the parent world at the same instant, so the comparison of
/// the `d61` lines is not the parent's comparison again.
#[test]
fn the_pause_d61_logs_reaches_the_kernels_day() {
    let tz = tz();
    let (mut n, mut moved) = (0usize, 0usize);
    for line in frozen_lines().iter().filter(|l| l["secondary"] == "d61") {
        let w = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        let parent = frozen_lines()
            .iter()
            .find(|l| l["class"] == line["derived"]["from"] && l["secondary"].is_null())
            .expect("the parent line");
        // The parent is at rest (README gap 3340), so the world the pause is compared
        // against is the D61 world as it stood before the housekeeping logged it.
        let _ = parent;
        let p = forkclass::before_housekeeping(&w);
        let k = forkclass::kernel_answer(&Built::of(w)).expect("the kernel plans the D61 world");
        let kp = forkclass::kernel_answer(&Built::of(p)).expect("the kernel plans the parent");
        n += 1;
        moved += usize::from(k.day != kp.day);
    }
    println!("D61 worlds: the logged pause moved the kernel's day on {moved} of {n}");
    assert!(n > 0 && moved > 0, "the logged pause changed the kernel's day on none of {n} D61 worlds");
}

/// **The D61 worlds are the pause the shipped binary logs** (W-37's land step, README gap
/// 3321). Track H derives a `d61` line's world from its parent by `forkclass::d61_worlds`, a
/// statement of D61's rule in the test harness; track T moved the rule the binary runs into the
/// kernel (`WallTimer`, README gap 3139), so the two are two definitions of one rule, and this
/// is what compares them: each parent world is written to disk as the binary reads it (its
/// documents, `.tm/log.jsonl`, `.tm/state.json`, an empty `config.toml` =
/// `Config::default()`), `tm now` runs at the derived world's instant, and the lines the binary
/// appends to the log must be the lines the derivation appended, value for value, with the
/// block left paused. The same is asked of the one world that reaches the rule's `unpause`
/// branch (the lounge world with a ten-minute wall at 09:30, `d61_logs_every_wall_the_block_ran_into`).
#[test]
fn every_d61_world_is_the_pause_the_binary_logs() {
    fn drive(parent: &ClassWorld, at: DateTime<Tz>) -> (Vec<Value>, bool) {
        let dir = tempfile::TempDir::new().expect("a temp dir");
        let plan = dir.path().join("plan");
        for (path, text) in &parent.docs {
            let f = plan.join(path);
            std::fs::create_dir_all(f.parent().expect("a parent")).expect("a directory");
            std::fs::write(&f, text).expect("a document");
        }
        std::fs::create_dir_all(plan.join(".tm")).expect(".tm");
        std::fs::write(plan.join(".tm/log.jsonl"), &parent.log).expect("the log");
        std::fs::write(plan.join(".tm/state.json"), serde_json::to_string(&parent.state).expect("a state")).expect("the state");
        std::fs::write(plan.join("config.toml"), "").expect("the config");
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_tm"))
            .arg("--dir").arg(&plan).arg("--now").arg(at.to_rfc3339()).arg("now")
            .output().expect("tm runs");
        assert!(out.status.success(), "tm now at {at}: {}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        let log = std::fs::read_to_string(plan.join(".tm/log.jsonl")).expect("the log");
        assert!(log.starts_with(&parent.log), "the binary rewrote the log it was handed");
        let added = log[parent.log.len()..].lines().map(|l| serde_json::from_str(l).expect("a log line")).collect();
        let st: Value = serde_json::from_str(&std::fs::read_to_string(plan.join(".tm/state.json")).expect("the state")).expect("state JSON");
        (added, st["active"]["paused"] == true)
    }
    let added_by = |parent: &ClassWorld, d: &ClassWorld| -> Vec<Value> {
        d.log[parent.log.len()..].lines().map(|l| serde_json::from_str(l).expect("a log line")).collect()
    };
    let tz = tz();
    let mut n = 0usize;
    for line in frozen_lines().iter().filter(|l| l["secondary"] == "d61") {
        let d = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        let parent = frozen_lines()
            .iter()
            .find(|l| l["class"] == line["derived"]["from"] && l["secondary"].is_null())
            .expect("the parent line");
        // The parent is at rest (README gap 3340): drive it as it stood before the
        // housekeeping, and the binary must log exactly the marks the stored world holds.
        let p = forkclass::before_housekeeping(&ClassWorld::of_json(&parent["world"], tz).expect("a stored world"));
        let (got, paused) = drive(&p, d.now);
        assert_eq!(got, added_by(&p, &d), "{} at {}: the binary logged another pause than the derivation", line["class"], d.now);
        assert!(paused, "{} at {}: the binary left the block running", line["class"], d.now);
        n += 1;
    }
    let line = frozen_lines().iter().find(|l| l["class"] == "wall-on-now/lounge" && l["secondary"].is_null()).expect("the primary line");
    let mut w = forkclass::before_housekeeping(&ClassWorld::of_json(&line["world"], tz).expect("a stored world"));
    let cal = w.docs.iter_mut().find(|(p, _)| p.starts_with("calendar/")).expect("a calendar document");
    cal.1.push_str("- [ ] 3 Coffee at:2026-09-07T09:30/09:40 ^wxa\n");
    let (d, _) = forkclass::d61_worlds(&w).into_iter().next().expect("D61 derives the world");
    let (got, paused) = drive(&w, d.now);
    assert_eq!(got.len(), 3, "pause, unpause, pause: {got:?}");
    assert_eq!(got, added_by(&w, &d), "the unpause branch: the binary logged another sequence than the derivation");
    assert!(paused);
    println!("D61 worlds the shipped binary logs as derived: {n} of {n}, and the unpause branch");
    assert!(n > 0, "no d61 line was asked");
}

/// **The owner's D64, as the re-bless applies it, bites and does not
/// over-bite** (AGENTS §5.8) — `forkclass::d64_allows` on a frozen P46 line
/// whose comparand is bent: no reason, an unregistered number, and a
/// registered number whose flag the line does not carry are each refused; the
/// number whose flag it carries is allowed; an unchanged line and a line whose
/// answers a D64(b) re-draw cleared are allowed; and a comparand that departs
/// from the shipped fork's day without keeping it by value is refused whatever
/// the reason.
#[test]
fn the_d64_rule_bites_and_does_not_over_bite() {
    let registered = forkclass::registered_parity();
    let old = frozen_lines()
        .iter()
        .find(|l| l["d57"]["p46"] == true && l["d60"]["p51"] == false && l["d57"]["p47"] == false)
        .expect("a frozen P46 line")
        .clone();
    let shipped = old["shipped"]["day"].clone();
    assert!(!shipped.is_null(), "a P46 line keeps the shipped fork's day");
    let mut bent = old.clone();
    bent["day"]["hash"] = Value::String("bent".to_string());
    assert!(forkclass::d64_allows(&old, &old, &shipped, &[], &registered).is_ok_and(|c| c.is_empty()));
    assert!(forkclass::d64_allows(&old, &bent, &shipped, &[], &registered).is_err(), "no reason passed");
    assert!(!registered.contains(&9999));
    assert!(forkclass::d64_allows(&old, &bent, &shipped, &[9999], &registered).is_err(), "an unregistered number passed");
    assert!(forkclass::d64_allows(&old, &bent, &shipped, &[51], &registered).is_err(), "a number the line has no flag of passed");
    assert_eq!(forkclass::d64_allows(&old, &bent, &shipped, &[46], &registered), Ok(vec!["day".to_string()]));
    let mut cleared = old.clone();
    for key in forkclass::ANSWERS {
        cleared[key] = Value::Null;
    }
    assert!(forkclass::d64_allows(&cleared, &bent, &shipped, &[], &registered).is_ok(), "a D64(b) re-draw's answers were refused");
    let mut lost = bent.clone();
    lost["shipped"] = Value::Null;
    assert!(forkclass::d64_allows(&old, &lost, &shipped, &[46], &registered).is_err(), "a comparand that dropped the shipped day passed");
    // **The W-37 repair's three clauses** (README gap 3331), each driven by a finding.
    // 1. A flag the RECOMPUTED answer sets licenses nothing: an unflagged line whose new
    //    answer sets `d60.p51` (the W-37 auditor's plant, `idle/lounge`).
    let plain = frozen_lines()
        .iter()
        .find(|l| !l["day"].is_null() && l["shipped"].is_null() && forkclass::parity_flags(l).iter().all(|f| !f.1))
        .expect("a frozen line with no parity flag set")
        .clone();
    let plain_day = plain["day"]["day"].clone();
    let mut self_certified = plain.clone();
    self_certified["day"]["hash"] = Value::String("bent".to_string());
    self_certified["d60"]["p51"] = Value::Bool(true);
    assert!(
        forkclass::d64_allows(&plain, &self_certified, &plain_day, &[51], &registered).is_err(),
        "a flag the recomputed answer set licensed its own change"
    );
    // 2. The shipped fork's day may not move, whatever number is named (the W-37 critic's
    //    case: a change under both the comparand and the shipped fork, on a flagged line).
    //    A flagged line whose comparand coincides with the shipped day (so it keeps no
    //    `shipped`), recomputed with the shipped day moved: only `day` changes, which P46
    //    governs — so clause 3 allows it, and the refusal is clause 2's alone.
    let mut moved = shipped.clone();
    moved["budget_blocks"] = serde_json::json!(99);
    let mut coincident = old.clone();
    coincident["day"]["day"] = shipped.clone();
    coincident["shipped"] = Value::Null;
    let mut both = coincident.clone();
    both["day"]["day"] = moved.clone();
    assert_eq!(
        forkclass::d64_allows(&coincident, &coincident, &shipped, &[46], &registered),
        Ok(Vec::new()),
        "the coincident line itself is not refused"
    );
    assert!(
        forkclass::d64_allows(&coincident, &both, &moved, &[46], &registered).is_err(),
        "a moved shipped fork passed under a comparand number"
    );
    // 3. A number governs the object its flag lives in, `day` and `whatif` — not another's.
    let mut other = bent.clone();
    other["d60"]["p51"] = Value::Bool(!old["d60"]["p51"].as_bool().unwrap_or(false));
    assert!(
        forkclass::d64_allows(&old, &other, &shipped, &[46], &registered).is_err(),
        "P46 licensed a change to P51's object"
    );
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gaps 2722, 2925)
use std::collections::BTreeMap;
use tm_core::dayplan::DayPlan;
use tm_core::planner::{self, PlanOverrides};
use tm_core::priority::Prio;
use tm_core::store::RuntimeState;

/// The fork's input for a stored world and a state.
fn fork_input<'a>(b: &'a Built, st: &'a RuntimeState) -> planner::PlanInput<'a> {
    planner::PlanInput::new(&b.tree, &b.replay, &b.cfg, &b.model, st, b.world.now)
}

/// **P46, by its property** — `planner_invariants`' `w35_is_p46`: a running
/// block, not paused, no break running, its worked minutes at or past its
/// estimate (fork `active_run`'s `left == 0` refusal).
fn is_p46(b: &Built, st: &RuntimeState) -> bool {
    let Some(a) = st.active.as_ref() else { return false };
    let worked = b.worked_for(st).unwrap_or(0);
    let breaking = st.break_.as_ref().is_some_and(|x| x.started.is_some());
    !a.paused && !breaking && worked >= a.est_min
}

/// P46's comparand state — `w35_p46_state`: the estimate raised by a whole
/// day, so the fork reserves the block from its own walls, wind-down and block
/// boundary; unchanged off P46.
fn p46_state(b: &Built, st: &RuntimeState) -> RuntimeState {
    let mut out = st.clone();
    if is_p46(b, st) {
        let worked = b.worked_for(st).unwrap_or(0);
        if let Some(a) = out.active.as_mut() {
            a.est_min = worked.saturating_add(24 * 60);
        }
    }
    out
}

/// P46's row — `w35_p46_row`: the reservation's `planned` and note carry the
/// fork's own saturating `left`, 0 in overtime.
fn p46_row(b: &Built, day: &mut DayPlan) {
    let now = b.world.now;
    for s in day.segments.iter_mut().filter(|s| {
        matches!(s.kind, SegKind::Block) && s.flags.current && s.energy.is_none() && s.start == now
    }) {
        s.flags.planned_min = Some(0);
        s.flags.note = Some("running · 0m left".to_string());
    }
}

/// P47, by its property, on the fork's own day — `w35_p47_day` over
/// `w35_pause_open_rows`.
fn p47_pause(b: &Built, day: &mut DayPlan) -> bool {
    let now = b.world.now;
    let mut spans: BTreeMap<String, (DateTime<Tz>, DateTime<Tz>)> = BTreeMap::new();
    for s in day.segments.iter().filter(|s| matches!(s.kind, SegKind::Wall)) {
        let id = s.item.as_ref().map(ToString::to_string).unwrap_or_default();
        let e = spans.entry(id).or_insert((s.start, s.end));
        e.0 = e.0.min(s.start);
        e.1 = e.1.max(s.end);
    }
    let on_now: Vec<DateTime<Tz>> = day
        .segments
        .iter()
        .filter(|s| matches!(s.kind, SegKind::Wall))
        .filter(|s| {
            let id = s.item.as_ref().map(ToString::to_string).unwrap_or_default();
            spans.get(&id).is_some_and(|(a, z)| *a <= now && now < *z)
        })
        .map(|s| s.start)
        .collect();
    if on_now.is_empty() {
        return false;
    }
    let mut hit = false;
    for s in day.segments.iter_mut().filter(|s| matches!(s.kind, SegKind::Block) && s.flags.open) {
        hit = true;
        s.flags.current = false;
        if let Some(cut) = on_now.iter().filter(|a| **a > s.start).min().copied() {
            if cut < s.end {
                s.end = cut;
            }
        }
    }
    hit
}

/// **The fork's answers for one stored world**: the shipped day, the comparand
/// (D57's P46/P47 and, since the W-36 land step, D60's P51 applied by their
/// properties) with its flags, and on a running-block day the two what-ifs —
/// `w35_fork_plan` and the W-34 arm's what-if, over the kernel's grants, with
/// D60's key as `planner_invariants`' `w36_fork_whatif` runs it.
fn fork_answers(b: &Built, prios: &[Prio]) -> Value {
    let st = &b.world.state;
    let shipped = planner::plan(&fork_input(b, st).with_ranking(&b.cands, prios));
    let st2 = p46_state(b, st);
    let dvec = forkclass::d60_cands(&b.cands, prios);
    let p51 = forkclass::is_p51(&b.cands, prios);
    let mut comparand = planner::plan(&fork_input(b, &st2).with_ranking(&dvec, prios));
    let p46 = is_p46(b, st);
    if p46 {
        p46_row(b, &mut comparand);
    }
    let p47 = p47_pause(b, &mut comparand);
    let whatif = forkclass::whatif_item(st).map(|id| {
        let bm = b.cfg.block_min();
        let mut rt = st.clone();
        if let Some(x) = rt.active.as_mut() {
            x.est_min = x.est_min.saturating_add(bm);
        }
        let ov = PlanOverrides::new().extending(id, bm);
        let rt = p46_state(b, &rt);
        let mut alt_est = planner::plan(&fork_input(b, &rt).with_ranking(&dvec, prios));
        let mut alt_full = planner::plan(&fork_input(b, &rt).with_ranking(&dvec, prios).with_overrides(&ov));
        p47_pause(b, &mut alt_est);
        p47_pause(b, &mut alt_full);
        serde_json::json!({
            "est": serde_json::to_value(planner::diff(&comparand, &alt_est)).expect("a diff serialises"),
            "full": serde_json::to_value(planner::diff(&comparand, &alt_full)).expect("a diff serialises"),
        })
    });
    serde_json::json!({
        "day": forkclass::frozen_day(&comparand),
        "shipped": (shipped != comparand).then(|| forkclass::frozen_day(&shipped)),
        "d57": {"p46": p46, "p47": p47},
        "d60": {"p51": p51},
        "whatif": whatif,
    })
}

/// The kernel's grants for a stored world — what `with_ranking` hands the fork.
fn kernel_prios(b: &Built) -> Vec<Prio> {
    forkclass::kernel_answer_with_grants(b).unwrap_or_else(|e| panic!("the kernel refused: {e}")).1
}

/// **The frozen answers are still the fork's on this tree** — while the fork
/// is here, every frozen line's `day`, `shipped`, `d57` and `whatif` is exactly
/// what the fork answers for its stored world over the kernel's grants now. A
/// failure here says the FORK's answer moved (or the kernel's ranking it is
/// handed); a failure of the surviving arm says the kernel's day moved.
#[test]
fn the_frozen_classes_are_the_forks_answer_today() {
    let mut stale = Vec::new();
    for line in frozen_lines() {
        let b = Built::of(ClassWorld::of_json(&line["world"], tz()).expect("a stored world"));
        let now = fork_answers(&b, &kernel_prios(&b));
        for key in ["day", "shipped", "d57", "d60", "whatif"] {
            if now[key] != line[key] {
                stale.push(format!("{}: `{key}`", line["class"]));
            }
        }
    }
    assert!(stale.is_empty(), "the frozen answers are not the fork's today (re-bless is a decision, AGENTS §7.2):\n  {}", stale.join("\n  "));
}

/// **The re-bless's reasons** (the owner's D64): the parity numbers
/// `TM_PLANNER_BLESS_BECAUSE` names, comma-separated as `P<n>`. A token that
/// is not one FAILS rather than being skipped.
fn bless_because() -> Vec<u32> {
    std::env::var("TM_PLANNER_BLESS_BECAUSE")
        .unwrap_or_default()
        .split(',')
        .map(str::trim)
        .filter(|t| !t.is_empty())
        .map(|t| {
            t.strip_prefix('P')
                .and_then(|d| d.parse().ok())
                .unwrap_or_else(|| panic!("TM_PLANNER_BLESS_BECAUSE: `{t}` is not a parity number P<n>"))
        })
        .collect()
}

/// **Re-bless the frozen fork classes — held to the owner's D64** (W-37 track
/// H, README gaps 3133, 3138) — inert without `TM_PLANNER_BLESS`.
///
/// It recomputes the FORK'S answers for every stored world and never changes a
/// world (a re-draw is [`the_frozen_class_worlds_are_redrawn`], which demands
/// D64(b)'s reason). Rewriting a committed comparand is a decision and never a
/// repair (AGENTS §7.3), and since D64 it is a decision by a STANDING RULE,
/// which this test enforces rather than leaving to a sentence: a line whose
/// answers change must carry the flag of a parity number the re-bless was run
/// for (`TM_PLANNER_BLESS_BECAUSE=P56`, say) that `kernel/parity.txt`
/// registers — D64(a) — or have had its answers cleared by a D64(b) re-draw;
/// the shipped fork's day stays beside a departing comparand by value; and a
/// re-bless that is neither FAILS BY NAME and writes nothing. After R3 this
/// test is gone with the region and the file is final. `TM_PLANNER_BLESS_OUT`
/// writes elsewhere (a scratch copy), for a dry run.
#[test]
#[ignore]
fn the_frozen_fork_classes_are_reblessed() {
    if std::env::var_os("TM_PLANNER_BLESS").is_none() {
        eprintln!("inert: set TM_PLANNER_BLESS=1 to rewrite {}", forkclass::FROZEN_CLASSES);
        return;
    }
    let because = bless_because();
    let registered = forkclass::registered_parity();
    let path = forkclass::frozen_path();
    let out_path = std::env::var_os("TM_PLANNER_BLESS_OUT").map(std::path::PathBuf::from).unwrap_or_else(|| path.clone());
    let text = std::fs::read_to_string(&path).expect("the frozen classes read");
    let mut out = String::new();
    let (mut refused, mut changed, mut filled) = (Vec::new(), Vec::new(), 0usize);
    for l in text.lines().filter(|l| !l.trim().is_empty()) {
        let old: Value = serde_json::from_str(l).expect("a frozen class line is JSON");
        let mut line = old.clone();
        let b = Built::of(ClassWorld::of_json(&line["world"], tz()).expect("a stored world"));
        let prios = kernel_prios(&b);
        let answers = fork_answers(&b, &prios);
        for key in forkclass::ANSWERS {
            line[key] = answers[key].clone();
        }
        let shipped = planner::plan(&fork_input(&b, &b.world.state).with_ranking(&b.cands, &prios));
        let shipped_day = serde_json::to_value(&shipped).expect("a day serialises");
        match forkclass::d64_allows(&old, &line, &shipped_day, &because, &registered) {
            Err(e) => refused.push(e),
            Ok(keys) if !keys.is_empty() => changed.push(format!("{} `{}`", line["class"], keys.join("`, `"))),
            Ok(_) => filled += usize::from(old["day"].is_null()),
        }
        assert_eq!(line["world"], old["world"], "a re-bless changed a world");
        out.push_str(&serde_json::to_string(&line).expect("a line serialises"));
        out.push('\n');
    }
    eprintln!(
        "re-bless for {:?}: {} line(s) changed ({}), {filled} cleared line(s) answered, {} refused",
        because,
        changed.len(),
        changed.join("; "),
        refused.len()
    );
    assert!(refused.is_empty(), "the re-bless is refused by the owner's D64 and wrote nothing:\n  {}", refused.join("\n  "));
    std::fs::write(&out_path, out).expect("the frozen classes are written");
}

/// **Re-draw frozen worlds under the owner's D64(b)** (W-37 track H, README
/// gaps 3138, 3123) — inert without `TM_PLANNER_DRAW`.
///
/// Every drawn line is re-drawn at its recorded seed, index and arm from the
/// shared generator (`forkclass::draws_of_line`). A world the generator no
/// longer draws may be replaced only when `TM_PLANNER_DRAW` lists its class and
/// `TM_PLANNER_DRAW_BECAUSE` gives D64(b)'s reason — dated, naming `D64(b)`: a
/// world the shipped binary cannot build — which the line then carries as
/// `d64b`, its answers cleared for the re-bless; a re-drawn world must keep its
/// class. Anything else FAILS BY NAME and writes nothing. It also keeps the
/// D61 lines exactly the worlds `forkclass::d61_worlds` derives from the
/// primary lines (README gap 3123): a missing one is added with its answers
/// cleared, a stale one is re-derived only under the same listing and reason.
/// `TM_PLANNER_DRAW_OUT` writes elsewhere, for a dry run. After R3 this test
/// is gone with the region: a world the fork cannot answer cannot be frozen.
#[test]
#[ignore]
fn the_frozen_class_worlds_are_redrawn() {
    let Ok(listed) = std::env::var("TM_PLANNER_DRAW") else {
        eprintln!("inert: set TM_PLANNER_DRAW=<class,…> to re-draw {}", forkclass::FROZEN_CLASSES);
        return;
    };
    let listed: BTreeSet<String> = listed.split(',').map(str::trim).filter(|c| !c.is_empty()).map(str::to_string).collect();
    let because = std::env::var("TM_PLANNER_DRAW_BECAUSE").unwrap_or_default();
    let reasoned = because.starts_with("20") && because.contains("D64(b)");
    let tz = tz();
    let path = forkclass::frozen_path();
    let out_path = std::env::var_os("TM_PLANNER_DRAW_OUT").map(std::path::PathBuf::from).unwrap_or_else(|| path.clone());
    let text = std::fs::read_to_string(&path).expect("the frozen classes read");
    let lines: Vec<Value> = text.lines().filter(|l| !l.trim().is_empty()).map(|l| serde_json::from_str(l).expect("JSON")).collect();
    let mut bad = Vec::new();
    let mut redrawn = Vec::new();
    let clear = |line: &mut Value| {
        for key in forkclass::ANSWERS {
            line[key] = Value::Null;
        }
    };
    // D64(b) is CHECKED, not asserted: the stored world must fail `forkclass::binary_holds`
    // (a world the shipped binary cannot build), the re-drawn one must pass it and keep its
    // class, and the line carries the clauses the old world failed beside the step's reason.
    let replace = |line: &mut Value, world: ClassWorld, what: String, bad: &mut Vec<String>, redrawn: &mut Vec<String>| {
        let key = line["class"].as_str().unwrap_or_default().to_string();
        let old = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        let held = forkclass::binary_holds(&Built::of(old)).err().unwrap_or_default();
        let fresh = Built::of(world.clone());
        if !listed.contains(&key) {
            bad.push(format!("{what}: the generator no longer draws this world and TM_PLANNER_DRAW does not list `{key}`"));
        } else if !reasoned {
            bad.push(format!("{what}: re-drawn with no D64(b) reason (TM_PLANNER_DRAW_BECAUSE must be dated and name D64(b))"));
        } else if held.is_empty() {
            bad.push(format!("{what}: the stored world is one the binary can hold, so D64(b) does not reach it"));
        } else if let Err(e) = forkclass::binary_holds(&fresh) {
            bad.push(format!("{what}: the re-drawn world is not one the binary can hold either: {}", e.join("; ")));
        } else if class_of(&fresh).key() != key {
            bad.push(format!("{what}: the re-drawn world is not a `{key}` world but a `{}` one", class_of(&fresh).key()));
        } else {
            line["world"] = world.to_json();
            line["d64b"] = serde_json::json!({"why": because.clone(), "held": held});
            clear(line);
            redrawn.push(what);
        }
    };
    let mut out: Vec<Value> = Vec::new();
    for mut line in lines.iter().filter(|l| l["derived"].is_null()).cloned() {
        let what = format!("{}{}", line["class"].as_str().unwrap_or_default(), line["secondary"].as_str().map(|s| format!(" ({s})")).unwrap_or_default());
        let stored = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        let worlds: Vec<ClassWorld> = forkclass::draws_of_line(&line).iter().map(forkclass::world_of).collect();
        if !worlds.contains(&stored) {
            // A line naming two draws (see `forkclass::draws_of_line`) is re-drawn from the
            // one that keeps its class, the first else (W-37 repair: `idle/late (rest_debt)`
            // is W-36's TARGETED draw, and its untargeted twin at the same index is another
            // class's world).
            let key = line["class"].as_str().unwrap_or_default().to_string();
            let keeps = worlds.iter().position(|w| class_of(&Built::of(w.clone())).key() == key).unwrap_or(0);
            match worlds.into_iter().nth(keeps) {
                Some(w) => replace(&mut line, w, what, &mut bad, &mut redrawn),
                None => bad.push(format!("{what}: no draw reproduces its recorded arm")),
            }
        }
        out.push(line);
    }
    // The D61 lines: derived from the PRIMARY lines, in their order.
    let parents: Vec<Value> = out.iter().filter(|l| l["secondary"].is_null()).cloned().collect();
    for parent in parents {
        let world = ClassWorld::of_json(&parent["world"], tz).expect("a stored world");
        for (w, pause) in forkclass::d61_worlds(&world) {
            let key = parent["class"].as_str().unwrap_or_default();
            let what = format!("{key} (d61 at {})", w.now.format("%H:%M"));
            let mut line = serde_json::json!({
                "class": key, "secondary": "d61", "arm": parent["arm"], "case": parent["case"],
                "seed": parent["seed"], "draw": parent["draw"],
                "derived": {"from": key, "pause": pause.to_rfc3339(), "now": w.now.to_rfc3339()},
                "world": w.to_json(),
            });
            clear(&mut line);
            match lines.iter().find(|l| l["derived"] == line["derived"]) {
                Some(old) if old["world"] == line["world"] => line = old.clone(),
                Some(old) => {
                    let mut kept = old.clone();
                    replace(&mut kept, w, what, &mut bad, &mut redrawn);
                    line = kept;
                }
                None => redrawn.push(format!("{what}: added")),
            }
            out.push(line);
        }
    }
    // A D61 line D61 no longer derives FAILS — unless its parent was re-drawn in this
    // run under D64(b)'s reason, when the derivation is the new world's (W-37 repair,
    // README gap 3340: a parent at rest already holds the pause at `now`, so the world
    // D61 derived at `now` IS the parent and only the one mid-meeting is derived).
    let parents_redrawn: BTreeSet<String> = out
        .iter()
        .filter(|l| l["secondary"].is_null() && l["day"].is_null() && !l["d64b"].is_null())
        .filter_map(|l| l["class"].as_str().map(str::to_string))
        .collect();
    for old in lines.iter().filter(|l| !l["derived"].is_null()) {
        if !out.iter().any(|l| l["derived"] == old["derived"]) {
            let key = old["class"].as_str().unwrap_or_default();
            if reasoned && parents_redrawn.contains(key) {
                redrawn.push(format!("{key} (d61 at {}): dropped -- its parent was re-drawn and D61 no longer derives it", old["derived"]["now"]));
            } else {
                bad.push(format!("{key} (d61 at {}): D61 no longer derives this world", old["derived"]["now"]));
            }
        }
    }
    eprintln!("re-draw: {} line(s): {}", redrawn.len(), redrawn.join("; "));
    assert!(bad.is_empty(), "the re-draw is refused by the owner's D64 and wrote nothing:\n  {}", bad.join("\n  "));
    let text: String = out.iter().map(|l| serde_json::to_string(l).expect("a line serialises") + "\n").collect();
    std::fs::write(&out_path, text).expect("the frozen classes are written");
}
// END THE FORK PLANNER
