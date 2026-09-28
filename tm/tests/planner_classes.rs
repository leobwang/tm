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
#[path = "support/srcwalk.rs"]
mod srcwalk;

use std::collections::BTreeSet;

use chrono::Duration;
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
/// [`the_frozen_days_cover_what_the_arms_floors_demand`] asserts.
const SECONDARY_FLOORS: [&str; 2] = ["rest_debt", "whatif"];

/// **What the frozen days cover beyond their class**, counted off the FORK's
/// frozen days (never the kernel's, which is the value under test): each floor
/// is one the differential arms hold their own random draws to, so the frozen
/// set is not narrower than the arms it stands in for at R3.
#[test]
fn the_frozen_days_cover_what_the_arms_floors_demand() {
    let mut kinds = BTreeSet::new();
    let mut n = [0usize; 17];
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
/// FAILS as STALE, so the list only shrinks.
const OUTSIDE_A_REGION: [(&str, &str); 1] = [(
    "tm/tests/planner_invariants.rs",
    "2026-09-27 (W-36 track H): the generated differential's arms plan with the fork beside the \
     kernel on every case, and this track may not touch the file (tracks K and T append to it this \
     run). EXIT: R3 retargets its arms onto `support/forkclass.rs`' frozen classes or deletes them \
     with the fork, and this line goes STALE (README gap 3084)",
)];

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

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gaps 2722, 2925)
use chrono::DateTime;
use std::collections::BTreeMap;
use tm_core::dayplan::DayPlan;
use tm_core::planner::{self, PlanOverrides};
use tm_core::priority::{self, Candidate, Prio};
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

/// **The order the request carries the candidates in** — `kernel_capacity::
/// send_order`, the fork's `priority::compute` sort — which is the kernel's
/// REQUEST POSITION, D60's tie-break after `until`. The same function as
/// `planner_invariants`' `send_order` (W-36 track K); both are fork-comparand
/// code and leave with the fork at R3 (README gap 3122).
fn send_order(cands: &[Candidate]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..cands.len()).collect();
    order.sort_by(|&a, &b| {
        let (ca, cb) = (&cands[a], &cands[b]);
        (ca.effective_due.is_none(), ca.effective_due, ca.own_order, a)
            .cmp(&(cb.effective_due.is_none(), cb.effective_due, cb.own_order, b))
    });
    order
}

/// **P51, by its PROPERTY, in the fork** (owner D60; W-36 land, README gap
/// 3121 — track H's gap 3085): a `p = 0` answer with a positive shortfall — the
/// kernel's `Planner.Ranked.imp` condition, read off the KERNEL's own §7 answer
/// for that id — is ranked by its `until` and then its request position, before
/// every other `p = 0` answer. Both fork sorts (`sorted_candidates`,
/// `build_groups`) read only `root_order`/`own_order` of a `with_ranking` day,
/// so the fork runs D60's key when those two fields are rewritten and nothing
/// else is: an impossible tie gets `(0, until)` and `(0, position)`, every other
/// candidate's root moves one file down (a uniform shift, which keeps the fork's
/// order among them). `planner_invariants`' `w36_d60_cands` is the same rule;
/// this one finds the answer by id rather than by index.
fn d60_cands(cands: &[Candidate], prios: &[Prio]) -> Vec<Candidate> {
    let mut pos = vec![0usize; cands.len()];
    for (k, &i) in send_order(cands).iter().enumerate() {
        pos[i] = k;
    }
    cands
        .iter()
        .enumerate()
        .map(|(i, c)| {
            let mut d = c.clone();
            let tie = prios.iter().find(|p| p.id == c.id).filter(|p| p.p == 0 && p.shortfall_min_exact.num > 0);
            match tie {
                Some(p) if !c.is_wall => {
                    let until = p.until.map_or(0, |u| usize::try_from(chrono::Datelike::num_days_from_ce(&u)).unwrap_or(0));
                    d.root_order = (0, until);
                    d.own_order = (0, pos[i]);
                }
                _ => d.root_order = (c.root_order.0.saturating_add(1), c.root_order.1),
            }
            d
        })
        .collect()
}

/// **A P51 day**: D60's key moves the fork's §7.4 order.
fn is_p51(cands: &[Candidate], prios: &[Prio]) -> bool {
    let dvec = d60_cands(cands, prios);
    let a: Vec<&str> = priority::sorted_candidates(prios, cands).iter().map(|c| c.id.as_str()).collect();
    let b: Vec<&str> = priority::sorted_candidates(prios, &dvec).iter().map(|c| c.id.as_str()).collect();
    a != b
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
    let dvec = d60_cands(&b.cands, prios);
    let p51 = is_p51(&b.cands, prios);
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

/// **D61's world, planned by both** (W-36 land, README gap 3123). Since the
/// owner's D61 the binary LOGS a `pause` at the start of a wall that begins
/// while a block runs, and marks the block paused in `.tm/state.json` (`tm/src/
/// cli/day.rs`' `stop_the_timer_at_walls`) — so a `wall-on-now` day the binary
/// produces carries that line, and the frozen `wall-on-now` worlds, drawn
/// before D61, do not. `pause` is an event the fork has always read, so this
/// needs no parity number at the planner (P53 is the host's writing of it): for
/// every frozen `wall-on-now` world whose wall began after the block started,
/// the pause D61 writes is appended, and the kernel's day is compared with the
/// fork's comparand for THAT world, by `compare_line`, exactly as a frozen line
/// is. It runs while the fork is here and leaves with it at R3; freezing these
/// worlds is gap 3123's exit.
#[test]
fn a_wall_on_now_day_with_the_pause_d61_logs_is_planned_as_the_fork_plans_it() {
    let tz = tz();
    let mut compared = Vec::new();
    let mut findings = Vec::new();
    let mut moved = 0usize;
    for line in frozen_lines().iter().filter(|l| l["class"].as_str().is_some_and(|c| c.starts_with("wall-on-now/"))) {
        let mut w = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        let b0 = Built::of(w.clone());
        let Some(a) = w.state.active.clone().filter(|a| !a.paused) else { continue };
        let started = tm_core::capacity::local_dt(tz, b0.date(), a.started);
        let now = w.now;
        // The walls' blocked spans, merged as `stop_the_timer_at_walls` merges them.
        let mut spans: Vec<(DateTime<Tz>, DateTime<Tz>)> = b0.walls().iter().map(|(_, lo, hi, _)| (*lo, *hi)).collect();
        spans.sort();
        let mut merged: Vec<(DateTime<Tz>, DateTime<Tz>)> = Vec::new();
        for (lo, hi) in spans {
            match merged.last_mut() {
                Some(m) if lo <= m.1 => m.1 = m.1.max(hi),
                _ => merged.push((lo, hi)),
            }
        }
        let Some((lo, hi)) = merged.into_iter().find(|(lo, hi)| *lo <= now && now < *hi && *lo > started) else {
            continue;
        };
        w.log.push_str(&format!(
            "{{\"t\":\"{}\",\"ev\":\"pause\",\"id\":\"{}\"}}\n",
            lo.format("%Y-%m-%dT%H:%M:%S%:z"),
            a.id
        ));
        if let Some(x) = w.state.active.as_mut() {
            x.paused = true;
        }
        // At the wall's start (the frozen `now`), and again twenty minutes INTO
        // the meeting — the drive's `tm now` at 13:20 — where the paused stretch
        // is already behind `now` and the open row must not be drawn across it.
        let mid = (lo + Duration::minutes(20)).min(hi - Duration::minutes(1));
        let unpaused = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        for at in [now, mid] {
            if at < now || at >= hi {
                continue;
            }
            let mut wa = w.clone();
            wa.now = at;
            let b = Built::of(wa.clone());
            // Non-vacuity: the logged pause reaches the kernel's day.
            let mut wu = unpaused.clone();
            wu.now = at;
            let (kp, ku) = (forkclass::kernel_answer(&b), forkclass::kernel_answer(&Built::of(wu)));
            if let (Ok(kp), Ok(ku)) = (kp, ku) {
                moved += usize::from(kp.day != ku.day);
            }
            let mut synth = fork_answers(&b, &kernel_prios(&b));
            synth["class"] = line["class"].clone();
            synth["world"] = wa.to_json();
            let mut t = ClassTally::default();
            findings.extend(compare_line(&synth, &mut t));
            compared.push(format!(
                "{} (pause at {}, now {})",
                line["class"].as_str().unwrap_or_default(),
                lo.format("%H:%M"),
                at.format("%H:%M")
            ));
        }
    }
    // A COMPARISON is one world at one instant, and a world is compared at up to
    // two (the wall's start and twenty minutes in): the land step printed the
    // comparisons as "worlds" (W-36 repair, README gap 3136), so both are counted.
    let worlds = compared
        .iter()
        .map(|c| c.split(" (pause at ").next().unwrap_or_default())
        .collect::<std::collections::BTreeSet<_>>()
        .len();
    println!(
        "D61 comparisons: {} over {worlds} wall-on-now class(es), the logged pause moved the kernel's day on {moved} of them: {}",
        compared.len(),
        compared.join(", ")
    );
    assert!(!compared.is_empty(), "no frozen wall-on-now world had a wall that began after its block started");
    assert!(moved > 0, "the logged pause changed the kernel's day on no world: the comparison is vacuous");
    assert!(findings.is_empty(), "{} disagreement(s) on D61's worlds:\n  {}", findings.len(), findings.join("\n  "));
}

/// **Re-bless the frozen fork classes** — inert without `TM_PLANNER_BLESS`.
///
/// It recomputes the FORK'S answers for every stored world and rewrites the
/// file; it never re-draws a world (support/forkclass.rs says why). Rewriting a
/// committed comparand is a decision and never a repair (AGENTS §7.2); after R3
/// this test is gone with the region and the file is final.
#[test]
#[ignore]
fn the_frozen_fork_classes_are_reblessed() {
    if std::env::var_os("TM_PLANNER_BLESS").is_none() {
        eprintln!("inert: set TM_PLANNER_BLESS=1 to rewrite {}", forkclass::FROZEN_CLASSES);
        return;
    }
    let path = forkclass::frozen_path();
    let text = std::fs::read_to_string(&path).expect("the frozen classes read");
    let mut out = String::new();
    for l in text.lines().filter(|l| !l.trim().is_empty()) {
        let mut line: Value = serde_json::from_str(l).expect("a frozen class line is JSON");
        let b = Built::of(ClassWorld::of_json(&line["world"], tz()).expect("a stored world"));
        let answers = fork_answers(&b, &kernel_prios(&b));
        for key in ["day", "shipped", "d57", "d60", "whatif"] {
            line[key] = answers[key].clone();
        }
        out.push_str(&serde_json::to_string(&line).expect("a line serialises"));
        out.push('\n');
    }
    std::fs::write(&path, out).expect("the frozen classes are written");
}
// END THE FORK PLANNER
