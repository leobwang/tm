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
//! it reads the frozen lines and the kernel, and nothing of the fork's planner —
//! and since W-45 track C (README gap 4680) every bless of the suite's frozen files
//! is in it too, asking fork 4748911 out of the tree (`tm-oracle plan`), so no file
//! is final at R3. **The fork's arm** — the checks that the frozen answers are still
//! the in-tree fork's on this tree, and P45's witness — plans with `planner::plan`
//! and is one region, `BEGIN THE FORK PLANNER` … `END THE FORK PLANNER`, which R3
//! deletes whole; [`the_fork_half_of_this_suite_is_one_region`] holds this file to
//! that.
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
//!
//! **Since W-38 track H (README gaps 3200, 3207, 3282, 3320) the fork region
//! compares nothing the frozen comparand does not**: the what-if and the worked
//! minutes are asked as R3's host will ask them, and the lines gain P45's
//! comparand after a running break, P52's re-ranked what-if, P55's host reading,
//! P56's closed pause against fork 4748911's drawing and a dated window task's
//! `⚠` — and `plan-basic`'s ten-minute days (`planner_w37_rows.rs`' arm) are
//! frozen beside the classes ([`the_kernel_plans_plan_basic_every_ten_minutes_as_the_fork_planned`]).
//! The D64(a) gate gained its INTRODUCTION: a number whose comparand did not
//! exist when a line was frozen may add its answer, and nothing else
//! (`forkclass::d64_allows`, README gap 3470).

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

/// The committed history a bless holds its lines against (README gap 4151).
#[allow(dead_code)]
#[path = "support/frozenhist.rs"]
mod frozenhist;

/// Parity P81's rule and fork 4748911's reading of a break the log holds inside a running block
/// (the owner's D87, W-42 track R): one module for the arm that survives R3 and the fork region.
#[allow(dead_code)]
#[path = "support/p81.rs"]
mod p81;

/// The fork's planner as a backend, and the comparand built over any backend (W-39,
/// the owner's D72): the in-tree fork until R3, `tm-oracle plan` after.
#[allow(dead_code)]
#[path = "support/forkplan.rs"]
mod forkplan;

/// `plan-basic` with its history — the tree the frozen ten-minute days are planned on (W-38).
#[allow(dead_code)]
mod planner_common;

use std::collections::BTreeSet;

use chrono::{DateTime, Duration};
use chrono_tz::Tz;
use serde_json::Value;
use tm_core::config::Config;
use tm_core::dayplan::SegKind;
use tm_core::store::RuntimeState;

use forkclass::{class_of, class_space, compare_line, frozen_lines, Built, ClassTally, ClassWorld, DayShape, Run};

fn tz() -> Tz {
    Config::default().tz
}

/// **The kernel plans every frozen class as the fork planned it**, by value,
/// with the declared classes and nothing else (see `support/forkclass.rs`).
#[test]
fn the_kernel_plans_every_generated_class_the_fork_planned() {
    // **Parity P81** (the owner's D87; W-42 track R, README gaps 4137 and 4240; frozen at W-43 track
    // C, README gap 4248): a line whose world's log holds a break P81 nets — the eight `worked`
    // lines, whose break the log holds INSIDE the running block — carries `p81`, fork 4748911's own
    // day asked the D87 day, and `compare_line` holds the kernel to it by value; its `day` stays the
    // fork's reading of the stored log. P81's RULE (`p81::planned_day` on the frozen `day`, the model
    // W-42 held the lines by) is held to that frozen answer here ([`p81_rule_unmet`]), so the rule
    // and the fork's own answer cannot drift apart unseen, and both are what the kernel meets.
    let mut t = ClassTally::default();
    let mut findings = Vec::new();
    let (mut p81_held, mut p81_moved) = (0usize, 0usize);
    for line in frozen_lines() {
        match p81_rule_unmet(line) {
            Err(why) => findings.push(why),
            Ok(None) => {}
            Ok(Some(moved)) => {
                p81_held += 1;
                p81_moved += usize::from(moved);
            }
        }
        findings.extend(compare_line(line, &mut t));
    }
    let line = t.line(findings.len());
    println!("parity P81: {p81_held} line(s) carry fork 4748911's answer asked the D87 day, P81's rule its value on every one ({p81_moved} moved by it)");
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
    // W-38 (README gap 3282): the request carries the host's grown facts, so a parity-P44 day
    // — the fork's `apply` moving its own what-if beyond the estimate's — is held to the
    // shipped TUI's what-if; and the break-day open row is compared, with the host's minutes.
    assert!(t.p44 > 0, "no parity-P44 day's what-if was held to the shipped TUI's: {t:?}");
    assert!(t.p45_open > 0, "no open row was compared on a break day: {t:?}");
    assert!(t.p45_host > 0, "on no break day did the host's minutes differ from the log's (P55): {t:?}");
    // README gap 3207: the kept breaks after a running break, against P45's comparand.
    assert!(t.p45_after > 0 && t.p45_kept > 0, "no kept break after a running break was compared: {t:?}");
    // README gap 3958: every line carrying P67's own answer was held to it, and no other.
    let p67_lines = frozen_lines().iter().filter(|l| !l["p67"].is_null()).count();
    assert!(p67_lines > 0 && t.p67 == p67_lines, "P67's answer held on {} line(s) of the {p67_lines} carrying it: {t:?}", t.p67);
    // README gap 3320: a meeting's CLOSED pause, drawn as the wall alone against fork 4748911.
    assert!(t.p56 > 0, "no P56 line: a meeting's closed pause is compared on no frozen day: {t:?}");
    // README gap 3200: a scheduled window task's Routine row marked `⚠` (gap 435), by value.
    assert!(t.day.hot_marks_435 > 0, "no routine `⚠` mark was compared on a frozen generated day: {t:?}");
    // README gap 3282: the host's worked minutes moving the day (P55), by value.
    // Since the owner's D87 (README gap 4242) the `worked` lines' P55 departure is from fork
    // 4748911's reading alone: the kernel's own replay nets their logged break (P81), so P55's
    // request field is what the break-day open rows above test (`p45_host`), and these lines
    // are held to their fork day with P81's rule applied.
    assert!(t.p55 > 0, "no P55 line: the host's worked minutes move no frozen day: {t:?}");
    // W-42 track R (README gap 4240): P81 was held on a frozen day, and on every line it is held on
    // its answer moves the day — the departure is never the identity; and since W-43 (README gap
    // 4248) the kernel was held to the frozen answer on exactly those lines.
    assert!(p81_held > 0 && p81_moved == p81_held, "P81's answer moves {p81_moved} of the {p81_held} line(s) carrying it");
    assert_eq!(t.p81, p81_held, "the kernel was held to P81's frozen answer on {} line(s) of the {p81_held} carrying it", t.p81);
    assert!(t.day.break_rows_551 > 0, "gap 551's class counted no row: {t:?}");
    assert!(t.day.mult_rows_550 > 0, "gap 550's class counted no row: {t:?}");
    assert!(
        t.day.underused_notes > 0 && t.notes_rendered == t.day.underused_notes,
        "every under-used note left to the renderer is rendered as the fork wrote it: {t:?}"
    );
}

/// **P81's frozen answer, and its rule, on one line** (W-43 track C, README gap 4248). A line
/// carries `p81` exactly when its world's log holds a break P81 nets — read off the log by fork
/// 4748911's own machine (`p81::netted_breaks`), never off the kernel's answer — and where it does,
/// P81's rule on the frozen `day` (`p81::planned_day`, re-digested) IS the frozen answer's day and
/// hash, by value. `Ok(None)` on a line P81 nets nothing on; `Ok(Some(moved))` where it holds,
/// `moved` saying the answer is not the line's own `day`; `Err` names the line and what failed.
fn p81_rule_unmet(line: &Value) -> Result<Option<bool>, String> {
    let who = format!("{}{}", line["class"].as_str().unwrap_or("?"), line["secondary"].as_str().map(|s| format!(" ({s})")).unwrap_or_default());
    let netted = p81::netted_breaks(line["world"]["log"].as_str().unwrap_or_default(), &[]).map_err(|e| format!("{who}: {e}"))?;
    let answer = line.get("p81").filter(|v| !v.is_null());
    match (netted.is_empty(), answer) {
        (true, None) => Ok(None),
        (true, Some(_)) => Err(format!("{who}: carries P81's answer and its log holds no break P81 nets")),
        (false, None) => Err(format!("{who}: its log holds {} break(s) P81 nets and it carries no P81 answer", netted.len())),
        (false, Some(a)) => {
            let rule = forkplan::frozen_day_json(&p81::planned_day(&line["day"]["day"], &netted).map_err(|e| format!("{who}: {e}"))?);
            let frozen = serde_json::json!({"hash": a["hash"], "day": a["day"]});
            if a["p81"] != true || rule != frozen {
                return Err(format!(
                    "{who}: P81's rule on the frozen day is not the frozen P81 answer ({})",
                    forkplan::first_difference("p81", &frozen, &rule).unwrap_or_else(|| "the flag".to_string())
                ));
            }
            Ok(Some(frozen != line["day"]))
        }
    }
}

/// **The kernel plans `plan-basic` at every ten minutes as the shipped fork planned it**
/// (W-38, README gaps 3200 and 3282) — `planner_w37_rows.rs`' arm, which compared the kernel
/// with the LIVE fork in a region R3 deletes, against the fork's days frozen by value
/// (`forkday::FROZEN_BASIC`): §4.3's own tree with its eight weeks of history, both of the
/// fixture suite's states, every ten minutes to 20:50 — the date, the window, the budget, all
/// twelve diagnostic fields, the priorities and every row in order, by value, and the hash.
/// Its floors are the arm's: gap 2870's `⚠` on a Routine row and gap 551's planned Break rows
/// on generated instants, every hash equal; and README gap 3201's host property is asked of
/// every instant without a fork — the encoder sends no empty window.
#[test]
fn the_kernel_plans_plan_basic_every_ten_minutes_as_the_fork_planned() {
    let fx = planner_common::load_with_log("plan-basic", Some(planner_common::BASIC_LOG));
    let mut t = forkday::DayTally::default();
    let mut findings = Vec::new();
    let lines = forkday::frozen_basic_days();
    let mut states = BTreeSet::new();
    let mut unsent = 0usize;
    for line in &lines {
        let name = line["name"].as_str().unwrap_or("<no name>");
        let state: tm_core::store::RuntimeState = serde_json::from_value(line["state"].clone()).expect("a stored state");
        states.insert(line["state"].to_string());
        let now = DateTime::parse_from_rfc3339(line["now"].as_str().unwrap_or_default()).expect("an instant").with_timezone(&fx.cfg.tz);
        let date = tm_core::planwire::plan_date(&state, now);
        let cands = tm_core::priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, date, now);
        let sent = tm_core::planwire::routine_instances(&cands, &fx.tree, now, date, fx.cfg.tz);
        assert!(sent.iter().all(|r| r.from < r.to), "{name}: an empty span was sent (README gap 3201)");
        // **…and the filter that keeps it from being sent FIRED** (W-45 track C, README gap 4682): the
        // windowed candidates fork collect_routines keeps (its own filter) that the encoder did not
        // send — a closed daily window, never placed — counted, as `planner_w37_rows.rs`' region
        // counted them beside its fork comparison, so the property above is not asserted of a run
        // that met no closed window.
        unsent += cands
            .iter()
            .filter(|c| !c.is_wall && !c.is_optional && c.eligible() && c.window.is_some() && c.remaining_min > 0)
            .filter(|c| !sent.iter().any(|r| r.id == c.id && r.inst == c.instance))
            .count();
        let w = planner_common::planreq::World {
            docs: &fx.docs,
            log: &fx.log,
            tree: &fx.tree,
            cfg: &fx.cfg,
            state: &state,
            now,
            cands: &cands,
            replay: &fx.replay,
        };
        match planner_common::planreq::kernel_day(&w, None) {
            Ok((k, _)) => findings.extend(forkday::compare_day_with_fork(name, &k, line, now, &mut t)),
            Err(e) => findings.push(format!("{name}: the kernel did not plan the day: {e}")),
        }
    }
    println!("{}", t.line("plan-basic every ten minutes", findings.len()));
    forkday::no_disagreement(&findings);
    assert_eq!((t.days, t.skipped), (lines.len(), 0), "every frozen day was compared: {t:?}");
    assert_eq!(states.len(), 2, "the two states of the fixture suite");
    assert_eq!(t.hashes_equal, t.days, "every day hashes as the fork's: {t:?}");
    assert!(t.hot_marks_435 >= 10, "a Routine row's `⚠` compared on too few days: {t:?}");
    assert!(t.break_rows_551 >= 10, "planned Break rows compared on too few days: {t:?}");
    assert!(unsent > 0, "no closed window instance was left unsent (README gap 3201's filter fired on no frozen instant)");
}

/// **The kernel plans every day of the seeded batch as the fork planned it** (W-39, the owner's
/// D72, README gap 3533) — `forkclass::compare_line`, the classes' own comparison, over every
/// line of `forkclass::FROZEN_BATCH`: the first `forkclass::BATCH_DRAWS` draws of
/// `forkclass::BATCH_SEED` the shipped binary holds, each frozen with the fork's answers by
/// value and every registered departure carried by its flag, as a class line carries it. It
/// reads the frozen lines and the kernel and nothing of the fork's planner, so it outlives R3.
#[test]
fn the_kernel_plans_every_frozen_batch_day_the_fork_planned() {
    let mut t = ClassTally::default();
    let mut findings = Vec::new();
    let lines = forkclass::batch_lines();
    for line in lines {
        findings.extend(compare_line(line, &mut t));
    }
    println!("seeded batch: {} line(s) — {}", lines.len(), t.line(findings.len()));
    assert!(
        findings.is_empty(),
        "{} disagreement(s) with the frozen batch (each must be one of the declared classes):\n  {}",
        findings.len(),
        findings.join("\n  ")
    );
    // The floors (AGENTS §9.2): the batch compares every departure the comparand carries on
    // at least one day, so none is asserted on nothing, and the comparison ran on every line.
    assert_eq!(t.day.days + t.p45, lines.len(), "every batch line was compared: {t:?}");
    assert!(lines.len() >= forkclass::BATCH_DRAWS / 2, "the batch holds {} of {} draws", lines.len(), forkclass::BATCH_DRAWS);
    assert!(t.p45 > 0 && t.p45_after > 0, "no running break was compared in the batch: {t:?}");
    let p67_lines = lines.iter().filter(|l| !l["p67"].is_null()).count();
    assert!(p67_lines > 0 && t.p67 == p67_lines, "P67's answer held on {} batch line(s) of the {p67_lines} carrying it: {t:?}", t.p67);
    assert!(t.p46 > 0 && t.p47 > 0 && t.p51 > 0, "a D57/D60 departure is compared on no batch day: {t:?}");
    assert!(t.whatifs > 0 && t.whatif_ids > 0, "no what-if with an id in it was compared in the batch: {t:?}");
    assert!(t.day.hashes_equal == t.day.days, "a batch day hashes otherwise than the fork's: {t:?}");
}

/// **Every frozen line is fork 4748911's answer out of the tree too** (W-39, the owner's D72) —
/// `tm-oracle plan` (fork 4748911, `09d38fa`'s ranking seam grafted) answers every class, batch
/// and driven line through `forkplan::comparand_answers`, the frozen lines' one definition, exactly as
/// the line holds it: every answer of `forkclass::ANSWERS`, by value, over the kernel's grants
/// now. The assertion bytes on disk cannot make about themselves, and the one that survives R3:
/// after it, the oracle is the only fork left to ask. Inert without `TM_ORACLE`.
///
/// **Every line is asked as it stands — no reordered log** (W-43 track C, README gaps 4247 and
/// 4250). Since the owner's D87 the kernel's replay nets a break the log holds inside the running
/// block, and fork 4748911's does not (parity P81), so the comparand's "fork reading" of the
/// block's worked minutes — what P55 and P46 move the estimate by — must be the FORK's: the
/// comparand asks each backend its own (`forkplan::ForkPlan::worked`, the oracle's `worked` op).
/// Until W-43 it read the kernel's replay as the fork's, and the land step asked the oracle a log
/// with the break moved ahead of the block's `start`, where the kernel's replay happened to read it
/// as the fork does (gap 4241's edge) — the owner's D92 nets exactly that shape, so the reordering
/// went with it. And a line P81 nets on is held to its frozen `p81` too: fork 4748911's own answer
/// asked the D87 day (`forkplan::p81_after`), asked again here like every other answer.
#[test]
#[ignore]
fn the_frozen_lines_are_the_forks_oracle_answer_today() {
    let Some(bin) = forkplan::oracle_path() else {
        eprintln!("inert: set TM_ORACLE to an oracle built by kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh");
        return;
    };
    let oracle = forkplan::Oracle::new(bin);
    let mut stale = Vec::new();
    let (mut n, mut p81_lines) = (0usize, 0usize);
    for line in frozen_lines().iter().chain(forkclass::batch_lines()).chain(forkclass::driven_lines()) {
        let who = line["name"].as_str().map(str::to_string).unwrap_or_else(|| {
            format!("{}{}", line["class"].as_str().unwrap_or("?"), line["secondary"].as_str().map(|s| format!(" ({s})")).unwrap_or_default())
        });
        let b = Built::of(ClassWorld::of_json(&line["world"], tz()).expect("a stored world"));
        let prios = forkclass::kernel_answer_with_grants(&b).unwrap_or_else(|e| panic!("{who}: the kernel refused: {e}")).1;
        match forkplan::comparand_answers(&b, &prios, &oracle) {
            Err(e) => stale.push(format!("{who}: the oracle did not answer: {e}")),
            Ok(now) => {
                n += 1;
                p81_lines += usize::from(!now["p81"].is_null());
                for key in forkclass::ANSWERS {
                    if let Some(d) = forkplan::first_difference(key, &now[key], &line[key]) {
                        stale.push(format!("{who}: {d}"));
                    }
                }
            }
        }
    }
    println!(
        "frozen lines the fork oracle answers as frozen: {} of {n} ({p81_lines} carrying P81's answer, asked the D87 day; {} oracle requests)",
        n - stale.len().min(n),
        oracle.asked.lock().expect("census")
    );
    // The lines first (W-44 track C): an oracle that answers no line — a stale one, refused by name in
    // `stale` — must fail with that name, not with the P81 floor its silence also empties.
    assert!(stale.is_empty(), "the fork oracle does not answer the frozen lines as frozen:\n  {}", stale.join("\n  "));
    assert!(p81_lines > 0, "no frozen line's D87 day was asked of the oracle, so P81 was asked nothing");
}

/// **The kernel plans every driven day as the fork planned it** (W-39, README gap 3390) —
/// `forkclass::compare_line` over every line of `forkclass::FROZEN_DRIVEN`: a world the shipped
/// binary's own verbs wrote over a frozen class world (`forkclass::DRIVES`), frozen with the fork's
/// answers by value. A drive whose gap another track of the run owns is `pending`: the comparison
/// then DEMANDS the difference the gap names (a window the kernel plans otherwise) and fails, by
/// the drive's name, the moment the kernel agrees — the composition's cue to delete `pending`.
#[test]
fn the_kernel_plans_every_driven_day_the_fork_planned() {
    let lines = forkclass::driven_lines();
    assert_eq!(lines.len(), forkclass::DRIVES.len(), "one driven line per drive");
    let mut bad = Vec::new();
    for (line, d) in lines.iter().zip(forkclass::DRIVES.iter()) {
        let mut t = ClassTally::default();
        let findings = compare_line(line, &mut t);
        println!("{}: {} difference(s) with the frozen fork day{}", d.name, findings.len(), d.pending.map(|_| " (pending)").unwrap_or_default());
        match d.pending {
            None if !findings.is_empty() => bad.push(format!("{}:\n  {}", d.name, findings.join("\n  "))),
            None => {}
            Some(gap) if !findings.iter().any(|f| f.contains("window")) => bad.push(format!(
                "{}: the kernel now plans the driven day's window as the fork did — {gap} is closed on this tree: \
                 delete the drive's `pending` in `forkclass::DRIVES`, and the line compares like any other{}",
                d.name,
                if findings.is_empty() { String::new() } else { format!(" (and it then differs: {})", findings.join("; ")) }
            )),
            Some(_) => {}
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// **Every driven world is the shipped binary's own output** (W-39, README gap 3390) — the property
/// that admits it (it is not a class line, `forkclass::FROZEN_DRIVEN` says why): each line is its
/// drive's, in order, and running the drive's verbs with the built binary over its parent — the
/// primary class line it names — leaves the stored world byte for byte.
#[test]
fn every_driven_world_is_the_binarys_own_output() {
    let tz = tz();
    let lines = forkclass::driven_lines();
    assert_eq!(lines.len(), forkclass::DRIVES.len(), "one driven line per drive");
    for (line, d) in lines.iter().zip(forkclass::DRIVES.iter()) {
        assert_eq!((line["name"].as_str(), line["from"].as_str(), line["now"].as_str()), (Some(d.name), Some(d.from), Some(d.now)), "a driven line is not its drive's");
        let parent = frozen_lines().iter().find(|l| l["class"] == d.from && l["secondary"].is_null()).expect("the drive's parent is a primary line");
        let driven = forkclass::drive(&ClassWorld::of_json(&parent["world"], tz).expect("a stored world"), d).unwrap_or_else(|e| panic!("{}: {e}", d.name));
        let stored = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        assert_eq!(driven, stored, "{}: the stored world is not what the binary writes", d.name);
    }
}

/// **The binary's own rebuild HOLDS every driven world** (the W-39 repair, README gap 3710, which
/// decided gap 3398). Until the repair `forkclass::binary_holds` failed each driven world by clause 5
/// alone, on exactly `arrival`, `window` and `budget` — `tm wake` cleared the three and D42's rebuild
/// restored them from the day's `arrive` — and this test pinned that, "when gap 3398 is decided
/// either way this fails". It was decided: the rebuild derives what a wake after the last arrival
/// wrote, so no clause refuses the world, and it is asserted so. (The world stays a driven line and
/// does not move among the class lines: README gap 3730.)
#[test]
fn the_driven_worlds_are_held_by_the_binarys_rebuild() {
    for line in forkclass::driven_lines() {
        let who = line["name"].as_str().unwrap_or("?");
        let e = forkclass::binary_holds(&Built::of(ClassWorld::of_json(&line["world"], tz()).expect("a stored world"))).err().unwrap_or_default();
        println!("{who}: binary_holds says {e:?}");
        assert!(e.is_empty(), "{who}: the binary's rebuild refuses the driven world: {e:?}");
    }
}

/// **The batch is exactly the draws the shipped binary holds** (W-39, the owner's D72 with his
/// D64(b)) — a property of the file, not a list: every index below `forkclass::BATCH_DRAWS` of
/// the class draw from `forkclass::BATCH_SEED` is RE-DRAWN from the shared generator
/// (`support/plangen.rs`, `forkclass::world_of`); a line the file holds must carry that draw's
/// world byte for byte and be one `forkclass::binary_holds` accepts, and an index it does not
/// hold must be one `binary_holds` refuses — so a draw left out for no reason, or a world the
/// binary cannot build frozen in, fails by name.
#[test]
fn the_frozen_batch_is_every_draw_the_binary_holds() {
    let tz = tz();
    let held: std::collections::BTreeMap<u64, &Value> =
        forkclass::batch_lines().iter().map(|l| (l["draw"].as_u64().expect("a draw"), l)).collect();
    let mut bad = Vec::new();
    let (mut holds, mut refused) = (0usize, 0usize);
    for (index, draw) in forkclass::class_draws(forkclass::BATCH_SEED, None).take(forkclass::BATCH_DRAWS).enumerate() {
        let world = forkclass::world_of(&draw);
        let verdict = forkclass::binary_holds(&Built::of(world.clone()));
        match (held.get(&(index as u64)), verdict) {
            (Some(line), Ok(())) => {
                holds += 1;
                let stored = ClassWorld::of_json(&line["world"], tz).unwrap_or_else(|e| panic!("draw {index}: {e}"));
                if stored != world {
                    bad.push(format!("batch draw {index}: the stored world is not the generator's draw"));
                }
                // Its provenance is the one the bless writes (`forkclass::batch_line`, the writer
                // held to the file): the name, the class, the arm, the case, the seed, the index.
                let class = class_of(&Built::of(world.clone())).key();
                let want = forkclass::batch_line(index, &draw, &world, &class);
                for key in ["name", "class", "arm", "case", "seed", "draw", "world"] {
                    if want[key] != line[key] {
                        bad.push(format!("batch draw {index}: its recorded `{key}` is not its draw's provenance"));
                    }
                }
            }
            (Some(_), Err(e)) => bad.push(format!("batch draw {index}: frozen, and a world the binary cannot hold: {}", e.join("; "))),
            (None, Ok(())) => bad.push(format!("batch draw {index}: a world the binary holds, left out of the batch")),
            (None, Err(_)) => refused += 1,
        }
    }
    let beyond: Vec<u64> = held.keys().copied().filter(|d| *d as usize >= forkclass::BATCH_DRAWS).collect();
    if !beyond.is_empty() {
        bad.push(format!("batch lines for draws past BATCH_DRAWS: {beyond:?}"));
    }
    println!("seeded batch: {holds} draw(s) held, {refused} refused by the binary, of {}", forkclass::BATCH_DRAWS);
    assert!(bad.is_empty(), "the frozen batch is not the draws the binary holds:\n  {}", bad.join("\n  "));
}

/// **What the batch holds that the classes do not** (W-39, the owner's D72): the class file holds
/// ONE primary world per class (and the worlds derived from them); the batch is the generator's
/// own mix. Counted here, from the files, so the README's figures are this test's output and a
/// re-bless that loses the batch's breadth fails: worlds per class, the widening arms, and the
/// generator's coordinates the classes pin once — items, walls, routines, done blocks, the
/// learned multiplier, a logged break.
#[test]
fn the_batch_holds_what_the_classes_do_not() {
    let tz = tz();
    let census = |lines: &[&Value]| {
        let mut by_class: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
        let mut arms: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
        let (mut items, mut walls, mut routines, mut dones, mut mults, mut breaks) =
            (BTreeSet::new(), BTreeSet::new(), BTreeSet::new(), BTreeSet::new(), BTreeSet::new(), 0usize);
        for l in lines {
            *by_class.entry(l["class"].as_str().unwrap_or("?").to_string()).or_default() += 1;
            *arms.entry(l["arm"].as_str().unwrap_or("?").to_string()).or_default() += 1;
            let w = ClassWorld::of_json(&l["world"], tz).expect("a stored world");
            let doc = |p: &str| w.docs.iter().find(|(q, _)| q == p).map(|(_, t)| t.clone()).unwrap_or_default();
            items.insert(doc("week/2026-W37.md").lines().filter(|x| x.starts_with("- [")).count());
            walls.insert(doc("calendar/2026-W37.md").lines().filter(|x| x.starts_with("- [")).count());
            routines.insert(doc("routines.md"));
            dones.insert(w.log.lines().filter(|x| x.contains("\"ev\":\"done\"")).count());
            mults.insert(w.mult.clone());
            breaks += usize::from(w.log.lines().any(|x| x.contains("\"ev\":\"break\"")));
        }
        (by_class, arms, items.len(), walls.len(), routines.len(), dones.len(), mults.len(), breaks)
    };
    let batch: Vec<&Value> = forkclass::batch_lines().iter().collect();
    let classes: Vec<&Value> = frozen_lines().iter().filter(|l| l["secondary"].is_null()).collect();
    let (bc, ba, bi, bw, br, bd, bm, bb) = census(&batch);
    let (cc, ca, ci, cw, cr, cd, cm, cb) = census(&classes);
    let many = bc.values().filter(|n| **n >= 2).count();
    println!(
        "seeded batch: {} worlds over {} classes ({many} with two or more; the most, {:?}), arms {ba:?}; distinct item \
         counts {bi}, wall counts {bw}, routine sets {br}, done-block counts {bd}, multipliers {bm}; logged breaks {bb}",
        batch.len(), bc.len(), bc.iter().max_by_key(|(_, n)| **n),
    );
    println!(
        "class primaries: {} worlds over {} classes (one each), arms {ca:?}; distinct item counts {ci}, wall counts {cw}, \
         routine sets {cr}, done-block counts {cd}, multipliers {cm}; logged breaks {cb}",
        classes.len(), cc.len(),
    );
    assert!(bc.keys().all(|k| cc.contains_key(k)), "a batch world of a class outside the class space: {bc:?}");
    assert!(many >= 10, "the batch holds two or more worlds of only {many} classes: {bc:?}");
    assert_eq!(ba.len(), 4, "the batch draws every arm's widenings: {ba:?}");
    assert!(bi > ci && br > cr, "the batch is not broader than the classes in items ({bi} vs {ci}) or routines ({br} vs {cr})");
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
            // A line is DRAWN (no `derived`) exactly when its floor is one a line is drawn for.
            assert_eq!(
                line["derived"].is_null(),
                DRAWN_FLOORS.contains(&why),
                "{key}: a `{why}` line is {} and its floor says otherwise",
                if line["derived"].is_null() { "drawn" } else { "derived" }
            );
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
/// exactly that set. `window` is derived too (W-38, README gap 3200): every
/// primary world with a dated window task (`forkclass::window_worlds`), held to
/// exactly that set by [`the_frozen_window_worlds_are_every_one_the_task_derives`];
/// `worked` (W-38, README gap 3282): a primary world with a break logged inside
/// its running block (`forkclass::worked_worlds`), held likewise by
/// [`the_frozen_worked_worlds_are_every_one_the_inner_break_derives`]; and `overrun`
/// (W-38, README gaps 3207 and 3480): a primary world whose running break is carried
/// past `break_min` (`forkclass::overrun_worlds`), held likewise by
/// [`the_frozen_overrun_worlds_are_every_one_the_break_derives`]; and since W-39 `typed`
/// (README gap 3473): the world after a meeting with the pause typed ten minutes wider
/// than the meeting at each end (`forkclass::typed_worlds`, P56's two-piece cut), and
/// `order` (README gaps 3474 and 3529): an interruption begun at a wall's start, planned
/// at the wall's end (`forkclass::order_worlds`, gap 3281's order), each held by
/// [`the_frozen_typed_and_order_worlds_are_every_one_their_rules_derive`].
const SECONDARY_FLOORS: [&str; 9] = ["rest_debt", "whatif", "p52", "d61", "window", "worked", "overrun", "typed", "order"];

/// The floors of [`SECONDARY_FLOORS`] a secondary line is DRAWN for (the rest are derived):
/// `rest_debt` and `whatif` (W-36), and `p52` (W-38, README gap 3282) — a day whose what-if the
/// host's grown facts re-rank, so the kernel departs from the shipped TUI's `diff` (parity P52),
/// which no class representative draws.
const DRAWN_FLOORS: [&str; 3] = ["rest_debt", "whatif", "p52"];

/// **What the frozen days cover beyond their class**, counted off the FORK's
/// frozen days (never the kernel's, which is the value under test): each floor
/// is one the differential arms hold their own random draws to, so the frozen
/// set is not narrower than the arms it stands in for at R3.
#[test]
fn the_frozen_days_cover_what_the_arms_floors_demand() {
    let mut kinds = BTreeSet::new();
    let mut n = [0usize; 21];
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
        // Since W-38 the compared side is the shipped TUI's (`full`), or on a parity-P52 day the
        // fork's ranked as the kernel ranks the grown request (`grown`).
        let w = &line["whatif"];
        if !w.is_null() {
            let side = if w["grown"].is_null() { &w["full"] } else { &w["grown"] };
            n[16] += side["removed"].as_array().map_or(0, Vec::len);
            n[20] += usize::from(!w["grown"].is_null());
        }
        // A secondary line drawn for P52 meets its floor itself (W-38).
        if line["secondary"] == "p52" {
            assert!(!w["grown"].is_null(), "{}: a `p52` line whose grown facts do not re-rank its what-if", line["class"]);
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
        "what-ifs the host's grown facts re-rank away from the shipped TUI's (P52)",
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
        // P73's reading, the binary's (the W-41 repair, README gap 4143).
        let started = brk.started_at(b.cfg.tz, now).expect("filtered");
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
///
/// **And a region holds nothing but the fork** (W-45 track C, README gap 4682): every `#[test]`
/// in a region reaches the fork's planner (`forkday::region_tests_unreached`), so R3's deletion
/// takes no test that asked the kernel alone, no harness check and no bless — W-45 found a bless
/// that reached no fork (the class worlds' re-draw), a precondition's bite test and the kernel halves
/// of four tests sitting in regions, and moved each out. The guard reads the regions while
/// `tm-core/src/planner.rs` exists and demands none once it is gone, so R3's deletion of both leaves
/// it nothing to rewrite.
#[test]
fn every_test_that_reaches_the_fork_keeps_it_in_one_region() {
    let mut bad = Vec::new();
    let mut regions = Vec::new();
    let mut exempt_seen = BTreeSet::new();
    let files: Vec<(String, String)> = srcwalk::every_rust_file()
        .into_iter()
        .filter(|(label, _)| label.split('/').any(|seg| seg == "tests"))
        .collect();
    // A region's names are the whole test tree's (W-38 land step, README gap 3510): every other
    // file's region names, read beside this file's own.
    let names: Vec<(String, Vec<String>)> = files.iter().map(|(l, t)| (l.clone(), forkday::region_names(t))).collect();
    for (label, text) in &files {
        let label = label.clone();
        let foreign: Vec<(String, String)> = names
            .iter()
            .filter(|(l, _)| *l != label)
            .flat_map(|(l, n)| n.iter().map(move |x| (forkday::module_of(l), x.clone())))
            .collect();
        let scan = forkday::fork_scan_with(text, &foreign);
        if !scan.deleted {
            regions.push(label.clone());
        }
        let unreached = forkday::region_tests_unreached(text, &foreign);
        if !unreached.is_empty() {
            bad.push(format!("{label}: the fork region holds test(s) that reach no fork planner, which R3 would delete for nothing: {unreached:?}"));
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
    println!("files with one fork region: {} ({})", regions.len(), regions.join(", "));
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    // Once R3 deletes `planner.rs`, a region left behind is dead code and none may remain.
    //
    // **The scan reads its banners on both sides of R3 without a count** (W-45 track C, README gap
    // 4682). Until W-45 a floor demanded seven regions while `planner.rs` exists, so "a guard that
    // reads no banner is reading nothing" — and R3 simulated as W-44 simulated it (the regions
    // deleted, the fork's file kept for the binary) went red on the floor alone. The escape check
    // above already bites a scan that reads no banner: every needle a region holds would read as an
    // escape (`the_fork_scan_sees_a_reference_outside_its_region_and_only_there` and
    // `the_region_guard_sees_code_outside_that_needs_the_region` bite the reader), and
    // `srcwalk::every_rust_file` refuses a walk of fewer than a hundred files.
    let fork_here = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-core/src/planner.rs").exists();
    if !fork_here {
        assert!(regions.is_empty(), "the fork is gone and regions remain: {regions:?}");
    }
}

/// **The region guard sees code outside that NEEDS the region** (W-38, README gap 3472;
/// AGENTS §5.8): a top-level `fn`, `static` or type the region declares, named by a code line
/// outside it, is an escape — R3 deletes the declaration, so the line would not build — while
/// the same name in a comment, in a string, as part of a longer name, or as a method or local
/// declared indented inside the region, is not. The banners are spelled in pieces so this file
/// holds no region of its own here.
#[test]
fn the_region_guard_sees_code_outside_that_needs_the_region() {
    let b = ["// BEGIN THE FORK", " PLANNER\n"].concat();
    let e = ["// END THE FORK", " PLANNER\n"].concat();
    let region = "fn helper() -> u8 { 1 }\nstatic TABLE: [u8; 1] = [1];\nimpl Thing {\n    fn method(&self) {}\n}\n";
    let quiet = "// helper() is named in a comment\nlet s = \"helper()\";\nlet x = helpers();\nlet y = t.method();\nlet w = t.helper;\n";
    let src = format!("{quiet}{b}{region}{e}");
    let over = forkday::fork_scan(&src).escapes;
    assert!(over.is_empty(), "the guard read a comment, a string, a longer name or a field as the region's: {over:?}");
    let calls = format!("{b}{region}{e}let x = helper();\nlet z = TABLE[0];\n");
    let scan = forkday::fork_scan(&calls);
    assert_eq!(scan.escapes.len(), 2, "the guard saw {} of the region's two names used outside it: {:?}", scan.escapes.len(), scan.escapes);
    assert!(scan.escapes.iter().any(|x| x.contains("`helper`, which the region defines")), "{:?}", scan.escapes);
    assert!(scan.escapes.iter().any(|x| x.contains("`TABLE`, which the region defines")), "{:?}", scan.escapes);
    assert_eq!(forkday::top_level_name("pub fn kernel_prios(plan: &Value)"), Some("kernel_prios".to_string()));
    // **Another file's region** (W-38 land step, README gap 3510): `kernel_unplaced_banner.rs`
    // imported `planner_common`'s region's `Fork` outside any region, and the per-file guard was
    // green. A foreign region's name used outside is an escape; the same name DECLARED outside
    // this file's region is this file's own.
    let foreign = vec![("planner_common".to_string(), "Fork".to_string())];
    let escaped = forkday::fork_scan_with("use planner_common::{at, Fork};\nlet d = planner_common::Fork.day();\n", &foreign).escapes;
    assert_eq!(escaped.len(), 2, "the guard saw {} of two reaches into another region: {escaped:?}", escaped.len());
    let own = forkday::fork_scan_with("use planner_common::{at, Kernel};\nlet Fork = 1;\nlet d = other::Fork;\n", &foreign).escapes;
    assert!(own.is_empty(), "a name not reached through the region's module was read as the region's: {own:?}");
    assert_eq!(forkday::module_of("tm/tests/planner_common/mod.rs"), "planner_common");
    assert_eq!(forkday::module_of("tm/tests/support/forkclass.rs"), "forkclass");
    assert_eq!(forkday::top_level_name("    fn day(&self)"), None, "a method is not a top-level name");
}

/// **A region's test that reaches no fork is seen, and only such a test** (AGENTS §5.8; W-45 track
/// C, README gap 4682): in a region, a test that calls the fork's planner, one that reaches it
/// through a region helper, through a region struct whose `impl` plans, through a method of an
/// `impl` the region adds to a type declared elsewhere, or through another file's region name, all
/// reach it; a test that asks the kernel alone, or names the fork only in a comment or a string, does
/// not — inside a `proptest!` block as at column zero. The banners are spelled in pieces so this
/// file holds no region of its own here.
#[test]
fn a_region_test_that_reaches_no_fork_is_seen() {
    let b = ["// BEGIN THE FORK", " PLANNER\n"].concat();
    let e = ["// END THE FORK", " PLANNER\n"].concat();
    let p = ["planner", "::plan"].concat();
    let region = format!(
        "fn helper() -> u8 {{ {p}(&x); 1 }}\nstruct Fork;\nimpl Planner for Fork {{\n    fn day(&self) {{ {p}(&y); }}\n}}\nimpl World {{\n    fn shipped(&self) {{ {p}(&z); }}\n}}\n\
         #[test]\nfn direct() {{ {p}(&a); }}\n#[test]\nfn through_a_helper() {{ helper(); }}\n#[test]\nfn through_a_struct() {{ check(&Fork); }}\n\
         #[test]\nfn through_a_method() {{ w.shipped(); }}\n#[test]\nfn through_another_region() {{ othermod::Backend.go(); }}\n\
         #[test]\nfn kernel_alone() {{ kernel_day(); }}\n#[test]\nfn only_in_prose() {{\n    // {p}(&x) is named here\n    let s = \"{p}\";\n}}\n\
         proptest! {{\n    #[test]\n    fn drawn_direct(x in any::<u8>()) {{ {p}(&x); }}\n    #[test]\n    fn drawn_kernel(x in any::<u8>()) {{ kernel_day(); }}\n}}\n"
    );
    let src = format!("fn outside() {{}}\n{b}{region}{e}");
    // Another file's region name, as the guard reads the in-tree backend's — spelled as names no real region
    // declares, so this file's own code holds no reach into a region.
    let foreign = vec![("othermod".to_string(), "Backend".to_string())];
    let mut unreached = forkday::region_tests_unreached(&src, &foreign);
    unreached.sort();
    assert_eq!(unreached, vec!["drawn_kernel", "kernel_alone", "only_in_prose"], "the reader saw {unreached:?}");
    assert!(forkday::region_tests_unreached("#[test]\nfn kernel_alone() { kernel_day(); }\n", &foreign).is_empty(), "a test outside any region was read as a region's");
}

/// **A grouped or renamed import of the fork's planner is a reach** (AGENTS §5.8; W-45 track C,
/// README gap 4683): `use tm_core::{config, planner as fp};` names the module by no needle, so every
/// later `fp::diff(…)` reached the fork unseen by both scans. Outside a region it is an escape, on one
/// line or several; inside one, a test calling through the alias — or importing it in its own body —
/// reaches the fork; and an import that merely holds the word (`planwire`, `planner_common`, a path
/// not rooted at the library) is neither. The banners and the crate's name are spelled in pieces so
/// this file holds no region and no import of its own here.
#[test]
fn a_grouped_or_renamed_import_of_the_fork_is_a_reach() {
    let b = ["// BEGIN THE FORK", " PLANNER\n"].concat();
    let e = ["// END THE FORK", " PLANNER\n"].concat();
    let m = ["tm_", "core"].concat();
    let one = forkday::fork_scan(&format!("{b}{e}use {m}::{{config, planner as fp}};\nfn f() {{ fp::diff(&a, &b); }}\n")).escapes;
    assert!(one.len() == 1 && one[0].contains("a `use` of the fork's planner module"), "a renamed import outside the region: {one:?}");
    let several = forkday::fork_scan(&format!("{b}{e}use {m}::{{\n    config,\n    planner,\n}};\n")).escapes;
    assert!(several.len() == 1 && several[0].contains("a `use` of the fork's planner module"), "a grouped import over four lines: {several:?}");
    let quiet = format!("{b}{e}use {m}::{{config, planwire}};\nuse planner_common::{{at, Kernel}};\nuse other::{{planner as p}};\nfn g() {{ let planner = 1; }}\n");
    let over = forkday::fork_scan(&quiet).escapes;
    assert!(over.is_empty(), "an import that merely holds the word was read as the fork's: {over:?}");
    let region = format!(
        "{b}use {m}::{{planner as fp}};\n#[test]\nfn through_the_alias() {{ fp::diff(&a, &b); }}\n#[test]\nfn kernel_alone() {{ kernel_day(); }}\n\
         #[test]\nfn imports_it_itself() {{\n    use {m}::{{planner as q}};\n    q::diff(&a, &b);\n}}\n{e}"
    );
    assert_eq!(forkday::region_tests_unreached(&region, &[]), vec!["kernel_alone"], "the alias was not read as a reach");
}

/// **A stored world reads back as the bytes it was written from** — the frozen
/// file is its own input, so `ClassWorld`'s two directions are one another's
/// inverse on every line of it.
#[test]
fn every_frozen_world_round_trips_through_its_json() {
    for line in frozen_lines().iter().chain(forkclass::batch_lines()).chain(forkclass::driven_lines()) {
        let w = ClassWorld::of_json(&line["world"], tz()).expect("a stored world");
        assert_eq!(w.to_json(), line["world"], "{}: the world does not round-trip", line["class"]);
    }
}

/// **The digest of every frozen day is its day's** (W-39): `forkplan::day_hash`, the digest the
/// shared comparand writes after it bends a day on its JSON (P46's row, P47's clip), is
/// `DayPlan::hash` of that day — held here on every day a frozen line carries: the comparand
/// and shipped days of the classes, the batch and the driven lines, and `plan-basic`'s. A digest
/// that disagreed with the fork's on one of them would re-bless every line it touches.
#[test]
fn the_hash_of_every_frozen_day_is_its_digest() {
    let mut n = 0usize;
    let mut bad = Vec::new();
    let basic = forkday::frozen_basic_days();
    let days = frozen_lines()
        .iter()
        .chain(forkclass::batch_lines())
        .chain(forkclass::driven_lines())
        .flat_map(|l| [l["day"].clone(), l["shipped"].clone()])
        .chain(basic.iter().map(|l| serde_json::json!({"hash": l["hash"], "day": l["day"]})))
        .filter(|d| !d.is_null());
    for d in days {
        n += 1;
        let got = forkplan::day_hash(&d["day"]);
        if Some(got.as_str()) != d["hash"].as_str() {
            bad.push(format!("a frozen day digests to {got}, its line says {}", d["hash"]));
        }
    }
    println!("frozen days whose digest is their day's: {} of {n}", n - bad.len());
    assert!(n > 300 && bad.is_empty(), "{n} day(s): {bad:?}");
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
        // The world each candidate draw builds — re-derived by the line's own rule for a
        // derived line: D61's at its instant, or the dated window task (W-38).
        let worlds: Vec<ClassWorld> = draws
            .iter()
            .map(forkclass::world_of)
            .filter_map(|w| match (at, line["secondary"].as_str()) {
                (None, _) => Some(w),
                (Some(_), Some("window")) => forkclass::window_worlds(&w).into_iter().next(),
                (Some(_), Some("worked")) => forkclass::worked_worlds(&w).into_iter().next(),
                (Some(_), Some("overrun")) => forkclass::overrun_worlds(&w).into_iter().next(),
                (Some(at), Some("typed")) => forkclass::typed_worlds(&w).into_iter().find(|d| d.now == at),
                (Some(_), Some("order")) => forkclass::order_worlds(&w).into_iter().next(),
                (Some(at), _) => forkclass::d61_worlds(&w).into_iter().find(|(d, _)| d.now == at).map(|(d, _)| d),
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

/// **README gap 320's two other inputs are worlds the shipped binary cannot hold** (W-38, owner
/// D64(b)): a stored window with `date: null`, and a stored window with no budget beside it —
/// the two inputs gap 3341 left open when it closed the third (a late day's window past
/// midnight). Each is `idle/lounge`'s frozen world with the one field taken out of
/// `.tm/state.json`, and each is refused by `forkclass::binary_holds`' clause 5, by name: with
/// the cache deleted the binary rebuilds it from the log (D42), and the log's `arrive` line —
/// which `tm arrive` writes whenever it stores a window — carries the date and the budget
/// beside the window. So neither can be frozen (D64(b)); the kernel's reading of them is the
/// planner's own business (`Planner.PlanReq.window`), and this pins that the comparand cannot
/// hold them rather than leaving it to a sentence.
#[test]
fn gap_320s_two_inputs_are_worlds_the_binary_cannot_hold() {
    let line = frozen_lines().iter().find(|l| l["class"] == "idle/lounge" && l["secondary"].is_null()).expect("the primary line");
    let w = ClassWorld::of_json(&line["world"], tz()).expect("a stored world");
    assert!(w.state.window.is_some() && w.state.date.is_some() && w.state.budget.is_some(), "the stored world holds all three");
    for (field, bent) in [
        ("date", { let mut x = w.clone(); x.state.date = None; x }),
        ("budget", { let mut x = w.clone(); x.state.budget = None; x }),
    ] {
        let e = forkclass::binary_holds(&Built::of(bent)).err().unwrap_or_default();
        println!("a stored window with no `{field}`: {e:?}");
        assert!(
            e.iter().any(|m| m.starts_with("5:") && m.contains(&format!("`{field}`"))),
            "a stored window with no `{field}` is not refused by clause 5 on `{field}`: {e:?}"
        );
    }
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
/// §5.8): each of its clauses fails, by its number, on a frozen world bent into a
/// state the binary cannot hold — the pre-W-37 shape among them — and the unbent
/// worlds pass (the test above). **Clause 4 is withdrawn since W-39 (README gap
/// 3536)**: its two plants — an interrupted block left running, a running block
/// paused for nothing — are refused by clause 5's pause, which asks the binary.
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
    // 5, the block's pause (clause 4's two plants until W-39, README gap 3536): an
    // interrupted block left running, a running block paused for nothing, and a block under
    // a running break left running — each refused by the binary's own derivation, by name.
    let paused_bites = |w: &ClassWorld| {
        let e = forkclass::binary_holds(&Built::of(w.clone())).err().unwrap_or_default();
        assert!(
            e.iter().any(|m| m.starts_with("5:") && m.contains("`active.paused`")),
            "clause 5 did not refuse the block's pause: {e:?}"
        );
    };
    let mut w = world("interrupted-block/lounge");
    assert!(w.state.interrupt.as_ref().is_some_and(|i| i.id.is_some()), "interrupted-block/lounge's interruption names its block");
    if let Some(a) = w.state.active.as_mut() {
        a.paused = false;
    }
    paused_bites(&w);
    let mut w = world("running/lounge");
    if let Some(a) = w.state.active.as_mut() {
        a.paused = true;
    }
    paused_bites(&w);
    let mut w = world("break-block/lounge");
    assert!(w.state.active.as_ref().is_some_and(|a| a.paused), "break-block/lounge's block is paused by its running break");
    if let Some(a) = w.state.active.as_mut() {
        a.paused = false;
    }
    paused_bites(&w);
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
    for line in frozen_lines().iter().chain(forkclass::batch_lines()).chain(forkclass::driven_lines()) {
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
            // Since W-38 D61 also derives the world after the meeting, which is no longer a wall
            // on `now` (README gap 3320): a derived line is keyed by its PARENT's class and files
            // under its own world's class, which `the_frozen_file_holds_every_class_the_arms_draw`
            // holds every line to.
            let class = class_of(&Built::of(d.clone())).key();
            want.insert((line["class"].as_str().unwrap_or_default().to_string(), pause.to_rfc3339(), class, d.to_json().to_string()));
        }
    }
    let have: BTreeSet<(String, String, String, String)> = frozen_lines()
        .iter()
        .filter(|l| l["secondary"] == "d61")
        .map(|l| {
            assert!(
                frozen_lines().iter().any(|p| p["secondary"].is_null() && p["class"] == l["derived"]["from"]),
                "a d61 line is derived from a primary line: {}",
                l["derived"]["from"]
            );
            (
                l["derived"]["from"].as_str().unwrap_or_default().to_string(),
                l["derived"]["pause"].as_str().unwrap_or_default().to_string(),
                l["class"].as_str().unwrap_or_default().to_string(),
                l["world"].to_string(),
            )
        })
        .collect();
    let missing: Vec<String> = want.difference(&have).map(|w| format!("{} at pause {} as {}", w.0, w.1, w.2)).collect();
    let extra: Vec<String> = have.difference(&want).map(|w| format!("{} at pause {} as {}", w.0, w.1, w.2)).collect();
    let after = want.iter().filter(|w| !w.2.starts_with("wall-on-now/")).count();
    println!("frozen D61 worlds: {} derived ({after} after the meeting), {} held", want.len(), have.len());
    assert!(missing.is_empty() && extra.is_empty(), "D61 worlds missing {missing:?}, held and not derived {extra:?}");
    assert!(!want.is_empty(), "no primary line's world is one D61 pauses");
    assert!(after > 0, "D61 derives no world after a meeting (README gap 3320)");
}

/// **The frozen window-task worlds are exactly the worlds the task derives** (W-38,
/// README gap 3200): for every PRIMARY line, `forkclass::window_worlds` of its world —
/// the same world with `plan-basic`'s dated window task added — is a `window` line
/// carrying that world, filed under the SAME class as its parent (a window task is no
/// wall, block, break or interruption, so it moves no coordinate of the class), and
/// no `window` line is anything else. And the mark is there to compare: the fork's
/// frozen days of those lines draw the task's Routine row marked `hot` (`⚠`) on at least
/// one line of every run state.
#[test]
fn the_frozen_window_worlds_are_every_one_the_task_derives() {
    let tz = tz();
    let mut want = BTreeSet::new();
    for line in frozen_lines().iter().filter(|l| l["secondary"].is_null()) {
        let w = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        for d in forkclass::window_worlds(&w) {
            let class = class_of(&Built::of(d.clone())).key();
            assert_eq!(class, line["class"].as_str().unwrap_or_default(), "the window task moved a world's class");
            assert_eq!(d.state, w.state, "the window task moved `.tm/state.json`");
            want.insert((line["class"].as_str().unwrap_or_default().to_string(), d.to_json().to_string()));
        }
    }
    let have: BTreeSet<(String, String)> = frozen_lines()
        .iter()
        .filter(|l| l["secondary"] == "window")
        .map(|l| {
            assert_eq!(l["derived"]["from"], l["class"], "a window line files under its parent's class");
            (l["class"].as_str().unwrap_or_default().to_string(), l["world"].to_string())
        })
        .collect();
    let missing: Vec<&String> = want.difference(&have).map(|w| &w.0).collect();
    let extra: Vec<&String> = have.difference(&want).map(|w| &w.0).collect();
    assert!(missing.is_empty() && extra.is_empty(), "window worlds missing {missing:?}, held and not derived {extra:?}");
    // The mark, read off the FORK's frozen days (the value under test is the kernel's).
    let mut runs_marked = BTreeSet::new();
    let mut marks = 0usize;
    for l in frozen_lines().iter().filter(|l| l["secondary"] == "window") {
        // The rows the kernel is held to after a running break: P67's where it departs, else
        // P45's, else the day (README gap 3958).
        let day = [&l["p67"], &l["p45"]].into_iter().find(|v| !v.is_null()).unwrap_or(&l["day"]["day"]);
        let rows = day.get("segments").or_else(|| day.get("rows")).and_then(Value::as_array).map(Vec::as_slice).unwrap_or_default();
        let n = rows.iter().filter(|s| s["kind"] == "routine" && s["flags"]["hot"] == true && s["item"] == "xaa").count();
        if n > 0 {
            runs_marked.insert(l["class"].as_str().unwrap_or_default().split('/').next().unwrap_or_default().to_string());
        }
        marks += n;
    }
    println!("frozen window-task worlds: {} derived, {} held; `⚠` on the task's row {marks} time(s), in run states {runs_marked:?}", want.len(), have.len());
    assert_eq!(want.len(), frozen_lines().iter().filter(|l| l["secondary"].is_null()).count(), "a primary line derives no window world");
    let runs: BTreeSet<String> = Run::all().into_iter().map(|r| r.word().to_string()).collect();
    assert_eq!(runs_marked, runs, "a run state holds no frozen day whose window task is marked `⚠`");
}

/// **The frozen inner-break worlds are exactly the worlds the break derives** (W-38,
/// README gap 3282; parity P55): for every PRIMARY line `forkclass::worked_worlds`
/// answers for, a `worked` line carrying that world under its parent's class, and no
/// `worked` line is anything else — and on every one the host's worked minutes are NOT
/// fork 4748911's reading (so the P55 comparand departs, which the line records as `p55`).
///
/// **Since the owner's D87 (W-42 track R, parity P81, README gaps 4137 and 4240) the kernel's
/// replay nets the logged break as the host does**, so on every one of these worlds the host's
/// minutes ARE the log's — one reading, the parent's less the inner break exactly — and fork
/// 4748911's reading is the parent's, which counts the break as worked. Two consequences, each
/// asserted rather than assumed: a world whose parent was in overtime by fewer minutes than the
/// break is RUNNING to the kernel, so its line files under that class with `derived.from` still
/// naming the parent's (README gap 4240's re-filing of `overtime/home` and `overtime/travel`);
/// and on every `worked` world P81 nets exactly the inner break (`support/p81.rs`' `netted_breaks`,
/// fork 4748911's own machine read off the log), the rule the comparison holds the kernel by.
#[test]
fn the_frozen_worked_worlds_are_every_one_the_inner_break_derives() {
    let tz = tz();
    let mut want = BTreeSet::new();
    let mut refiled = 0usize;
    for line in frozen_lines().iter().filter(|l| l["secondary"].is_null()) {
        let w = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        let parent = Built::of(w.clone());
        let pc = class_of(&parent);
        assert_eq!(pc.key(), line["class"].as_str().unwrap_or_default(), "a primary line's world classifies as another class");
        for d in forkclass::worked_worlds(&w) {
            let b = Built::of(d.clone());
            let dc = class_of(&b);
            assert_eq!(d.state, w.state, "the inner break moved `.tm/state.json`");
            // D87: ONE reading — the host's and the kernel's log reading agree, and both are the
            // parent's (fork 4748911's reading of this world: it nets no break) less the break.
            let net = parent.worked().map(|m| m.saturating_sub(forkclass::INNER_BREAK.1));
            assert_eq!(b.worked(), net, "the kernel's replay does not net the inner break (P81)");
            assert_eq!(forkclass::host_worked(&b), b.worked(), "the inner break left the host's reading and the log's apart");
            assert_ne!(forkclass::host_worked(&b), parent.worked(), "the inner break left fork 4748911's reading and the host's equal");
            // The class is the parent's, or — P81's re-filing — the parent was in overtime by its
            // block's span and the break's minutes take the kernel's reading below the estimate.
            if dc != pc {
                let est = d.state.active.as_ref().map(|a| a.est_min);
                assert!(
                    pc.run == Run::Overtime
                        && dc.run == Run::Running
                        && dc.shape == pc.shape
                        && est.is_some_and(|e| parent.worked().is_some_and(|p| p >= e) && net.is_some_and(|n| n < e)),
                    "the inner break moved {} to {} for another reason than P81's netting",
                    pc.key(),
                    dc.key()
                );
                refiled += 1;
            }
            want.insert((pc.key(), dc.key(), d.to_json().to_string()));
        }
    }
    let have: BTreeSet<(String, String, String)> = frozen_lines()
        .iter()
        .filter(|l| l["secondary"] == "worked")
        .map(|l| {
            assert_eq!(l["p55"]["p55"], true, "a worked line whose comparand does not read the host's minutes");
            // P81's rule holds on it: the log nets exactly its inner break, in its running block.
            let w = ClassWorld::of_json(&l["world"], tz).expect("a stored world");
            let netted = p81::netted_breaks(&w.log, &[]).expect("the log reads");
            let running = w.state.active.as_ref().map(|a| a.id.as_str().to_string());
            assert!(
                netted.len() == 1 && Some(&netted[0].id) == running.as_ref(),
                "{}: P81 nets {netted:?} in a worked world, not its one inner break (README gap 4240)",
                l["class"]
            );
            (
                l["derived"]["from"].as_str().unwrap_or_default().to_string(),
                l["class"].as_str().unwrap_or_default().to_string(),
                l["world"].to_string(),
            )
        })
        .collect();
    let missing: Vec<(&String, &String)> = want.difference(&have).map(|w| (&w.0, &w.1)).collect();
    let extra: Vec<(&String, &String)> = have.difference(&want).map(|w| (&w.0, &w.1)).collect();
    println!("frozen inner-break worlds: {} derived, {} held, {refiled} re-filed by P81's netting", want.len(), have.len());
    assert!(missing.is_empty() && extra.is_empty(), "worked worlds missing {missing:?}, held and not derived {extra:?}");
    assert!(!want.is_empty(), "no primary line's running block can take an inner break");
    assert!(refiled > 0, "no worked world's class is moved by P81's netting: the re-filing clause is asserted on nothing");
}

/// **The frozen overrun worlds are exactly the worlds the break derives** (W-38, README gaps
/// 3207 and 3480; parity P45): for every PRIMARY line `forkclass::overrun_worlds` answers for,
/// an `overrun` line carrying that world under its parent's class, and no `overrun` line is
/// anything else — on every one the break still runs, has run at least `break_min` (so P45's
/// comparand logs it and the fork's counter resets), and the line carries P45's comparand.
#[test]
fn the_frozen_overrun_worlds_are_every_one_the_break_derives() {
    let tz = tz();
    let mut want = BTreeSet::new();
    for line in frozen_lines().iter().filter(|l| l["secondary"].is_null()) {
        let w = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
        for d in forkclass::overrun_worlds(&w) {
            let b = Built::of(d.clone());
            assert_eq!(class_of(&b).key(), line["class"].as_str().unwrap_or_default(), "carrying `now` moved a world's class");
            assert_eq!((&d.state, &d.log, &d.docs), (&w.state, &w.log, &w.docs), "an overrun world changed more than `now`");
            let brk = d.state.break_.as_ref().expect("a running break");
            let t = brk.started_at(tz, d.now).expect("started");
            assert!(d.now - t >= Duration::minutes(i64::from(b.cfg.day.break_min)), "the break has not run `break_min`");
            want.insert((line["class"].as_str().unwrap_or_default().to_string(), d.to_json().to_string()));
        }
    }
    let have: BTreeSet<(String, String)> = frozen_lines()
        .iter()
        .filter(|l| l["secondary"] == "overrun")
        .map(|l| {
            assert_eq!(l["derived"]["from"], l["class"], "an overrun line files under its parent's class");
            assert_eq!(l["p45"]["p45"], true, "an overrun line carries no P45 comparand");
            (l["class"].as_str().unwrap_or_default().to_string(), l["world"].to_string())
        })
        .collect();
    let missing: Vec<&String> = want.difference(&have).map(|w| &w.0).collect();
    let extra: Vec<&String> = have.difference(&want).map(|w| &w.0).collect();
    println!("frozen overrun worlds: {} derived, {} held", want.len(), have.len());
    assert!(missing.is_empty() && extra.is_empty(), "overrun worlds missing {missing:?}, held and not derived {extra:?}");
    assert!(want.len() >= 3, "only {} primary break world(s) can be carried past `break_min`", want.len());
}

/// **The frozen `typed` and `order` worlds are exactly the worlds their rules derive** (W-39,
/// README gaps 3473, 3474 and 3529), as the other derived kinds are: from every PRIMARY world,
/// `forkclass::typed_worlds` (a meeting's pause typed ten minutes wider at each end, after it)
/// and `forkclass::order_worlds` (an interruption begun at a wall's start, at the wall's end)
/// are lines of their kind carrying that world, and no line of either kind is anything else —
/// and each line's frozen day holds the shape it was derived for: a typed line's shipped day
/// (fork 4748911's drawing) the whole pause across the wall and its comparand the two pieces
/// P56's cut leaves (`p56`); an order line's day a Wall row and a Lost row tied on `(start,
/// end)`, the Wall FIRST — fork `collect_walls`' order, which the kernel before W-38 track R
/// did not draw.
#[test]
fn the_frozen_typed_and_order_worlds_are_every_one_their_rules_derive() {
    let tz = tz();
    for kind in ["typed", "order"] {
        let mut want = BTreeSet::new();
        for line in frozen_lines().iter().filter(|l| l["secondary"].is_null()) {
            let w = ClassWorld::of_json(&line["world"], tz).expect("a stored world");
            let derived = if kind == "typed" { forkclass::typed_worlds(&w) } else { forkclass::order_worlds(&w) };
            for d in derived {
                want.insert((line["class"].as_str().unwrap_or_default().to_string(), d.to_json().to_string()));
            }
        }
        let held: Vec<&Value> = frozen_lines().iter().filter(|l| l["secondary"] == kind).collect();
        let have: BTreeSet<(String, String)> = held
            .iter()
            .map(|l| (l["derived"]["from"].as_str().unwrap_or_default().to_string(), l["world"].to_string()))
            .collect();
        let missing: Vec<&String> = want.difference(&have).map(|w| &w.0).collect();
        let extra: Vec<&String> = have.difference(&want).map(|w| &w.0).collect();
        println!("frozen {kind} worlds: {} derived, {} held", want.len(), have.len());
        assert!(missing.is_empty() && extra.is_empty(), "{kind} worlds missing {missing:?}, held and not derived {extra:?}");
        assert!(!want.is_empty(), "no primary world derives a `{kind}` world");
        for l in &held {
            let who = format!("{} ({kind})", l["class"].as_str().unwrap_or("?"));
            let rows = |d: &Value| d["day"]["segments"].as_array().cloned().unwrap_or_default();
            let at = |v: &Value| DateTime::parse_from_rfc3339(v.as_str().unwrap_or_default()).ok();
            if kind == "typed" {
                // The shipped day draws the typed pause whole across the meeting; the comparand
                // cuts the wall out of it, leaving a piece on each side (P56).
                assert_eq!(l["p56"]["p56"], true, "{who}: a typed line's comparand does not depart by P56");
                let paused = |d: &Value| -> Vec<Value> {
                    rows(d).into_iter().filter(|r| r["kind"] == "lost" && r["flags"]["note"] == "paused").collect()
                };
                let (shipped, day) = (paused(&l["shipped"]), paused(&l["day"]));
                assert_eq!(shipped.len(), 1, "{who}: the shipped day draws the typed pause as {} row(s)", shipped.len());
                assert_eq!(day.len(), 2, "{who}: P56's cut leaves the typed pause in {} piece(s), not two", day.len());
                let whole = (at(&shipped[0]["start"]), at(&shipped[0]["end"]));
                assert_eq!((at(&day[0]["start"]), at(&day[1]["end"])), whole, "{who}: the two pieces are not the pause's ends");
            } else {
                // The Wall row and the interruption's Lost row, tied on `(start, end)`, Wall first.
                let r = rows(&l["day"]);
                let tied = r.windows(2).any(|p| {
                    p[0]["kind"] == "wall" && p[1]["kind"] == "lost" && p[1]["flags"]["note"] == "interruption"
                        && p[0]["start"] == p[1]["start"] && p[0]["end"] == p[1]["end"]
                });
                assert!(tied, "{who}: the day holds no Wall row tied with the interruption's Lost row, the Wall first");
            }
        }
    }
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
    let (mut n, mut after) = (0usize, 0usize);
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
        // Inside the meeting the block is paused; after it (W-38) the unpause runs it again.
        let want = d.state.active.as_ref().is_some_and(|a| a.paused);
        assert_eq!(paused, want, "{} at {}: the binary left the block {}", line["class"], d.now, if paused { "paused" } else { "running" });
        after += usize::from(!want);
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
    println!("D61 worlds the shipped binary logs as derived: {n} of {n} ({after} after the meeting), and the unpause branch");
    assert!(n > 0, "no d61 line was asked");
    assert!(after > 0, "no d61 line after a meeting was asked (README gap 3320)");
}

/// **The comparison of each W-38 answer bites, and does not over-bite** (AGENTS §5.8):
/// every frozen line of each kind compares clean, and the same line with that answer bent
/// — the break-day open row's `so far`, a row after the running break (P45's comparand),
/// the shipped TUI's what-if, the re-ranked what-if (P52), the fork-4748911 drawing a P56
/// line departs from, a P55 line's reservation — is refused by `forkclass::compare_line`,
/// naming what it compared.
#[test]
fn every_w38_comparison_bites_a_bent_answer() {
    /// A line as the comparison holds it — since W-43 (README gap 4248) the line itself: a line
    /// whose world's log holds a break P81 nets carries P81's answer, which `compare_line` holds
    /// the kernel to, and P81's rule is held to that answer by [`p81_rule_unmet`].
    fn check(line: &Value, what: &str, bend: impl Fn(&mut Value) -> bool, name: &str) {
        let mut t = ClassTally::default();
        assert!(forkclass::compare_line(line, &mut t).is_empty(), "{}: the unbent line differs", line["class"]);
        let mut bent = line.clone();
        assert!(bend(&mut bent), "{what}: {} holds nothing to bend", line["class"]);
        let mut t = ClassTally::default();
        let found = forkclass::compare_line(&bent, &mut t);
        assert!(found.iter().any(|f| f.contains(name)), "{what} on {}: bent and not refused by name `{name}`: {found:?}", line["class"]);
    }
    /// The day `compare_line` holds the kernel to on a line: P81's answer where it carries one.
    fn held_day(x: &mut Value) -> &mut Value {
        if x["p81"].is_null() {
            &mut x["day"]["day"]
        } else {
            &mut x["p81"]["day"]
        }
    }
    let first = |f: &dyn Fn(&Value) -> bool| frozen_lines().iter().find(|l| f(l)).expect("a frozen line of the kind").clone();
    // P45's open row, with the host's minutes (a break-block day).
    let l = first(&|l| l["class"].as_str().is_some_and(|c| c.starts_with("break-block/")) && l["secondary"].is_null());
    check(&l, "the break-day open row", |x| {
        let rows = x["day"]["day"]["segments"].as_array_mut().expect("rows");
        rows.iter_mut().find(|r| r["kind"] == "block" && r["flags"]["open"] == true).map(|r| r["start"] = Value::String("2026-09-07T00:00:00-05:00".into())).is_some()
    }, "the open row on a break day");
    // P45's comparand after the break, on a line where P67 does not depart (README gap 3958).
    let l = first(&|l| !l["p45"].is_null() && l["p67"].is_null());
    check(&l, "a row after the running break", |x| {
        x["p45"]["rows"].as_array_mut().and_then(|r| r.first_mut()).map(|r| r["kind"] = Value::String("rest".into())).is_some()
    }, "after the running break (P45");
    // P67's comparand after the break, where it departs from P45's (W-41, README gap 3958):
    // the kernel is held to `p67`, so bending it bites and bending `p45` there does not.
    let l = first(&|l| !l["p67"].is_null());
    check(&l, "a row after the running break, P67's", |x| {
        x["p67"]["rows"].as_array_mut().and_then(|r| r.first_mut()).map(|r| r["kind"] = Value::String("rest".into())).is_some()
    }, "after the running break (P67");
    // The shipped TUI's what-if (held since W-38, the grown facts sent).
    let l = first(&|l| !l["whatif"].is_null() && l["whatif"]["grown"].is_null() && l["whatif"]["full"]["drift_min"].as_u64().is_some());
    check(&l, "the shipped TUI's what-if", |x| {
        x["whatif"]["full"]["drift_min"] = serde_json::json!(9999);
        true
    }, "the overtime what-if differs from the shipped TUI's");
    // P52's re-ranked what-if.
    let l = first(&|l| !l["whatif"]["grown"].is_null());
    check(&l, "the re-ranked what-if", |x| {
        x["whatif"]["grown"]["drift_min"] = serde_json::json!(9999);
        true
    }, "a parity-P52 day");
    // P56: a line whose `shipped` no longer draws the pause under the wall.
    let l = first(&|l| l["p56"]["p56"] == true);
    check(&l, "fork 4748911's drawing", |x| {
        x["shipped"] = x["day"].clone();
        true
    }, "a P56 line whose shipped day");
    // P55: the reservation the host's minutes place — on a `worked` line since D87, where the host's
    // minutes are the kernel's one reading, in the day P81's answer holds (README gap 4248).
    let l = first(&|l| l["p55"]["p55"] == true && l["day"]["day"]["segments"].as_array().is_some_and(|r| r.iter().any(|s| s["flags"]["current"] == true)));
    check(&l, "the P55 reservation", |x| {
        let rows = held_day(x)["segments"].as_array_mut().expect("rows");
        rows.iter_mut().find(|r| r["flags"]["current"] == true).map(|r| r["flags"]["planned_min"] = serde_json::json!(9999)).is_some()
    }, "the rows differ");
    // **P81** (the owner's D87; README gaps 4240 and 4248): the open row P81's answer holds after the
    // break, its start bent by a minute, is refused by name; and the rule, bent on the line's own
    // `day`, no longer meets the frozen answer ([`p81_rule_unmet`]).
    let worked = |l: &Value| !l["p81"].is_null();
    let l = first(&|l| worked(l));
    check(&l, "the open row P81's answer holds", |x| {
        let rows = x["p81"]["day"]["segments"].as_array_mut().expect("rows");
        rows.iter_mut()
            .find(|r| r["kind"] == "block" && r["flags"]["open"] == true)
            .map(|r| r["start"] = Value::String("2026-09-07T07:55:00-05:00".into()))
            .is_some()
    }, "the rows differ");
    let mut bent = l.clone();
    let rows = bent["day"]["day"]["segments"].as_array_mut().expect("rows");
    let open = rows.iter_mut().find(|r| r["kind"] == "block" && r["flags"]["open"] == true).expect("the open row the rule cuts");
    open["start"] = Value::String("2026-09-07T07:55:00-05:00".into());
    assert!(p81_rule_unmet(&l).is_ok(), "the unbent line's rule is its answer");
    assert!(
        p81_rule_unmet(&bent).is_err_and(|e| e.contains("P81's rule on the frozen day is not the frozen P81 answer")),
        "a `day` bent under P81's answer passed the rule"
    );
    // **P81 is not the identity**: on every line carrying P81's answer, the kernel's day is NOT the
    // line's own `day` — the fork's reading of a log whose break it counts as worked — so the answer
    // is what makes it pass, never what lets anything through.
    let mut refused = 0usize;
    for l in frozen_lines().iter().filter(|l| worked(l)) {
        let mut bare = l.clone();
        bare.as_object_mut().expect("a line").remove("p81");
        let mut t = ClassTally::default();
        let found = forkclass::compare_line(&bare, &mut t);
        assert!(found.iter().any(|f| f.contains("the rows differ")), "{}: the line's own day still matches the kernel: {found:?}", l["class"]);
        refused += 1;
    }
    assert!(refused > 0, "no line carries P81's answer");
    // A finding names the LINE: a secondary line's carries its kind after its class.
    let l = first(&|l| l["secondary"] == "window" && l["p45"].is_null());
    let who = format!("{} (window): ", l["class"].as_str().expect("a class"));
    check(&l, "a secondary line's name", |x| {
        let rows = x["day"]["day"]["segments"].as_array_mut().expect("rows");
        rows.first_mut().map(|r| r["kind"] = Value::String("rest".into())).is_some()
    }, &who);
}

/// **An optional answer is written only where it is set** (W-38): `forkclass::set_answer`
/// removes a `null` optional answer and writes every other, so a line no W-38 rule departs on
/// keeps its bytes — and the committed file carries no optional answer set to `null`.
#[test]
fn an_optional_answer_is_written_only_where_it_is_set() {
    let mut line = serde_json::json!({"day": 1, "p45": {"p45": true}});
    forkclass::set_answer(&mut line, "p45", Value::Null);
    assert!(line.get("p45").is_none(), "a null optional answer was kept");
    forkclass::set_answer(&mut line, "p56", serde_json::json!({"p56": true}));
    assert_eq!(line["p56"]["p56"], true);
    forkclass::set_answer(&mut line, "shipped", Value::Null);
    assert!(line.get("shipped").is_some_and(Value::is_null), "an answer every line carries was removed");
    for l in frozen_lines() {
        for k in forkclass::ANSWERS.iter().filter(|k| !forkclass::ALWAYS.contains(k)) {
            assert!(l.get(*k).is_none_or(|v| !v.is_null()), "{}: `{k}` is written null", l["class"]);
        }
    }
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
    assert!(forkclass::d64_allows(&old, &old, &shipped, &[], None, &registered).is_ok_and(|c| c.is_empty()));
    assert!(forkclass::d64_allows(&old, &bent, &shipped, &[], None, &registered).is_err(), "no reason passed");
    assert!(!registered.contains(&9999));
    assert!(forkclass::d64_allows(&old, &bent, &shipped, &[9999], None, &registered).is_err(), "an unregistered number passed");
    assert!(forkclass::d64_allows(&old, &bent, &shipped, &[51], None, &registered).is_err(), "a number the line has no flag of passed");
    assert_eq!(forkclass::d64_allows(&old, &bent, &shipped, &[46], None, &registered), Ok(vec!["day".to_string()]));
    let mut cleared = old.clone();
    for key in forkclass::ANSWERS {
        cleared[key] = Value::Null;
    }
    assert!(forkclass::d64_allows(&cleared, &bent, &shipped, &[], None, &registered).is_ok(), "a D64(b) re-draw's answers were refused");
    let mut lost = bent.clone();
    lost["shipped"] = Value::Null;
    assert!(forkclass::d64_allows(&old, &lost, &shipped, &[46], None, &registered).is_err(), "a comparand that dropped the shipped day passed");
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
        forkclass::d64_allows(&plain, &self_certified, &plain_day, &[51], None, &registered).is_err(),
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
        forkclass::d64_allows(&coincident, &coincident, &shipped, &[46], None, &registered),
        Ok(Vec::new()),
        "the coincident line itself is not refused"
    );
    assert!(
        forkclass::d64_allows(&coincident, &both, &moved, &[46], None, &registered).is_err(),
        "a moved shipped fork passed under a comparand number"
    );
    // 3. A number governs the object its flag lives in, `day` and `whatif` — not another's.
    let mut other = bent.clone();
    other["d60"]["p51"] = Value::Bool(!old["d60"]["p51"].as_bool().unwrap_or(false));
    assert!(
        forkclass::d64_allows(&old, &other, &shipped, &[46], None, &registered).is_err(),
        "P46 licensed a change to P51's object"
    );
    // **The W-38 introduction** (README gap 3470): a number whose comparand did not exist
    // when a line was frozen may ADD its answer to that line, and do nothing else.
    // Introduced: `p45` added, its flag set, P45 named and registered, nothing else moved.
    assert!(registered.contains(&45) && registered.contains(&56));
    let mut intro = old.clone();
    intro["p45"] = serde_json::json!({"p45": true, "from": "t", "rows": []});
    assert_eq!(
        forkclass::d64_allows(&old, &intro, &shipped, &[45], None, &registered),
        Ok(vec!["p45".to_string()]),
        "an introduction that only adds its own answer was refused"
    );
    // Refused: no reason; another number; an unregistered one.
    assert!(forkclass::d64_allows(&old, &intro, &shipped, &[], None, &registered).is_err(), "an introduction with no reason passed");
    assert!(forkclass::d64_allows(&old, &intro, &shipped, &[56], None, &registered).is_err(), "P56 introduced P45's answer");
    assert!(forkclass::d64_allows(&old, &intro, &shipped, &[9999], None, &registered).is_err(), "an unregistered introduction passed");
    // Refused: an introduction that ALSO moves a frozen answer (P45 carries no flag on the
    // committed line, so nothing licenses the change to `day`).
    let mut intro_and_day = intro.clone();
    intro_and_day["day"]["hash"] = Value::String("bent".to_string());
    assert!(
        forkclass::d64_allows(&old, &intro_and_day, &shipped, &[45], None, &registered).is_err(),
        "an introduction moved a frozen answer"
    );
    // Refused: an added answer whose flag is NOT set, and one holding a number the committed
    // line already carries a flag of (flipping `d57.p46` false → true by a new key is clause
    // 1's self-certification in another spelling).
    let mut unset = old.clone();
    unset["p45"] = serde_json::json!({"p45": false});
    assert!(forkclass::d64_allows(&old, &unset, &shipped, &[45], None, &registered).is_err(), "an unset flag introduced itself");
    let plain_line = plain.clone();
    assert_eq!(plain_line["d57"]["p46"], false, "the plain line carries P46's flag unset");
    let mut respelled = plain_line.clone();
    respelled["p45"] = serde_json::json!({"p46": true});
    assert!(
        forkclass::d64_allows(&plain_line, &respelled, &plain_day, &[46], None, &registered).is_err(),
        "a new key flipped a flag the committed line carries"
    );
    // Refused: an introduction that ALTERS an object the committed line carries — P45's flag
    // added INTO `d57`, which the line holds — rather than adding one of its own.
    let mut into_d57 = old.clone();
    into_d57["d57"]["p45"] = Value::Bool(true);
    assert!(
        forkclass::d64_allows(&old, &into_d57, &shipped, &[45], None, &registered).is_err(),
        "an introduction altered an object the committed line carries"
    );
    // Refused: an introduction on a line whose SHIPPED fork's day moved (clause 2 holds):
    // the P46 line departs, so it keeps the shipped day; the live shipped fork now answers
    // the comparand's day, which is the shipped fork moving under the line.
    let departed = old["day"]["day"].clone();
    assert_ne!(departed, shipped, "the P46 line departs from its shipped day");
    assert!(
        forkclass::d64_allows(&old, &intro, &departed, &[45], None, &registered).is_err(),
        "an introduction passed while the shipped fork's day moved"
    );
    // **Refused: a key of the world or the provenance moved with no answer moving** (W-42
    // repair, README gaps 4320 and 4338) — the verifier's P4b and P8, `tests` and `class`
    // rewritten in place with no reason, passed with "0 changed".  And with the answers moving
    // under a number the line carries a flag of, a moved provenance key is still refused; and
    // with a D64(c) reason, (c)'s own refusal of it is no longer discarded by the fallback.
    for key in ["class", "tests"] {
        let mut moved = old.clone();
        moved[key] = Value::String("planted".to_string());
        let quiet = forkclass::d64_allows(&old, &moved, &shipped, &[], None, &registered);
        assert!(quiet.as_ref().is_err_and(|e| e.contains(key)), "`{key}` moved in place with no reason: {quiet:?}");
        let mut both = bent.clone();
        both[key] = Value::String("planted".to_string());
        assert!(forkclass::d64_allows(&old, &both, &shipped, &[46], None, &registered).is_err(), "`{key}` moved under P46");
        let why = "2026-10-03 D64(c): a harness reading corrected (README gap 4338)";
        let c = forkclass::d64_allows(&old, &moved, &shipped, &[], Some(why), &registered);
        assert!(c.as_ref().is_err_and(|e| e.contains("D64(c)")), "(c)'s refusal was discarded: {c:?}");
    }
}

/// **The owner's D85, D64(c), bites and does not over-bite** (W-42 track C, README gaps 4123,
/// 4139 and 4281; AGENTS §5.8) — `forkclass::d64_allows` with a corrected harness reading named,
/// on a frozen P46 line: the comparand's `day` and a flag object the line carries moving, with a
/// D64(c) reason, is allowed — the flag FLIPPED included, which (a) refuses (clause 1: a flag the
/// recomputed answer sets licenses nothing) — and refused with no reason or with a reason that is
/// not one; a moved world, a moved provenance key, a moved shipped fork's day (on the line or
/// live), and an answer the committed line records no flag of are each refused under (c) whatever
/// the reason; and a departure leaving the line (gap 4123's P55) is one of the moves it allows.
#[test]
fn the_d64c_rule_bites_and_does_not_over_bite() {
    let registered = forkclass::registered_parity();
    let why = "2026-10-02 D64(c): the harness reads the host's worked minutes as the binary does (README gap 3941)";
    assert!(forkclass::is_d64c_reason(why));
    for not in [
        "D64(c): undated (gap 3941)",
        "2026-10-02 D64(c): names no gap",
        "2026-10-02 D64(c): gap three",
        "2026-10-02 D64(b): the wrong clause (gap 3941)",
    ] {
        assert!(!forkclass::is_d64c_reason(not), "`{not}` read as a D64(c) reason");
    }
    let old = frozen_lines()
        .iter()
        .find(|l| l["d57"]["p46"] == true && l["d57"]["p47"] == false && !l["shipped"].is_null() && l["p45"].is_null() && l["p55"].is_null())
        .expect("a frozen P46 line with no P45 and no P55 answer")
        .clone();
    let shipped = forkclass::shipped_of(&old).clone();
    // Allowed: the comparand's day and a flag object it carries — the flag flipped.
    let mut corrected = old.clone();
    corrected["day"]["hash"] = Value::String("corrected".to_string());
    corrected["d57"]["p47"] = Value::Bool(true);
    assert_eq!(
        forkclass::d64_allows(&old, &corrected, &shipped, &[], Some(why), &registered),
        Ok(vec!["day".to_string(), "d57".to_string()]),
        "a corrected harness reading moving the recorded departures was refused"
    );
    assert_eq!(forkclass::d64c_allows(&old, &corrected, &shipped, why), Ok(vec!["d57".to_string(), "day".to_string()]));
    // Refused: no reason; a reason that is not one; and (a) for the flipped flag.
    assert!(forkclass::d64_allows(&old, &corrected, &shipped, &[], None, &registered).is_err(), "no reason passed");
    assert!(forkclass::d64c_allows(&old, &corrected, &shipped, "2026-10-02 D64(c): no gap named").is_err(), "a reason naming no gap passed");
    assert!(
        forkclass::d64_allows(&old, &corrected, &shipped, &[47], None, &registered).is_err(),
        "(a) licensed a flag its recomputed answer set (clause 1)"
    );
    // Refused under (c), whatever the reason: the world, a provenance key, the shipped fork's day.
    let mut world = corrected.clone();
    world["world"]["now"] = Value::String("2026-09-07T23:59:00-05:00".to_string());
    assert!(forkclass::d64c_allows(&old, &world, &shipped, why).is_err_and(|e| e.contains("`world` moved")), "a moved world passed");
    let mut seed = corrected.clone();
    seed["draw"] = serde_json::json!(9999);
    assert!(forkclass::d64c_allows(&old, &seed, &shipped, why).is_err_and(|e| e.contains("`draw` moved")), "a moved provenance key passed");
    let mut moved = shipped.clone();
    moved["budget_blocks"] = serde_json::json!(99);
    let mut on_line = corrected.clone();
    on_line["shipped"]["day"] = moved.clone();
    assert!(forkclass::d64c_allows(&old, &on_line, &shipped, why).is_err_and(|e| e.contains("SHIPPED")), "a shipped day moved on the line passed");
    assert!(forkclass::d64c_allows(&old, &corrected, &moved, why).is_err_and(|e| e.contains("SHIPPED")), "a shipped day moved live passed");
    assert!(forkclass::d64_allows(&old, &on_line, &shipped, &[46], Some(why), &registered).is_err(), "(a) passed what (c) refused");
    // Refused under (c): an answer the committed line records no flag of — an introduction, (a)'s.
    let mut intro = corrected.clone();
    intro["p45"] = serde_json::json!({"p45": true, "from": "t", "rows": []});
    assert!(forkclass::d64c_allows(&old, &intro, &shipped, why).is_err_and(|e| e.contains("`p45` moved")), "an introduction passed as (c)");
    // Allowed: a departure LEAVING the line (gap 4123's P55) — a flag object the line carries, gone.
    let mut with_p55 = old.clone();
    with_p55["p55"] = serde_json::json!({"p55": true});
    let mut gone = with_p55.clone();
    gone.as_object_mut().expect("a line").remove("p55");
    gone["d57"]["p47"] = Value::Bool(true);
    assert_eq!(forkclass::d64c_allows(&with_p55, &gone, &shipped, why), Ok(vec!["d57".to_string(), "p55".to_string()]));
    // And a line whose shipped day moves from the comparand to `shipped` — the comparand starting to
    // depart from the same shipped day — is (c)'s too: the shipped fork's day did not move.
    let mut coincident = old.clone();
    coincident["day"]["day"] = shipped.clone();
    coincident["shipped"] = Value::Null;
    assert_eq!(
        forkclass::d64c_allows(&coincident, &old, &shipped, why),
        Ok(vec!["day".to_string(), "shipped".to_string()]),
        "the comparand starting to depart from the same shipped day was refused"
    );
    // The reason is read STRICTLY, as `because_of` reads a number: absent is none, a malformed one
    // fails rather than being ignored.
    assert_eq!(forkclass::harness_of("TM_W42_C_HARNESS_UNSET_PROBE"), None);
    std::env::set_var("TM_W42_C_HARNESS_PROBE", why);
    assert_eq!(forkclass::harness_of("TM_W42_C_HARNESS_PROBE").as_deref(), Some(why));
    std::env::set_var("TM_W42_C_HARNESS_BAD_PROBE", "a harness reading corrected, undated");
    assert!(std::panic::catch_unwind(|| forkclass::harness_of("TM_W42_C_HARNESS_BAD_PROBE")).is_err(), "a malformed D64(c) reason was ignored");
}

/// **A world re-drawn since its committed line is held to D64(b) as the re-draw ran it** (W-42 track
/// C, README gap 4151; `forkclass::redrawn_since`): asked of the COMMITTED line, so a world edited in
/// the working copy cannot pass for a re-draw at the re-bless. A committed world the binary cannot
/// hold, re-drawn to one it can, of the same class, carrying a new dated D64(b) reason, passes; the
/// same with no new reason, with an undated one, from a committed world the binary CAN hold, to a
/// world it cannot, or to another class, is refused by name.
#[test]
fn a_world_redrawn_since_its_committed_line_is_held_to_d64b() {
    let tz = tz();
    let held = frozen_lines()
        .iter()
        .find(|l| l["secondary"].is_null() && !l["world"]["state"]["active"].is_null())
        .expect("a primary line with a running block")
        .clone();
    assert!(forkclass::binary_holds(&Built::of(ClassWorld::of_json(&held["world"], tz).expect("a world"))).is_ok());
    // The committed world: the cache names a block the log does not hold open (clause 1 fails).
    let mut committed = held.clone();
    committed["world"]["state"]["active"]["id"] = serde_json::json!("zz99");
    assert!(forkclass::binary_holds(&Built::of(ClassWorld::of_json(&committed["world"], tz).expect("a world"))).is_err());
    let why = serde_json::json!({"why": "2026-10-02 D64(b): the cache names a block the log does not hold", "held": ["1: …"]});
    let mut redrawn = held.clone();
    redrawn["d64b"] = why.clone();
    assert_eq!(forkclass::redrawn_since(&committed, &redrawn, tz), Ok(()), "a licensed re-draw was refused");
    let no_reason = held.clone();
    assert!(forkclass::redrawn_since(&committed, &no_reason, tz).is_err_and(|e| e.contains("no new D64(b) reason")));
    let mut stale = held.clone();
    stale["d64b"] = why.clone();
    let mut committed_with = committed.clone();
    committed_with["d64b"] = why.clone();
    assert!(forkclass::redrawn_since(&committed_with, &stale, tz).is_err_and(|e| e.contains("no new D64(b) reason")), "the committed line's own reason licensed a new re-draw");
    let mut undated = held.clone();
    undated["d64b"] = serde_json::json!({"why": "D64(b): undated"});
    assert!(forkclass::redrawn_since(&committed, &undated, tz).is_err(), "an undated reason passed");
    assert!(forkclass::redrawn_since(&held, &redrawn, tz).is_err_and(|e| e.contains("one the binary can hold")), "a held committed world was re-drawn");
    assert!(forkclass::redrawn_since(&committed, &{ let mut x = committed.clone(); x["d64b"] = why.clone(); x }, tz).is_err_and(|e| e.contains("not one the binary can hold")));
    let mut other_class = committed.clone();
    other_class["class"] = serde_json::json!("idle/elsewhere");
    assert!(forkclass::redrawn_since(&other_class, &redrawn, tz).is_err_and(|e| e.contains("world")), "a re-draw into another class passed");
}

/// **P67's answer is its own, and it departs only where its rule does** (W-41 track H, README
/// gap 3958). From W-40 track P until W-41 six frozen lines held P67's change under P45's flag:
/// the comparand's P45 transformation had been edited to P67's rule, which the D64 gate cannot
/// see (README gap 3331's residue). Now `forkplan::p45_after` is P45's rest reading again and
/// `forkplan::p67_after` is P67's, present only where the two plan different rows, so:
///
/// * every line carrying `p67` (the classes and the batch) also carries `p45`, from the same
///   instant, with DIFFERENT rows — and its running break had run LESS than `break_min` by
///   then, the one case P67's register row says the two readings part (P45 reset the fork's
///   counter only at a rest of `break_min`; P67 at any length);
/// * no line whose running break had run `break_min` carries `p67`;
/// * the gate attributes each answer to its own number: a change to `p67` is refused under P45
///   and allowed under P67, and moving P67's rows back under P45's flag — the shape gap 3958
///   named — is refused when only P45 is named;
/// * and the floors: a line of each kind is held, so neither half is vacuous.
#[test]
fn p67s_answer_is_its_own_and_departs_only_where_its_rule_does() {
    let tz = tz();
    let registered = forkclass::registered_parity();
    assert!(registered.contains(&45) && registered.contains(&67), "P45 and P67 are registered");
    let lines: Vec<&Value> = frozen_lines().iter().chain(forkclass::batch_lines().iter()).collect();
    let (mut departs, mut agrees) = (0usize, 0usize);
    let mut bad = Vec::new();
    for l in &lines {
        let who = l["name"].as_str().map_or_else(
            || format!("{}{}", l["class"].as_str().unwrap_or("?"), l["secondary"].as_str().map(|s| format!(" ({s})")).unwrap_or_default()),
            str::to_string,
        );
        if l["p45"].is_null() {
            if !l["p67"].is_null() {
                bad.push(format!("{who}: carries `p67` and no `p45`"));
            }
            continue;
        }
        let b = Built::of(ClassWorld::of_json(&l["world"], tz).expect("a stored world"));
        let t = b.world.state.break_.as_ref().and_then(|x| x.started_at(tz, b.world.now)).expect("a P45 line has a running break");
        let from = |v: &Value| DateTime::parse_from_rfc3339(v["from"].as_str().unwrap_or_default()).expect("from").with_timezone(&tz);
        let taken = (from(&l["p45"]) - t).num_minutes();
        let short = taken < i64::from(b.cfg.day.break_min);
        if l["p67"].is_null() {
            agrees += 1;
            continue;
        }
        departs += 1;
        assert_eq!(l["p67"]["p67"], true, "{who}: P67's flag is set in its home");
        if l["p67"]["from"] != l["p45"]["from"] {
            bad.push(format!("{who}: `p67` from {} and `p45` from {}", l["p67"]["from"], l["p45"]["from"]));
        }
        if l["p67"]["rows"] == l["p45"]["rows"] {
            bad.push(format!("{who}: `p67` plans P45's rows — it departs nowhere"));
        }
        if !short {
            bad.push(format!("{who}: `p67` on a break that had run {taken} of `break_min` {} minutes", b.cfg.day.break_min));
        }
    }
    // Every parity answer a line carries is one of `forkclass::ANSWERS`: the D64 gate reads what
    // changed off that list, so an answer outside it could move under no gate at all.
    for l in &lines {
        for k in l.as_object().into_iter().flatten().map(|(k, _)| k) {
            let parity = k.strip_prefix('p').is_some_and(|d| !d.is_empty() && d.bytes().all(|c| c.is_ascii_digit()));
            if parity && !forkclass::ANSWERS.contains(&k.as_str()) {
                bad.push(format!("{}: carries `{k}`, an answer `forkclass::ANSWERS` does not list", l["class"]));
            }
        }
    }
    println!("lines after a running break: {departs} carry P67's own answer, {agrees} where P45's is P67's too");
    assert!(bad.is_empty(), "{}", bad.join("\n  "));
    assert!(departs > 0, "no frozen line holds P67's departure");
    assert!(agrees > 0, "no frozen line holds a break where P45 and P67 agree");
    // The gate, on a P67 line (README gap 3958's attribution, as a test).
    let l = (*lines.iter().find(|l| !l["p67"].is_null()).expect("a P67 line")).clone();
    let shipped = if l["shipped"].is_null() { l["day"]["day"].clone() } else { l["shipped"]["day"].clone() };
    let mut bent = l.clone();
    bent["p67"]["rows"][0]["kind"] = Value::String("rest".into());
    assert!(forkclass::d64_allows(&l, &bent, &shipped, &[45], None, &registered).is_err(), "P45 licensed a change to P67's answer");
    assert_eq!(forkclass::d64_allows(&l, &bent, &shipped, &[67], None, &registered), Ok(vec!["p67".to_string()]), "P67 may move its own answer");
    let mut merged = l.clone();
    merged["p45"]["rows"] = l["p67"]["rows"].clone();
    merged.as_object_mut().expect("a line").remove("p67");
    assert!(
        forkclass::d64_allows(&l, &merged, &shipped, &[45], None, &registered).is_err(),
        "P67's rows moved back under P45's flag with only P45 named (README gap 3958)"
    );
}

/// **Re-bless the frozen fork classes — held to the owner's D64, asking fork 4748911 OUT of the
/// tree** (W-37 track H, README gaps 3133, 3138; moved out of the fork region and onto the oracle at
/// W-43 track C, README gaps 4248 and 4462) — inert without `TM_PLANNER_BLESS`; it asks `TM_ORACLE`.
///
/// It recomputes the FORK'S answers for every stored world and never changes a
/// world (a re-draw is `the_frozen_class_worlds_are_redrawn`, which demands
/// D64(b)'s reason). Rewriting a committed comparand is a decision and never a
/// repair (AGENTS §7.3), and since D64 it is a decision by a STANDING RULE,
/// which this test enforces rather than leaving to a sentence: a line whose
/// answers change must carry the flag of a parity number the re-bless was run
/// for (`TM_PLANNER_BLESS_BECAUSE=P56`, say) that `kernel/parity.txt`
/// registers — D64(a), or its introduction (D70) — or have had its answers cleared by a D64(b)
/// re-draw; the shipped fork's day stays beside a departing comparand by value; and a re-bless
/// that is neither FAILS BY NAME and writes nothing. `TM_PLANNER_BLESS_OUT` writes elsewhere (a
/// scratch copy), for a dry run. Since the owner's D85, `TM_PLANNER_BLESS_HARNESS` names a
/// corrected harness reading (D64(c)).
///
/// **Why the oracle, and why outside the region** (W-43 track C). The frozen answers are fork
/// 4748911's (D21) as the shipped binary ranks it (D53). The in-tree fork plans over the KERNEL's
/// replay, which since the owner's D87 nets the eight `worked` lines' logged break (parity P81) —
/// so on those lines it is no longer fork 4748911, its shipped day moved, and D64's clause 2 refused
/// them on every in-tree run (the W-42 land, §2 point 5): the in-tree re-bless could rewrite this
/// file for no reason at all. The oracle IS fork 4748911 and reads the world as it does (the
/// comparand asks it its own reading of the running block, `forkplan::ForkPlan::worked`), so it
/// answers every line as frozen — and it needs no in-tree planner, so the gate outlives R3.
///
/// **What a line is held against is the file's COMMITTED history, not the
/// working copy** (W-42 track C, README gap 4151; `frozenhist::held`, keyed by
/// `frozenhist::class_key`). The working copy is still the INPUT — its
/// worlds, where a pending re-draw lives — but a line's answers are held to
/// its latest committed version: a re-drawn world to D64(b) as
/// `forkclass::redrawn_since` asks it of the committed line, the rest to
/// `forkclass::d64_allows`. So a line whose answers were cleared, or deleted
/// and re-derived, in the working copy is not a fresh freeze; a line no
/// committed version holds is. And a line HEAD holds that the re-bless no
/// longer writes is refused, unless it is derived from a primary line this
/// re-bless re-drew (the re-draw re-derives those). **And since W-43 (README gap 4320) a key any
/// committed version held that the re-bless does not write must be a line that MOVED to a new key**
/// (`frozenhist::refiles`: one written line holds its world), held as one line by
/// `frozenhist::refiled_allows` — its class, a reading of the world, moves only under a newly set
/// flag of the number that moved the reading, which must be registered.
#[test]
#[ignore]
fn the_frozen_fork_classes_are_reblessed() {
    if std::env::var_os("TM_PLANNER_BLESS").is_none() {
        eprintln!("inert: set TM_PLANNER_BLESS=1 (with TM_ORACLE) to rewrite {}", forkclass::FROZEN_CLASSES);
        return;
    }
    let oracle = forkplan::Oracle::new(forkplan::oracle_path().expect("TM_PLANNER_BLESS asks fork 4748911 out of the tree: set TM_ORACLE"));
    let because = forkclass::because_of("TM_PLANNER_BLESS_BECAUSE");
    let harness = forkclass::harness_of("TM_PLANNER_BLESS_HARNESS");
    let registered = forkclass::registered_parity();
    let path = forkclass::frozen_path();
    let held = frozenhist::held(&path, frozenhist::class_key).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", held.census(forkclass::FROZEN_CLASSES));
    let out_path = std::env::var_os("TM_PLANNER_BLESS_OUT").map(std::path::PathBuf::from).unwrap_or_else(|| path.clone());
    let text = std::fs::read_to_string(&path).expect("the frozen classes read");
    let mut out = String::new();
    let (mut refused, mut changed, mut filled) = (Vec::new(), Vec::new(), 0usize);
    let mut written: std::collections::BTreeMap<String, Value> = std::collections::BTreeMap::new();
    let mut redrawn_parents = BTreeSet::new();
    for l in text.lines().filter(|l| !l.trim().is_empty()) {
        let input: Value = serde_json::from_str(l).expect("a frozen class line is JSON");
        let key = frozenhist::class_key(&input).expect("a frozen class line names its class");
        let mut line = input.clone();
        let b = Built::of(ClassWorld::of_json(&line["world"], tz()).expect("a stored world"));
        let prios = forkclass::kernel_answer_with_grants(&b).unwrap_or_else(|e| panic!("{key}: the kernel refused: {e}")).1;
        let answers = forkplan::comparand_answers(&b, &prios, &oracle).unwrap_or_else(|e| panic!("{key}: the oracle: {e}"));
        for key in forkclass::ANSWERS {
            forkclass::set_answer(&mut line, key, answers[key].clone());
        }
        // The SHIPPED fork's day: fork 4748911's own drawing, every replayed pause whole (P56).
        let ask = forkplan::ForkAsk { state: &b.world.state, now: b.world.now, d60: false, p64: false, prios: &prios, extend: None, log_line: None };
        let shipped_day = forkplan::ForkPlan::plan(&oracle, &b, &ask).unwrap_or_else(|e| panic!("{key}: the oracle: {e}")).fork_day;
        match held.get(&key) {
            None => filled += 1,
            Some(old) if old["world"] != line["world"] => match forkclass::redrawn_since(old, &line, tz()) {
                Err(e) => refused.push(e),
                Ok(()) => {
                    if line["secondary"].is_null() {
                        redrawn_parents.insert(line["class"].as_str().unwrap_or_default().to_string());
                    }
                    changed.push(format!("{key} re-drawn"));
                }
            },
            Some(old) => match forkclass::d64_allows(old, &line, &shipped_day, &because, harness.as_deref(), &registered) {
                Err(e) => refused.push(e),
                Ok(keys) if !keys.is_empty() => changed.push(format!("{} `{}`", line["class"], keys.join("`, `"))),
                Ok(_) => {}
            },
        }
        assert_eq!(line["world"], input["world"], "a re-bless changed a world");
        written.insert(key, line.clone());
        out.push_str(&serde_json::to_string(&line).expect("a line serialises"));
        out.push('\n');
    }
    // **A committed key the re-bless no longer writes** — any committed version's, not HEAD's alone
    // (README gap 4320): one written line holding its world means the line MOVED to a new key, and it
    // is held as one line (`frozenhist::refiled_allows`: its class, a reading of the world, moves only
    // under a newly set flag of a REGISTERED number); a key HEAD holds that no written line holds the
    // world of is refused unless it is derived from a primary this re-bless re-drew. (A key only in
    // history whose world no line holds left in a commit, which the plain run judges.)
    let gone: std::collections::BTreeMap<String, Value> =
        held.ever.iter().filter(|(k, _)| !written.contains_key(*k)).map(|(k, c)| (k.clone(), c.line.clone())).collect();
    let (paired, unpaired) = frozenhist::refiles(&gone, &written);
    for (k, k2) in &paired {
        match frozenhist::refiled_allows(&gone[k], &written[k2]) {
            Err(e) => refused.push(format!("{k} → {k2}: {e}")),
            Ok(ns) => match ns.iter().find(|n| !registered.contains(n)) {
                Some(n) => refused.push(format!("{k} → {k2}: re-filed under P{n}, which kernel/parity.txt does not register")),
                None => eprintln!("{k} → {k2}: a line that moved to a new key, licensed by {:?}", ns.iter().map(|n| format!("P{n}")).collect::<Vec<_>>()),
            },
        }
    }
    for (k, what) in unpaired {
        let parent = gone.get(&k).and_then(|l| l["derived"]["from"].as_str()).unwrap_or_default();
        if held.head.contains(&k) && !redrawn_parents.contains(parent) {
            refused.push(format!("{what}: a committed line the re-bless no longer writes, derived from no primary it re-drew"));
        }
    }
    eprintln!(
        "re-bless for {:?}: {} line(s) changed ({}), {filled} line(s) no committed version holds answered, {} refused",
        because,
        changed.len(),
        changed.join("; "),
        refused.len()
    );
    assert!(refused.is_empty(), "the re-bless is refused by the owner's D64 and wrote nothing:\n  {}", refused.join("\n  "));
    std::fs::write(&out_path, out).expect("the frozen classes are written");
}

/// **The oracle's `worked` op reads fork 4748911's OWN lines** (W-44 track C, README gap 4507).
/// The comparand moves the running estimate by what the fork reads as the block's worked minutes
/// (P55, P46), and the oracle answered that with a selection it RE-TYPED out of fork `active_run`,
/// where the reading is a local of a private method — so every frozen line asked through the op
/// was partly computed by code this repository owns.  `worked-seam.patch` MOVES those lines into a
/// method `active_run` itself calls, and the op calls an entry that reaches it.  This holds the
/// graft to being a move — every line it removes is a line it adds, in order, as one run, and those
/// lines are the reading (the log's open block, the clock since `started`) — the build script to
/// applying it, and the oracle's own code to reading no open block, no `worked_min_at` and no
/// `local_dt` itself, and to naming the entry the harness asks for: the selection cannot be typed
/// back in without this failing.  Files read; no oracle and no fork, so it outlives R3.
#[test]
fn the_oracles_worked_op_reads_the_forks_own_lines() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/tm-kernel-ffi/examples/oracle");
    let read = |f: &str| std::fs::read_to_string(dir.join(f)).unwrap_or_else(|e| panic!("{f}: {e}"));
    let patch = read("worked-seam.patch");
    let diff = &patch[patch.find("\n--- a/tm-core/src/planner.rs\n").expect("the graft diffs the fork's planner")..];
    assert_eq!(diff.matches("\n--- a/").count(), 1, "the graft touches another file of the fork than its planner");
    let removed: Vec<&str> = diff.lines().filter(|l| l.starts_with('-') && !l.starts_with("---")).map(|l| &l[1..]).collect();
    let added: Vec<&str> = diff.lines().filter(|l| l.starts_with('+') && !l.starts_with("+++")).map(|l| &l[1..]).collect();
    assert!(!removed.is_empty(), "the graft removes nothing, so it moves nothing");
    assert!(
        added.windows(removed.len()).any(|w| w == removed.as_slice()),
        "the graft does not add back, in order and as one run, every line it removes — it is not a move:\n{}",
        removed.join("\n")
    );
    for word in ["open_block", "worked_min_at", "local_dt"] {
        assert!(removed.iter().any(|l| l.contains(word)), "the moved lines are not fork `active_run`'s reading: no `{word}`");
    }
    let build = read("build-oracle.sh");
    assert!(build.contains("worked=\"$here/worked-seam.patch\"") && build.contains("git apply \"$worked\""), "build-oracle.sh does not apply the worked seam");
    let main = read("src/main.rs");
    let code: Vec<&str> = main.lines().filter(|l| !l.trim_start().starts_with("//")).collect();
    for word in ["open_block", "worked_min_at", "local_dt"] {
        let hits: Vec<&&str> = code.iter().filter(|l| l.contains(word)).collect();
        assert!(hits.is_empty(), "the oracle's own code reads `{word}` — the fork's reading is re-typed again: {hits:?}");
    }
    assert!(code.iter().any(|l| l.contains("planner::active_worked(")), "the oracle's `worked` op does not call the graft's entry");
    assert!(main.contains(&format!("{:?}", forkplan::WORKED_READ_BY)), "the oracle's answer does not name the entry the harness refuses an answer without");
}

// ---------------------------------------------------------------------------
// The blesses that outlive R3 (W-45 track C, README gap 4680). Each asks fork 4748911 OUT of the
// tree — `tm-oracle plan`, the owner's D72 — so no frozen file of this suite is final at R3. Until
// W-45 the four below sat in the fork region with the in-tree fork they planned by, and R3's
// deletion would have taken every way to re-bless `plan-basic`'s days, the batch, the driven days
// and the classes' worlds (README gap 4463 named three of the four).
// ---------------------------------------------------------------------------

/// **`plan-basic`'s two states, as the fixture suite plans them**: arrived at 07:00
/// (`planner_common::basic_state`) and at 10:30 (`planner_fixtures.rs`' and
/// `planner_w37_rows.rs`' late state) — and the instants, every ten minutes from the arrival
/// to 20:50. Only the bless below reads them: the frozen lines carry the state and the
/// instant they were planned from, so the arm that survives R3 needs neither.
fn basic_instants() -> Vec<(String, RuntimeState, DateTime<Tz>)> {
    let late = RuntimeState {
        date: Some(planner_common::date("2026-09-07")),
        wake: Some(planner_common::time(9, 0)),
        arrival: Some(planner_common::time(10, 30)),
        loc: Some("lounge".to_string()),
        ..RuntimeState::default()
    };
    let mut out = Vec::new();
    for (label, state, from) in [("early", planner_common::basic_state(), (7, 0)), ("late", late, (10, 30))] {
        let mut t = planner_common::at("2026-09-07", from.0, from.1);
        let end = planner_common::at("2026-09-07", 20, 50);
        while t <= end {
            out.push((format!("plan-basic {label} {}", t.format("%H:%M")), state.clone(), t));
            t += Duration::minutes(10);
        }
    }
    out
}

/// **One frozen `plan-basic` line, asked of fork 4748911 out of the tree** (W-45 track C, README
/// gap 4680): the fixture's world as a class world reads it (`forkclass::Built::of_fixture`, which
/// refuses a configuration the oracle would not read), the kernel's grants for its request — what
/// the shipped binary hands its fork (D53, `planning::build_ranked`'s call) — and `tm-oracle plan`'s
/// day for `state` at `now`, as the shipped binary draws it (`forkplan::Planned::day`), digested as
/// fork 4748911's `DayPlan::hash` (`forkplan::day_hash`). The line is `forkday::basic_line_of`'s, the
/// one writer the in-tree fork's line went through.
fn basic_oracle_line(
    fx: &planner_common::Fixture,
    oracle: &forkplan::Oracle,
    name: &str,
    state: &RuntimeState,
    now: DateTime<Tz>,
) -> Result<String, String> {
    let b = Built::of_fixture(&fx.docs, &fx.log, state, now, &fx.cfg)?;
    let (_, ans) = planreq::kernel_day(&b.request_world(), None).map_err(|e| format!("the kernel: {e}"))?;
    let ask = forkplan::ForkAsk { state, now, d60: false, p64: false, prios: &ans.prios, extend: None, log_line: None };
    let day = forkplan::ForkPlan::plan(oracle, &b, &ask).map_err(|e| format!("the oracle: {e}"))?.day;
    Ok(forkday::basic_line_of(name, state, now, &forkplan::day_hash(&day), &day))
}

/// **The frozen `plan-basic` days are fork 4748911's answer today, out of the tree** (W-45 track C,
/// README gap 4680) — every line, byte for byte, as [`basic_oracle_line`] writes it now: the
/// assertion the in-region the_frozen_plan_basic_days_are_the_forks_answer_today makes of the
/// in-tree fork, made of `tm-oracle plan`, so it outlives R3. Inert without `TM_ORACLE`.
#[test]
#[ignore]
fn the_frozen_plan_basic_days_are_the_forks_oracle_answer_today() {
    let Some(bin) = forkplan::oracle_path() else {
        eprintln!("inert: set TM_ORACLE to an oracle built by kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh");
        return;
    };
    let oracle = forkplan::Oracle::new(bin);
    let fx = planner_common::load_with_log("plan-basic", Some(planner_common::BASIC_LOG));
    let lines = forkday::frozen_basic_days();
    let mut stale = Vec::new();
    for line in &lines {
        let name = line["name"].as_str().unwrap_or_default();
        let state: RuntimeState = serde_json::from_value(line["state"].clone()).expect("a stored state");
        let now = DateTime::parse_from_rfc3339(line["now"].as_str().unwrap_or_default()).expect("an instant").with_timezone(&fx.cfg.tz);
        match basic_oracle_line(&fx, &oracle, name, &state, now) {
            Err(e) => stale.push(format!("{name}: {e}")),
            Ok(again) if again.trim_end() != serde_json::to_string(line).expect("a line").as_str() => {
                let v: Value = serde_json::from_str(&again).expect("a line");
                stale.push(format!("{name}: {}", forkplan::first_difference("line", line, &v).unwrap_or_else(|| "the bytes".to_string())));
            }
            Ok(_) => {}
        }
    }
    println!("frozen plan-basic days the fork oracle answers as frozen: {} of {} ({} oracle request(s))", lines.len() - stale.len(), lines.len(), oracle.asked.lock().expect("census"));
    assert!(!lines.is_empty() && stale.is_empty(), "the fork oracle does not answer the frozen plan-basic days as frozen:\n  {}", stale.join("\n  "));
}

/// **Freeze `plan-basic`'s ten-minute days** (W-38) — inert without `TM_PLANNER_BLESS_BASIC`.
/// It writes a line for every instant the file does not hold yet and REFUSES, by name, to
/// change a line it holds: under the owner's D64 a frozen day changes only for a registered
/// parity number or a world the binary cannot build, and these lines carry no flag a number
/// could license — so a day of this file that the fork answers differently is a finding to
/// report, never a line to rewrite. (These lines carry no departure, so the owner's D85 — D64(c), a corrected harness reading —
/// cannot reach them either: what it may move is a departure the line records, and the shipped
/// fork's day it holds by value is the whole line.) **What a line is held against is the file's
/// COMMITTED history** (W-42 track C, README gap 4151; `frozenhist::held`), never the working copy,
/// so deleting the file is not a fresh freeze; a line HEAD holds that no instant draws is refused.
///
/// **It asks fork 4748911 OUT of the tree and sits outside the fork region** (W-45 track C, README
/// gap 4680): each day is [`basic_oracle_line`]'s — `tm-oracle plan` over the fixture's world,
/// ranked by the kernel's grants as the binary ranks it (D53) — so the file stays re-blessable after
/// R3 (until W-45 the bless planned in-tree and R3 made the file final, gap 4463).
/// `TM_PLANNER_BLESS_BASIC_OUT` writes elsewhere, for a dry run.
#[test]
#[ignore]
fn the_frozen_plan_basic_days_are_blessed() {
    if std::env::var_os("TM_PLANNER_BLESS_BASIC").is_none() {
        eprintln!("inert: set TM_PLANNER_BLESS_BASIC=1 (with TM_ORACLE) to write {}", forkday::FROZEN_BASIC);
        return;
    }
    let oracle = forkplan::Oracle::new(forkplan::oracle_path().expect("TM_PLANNER_BLESS_BASIC asks fork 4748911 out of the tree: set TM_ORACLE"));
    let fx = planner_common::load_with_log("plan-basic", Some(planner_common::BASIC_LOG));
    let path = forkday::frozen_basic_path();
    let held = frozenhist::held(&path, frozenhist::key_of("name")).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", held.census(forkday::FROZEN_BASIC));
    let (mut out, mut added, mut refused, mut names) = (String::new(), 0usize, Vec::new(), Vec::new());
    for (name, state, now) in basic_instants() {
        let line = basic_oracle_line(&fx, &oracle, &name, &state, now).unwrap_or_else(|e| panic!("{name}: {e}"));
        match held.ever.get(&name) {
            Some(old) if old.raw.as_str() != line.trim_end() => refused.push(name.clone()),
            Some(_) => {}
            None => added += 1,
        }
        names.push(name);
        out.push_str(&line);
    }
    refused.extend(held.head.iter().filter(|n| !names.contains(n)).map(|n| format!("{n}: a frozen line no instant draws any more")));
    eprintln!("plan-basic days: {added} added, {} refused", refused.len());
    assert!(refused.is_empty(), "the fork answers these frozen days differently, and they are not rewritten:\n  {}", refused.join("\n  "));
    let out_path = std::env::var_os("TM_PLANNER_BLESS_BASIC_OUT").map(std::path::PathBuf::from).unwrap_or_else(|| path.clone());
    std::fs::write(&out_path, out).expect("the frozen plan-basic days are written");
}

/// **Freeze the seeded batch** (W-39, the owner's D72, README gap 3533) — inert without
/// `TM_PLANNER_BLESS_BATCH`. It draws `forkclass::BATCH_DRAWS` draws of the class draw from
/// `forkclass::BATCH_SEED`, keeps the ones whose world the shipped binary holds
/// (`forkclass::binary_holds`, D64(b)), and writes each with the fork's answers
/// (`forkplan::comparand_answers`, the classes' own, over the oracle). A line it already holds is held to the owner's D64
/// exactly as the classes' re-bless is (`forkclass::d64_allows`, `TM_PLANNER_BLESS_BECAUSE`):
/// a changed answer needs a registered number the line carries, and a changed WORLD is a
/// re-draw, which this refuses by name. `TM_PLANNER_BLESS_BATCH_OUT` writes elsewhere, for a
/// dry run. **What a line is held
/// against is the file's COMMITTED history** (W-42 track C, README gap 4151;
/// `frozenhist::held`), never the working copy — so deleting the file is not a fresh freeze — and
/// a line HEAD holds that the draw no longer writes is refused; `TM_PLANNER_BLESS_HARNESS` names a
/// corrected harness reading (the owner's D85, D64(c)).
///
/// **It asks fork 4748911 OUT of the tree and sits outside the fork region** (W-45 track C, README
/// gap 4680): every answer is `forkplan::comparand_answers` over `tm-oracle plan` (the classes'
/// re-bless's shape since W-43, README gap 4462) and the shipped fork's day the oracle's, so the
/// batch stays re-blessable under D64 after R3 deletes the in-tree fork.
#[test]
#[ignore]
fn the_frozen_batch_is_blessed() {
    if std::env::var_os("TM_PLANNER_BLESS_BATCH").is_none() {
        eprintln!("inert: set TM_PLANNER_BLESS_BATCH=1 (with TM_ORACLE) to write {}", forkclass::FROZEN_BATCH);
        return;
    }
    let oracle = forkplan::Oracle::new(forkplan::oracle_path().expect("TM_PLANNER_BLESS_BATCH asks fork 4748911 out of the tree: set TM_ORACLE"));
    let because = forkclass::because_of("TM_PLANNER_BLESS_BECAUSE");
    let harness = forkclass::harness_of("TM_PLANNER_BLESS_HARNESS");
    let registered = forkclass::registered_parity();
    let path = forkclass::batch_path();
    let out_path = std::env::var_os("TM_PLANNER_BLESS_BATCH_OUT").map(std::path::PathBuf::from).unwrap_or_else(|| path.clone());
    let held = frozenhist::held(&path, frozenhist::key_of("draw")).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", held.census(forkclass::FROZEN_BATCH));
    let mut written = Vec::new();
    let (mut out, mut added, mut changed, mut refused, mut not_held) = (String::new(), 0usize, Vec::new(), Vec::new(), Vec::new());
    for (index, draw) in forkclass::class_draws(forkclass::BATCH_SEED, None).take(forkclass::BATCH_DRAWS).enumerate() {
        let world = forkclass::world_of(&draw);
        let b = Built::of(world.clone());
        if let Err(e) = forkclass::binary_holds(&b) {
            not_held.push(format!("draw {index}: {}", e.join("; ")));
            continue;
        }
        let prios = forkclass::kernel_answer_with_grants(&b).unwrap_or_else(|e| panic!("draw {index}: the kernel refused: {e}")).1;
        let answers = forkplan::comparand_answers(&b, &prios, &oracle).unwrap_or_else(|e| panic!("draw {index}: the oracle: {e}"));
        let mut line = forkclass::batch_line(index, &draw, &world, &class_of(&b).key());
        for key in forkclass::ANSWERS {
            forkclass::set_answer(&mut line, key, answers[key].clone());
        }
        written.push(index.to_string());
        match held.get(&index.to_string()) {
            None => added += 1,
            Some(old) if old["world"] != line["world"] => {
                refused.push(format!("draw {index}: the generator draws another world — a re-draw, which D64(b) must decide"));
            }
            Some(old) => {
                let ask = forkplan::ForkAsk { state: &b.world.state, now: b.world.now, d60: false, p64: false, prios: &prios, extend: None, log_line: None };
                let shipped_day = forkplan::ForkPlan::plan(&oracle, &b, &ask).unwrap_or_else(|e| panic!("draw {index}: the oracle: {e}")).fork_day;
                match forkclass::d64_allows(old, &line, &shipped_day, &because, harness.as_deref(), &registered) {
                    Err(e) => refused.push(e),
                    Ok(keys) if !keys.is_empty() => changed.push(format!("draw {index} `{}`", keys.join("`, `"))),
                    Ok(_) => {}
                }
            }
        }
        out.push_str(&serde_json::to_string(&line).expect("a line serialises"));
        out.push('\n');
    }
    refused.extend(held.head.iter().filter(|d| !written.contains(d)).map(|d| format!("draw {d}: a frozen line the draw no longer writes")));
    eprintln!(
        "batch: {added} line(s) added, {} changed ({}), {} refused; {} draw(s) of {} not held by the binary:\n  {}",
        changed.len(),
        changed.join("; "),
        refused.len(),
        not_held.len(),
        forkclass::BATCH_DRAWS,
        not_held.join("\n  ")
    );
    assert!(refused.is_empty(), "the batch re-bless is refused by the owner's D64 and wrote nothing:\n  {}", refused.join("\n  "));
    std::fs::write(&out_path, out).expect("the frozen batch is written");
}

/// **Freeze the driven days** (W-39, README gap 3390) — inert without `TM_PLANNER_BLESS_DRIVEN`.
/// Each of `forkclass::DRIVES` is driven with the built binary over its parent primary line and
/// frozen with `forkplan::comparand_answers` over `tm-oracle plan`, the classes' own. A line it holds is held to the owner's D64 as the
/// classes' re-bless is (`forkclass::d64_allows`, `TM_PLANNER_BLESS_BECAUSE`), and a changed world
/// is refused by name. `TM_PLANNER_BLESS_DRIVEN_OUT` writes elsewhere, for a dry run. **What a
/// line is held against is the file's COMMITTED history** (W-42 track C, README gap 4151;
/// `frozenhist::held`), never the working copy, and a line HEAD holds that no drive writes is
/// refused; `TM_PLANNER_BLESS_HARNESS` names a corrected harness reading (the owner's D85).
///
/// **It asks fork 4748911 OUT of the tree and sits outside the fork region** (W-45 track C, README
/// gap 4680), as the batch's bless does, so the driven days stay re-blessable after R3.
#[test]
#[ignore]
fn the_frozen_driven_days_are_blessed() {
    if std::env::var_os("TM_PLANNER_BLESS_DRIVEN").is_none() {
        eprintln!("inert: set TM_PLANNER_BLESS_DRIVEN=1 (with TM_ORACLE) to write {}", forkclass::FROZEN_DRIVEN);
        return;
    }
    let oracle = forkplan::Oracle::new(forkplan::oracle_path().expect("TM_PLANNER_BLESS_DRIVEN asks fork 4748911 out of the tree: set TM_ORACLE"));
    let tz = tz();
    let because = forkclass::because_of("TM_PLANNER_BLESS_BECAUSE");
    let harness = forkclass::harness_of("TM_PLANNER_BLESS_HARNESS");
    let registered = forkclass::registered_parity();
    let path = forkclass::driven_path();
    let out_path = std::env::var_os("TM_PLANNER_BLESS_DRIVEN_OUT").map(std::path::PathBuf::from).unwrap_or_else(|| path.clone());
    let held = frozenhist::held(&path, frozenhist::key_of("name")).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", held.census(forkclass::FROZEN_DRIVEN));
    let (mut out, mut refused) = (String::new(), Vec::new());
    for d in &forkclass::DRIVES {
        let parent = frozen_lines().iter().find(|l| l["class"] == d.from && l["secondary"].is_null()).expect("a primary parent");
        let world = forkclass::drive(&ClassWorld::of_json(&parent["world"], tz).expect("a stored world"), d).unwrap_or_else(|e| panic!("{}: {e}", d.name));
        let b = Built::of(world.clone());
        let prios = forkclass::kernel_answer_with_grants(&b).unwrap_or_else(|e| panic!("{}: the kernel refused: {e}", d.name)).1;
        let answers = forkplan::comparand_answers(&b, &prios, &oracle).unwrap_or_else(|e| panic!("{}: the oracle: {e}", d.name));
        let mut line = serde_json::json!({
            "name": d.name, "class": class_of(&b).key(), "from": d.from,
            "verbs": d.verbs.iter().map(|(at, args)| serde_json::json!([at, args])).collect::<Vec<_>>(),
            "now": d.now, "world": world.to_json(),
        });
        for key in forkclass::ANSWERS {
            forkclass::set_answer(&mut line, key, answers[key].clone());
        }
        if let Some(old) = held.get(d.name) {
            if old["world"] != line["world"] {
                refused.push(format!("{}: the binary writes another world now — a re-draw, which D64(b) must decide", d.name));
            } else {
                let ask = forkplan::ForkAsk { state: &b.world.state, now: b.world.now, d60: false, p64: false, prios: &prios, extend: None, log_line: None };
                let shipped_day = forkplan::ForkPlan::plan(&oracle, &b, &ask).unwrap_or_else(|e| panic!("{}: the oracle: {e}", d.name)).fork_day;
                if let Err(e) = forkclass::d64_allows(old, &line, &shipped_day, &because, harness.as_deref(), &registered) {
                    refused.push(e);
                }
            }
        }
        out.push_str(&serde_json::to_string(&line).expect("a line serialises"));
        out.push('\n');
    }
    refused.extend(
        held.head.iter().filter(|n| !forkclass::DRIVES.iter().any(|d| d.name == n.as_str())).map(|n| format!("{n}: a frozen line no drive writes any more")),
    );
    assert!(refused.is_empty(), "the driven re-bless is refused and wrote nothing:\n  {}", refused.join("\n  "));
    std::fs::write(&out_path, out).expect("the frozen driven days are written");
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
/// primary lines (README gap 3123) — and since W-38 the `window` and `worked`
/// lines exactly the worlds `forkclass::window_worlds` and
/// `forkclass::worked_worlds` derive: a missing one is added with its answers
/// cleared, a stale one is re-derived only under the same listing and reason.
/// `TM_PLANNER_DRAW_ADD=<floor>@<index>[,…]` adds a DRAWN secondary line for a
/// floor of [`DRAWN_FLOORS`] (W-38: the two `p52` lines), only for a world the
/// binary can hold and a draw no line records. `TM_PLANNER_DRAW_OUT` writes
/// elsewhere, for a dry run. Since W-42 track C (README gap 4151) a derived line
/// the working copy lacks is looked up in the file's COMMITTED history
/// (`frozenhist::held`) before it is re-derived as added.
///
/// **It reaches no fork planner, and sits outside the fork region** (W-45 track C,
/// README gap 4680): it clears a re-drawn line's answers and writes no answer, and
/// the re-bless that fills them asks `tm-oracle plan`
/// ([`the_frozen_fork_classes_are_reblessed`], since W-43), so a re-draw stays possible
/// after R3. Until W-45 it sat in the region, and R3 would have deleted it with the
/// fork it never asked.
#[test]
#[ignore]
fn the_frozen_class_worlds_are_redrawn() {
    let Ok(listed) = std::env::var("TM_PLANNER_DRAW") else {
        eprintln!("inert: set TM_PLANNER_DRAW=<class,…> to re-draw {}", forkclass::FROZEN_CLASSES);
        return;
    };
    let listed: BTreeSet<String> = listed.split(',').map(str::trim).filter(|c| !c.is_empty()).map(str::to_string).collect();
    let because = std::env::var("TM_PLANNER_DRAW_BECAUSE").unwrap_or_default();
    let reasoned = forkclass::is_d64b_reason(&because);
    let tz = tz();
    let path = forkclass::frozen_path();
    let out_path = std::env::var_os("TM_PLANNER_DRAW_OUT").map(std::path::PathBuf::from).unwrap_or_else(|| path.clone());
    let text = std::fs::read_to_string(&path).expect("the frozen classes read");
    let lines: Vec<Value> = text.lines().filter(|l| !l.trim().is_empty()).map(|l| serde_json::from_str(l).expect("JSON")).collect();
    // **A derived line the working copy lacks is found in the COMMITTED history** (W-42 track C,
    // README gap 4151; `frozenhist::held`): deleting one is then not re-derived as an "added" line
    // with its answers cleared — the re-bless would hold it to its committed self anyway.
    let committed = frozenhist::held(&path, frozenhist::class_key).unwrap_or_else(|e| panic!("{e}"));
    let derived_of = |secondary: &str, derived: &Value| -> Option<Value> {
        let same = |l: &&Value| l["secondary"] == secondary && l["derived"] == *derived;
        lines.iter().find(same).or_else(|| committed.ever.values().map(|c| &c.line).find(same)).cloned()
    };
    let mut bad = Vec::new();
    let mut redrawn = Vec::new();
    let clear = |line: &mut Value| {
        for key in forkclass::ANSWERS {
            forkclass::set_answer(line, key, Value::Null);
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
    // **A drawn SECONDARY line, added** (W-38): `TM_PLANNER_DRAW_ADD=<floor>@<index>[,…]` draws
    // the class draw at `index` from the file's own seed, with the arm the draw itself names,
    // and adds it as a secondary line for `floor`, its answers cleared for the re-bless — only
    // for a floor the file's secondaries may be drawn for ([`DRAWN_FLOORS`]), a world the
    // shipped binary can hold (D64(b)'s property), and a draw no line already records. Whether
    // the line MEETS its floor is asked after the re-bless fills it
    // (`the_frozen_days_cover_what_the_arms_floors_demand`), as every secondary's is.
    let seed = out.iter().find_map(|l| l["seed"].as_str()).unwrap_or_default().to_string();
    for spec in std::env::var("TM_PLANNER_DRAW_ADD").unwrap_or_default().split(',').map(str::trim).filter(|x| !x.is_empty()) {
        let parsed = spec.split_once('@').and_then(|(f, i)| i.parse::<usize>().ok().map(|i| (f.to_string(), i)));
        let Some((floor, index)) = parsed else {
            bad.push(format!("TM_PLANNER_DRAW_ADD: `{spec}` is not <floor>@<index>"));
            continue;
        };
        if !DRAWN_FLOORS.contains(&floor.as_str()) {
            bad.push(format!("TM_PLANNER_DRAW_ADD: `{floor}` is not a floor a secondary line is drawn for: {DRAWN_FLOORS:?}"));
            continue;
        }
        if out.iter().any(|l| l["seed"] == seed && l["draw"] == index) {
            bad.push(format!("TM_PLANNER_DRAW_ADD: draw {index} is already a line of the file"));
            continue;
        }
        let Some(draw) = forkclass::class_draws(&seed, None).nth(index) else {
            bad.push(format!("TM_PLANNER_DRAW_ADD: no draw {index}"));
            continue;
        };
        let w = forkclass::world_of(&draw);
        let b = Built::of(w.clone());
        if let Err(e) = forkclass::binary_holds(&b) {
            bad.push(format!("TM_PLANNER_DRAW_ADD: draw {index} is a world the binary cannot hold: {}", e.join("; ")));
            continue;
        }
        let key = class_of(&b).key();
        let mut line = serde_json::json!({
            "class": key, "secondary": floor, "arm": draw.widening.arm(), "case": format!("{:?}", draw.case),
            "seed": seed, "draw": index, "world": w.to_json(),
        });
        clear(&mut line);
        redrawn.push(format!("{key} ({floor}) at draw {index}: added"));
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
                "class": class_of(&Built::of(w.clone())).key(), "secondary": "d61", "arm": parent["arm"], "case": parent["case"],
                "seed": parent["seed"], "draw": parent["draw"],
                "derived": {"from": key, "pause": pause.to_rfc3339(), "now": w.now.to_rfc3339()},
                "world": w.to_json(),
            });
            clear(&mut line);
            match derived_of("d61", &line["derived"]) {
                Some(old) if old["world"] == line["world"] => line = old,
                Some(old) => {
                    let mut kept = old;
                    replace(&mut kept, w, what, &mut bad, &mut redrawn);
                    line = kept;
                }
                None => redrawn.push(format!("{what}: added")),
            }
            out.push(line);
        }
    }
    // The window-task lines (W-38, README gap 3200): one derived from every PRIMARY line, by
    // `forkclass::window_worlds`, under the same rules as D61's.
    for parent in out.iter().filter(|l| l["secondary"].is_null()).cloned().collect::<Vec<_>>() {
        let world = ClassWorld::of_json(&parent["world"], tz).expect("a stored world");
        for w in forkclass::window_worlds(&world) {
            let key = parent["class"].as_str().unwrap_or_default();
            let what = format!("{key} (window)");
            let mut line = serde_json::json!({
                "class": class_of(&Built::of(w.clone())).key(), "secondary": "window", "arm": parent["arm"],
                "case": parent["case"], "seed": parent["seed"], "draw": parent["draw"],
                "derived": {"from": key, "now": w.now.to_rfc3339()},
                "world": w.to_json(),
            });
            clear(&mut line);
            match derived_of("window", &line["derived"]) {
                Some(old) if old["world"] == line["world"] => line = old,
                Some(old) => {
                    let mut kept = old;
                    replace(&mut kept, w, what, &mut bad, &mut redrawn);
                    line = kept;
                }
                None => redrawn.push(format!("{what}: added")),
            }
            out.push(line);
        }
    }
    // The inner-break lines (W-38, README gap 3282; parity P55): derived from every PRIMARY
    // line `forkclass::worked_worlds` answers for, under the same rules.
    for parent in out.iter().filter(|l| l["secondary"].is_null()).cloned().collect::<Vec<_>>() {
        let world = ClassWorld::of_json(&parent["world"], tz).expect("a stored world");
        for w in forkclass::worked_worlds(&world) {
            let key = parent["class"].as_str().unwrap_or_default();
            let what = format!("{key} (worked)");
            let mut line = serde_json::json!({
                "class": class_of(&Built::of(w.clone())).key(), "secondary": "worked", "arm": parent["arm"],
                "case": parent["case"], "seed": parent["seed"], "draw": parent["draw"],
                "derived": {"from": key, "now": w.now.to_rfc3339()},
                "world": w.to_json(),
            });
            clear(&mut line);
            match derived_of("worked", &line["derived"]) {
                Some(old) if old["world"] == line["world"] => line = old,
                Some(old) => {
                    let mut kept = old;
                    replace(&mut kept, w, what, &mut bad, &mut redrawn);
                    line = kept;
                }
                None => redrawn.push(format!("{what}: added")),
            }
            out.push(line);
        }
    }
    // The overrun lines (W-38, README gaps 3207 and 3480; parity P45): derived from every
    // PRIMARY line `forkclass::overrun_worlds` answers for, under the same rules.
    for parent in out.iter().filter(|l| l["secondary"].is_null()).cloned().collect::<Vec<_>>() {
        let world = ClassWorld::of_json(&parent["world"], tz).expect("a stored world");
        for w in forkclass::overrun_worlds(&world) {
            let key = parent["class"].as_str().unwrap_or_default();
            let what = format!("{key} (overrun)");
            let mut line = serde_json::json!({
                "class": class_of(&Built::of(w.clone())).key(), "secondary": "overrun", "arm": parent["arm"],
                "case": parent["case"], "seed": parent["seed"], "draw": parent["draw"],
                "derived": {"from": key, "now": w.now.to_rfc3339()},
                "world": w.to_json(),
            });
            clear(&mut line);
            match derived_of("overrun", &line["derived"]) {
                Some(old) if old["world"] == line["world"] => line = old,
                Some(old) => {
                    let mut kept = old;
                    replace(&mut kept, w, what, &mut bad, &mut redrawn);
                    line = kept;
                }
                None => redrawn.push(format!("{what}: added")),
            }
            out.push(line);
        }
    }
    // The typed-pause and interruption-order lines (W-39, README gaps 3473, 3474 and 3529):
    // derived from every PRIMARY line `forkclass::typed_worlds` and `forkclass::order_worlds`
    // answer for, under the same rules.
    for kind in ["typed", "order"] {
        for parent in out.iter().filter(|l| l["secondary"].is_null()).cloned().collect::<Vec<_>>() {
            let world = ClassWorld::of_json(&parent["world"], tz).expect("a stored world");
            let derived = if kind == "typed" { forkclass::typed_worlds(&world) } else { forkclass::order_worlds(&world) };
            for w in derived {
                let key = parent["class"].as_str().unwrap_or_default();
                let what = format!("{key} ({kind} at {})", w.now.format("%H:%M"));
                let mut line = serde_json::json!({
                    "class": class_of(&Built::of(w.clone())).key(), "secondary": kind, "arm": parent["arm"],
                    "case": parent["case"], "seed": parent["seed"], "draw": parent["draw"],
                    "derived": {"from": key, "now": w.now.to_rfc3339()},
                    "world": w.to_json(),
                });
                clear(&mut line);
                match lines.iter().find(|l| l["secondary"] == kind && l["derived"] == line["derived"]) {
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
        if !out.iter().any(|l| l["secondary"] == old["secondary"] && l["derived"] == old["derived"]) {
            // The PARENT's class (a line after a meeting files under its own, W-38).
            let key = old["derived"]["from"].as_str().unwrap_or_default();
            let kind = old["secondary"].as_str().unwrap_or("?");
            if reasoned && parents_redrawn.contains(key) {
                redrawn.push(format!("{key} ({kind} at {}): dropped -- its parent was re-drawn and its rule no longer derives it", old["derived"]["now"]));
            } else {
                bad.push(format!("{key} ({kind} at {}): its rule no longer derives this world", old["derived"]["now"]));
            }
        }
    }
    eprintln!("re-draw: {} line(s): {}", redrawn.len(), redrawn.join("; "));
    assert!(bad.is_empty(), "the re-draw is refused by the owner's D64 and wrote nothing:\n  {}", bad.join("\n  "));
    let text: String = out.iter().map(|l| serde_json::to_string(l).expect("a line serialises") + "\n").collect();
    std::fs::write(&out_path, text).expect("the frozen classes are written");
}

/// **P45's reset clause, witnessed over one backend** (W-38, README gap 3480; split from the region's
/// test at W-45 track C, README gap 4682, so the witness outlives R3): on a frozen `overrun` line the
/// fork's rows after the break planned with the break LOGGED (`forkplan::p45_after`, the comparand)
/// are not the rows planned at the same instant with it unlogged — so the frozen comparand pins the
/// clause, and the kernel, held to it, resets its counter at a running break of at least
/// `break_min`. Until W-38's `overrun` lines no frozen break day could tell the two apart. The
/// overrun lines read, and the classes of those that witness it.
fn overrun_witnesses(fp: &dyn forkplan::ForkPlan) -> (usize, Vec<String>) {
    let tz = tz();
    let (mut lines, mut witnessed) = (0, Vec::new());
    for line in frozen_lines().iter().filter(|l| l["secondary"] == "overrun") {
        lines += 1;
        let b = Built::of(ClassWorld::of_json(&line["world"], tz).expect("a stored world"));
        let prios = forkclass::kernel_answer_with_grants(&b).expect("the kernel answers").1;
        let with = forkplan::p45_after(&b, &prios, fp).expect("the fork plans").expect("a running break");
        let from = DateTime::parse_from_rfc3339(with["from"].as_str().expect("from")).expect("an instant").with_timezone(&tz);
        let ask = forkplan::ForkAsk { state: &b.world.state, now: from, d60: true, p64: true, prios: &prios, extend: None, log_line: None };
        let day = fp.plan(&b, &ask).expect("the fork plans").day;
        let unlogged: Vec<Value> = day["segments"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .filter(|s| forkplan::at(&s["start"]).is_some_and(|a| a >= from.fixed_offset()))
            .cloned()
            .collect();
        if with["rows"] != Value::Array(unlogged) {
            witnessed.push(line["class"].as_str().unwrap_or("?").to_string());
        }
    }
    (lines, witnessed)
}

/// **P45's reset clause has a witness, out of the tree** — [`overrun_witnesses`] over `tm-oracle
/// plan`, fork 4748911 (W-45 track C, README gap 4682): the region's
/// the_overrun_lines_witness_p45s_reset asks the in-tree fork, which R3 deletes; this asks the
/// fork that outlives it. Inert without `TM_ORACLE`.
#[test]
#[ignore]
fn the_overrun_lines_witness_p45s_reset_out_of_the_tree() {
    let Some(bin) = forkplan::oracle_path() else {
        eprintln!("inert: set TM_ORACLE to an oracle built by kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh");
        return;
    };
    let oracle = forkplan::Oracle::new(bin);
    let (lines, witnessed) = overrun_witnesses(&oracle);
    println!("overrun lines whose rows the logged break changes, asked of fork 4748911: {} of {lines}: {witnessed:?}", witnessed.len());
    assert!(!witnessed.is_empty(), "no frozen overrun line witnesses P45's reset ({lines} line(s))");
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gaps 2722, 2925)
use tm_core::dayplan::DayPlan;
use tm_core::planner;
use tm_core::priority::Prio;

/// **The fork's answers for one stored world** — since W-39 `forkplan::comparand_answers`
/// over the in-tree fork (`forkplan::InTree`), the ONE definition the oracle arm's comparand
/// is built by too (the owner's D72): the departures are applied to the day's JSON there, so
/// this region only PLANS. Every frozen line was re-blessed through it unchanged
/// ([`the_frozen_classes_are_the_forks_answer_today`]).
fn fork_answers(b: &Built, prios: &[Prio]) -> Value {
    forkplan::comparand_answers(b, prios, &forkplan::InTree).unwrap_or_else(|e| panic!("the in-tree fork: {e}"))
}

/// **P45's reset clause has a witness** (W-38, README gap 3480) — [`overrun_witnesses`] over the
/// in-tree fork; its out-of-the-tree twin, `the_overrun_lines_witness_p45s_reset_out_of_the_tree`,
/// outlives R3.
#[test]
fn the_overrun_lines_witness_p45s_reset() {
    let (lines, witnessed) = overrun_witnesses(&forkplan::InTree);
    println!("overrun lines whose rows the logged break changes: {} of {lines}: {witnessed:?}", witnessed.len());
    assert!(!witnessed.is_empty(), "no frozen overrun line witnesses P45's reset ({lines} line(s))");
}

/// The kernel's grants for a stored world — what `with_ranking` hands the fork.
fn kernel_prios(b: &Built) -> Vec<Prio> {
    forkclass::kernel_answer_with_grants(b).unwrap_or_else(|e| panic!("the kernel refused: {e}")).1
}

/// **The frozen answers are still the fork's on this tree** — while the fork
/// is here, every frozen line's answers (`forkclass::ANSWERS`: the day, `shipped`,
/// the flags, the what-if and since W-38 `p45`, `p52`, `p55` and `p56`) are exactly
/// what the fork answers for its stored world over the kernel's grants now. A
/// failure here says the FORK's answer moved (or the kernel's ranking it is
/// handed); a failure of the surviving arm says the kernel's day moved.
///
/// **A line P81 nets on** (the owner's D87, W-42 track R; README gaps 4240 and 4248): the in-tree
/// fork plans over the KERNEL's replay, which since D87 nets the line's logged break, so it cannot
/// answer the line's fork-4748911 reading — `day`, `shipped` and `p55` — and those three are asked
/// out of the tree (`the_frozen_lines_are_the_forks_oracle_answer_today`, with the oracle's own
/// reading of the block's minutes since W-43, README gap 4250: the reordered log the in-tree fork
/// was asked until then is a shape the owner's D92 nets). What the in-tree fork CAN answer is held
/// here: P81's answer (`p81`, the comparand asked the D87 day) is the frozen one; over the kernel's
/// replay of the stored world it draws THAT day; and every other answer is the line's.
#[test]
fn the_frozen_classes_are_the_forks_answer_today() {
    let mut stale = Vec::new();
    let mut p81_lines = 0usize;
    for line in frozen_lines() {
        let world = ClassWorld::of_json(&line["world"], tz()).expect("a stored world");
        let b = Built::of(world.clone());
        let prios = kernel_prios(&b);
        let now = fork_answers(&b, &prios);
        // The LINE, as `compare_line` names it: a secondary line carries its kind (W-38).
        let who = format!("{}{}", line["class"].as_str().unwrap_or("?"), line["secondary"].as_str().map(|s| format!(" ({s})")).unwrap_or_default());
        if line["p81"].is_null() {
            for key in forkclass::ANSWERS {
                if now[key] != line[key] {
                    stale.push(format!("{who}: `{key}`"));
                }
            }
            continue;
        }
        p81_lines += 1;
        // Over the kernel's replay the in-tree fork draws P81's answer's day — the netting is the
        // kernel's reading, and P81's answer is fork 4748911 asked it.
        if now["day"]["day"] != line["p81"]["day"] || now["day"]["hash"] != line["p81"]["hash"] {
            stale.push(format!("{who}: `day` over the kernel's replay is not P81's answer's day"));
        }
        for key in forkclass::ANSWERS.iter().filter(|k| !["day", "shipped", "p55"].contains(k)) {
            if now[*key] != line[*key] {
                stale.push(format!("{who}: `{key}` over the kernel's replay"));
            }
        }
    }
    println!("frozen fork classes re-asked: {} line(s), {p81_lines} of them carrying P81's answer", frozen_lines().len());
    assert!(p81_lines > 0, "no frozen line carries P81's answer");
    assert!(stale.is_empty(), "the frozen answers are not the fork's today (re-bless is a decision, AGENTS §7.2):\n  {}", stale.join("\n  "));
}

/// The shipped fork's day for one frozen `plan-basic` instant (D53: `planner::plan` over the
/// kernel's own grants — `planning::build_ranked`'s call), as `planner_w37_rows.rs` planned it.
fn basic_fork_day(fx: &planner_common::Fixture, state: &RuntimeState, now: DateTime<Tz>) -> DayPlan {
    let date = tm_core::planwire::plan_date(state, now);
    let cands = tm_core::priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, date, now);
    let w = planner_common::planreq::World { docs: &fx.docs, log: &fx.log, tree: &fx.tree, cfg: &fx.cfg, state, now, cands: &cands, replay: &fx.replay };
    let (_, ans) = planner_common::planreq::kernel_day(&w, None).expect("the kernel plans the day");
    planner::plan(&fx.input(state, now).with_ranking(&cands, &ans.prios))
}

/// **The frozen `plan-basic` days are still the fork's on this tree** (W-38), every line by
/// value, while the fork is here.
#[test]
fn the_frozen_plan_basic_days_are_the_forks_answer_today() {
    let fx = planner_common::load_with_log("plan-basic", Some(planner_common::BASIC_LOG));
    let mut stale = Vec::new();
    for line in forkday::frozen_basic_days() {
        let state: RuntimeState = serde_json::from_value(line["state"].clone()).expect("a stored state");
        let now = DateTime::parse_from_rfc3339(line["now"].as_str().unwrap_or_default()).expect("an instant").with_timezone(&fx.cfg.tz);
        let name = line["name"].as_str().unwrap_or_default();
        if forkday::basic_line(name, &state, now, &basic_fork_day(&fx, &state, now)).trim_end() != serde_json::to_string(&line).expect("a line").as_str() {
            stale.push(name.to_string());
        }
    }
    assert!(stale.is_empty(), "the frozen plan-basic days are not the fork's today (a re-bless is a decision):\n  {}", stale.join("\n  "));
}

/// **The frozen batch is still the fork's answer on this tree** (W-39, the owner's D72) — every
/// batch line's answers are exactly what the fork answers for its stored world over the kernel's
/// grants now, as the classes' live check asks of theirs.
#[test]
fn the_frozen_batch_is_the_forks_answer_today() {
    let mut stale = Vec::new();
    for line in forkclass::batch_lines() {
        let b = Built::of(ClassWorld::of_json(&line["world"], tz()).expect("a stored world"));
        let now = fork_answers(&b, &kernel_prios(&b));
        for key in forkclass::ANSWERS {
            if now[key] != line[key] {
                stale.push(format!("{}: `{key}`", line["name"].as_str().unwrap_or("?")));
            }
        }
    }
    assert!(stale.is_empty(), "the frozen batch is not the fork's answer today (a re-bless is a decision, AGENTS §7.2):\n  {}", stale.join("\n  "));
}

/// **The frozen driven days are still the fork's answer on this tree** (W-39, README gap 3390).
#[test]
fn the_frozen_driven_days_are_the_forks_answer_today() {
    let mut stale = Vec::new();
    for line in forkclass::driven_lines() {
        let b = Built::of(ClassWorld::of_json(&line["world"], tz()).expect("a stored world"));
        let now = fork_answers(&b, &kernel_prios(&b));
        for key in forkclass::ANSWERS {
            if now[key] != line[key] {
                stale.push(format!("{}: `{key}`", line["name"].as_str().unwrap_or("?")));
            }
        }
    }
    assert!(stale.is_empty(), "the frozen driven days are not the fork's answer today:\n  {}", stale.join("\n  "));
}

// END THE FORK PLANNER
