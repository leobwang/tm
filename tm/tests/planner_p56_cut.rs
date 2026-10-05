//! **P56 on days drawn to hold it: the comparand's rule against the in-tree fork's cut, before
//! R3 live and after it by value** (stage 6 W-40 track H, README gap 3719).
//!
//! `support/forkp56.rs` says what is drawn and frozen. Outside the fork region, three plain
//! tests that survive R3: the kernel planned against every frozen P56 day by the class lines'
//! one comparison (`forkclass::compare_line`); `forkplan::p56_cut` over fork 4748911's drawing
//! held, by value, to the day the in-tree fork's `cut_out` drew; and every frozen world its
//! seed's draw. Inside it, while `tm-core/src/planner.rs` is here: the frozen answers still
//! the in-tree fork's, `p56_cut` against `cut_out` live on more seeded days than are frozen, and
//! the oracle against the in-tree fork on the same days (`TM_ORACLE`). The bless asks
//! `tm-oracle plan` alone and sits outside the region since W-45 track C (README gap 4680), so the
//! file is not final at R3: it re-blesses every answer out of the tree and carries each line's
//! `cut` — the in-tree fork's own drawing, which no backend left after R3 can draw — by value.

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
#[path = "support/forkp56.rs"]
mod forkp56;

/// The committed history a bless holds its lines against (README gap 4151).
#[allow(dead_code)]
#[path = "support/frozenhist.rs"]
mod frozenhist;

use chrono::DateTime;
use chrono_tz::Tz;
use serde_json::Value;

use forkclass::{Built, ClassTally, ClassWorld};

fn tz() -> Tz {
    tm_core::config::Config::default().tz
}

/// The walls `forkplan::p56_cut` reads for a world (`forkclass::Built::walls`' spans).
fn walls(b: &Built) -> Vec<(DateTime<Tz>, DateTime<Tz>)> {
    b.walls().iter().map(|(_, lo, hi, _)| (*lo, *hi)).collect()
}

/// `paused` Lost rows of a serialised day, as `(start, end)` texts.
fn paused_rows(day: &Value) -> Vec<(String, String)> {
    day["segments"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|r| r["kind"] == "lost" && r["flags"]["note"] == "paused")
        .map(|r| (r["start"].as_str().unwrap_or_default().to_string(), r["end"].as_str().unwrap_or_default().to_string()))
        .collect()
}

/// **The kernel plans every frozen P56 day as the comparand says** — the class lines' one
/// comparison, every registered departure by its property, P56's among them; and the floors
/// (AGENTS §9.2): every line a P56 line, typed and untyped pauses both compared.
#[test]
fn the_kernel_plans_every_frozen_p56_day_the_fork_planned() {
    let lines = forkp56::p56_lines();
    let mut t = ClassTally::default();
    let mut findings = Vec::new();
    for l in &lines {
        findings.extend(forkclass::compare_line(l, &mut t));
    }
    println!("seeded P56 days: {} line(s) — {}", lines.len(), t.line(findings.len()));
    assert!(findings.is_empty(), "{} disagreement(s) with the frozen P56 days:\n  {}", findings.len(), findings.join("\n  "));
    assert_eq!(lines.len(), forkp56::P56_FROZEN, "the file holds every seeded P56 day it freezes");
    assert_eq!(t.p56, lines.len(), "every frozen P56 day is a line P56 departs on: {t:?}");
    assert!(lines.iter().any(|l| l["typed"] == true) && lines.iter().any(|l| l["typed"] == false), "typed and untyped pauses both");
}

/// **`forkplan::p56_cut` is the in-tree fork's cut, on every frozen P56 day, by value** — the
/// comparand's rule over fork 4748911's own drawing (`shipped`) gives exactly the day the
/// in-tree fork's `cut_out` drew (`cut`), so after R3, when `p56_cut` is the comparand's only
/// P56, it is still a rule checked against the cut the shipped binary's fork made, with no oracle
/// and no in-tree fork. The floors: a paused row cut on every line, and a typed pause the cut
/// leaves in two pieces.
#[test]
fn p56_cut_is_the_in_tree_cut_on_every_frozen_p56_day() {
    let lines = forkp56::p56_lines();
    let (mut cut_rows, mut split) = (0usize, 0usize);
    let mut findings = Vec::new();
    for l in &lines {
        let who = l["name"].as_str().unwrap_or("?");
        let b = Built::of(ClassWorld::of_json(&l["world"], tz()).expect("a stored world"));
        let mut d = l["shipped"]["day"].clone();
        forkplan::p56_cut(b.cfg.tz, &mut d, &walls(&b));
        if let Some(diff) = forkplan::first_difference("day", &d, &l["cut"]["day"]) {
            findings.push(format!("{who}: p56_cut over fork 4748911's drawing is not the in-tree cut: {diff}"));
        }
        let (before, after) = (paused_rows(&l["shipped"]["day"]), paused_rows(&l["cut"]["day"]));
        cut_rows += usize::from(before != after);
        split += usize::from(after.len() > before.len());
    }
    println!("p56_cut against the in-tree cut: {} frozen day(s), a paused row cut on {cut_rows}, a pause left in two pieces on {split}", lines.len());
    assert!(findings.is_empty(), "{}", findings.join("\n  "));
    assert_eq!(cut_rows, lines.len(), "a frozen P56 day whose cut moves no paused row");
    assert!(split > 0, "no frozen P56 day whose pause the cut leaves in two pieces");
}

/// **Every frozen P56 world is its seed's draw** — `forkp56::p56_days` re-run from
/// `forkp56::P56_SEED`: the line at each position is the draw at that index, its `typed` coin,
/// and its world byte for byte. A generator change that moves one fails here by name.
#[test]
fn every_frozen_p56_day_is_its_seeds_draw() {
    let lines = forkp56::p56_lines();
    for (l, (d, w)) in lines.iter().zip(forkp56::p56_days(forkp56::P56_SEED)) {
        let who = l["name"].as_str().unwrap_or("?");
        assert_eq!(l["draw"].as_u64(), Some(d.index as u64), "{who}: the seed's next P56 day is another draw");
        assert_eq!(l["typed"].as_bool(), Some(d.typed), "{who}: the typed coin");
        assert_eq!(ClassWorld::of_json(&l["world"], tz()).expect("a stored world"), w, "{who}: the draw builds another world");
    }
}

/// **A seeded day cannot be shadowed** (AGENTS §5.8): a frozen P56 file carrying one draw twice
/// is refused by name when it is read.
#[test]
#[should_panic(expected = "two P56 lines for draw 0")]
fn a_frozen_p56_draw_carried_twice_is_refused() {
    let lines = forkp56::p56_lines();
    let one = serde_json::to_string(&lines[0]).expect("a line");
    assert_eq!(lines[0]["draw"], 0, "the file's first line is draw 0");
    let _ = forkp56::p56_lines_of(&format!("{one}\n{one}\n"));
}

/// **Every frozen P56 day is fork 4748911's answer today** — `tm-oracle plan` asked again about
/// every line's world, through the comparand's one definition (`forkplan::comparand_answers`
/// over the oracle backend, ranked by the kernel's grants as the binary ranks it), answers every
/// key of `forkclass::ANSWERS` exactly as frozen. The assertion bytes on disk cannot make about
/// themselves; after R3 the oracle is the only fork left to ask (`cut`, the in-tree fork's own
/// drawing, is held by value by `p56_cut_is_the_in_tree_cut_on_every_frozen_p56_day`). Inert
/// without `TM_ORACLE`.
#[test]
#[ignore]
fn the_frozen_p56_days_are_the_forks_oracle_answer_today() {
    let Some(bin) = forkplan::oracle_path() else {
        eprintln!("inert: set TM_ORACLE to an oracle built by kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh");
        return;
    };
    let oracle = forkplan::Oracle::new(bin);
    let lines = forkp56::p56_lines();
    let mut stale = Vec::new();
    for l in &lines {
        let b = Built::of(ClassWorld::of_json(&l["world"], tz()).expect("a stored world"));
        let prios = forkclass::kernel_answer_with_grants(&b).unwrap_or_else(|e| panic!("{}: the kernel refused: {e}", l["name"])).1;
        match forkplan::comparand_answers(&b, &prios, &oracle) {
            Err(e) => stale.push(format!("{}: the oracle: {e}", l["name"])),
            Ok(now) => {
                for key in forkclass::ANSWERS {
                    if let Some(diff) = forkplan::first_difference(key, &now[key], &l[key]) {
                        stale.push(format!("{}: {diff}", l["name"]));
                    }
                }
            }
        }
    }
    println!(
        "frozen P56 days the fork oracle answers as frozen: {} of {} ({} oracle request(s))",
        lines.len() - stale.len(),
        lines.len(),
        oracle.asked.lock().expect("census")
    );
    assert!(stale.is_empty(), "the fork oracle does not answer the frozen P56 days as frozen:\n  {}", stale.join("\n  "));
}

/// The fresh arm's census: `[days, compared, P56 lines]`.
static FRESH: std::sync::Mutex<[u64; 3]> = std::sync::Mutex::new([0; 3]);

/// The plain fresh arm's census: `[days, planned by the kernel, typed]`.
static KERNEL_FRESH: std::sync::Mutex<[u64; 3]> = std::sync::Mutex::new([0; 3]);

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(16),
        max_shrink_iters: 0,
        ..proptest::prelude::ProptestConfig::default()
    })]

    /// **The kernel plans every fresh P56 day — of the kernel alone, in a plain run** (W-45 track C,
    /// README gap 4682): the first P56 day of a fresh seed's draw, asked as R3's host asks it
    /// (`forkclass::kernel_answer_with_grants`) and decoded by the host's codec, and its paused rows
    /// held to P56 by the rule the comparand applies (the part of a replayed pause a wall covers is
    /// not drawn: no `paused` row of the kernel's day overlaps a wall's blocked span). The region's
    /// meeting arm (`planner_invariants`' the_kernel_cuts_a_meeting_out_of_a_pause_as_the_fork_does)
    /// asserted the kernel PLANS such a day beside its fork comparison, and R3 deleted it; the fork's
    /// half meets fresh P56 days only under `TM_ORACLE` after R3 (the arm below), and this keeps the
    /// kernel's half in every `cargo test` run.
    #[test]
    fn the_kernel_plans_every_fresh_p56_day(bytes in proptest::prelude::any::<[u8; 12]>()) {
        let seed: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
        let (d, w) = forkp56::p56_days(&seed).next().expect("a P56 day");
        let b = Built::of(w);
        let (k, _) = forkclass::kernel_answer_with_grants(&b)
            .map_err(|e| proptest::test_runner::TestCaseError::fail(format!("seed {seed} (p56 draw {}): the kernel refused a P56 day the binary holds: {e}", d.index)))?;
        let walls = walls(&b);
        let over: Vec<String> = k
            .day
            .segments
            .iter()
            .filter(|s| s.is_pause())
            .filter(|s| walls.iter().any(|(lo, hi)| s.start < *hi && *lo < s.end))
            .map(|s| format!("{}–{}", s.start, s.end))
            .collect();
        proptest::prop_assert!(over.is_empty(), "seed {} (p56 draw {}): a paused row the kernel drew over a wall (P56): {:?}", seed, d.index, over);
        let [days, planned, typed] = {
            let mut c = KERNEL_FRESH.lock().expect("census");
            c[0] += 1;
            c[1] += 1;
            c[2] += u64::from(d.typed);
            *c
        };
        eprintln!("planner_p56_cut plain fresh census: {days} fresh P56 day(s), {planned} planned by the kernel, {typed} with a typed pause");
    }

    /// **The kernel plans every fresh P56 day as fork 4748911 does, P56 by `p56_cut`** — the
    /// exploring half after R3 (D46): the first P56 day of a fresh seed's draw
    /// (`forkp56::p56_days`), its comparand built over `tm-oracle plan` (fork 4748911 out of the
    /// tree, every registered departure by its property, P56 by `forkplan::p56_cut`) and held to
    /// the kernel by the class lines' one comparison, as a frozen P56 line is. Inert without
    /// `TM_ORACLE`; a failure names the seed.
    #[test]
    #[ignore]
    fn the_kernel_plans_every_fresh_p56_day_as_the_forks_oracle_plans_it(bytes in proptest::prelude::any::<[u8; 12]>()) {
        let Some(bin) = forkplan::oracle_path() else { return Ok(()) };
        static ORACLE: std::sync::OnceLock<forkplan::Oracle> = std::sync::OnceLock::new();
        let oracle = ORACLE.get_or_init(|| forkplan::Oracle::new(bin));
        let seed: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
        let (d, w) = forkp56::p56_days(&seed).next().expect("a P56 day");
        let b = Built::of(w.clone());
        let prios = forkclass::kernel_answer_with_grants(&b)
            .map_err(|e| proptest::test_runner::TestCaseError::fail(format!("seed {seed}: the kernel refused: {e}")))?
            .1;
        let answers = forkplan::comparand_answers(&b, &prios, oracle)
            .map_err(|e| proptest::test_runner::TestCaseError::fail(format!("seed {seed}: the oracle: {e}")))?;
        let mut line = forkp56::p56_line(&d, &w, &forkclass::class_of(&b).key());
        for key in forkclass::ANSWERS {
            forkclass::set_answer(&mut line, key, answers[key].clone());
        }
        let mut t = ClassTally::default();
        let findings = forkclass::compare_line(&line, &mut t);
        proptest::prop_assert!(findings.is_empty(), "seed {} (p56 draw {}, typed {}): {} disagreement(s) with fork 4748911:\n  {}", seed, d.index, d.typed, findings.len(), findings.join("\n  "));
        let [days, compared, p56] = {
            let mut c = FRESH.lock().expect("census");
            c[0] += 1;
            c[1] += 1;
            c[2] += t.p56 as u64;
            *c
        };
        eprintln!("planner_p56_cut fresh census: {days} fresh P56 day(s), {compared} compared with fork 4748911 out of the tree, {p56} P56 line(s)");
    }
}

/// The kernel's grants for a world — what the fork is ranked by (D53).
fn grants(b: &Built) -> Vec<tm_core::priority::Prio> {
    forkclass::kernel_answer_with_grants(b).unwrap_or_else(|e| panic!("the kernel refused a seeded P56 day: {e}")).1
}

/// The shipped ask: the world's state and instant, the fork's own order, no what-if.
fn shipped_ask<'a>(b: &'a Built, prios: &'a [tm_core::priority::Prio]) -> forkplan::ForkAsk<'a> {
    forkplan::ForkAsk { state: &b.world.state, now: b.world.now, d60: false, p64: false, prios, extend: None, log_line: None }
}

/// **Freeze the seeded P56 days** — inert without both `TM_P56_BLESS` and `TM_ORACLE`. The
/// first `forkp56::P56_FROZEN` seeded P56 days, each a class line (`forkp56::p56_line`) whose
/// answers are `forkplan::comparand_answers` over `tm-oracle plan` — fork 4748911 out of the tree,
/// P56 by `p56_cut` — and whose `cut` is the in-tree fork's shipped day as the committed line holds
/// it. A line it already holds is held to the owner's D64 (`forkclass::d64_allows`,
/// `TM_P56_BLESS_BECAUSE`, and since the owner's D85 `TM_P56_BLESS_HARNESS`, D64(c)), its world by
/// value; a refusal writes nothing.
///
/// **Out of the tree and outside the fork region since W-45 track C** (README gap 4680): until then
/// the bless computed every answer by BOTH backends and `cut` by the in-tree fork's `cut_out`, in the
/// region R3 deleted, so the file was final at R3 (gap 4463). The two backends' agreement is the
/// region's cross-check, the_oracle_draws_every_seeded_p56_day_as_the_in_tree_fork, while both exist.
/// **`cut` is never recomputed**: it is the in-tree fork's own drawing, and
/// `p56_cut_is_the_in_tree_cut_on_every_frozen_p56_day` holds `forkplan::p56_cut` to it — a `cut`
/// rewritten by `p56_cut` would hold the rule to itself (the comparison R3 must not leave
/// kernel-against-kernel's shape, lesson 5). So `cut` is carried from the committed line, and a draw
/// no committed version holds is refused by name. `TM_P56_BLESS_OUT` writes elsewhere, for a dry run. **What a line is held against is the file's COMMITTED
/// history** (W-42 track C, README gap 4151; `frozenhist::held`), never the working copy — and a
/// line HEAD holds that the seed no longer draws is refused.
#[test]
#[ignore]
fn the_seeded_p56_days_are_blessed() {
    if std::env::var_os("TM_P56_BLESS").is_none() {
        eprintln!("inert: set TM_P56_BLESS=1 and TM_ORACLE to write {}", forkp56::FROZEN_P56);
        return;
    }
    let oracle = forkplan::Oracle::new(forkplan::oracle_path().expect("the bless asks fork 4748911: set TM_ORACLE"));
    let because: Vec<u32> = std::env::var("TM_P56_BLESS_BECAUSE")
        .unwrap_or_default()
        .split(',')
        .filter_map(|s| s.trim().trim_start_matches('P').parse().ok())
        .collect();
    let harness = forkclass::harness_of("TM_P56_BLESS_HARNESS");
    let registered = forkclass::registered_parity();
    let held = frozenhist::held(&forkp56::p56_path(), frozenhist::key_of("draw")).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", held.census(forkp56::FROZEN_P56));
    let (mut out, mut refused, mut changed, mut drawn) = (String::new(), Vec::new(), Vec::new(), Vec::new());
    for (d, w) in forkp56::p56_days(forkp56::P56_SEED).take(forkp56::P56_FROZEN) {
        let b = Built::of(w.clone());
        let prios = grants(&b);
        let answers = forkplan::comparand_answers(&b, &prios, &oracle).unwrap_or_else(|e| panic!("p56 draw {}: the oracle: {e}", d.index));
        let p = forkplan::ForkPlan::plan(&oracle, &b, &shipped_ask(&b, &prios)).unwrap_or_else(|e| panic!("p56 draw {}: the oracle: {e}", d.index));
        let mut line = forkp56::p56_line(&d, &w, &forkclass::class_of(&b).key());
        for key in forkclass::ANSWERS {
            forkclass::set_answer(&mut line, key, answers[key].clone());
        }
        drawn.push(line["draw"].to_string());
        match held.get(&line["draw"].to_string()) {
            None => refused.push(format!(
                "{}: no committed version holds this draw, and its `cut` is the in-tree fork's own drawing, which no \
                 backend after R3 draws (a `cut` written by `p56_cut` would hold the rule to itself)",
                line["name"]
            )),
            Some(old) => {
                line["cut"] = old["cut"].clone();
                if old["world"] != line["world"] || old["typed"] != line["typed"] {
                    refused.push(format!("{}: the seed draws another world — a re-draw, which D64(b) must decide", line["name"]));
                } else {
                    match forkclass::d64_allows(old, &line, &p.fork_day, &because, harness.as_deref(), &registered) {
                        Err(e) => refused.push(e),
                        Ok(k) if !k.is_empty() => changed.push(format!("{} `{}`", line["name"], k.join("`, `"))),
                        Ok(_) => {}
                    }
                }
            }
        }
        out.push_str(&serde_json::to_string(&line).expect("a line serialises"));
        out.push('\n');
    }
    for draw in held.head.iter().filter(|d| !drawn.contains(d)) {
        refused.push(format!("p56 draw {draw}: a frozen line the seed no longer draws"));
    }
    eprintln!("seeded P56 days: {} changed ({}), {} refused", changed.len(), changed.join("; "), refused.len());
    assert!(refused.is_empty(), "the re-bless is refused and wrote nothing:\n  {}", refused.join("\n  "));
    let out_path = std::env::var_os("TM_P56_BLESS_OUT").map(std::path::PathBuf::from).unwrap_or_else(forkp56::p56_path);
    std::fs::write(out_path, out).expect("the frozen P56 days are written");
}

