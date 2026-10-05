//! §17 M4's definition of done, on a **real** plan: "snapshot of the
//! generated day section and SVG for three fixture days (early start, late
//! start with a wall, home day)".
//!
//! `emit_day_section.rs` and `emit_svg.rs` pin the renderer against a
//! hand-built `DayPlan` — that is what makes §4.3's exact rows readable in a
//! diff — but a hand-built plan cannot catch a *disagreement* between the
//! planner and the renderer: change a field `planner.rs` sets on a `Segment`
//! and every hand-built snapshot still passes. These three go through
//! `planner::plan`, so the pair is tested together.
//!
//! The days are `planner_fixtures.rs`'s, at the same instants and with the
//! same runtime state, so a row here can be read against the timeline there.
//!
//! # Two arms since W-36 track H (README gap 2872)
//!
//! **The arm that survives R3** renders the KERNEL's day (the whole request
//! through `planreq`, read back by the host's codec `tm_core::planwire`) and
//! holds it to the FORK's rendering of the same day — the committed snapshot
//! file, which is the fork's frozen answer (it is only ever written by the
//! fork's arm below, and after R3 by nothing). The two must be equal line for
//! line: the two classes they differed by until W-37 — gap 551 (a planned
//! Break row the kernel did not draw, with its SVG title) and gap 435 (a
//! routine row's `⚠` and the `due today` note the renderer prints beside it) —
//! closed at W-37 (track R), and their lines are counted and bounded exactly as
//! lines the two renderings share. **The fork's arm** — the snapshots
//! themselves, written by the in-tree fork's own §7 day — is one region R3
//! deletes.
//!
//! **The snapshots are not final at R3** (W-45 track C, README gap 4680): until
//! W-45 the region's three `insta` assertions were the files' only writers, so R3
//! would have made them the fork's last word. [`the_frozen_fork_renderings_are_blessed`]
//! writes them out of the tree: the day `tm-oracle plan` (fork 4748911, ranked as the
//! shipped binary ranks it, D53) answers — held to the frozen fixture day
//! (`forkday::FROZEN_DAYS`, the day comparand of the same three days) — rendered over
//! the kernel's day where the kernel's day IS that day, by value.

mod planner_common;

/// The comparand's backends and the frozen day comparand the bless reads (W-45 track C).
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
#[path = "support/plangen.rs"]
mod plangen;

#[allow(dead_code)]
#[path = "support/forkclass.rs"]
mod forkclass;

#[allow(dead_code)]
#[path = "support/forkplan.rs"]
mod forkplan;

/// The committed history a bless holds what it writes against (README gap 4151).
#[allow(dead_code)]
#[path = "support/frozenhist.rs"]
mod frozenhist;

use chrono::NaiveTime;
use planner_common::{at, basic_state, date, load, load_with_log, DayPlanner, Fixture, Kernel, BASIC_LOG};
use tm_core::config::Config;
use tm_core::emit;
use tm_core::dayplan::DayPlan;
use tm_core::store::RuntimeState;
use tm_core::tree::Tree;

/// `(section body, a digest of the SVG)` for one plan.
fn rendered(plan: &DayPlan, tree: &Tree, cfg: &Config, h: u32, m: u32) -> String {
    let now = at("2026-09-07", h, m);
    let wake = at("2026-09-07", 6, 5);
    let (info, body) = emit::render_plan_section(plan, tree, cfg, now);
    let bar = emit::daybar_cells(plan, None, tree, cfg, 96, wake, now);
    let svg = emit::render_svg(&bar, plan, cfg, 960, 64);
    let mut out = format!("<!-- tm:plan start {info} -->\n{body}<!-- tm:plan end -->\n\nsvg\n");
    // The whole SVG is thousands of characters of geometry; what this test is
    // for is that the *segments* reach it with their §12.1 tooltips, so the
    // digest is one line per `<title>` plus the structural markers.
    for marker in ["<defs>", "class=\"plan\"", "id=\"tm-lost\"", "class=\"cursor\""] {
        out.push_str(&format!(
            "  {marker}: {}\n",
            if svg.contains(marker) { "yes" } else { "no" }
        ));
    }
    for title in svg.match_indices("<title>").map(|(i, _)| {
        let rest = &svg[i + "<title>".len()..];
        rest[..rest.find("</title>").unwrap_or(0)].to_string()
    }) {
        out.push_str(&format!("  {title}\n"));
    }
    out
}

/// One of the three fixture days: the world, the state, and the hour planned at.
fn fixture_day(which: &str) -> (Fixture, RuntimeState, u32, u32) {
    match which {
        // (a) `plan-basic`, early start — the §4.3 day planned at 07:00.
        "plan_basic_early_emit" => (load_with_log("plan-basic", Some(BASIC_LOG)), basic_state(), 7, 0),
        // (b) `plan-basic`, late start with the 12:50 wall.
        "plan_basic_late_emit" => (
            load_with_log("plan-basic", Some(BASIC_LOG)),
            RuntimeState {
                date: Some(date("2026-09-07")),
                wake: Some(NaiveTime::from_hms_opt(9, 0, 0).expect("time")),
                arrival: Some(NaiveTime::from_hms_opt(10, 30, 0).expect("time")),
                loc: Some("lounge".to_string()),
                ..RuntimeState::default()
            },
            10,
            30,
        ),
        // (c) `plan-home-day` — §8.2 step 3's `home_max_ci` cap.
        "plan_home_day_emit" => {
            let fx = load("plan-home-day");
            let state = fx.state.clone();
            (fx, state, 9, 0)
        }
        other => panic!("no fixture day is named `{other}`"),
    }
}

/// The day `p` plans for one fixture day, rendered.
fn render_with(p: &dyn DayPlanner, which: &str) -> String {
    let (fx, state, h, m) = fixture_day(which);
    let day = p.day(&fx, &state, at("2026-09-07", h, m));
    rendered(&day, &fx.tree, &fx.cfg, h, m)
}

/// The fork's frozen rendering of a day: the committed snapshot's body.
fn frozen_render(which: &str) -> String {
    let path = format!("{}/tests/snapshots/emit_planner__{which}.snap", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    text.splitn(3, "---\n").nth(2).unwrap_or_else(|| panic!("{path} has no insta header")).to_string()
}

/// What [`compare_with_the_frozen_render`] counted.
#[derive(Debug, Default, PartialEq)]
struct RenderTally {
    rows: usize,
    breaks_551: usize,
    marks_435: usize,
}

/// A section row `HH:MM  ·      break Nm` at or after `now`: a planned Break.
fn is_planned_break_row(line: &str, now: &str) -> bool {
    line.len() > 5
        && line.is_char_boundary(5)
        && line[..5] >= *now
        && line[5..].trim_start().starts_with("·")
        && line[5..].trim_start().trim_start_matches('·').trim_start().starts_with("break ")
}

/// **The kernel's rendering is the fork's, line for line.**  Until W-37 two
/// classes were declared here — a planned Break row the kernel did not draw
/// (gap 551: the section row and its SVG title `  break · Nm`) and a routine
/// row's `⚠` with its `due today` note (gap 435) — and both CLOSED at W-37
/// (track R): every line must now be equal.  The rows of the two old classes
/// are still COUNTED, on lines the two renderings share, so a caller's exact
/// count fails if the frozen rendering stops holding one.  Returns what was
/// counted and every difference, by line.
fn compare_with_the_frozen_render(fork: &str, kernel: &str, now: &str) -> (RenderTally, Vec<String>) {
    let (f, k): (Vec<&str>, Vec<&str>) = (fork.lines().collect(), kernel.lines().collect());
    let mut t = RenderTally::default();
    let mut findings = Vec::new();
    for (i, fl) in f.iter().map(|l| l.trim_end()).enumerate() {
        t.rows += 1;
        let Some(kl) = k.get(i).map(|l| l.trim_end()) else {
            findings.push(format!("fork line {i} `{fl}` has no kernel line"));
            continue;
        };
        if fl != kl {
            findings.push(format!("fork line {i} `{fl}` against kernel line {i} `{kl}`"));
            continue;
        }
        t.breaks_551 += usize::from(is_planned_break_row(fl, now));
        t.marks_435 += usize::from(fl.contains('⚠'));
    }
    for l in k.iter().skip(f.len()) {
        findings.push(format!("a kernel line the fork's rendering does not hold: `{l}`"));
    }
    (t, findings)
}

/// The kernel arm of one day: its rendering against the fork's frozen one.
fn kernel_render_is_the_forks(which: &str, now: &str) -> RenderTally {
    let (t, findings) = compare_with_the_frozen_render(&frozen_render(which), &render_with(&Kernel, which), now);
    assert!(findings.is_empty(), "{which}: {} difference(s) (gaps 551 and 435 are closed):\n  {}", findings.len(), findings.join("\n  "));
    t
}

/// Every line of the fork's frozen rendering was walked — a comparison that
/// stopped early, or never ran, counts fewer.
fn every_frozen_line_was_walked(which: &str, t: &RenderTally) {
    assert_eq!(t.rows, frozen_render(which).lines().count(), "{which}: {t:?}");
}

/// (a) `plan-basic`, early start — the kernel's rendering is the fork's.
#[test]
fn plan_basic_early_start_section_and_svg() {
    let t = kernel_render_is_the_forks("plan_basic_early_emit", "07:00");
    assert_eq!((t.breaks_551, t.marks_435), (1, 1), "{t:?}");
    every_frozen_line_was_walked("plan_basic_early_emit", &t);
}

/// (b) `plan-basic`, late start with the 12:50 wall.
#[test]
fn plan_basic_late_start_section_and_svg() {
    let t = kernel_render_is_the_forks("plan_basic_late_emit", "10:30");
    assert_eq!((t.breaks_551, t.marks_435), (1, 1), "{t:?}");
    every_frozen_line_was_walked("plan_basic_late_emit", &t);
}

/// (c) `plan-home-day` — §8.2 step 3's `home_max_ci` cap.
#[test]
fn plan_home_day_section_and_svg() {
    let t = kernel_render_is_the_forks("plan_home_day_emit", "09:00");
    assert_eq!((t.breaks_551, t.marks_435), (1, 1), "{t:?}");
    every_frozen_line_was_walked("plan_home_day_emit", &t);
}

/// **The comparison bites, both ways** (AGENTS §5.8): a moved row, a dropped
/// row, a moved break, and — since gaps 551 and 435 closed at W-37 — a missing
/// planned break or a missing routine `⚠` each fail; the kernel's own rendering
/// passes.
#[test]
fn the_render_comparison_sees_what_is_not_a_declared_class() {
    let fork = frozen_render("plan_basic_early_emit");
    let kernel = render_with(&Kernel, "plan_basic_early_emit");
    assert!(compare_with_the_frozen_render(&fork, &kernel, "07:00").1.is_empty());
    let moved = kernel.replacen("11:30  ·      lunch 30m", "11:35  ·      lunch 30m", 1);
    assert!(!compare_with_the_frozen_render(&fork, &moved, "07:00").1.is_empty(), "a moved row passed");
    let lost = kernel.replacen("11:30  ·      lunch 30m\n", "", 1);
    assert!(!compare_with_the_frozen_render(&fork, &lost, "07:00").1.is_empty(), "a lost row passed");
    let early = fork.replacen("14:50  ·      break 20m", "06:50  ·      break 20m", 1);
    assert!(!compare_with_the_frozen_render(&early, &kernel, "07:00").1.is_empty(), "a moved break passed");
    // …and since W-37 (gaps 551 and 435 closed) a kernel rendering WITHOUT its
    // planned break, or without the routine row's `⚠`, fails as any other line.
    let unbroken = kernel.replacen("14:50  ·      break 20m\n", "", 1);
    assert!(!compare_with_the_frozen_render(&fork, &unbroken, "07:00").1.is_empty(), "a missing break passed");
    let unmarked = kernel.replacen("p0 ⚠ Pick up package", "p0   Pick up package", 1);
    assert!(!compare_with_the_frozen_render(&fork, &unmarked, "07:00").1.is_empty(), "a missing `⚠` passed");
}

/// The renderer's contract with the planner, asserted rather than snapshotted:
/// no row may print the same fact twice.
///
/// `SegFlags::note` is §4.3's *trailing note column* ("due today", "↓ slot 4,
/// item 3"). The planner used to put the item's title there for routines,
/// optionals and the wind-down, and a finished block's actual minutes there
/// too, so every one of those rows printed its title (or its actual) once in
/// its own column and again in the note.
fn no_row_repeats_its_own_title_or_actual_on(p: &dyn DayPlanner) {
    for (name, log) in [("plan-basic", Some(BASIC_LOG)), ("plan-recur", None)] {
        let fx = load_with_log(name, log);
        let state = basic_state();
        let day = p.day(&fx, &state, at("2026-09-07", 7, 0));
        let (_, body) = emit::render_plan_section(
            &day,
            &fx.tree,
            &fx.cfg,
            at("2026-09-07", 7, 0),
        );
        // The `───  window ends` divider is a row without a segment (§4.3).
        let rows: Vec<&str> = body
            .lines()
            .filter(|l| !l.contains(emit::DIVIDER))
            .collect();
        assert_eq!(rows.len(), day.segments.len(), "{name}: row/segment drift");
        for (seg, row) in day.segments.iter().zip(rows) {
            let title = seg
                .item
                .as_ref()
                .and_then(|id| fx.tree.get(id))
                .map(|i| i.title.clone())
                .filter(|t| !t.is_empty());
            if let Some(title) = title {
                // A long title is truncated with `…` in the title cell, so
                // compare on a prefix short enough to survive it.
                let head: String = title.chars().take(12).collect();
                assert_eq!(
                    row.matches(head.as_str()).count(),
                    1,
                    "{name}: `{title}` twice in `{row}`"
                );
            }
            if matches!(seg.kind, tm_core::dayplan::SegKind::WindDown) {
                assert_eq!(row.matches("wind-down").count(), 1, "{name}: `{row}`");
            }
            if seg.flags.done {
                // The `(actual)` cell, once — §4.3's `✓ break 20m  (24m)`
                // keeps the planned length in the title, which is not a
                // repeat of the actual.
                let actual = format!("({}m)", seg.minutes());
                assert_eq!(
                    row.matches(actual.as_str()).count(),
                    1,
                    "{name}: `{actual}` is not printed exactly once in `{row}`"
                );
            }
        }
    }
}

/// [`no_row_repeats_its_own_title_or_actual_on`], asked of the kernel — the
/// arm that survives R3.
#[test]
fn no_row_repeats_its_own_title_or_actual() {
    no_row_repeats_its_own_title_or_actual_on(&Kernel);
}

/// The three days a snapshot renders, each with the frozen fixture day (`forkday::FROZEN_DAYS`,
/// `planner_fixtures.rs`' `DAYS`) that is the same world, state and instant.
const EMIT_DAYS: [(&str, &str); 3] = [
    ("plan_basic_early_emit", "plan-basic early 07:00"),
    ("plan_basic_late_emit", "plan-basic late 10:30"),
    ("plan_home_day_emit", "plan-home-day 09:00"),
];

/// The committed snapshot a rendering is frozen in.
fn snapshot_path(which: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("tests/snapshots/emit_planner__{which}.snap"))
}

/// **The fork's rendering of one day, asked out of the tree** (W-45 track C, README gap 4680):
/// `tm-oracle plan`'s day for the world — fork 4748911 ranked by the kernel's grants for its
/// request, as the shipped binary ranks it (D53) — which must be the frozen fixture day of the
/// same world by value (the day comparand, re-blessed through the oracle by `planner_fixtures.rs`'
/// bless): a fork day that moved is that comparand's to decide under D64, never this rendering's.
/// It is rendered over the kernel's day, which the codec decodes into the type the renderer reads,
/// where that day IS the fork's — every field `forkday::compare_day_with_fork` compares, by value,
/// no under-used note left to the renderer, and the one field it cannot compare
/// (`Diagnostics::unplaced`, printed and never serialised) set to the fork's, which names none.
/// So the snapshot is a function of a day held by value, and a kernel that drifts from the fork
/// cannot be blessed into it.
fn fork_rendering(which: &str, frozen_name: &str, oracle: &forkplan::Oracle) -> Result<String, String> {
    let (fx, state, h, m) = fixture_day(which);
    let now = at("2026-09-07", h, m);
    let b = forkclass::Built::of_fixture(&fx.docs, &fx.log, &state, now, &fx.cfg)?;
    let (_, ans) = planreq::kernel_day(&b.request_world(), None).map_err(|e| format!("the kernel's grants: {e}"))?;
    let ask = forkplan::ForkAsk { state: &state, now, d60: false, p64: false, prios: &ans.prios, extend: None, log_line: None };
    let day = forkplan::ForkPlan::plan(oracle, &b, &ask).map_err(|e| format!("the oracle: {e}"))?.day;
    let fork = serde_json::json!({"hash": forkplan::day_hash(&day), "day": day});
    let frozen = forkday::frozen_days().get(frozen_name).ok_or_else(|| format!("no frozen fixture day `{frozen_name}`"))?;
    if fork["day"] != frozen["day"] || fork["hash"] != frozen["hash"] {
        return Err(format!(
            "fork 4748911's day is not the frozen fixture day `{frozen_name}` ({}) — re-bless the day comparand first, under D64",
            forkplan::first_difference("day", &frozen["day"], &fork["day"]).unwrap_or_else(|| "the hash".to_string())
        ));
    }
    let cands = tm_core::priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, tm_core::planwire::plan_date(&state, now), now);
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
    let (k, _) = planner_common::planreq::kernel_day(&w, None).map_err(|e| format!("the kernel: {e}"))?;
    let mut t = forkday::DayTally::default();
    let findings = forkday::compare_day_with_fork(which, &k, &fork, now, &mut t);
    if !findings.is_empty() || t.underused_notes > 0 {
        return Err(format!("the kernel's day is not fork 4748911's by value, so it cannot stand for it: {findings:?} ({t:?})"));
    }
    let mut day = k.day;
    day.diagnostics.unplaced.clear();
    Ok(rendered(&day, &fx.tree, &fx.cfg, h, m))
}

/// **A committed snapshot, split**: the commit that holds it, its insta header (kept as committed)
/// and its body — or why not. `held` is `frozenhist::held_text`'s answer for [`snapshot_path`].
fn held_snapshot(which: &str, held: Result<Option<(String, String)>, String>) -> Result<(String, String, String), String> {
    let path = snapshot_path(which);
    let (sha, text) = held?.ok_or_else(|| format!("{}: no committed version holds it", path.display()))?;
    let mut parts = text.splitn(3, "---\n");
    let (open, meta, body) = (parts.next(), parts.next(), parts.next());
    match (open, meta, body) {
        (Some(""), Some(meta), Some(body)) => Ok((sha, format!("---\n{meta}---\n"), body.to_string())),
        _ => Err(format!("{}: the committed snapshot at {sha} has no insta header", path.display())),
    }
}

/// **The frozen renderings are the fork's today, out of the tree** (W-45 track C, README gap 4680):
/// [`fork_rendering`] of every day is the committed snapshot's body, byte for byte — what the
/// region's three `insta` assertions claim of the in-tree fork's own §7 day, claimed of fork
/// 4748911 as the shipped binary runs it, so it outlives R3. Inert without `TM_ORACLE`.
#[test]
#[ignore]
fn the_frozen_fork_renderings_are_the_forks_oracle_answer_today() {
    let Some(bin) = forkplan::oracle_path() else {
        eprintln!("inert: set TM_ORACLE to an oracle built by kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh");
        return;
    };
    let oracle = forkplan::Oracle::new(bin);
    let mut stale = Vec::new();
    for (which, frozen_name) in EMIT_DAYS {
        let (sha, _, body) = held_snapshot(which, frozenhist::held_text(&snapshot_path(which))).unwrap_or_else(|e| panic!("{e}"));
        match fork_rendering(which, frozen_name, &oracle) {
            Err(e) => stale.push(format!("{which}: {e}")),
            Ok(again) => {
                let (_, findings) = compare_with_the_frozen_render(&body, &again, "00:00");
                if again != body {
                    stale.push(format!("{which}: the fork's rendering is not the snapshot held since {sha}: {findings:?}"));
                }
            }
        }
    }
    println!("frozen renderings the fork oracle answers byte for byte: {} of {} ({} oracle request(s))", EMIT_DAYS.len() - stale.len(), EMIT_DAYS.len(), oracle.asked.lock().expect("census"));
    assert!(stale.is_empty(), "{}", stale.join("\n  "));
}

/// **Freeze the fork's renderings of the three days** — inert without `TM_EMIT_BLESS`, and it asks
/// `TM_ORACLE` (W-45 track C, README gap 4680). Each snapshot keeps its committed insta header and
/// gets [`fork_rendering`]'s body. **What a snapshot is held against is its COMMITTED text**
/// (`frozenhist::held_text`, README gap 4151's rule for a whole file), never the working copy, and
/// it is held by what it is a function of: the day it renders is held by value to the frozen
/// fixture day ([`fork_rendering`] refuses a fork day that moved), so a body that moves here moves
/// because the RENDERER moved — the binary's own `emit`, which the snapshot is drawn with — and every
/// moved line is printed. A snapshot no committed version holds is refused (this bless never makes
/// one). `TM_EMIT_BLESS_OUT` names a directory to write into instead, for a dry run.
#[test]
#[ignore]
fn the_frozen_fork_renderings_are_blessed() {
    if std::env::var_os("TM_EMIT_BLESS").is_none() {
        eprintln!("inert: set TM_EMIT_BLESS=1 (with TM_ORACLE) to rewrite tests/snapshots/emit_planner__*.snap");
        return;
    }
    let oracle = forkplan::Oracle::new(forkplan::oracle_path().expect("TM_EMIT_BLESS asks fork 4748911 out of the tree: set TM_ORACLE"));
    let out_dir = std::env::var_os("TM_EMIT_BLESS_OUT").map(std::path::PathBuf::from);
    let (mut out, mut refused) = (Vec::new(), Vec::new());
    for (which, frozen_name) in EMIT_DAYS {
        let (sha, header, body) = match held_snapshot(which, frozenhist::held_text(&snapshot_path(which))) {
            Ok(x) => x,
            Err(e) => {
                refused.push(e);
                continue;
            }
        };
        match fork_rendering(which, frozen_name, &oracle) {
            Err(e) => refused.push(format!("{which}: {e}")),
            Ok(again) => {
                if again != body {
                    let (_, moved) = compare_with_the_frozen_render(&body, &again, "00:00");
                    eprintln!("{which}: the renderer moved {} line(s) of the snapshot held since {sha}:\n  {}", moved.len(), moved.join("\n  "));
                }
                out.push((which, format!("{header}{again}")));
            }
        }
    }
    assert!(refused.is_empty(), "the rendering bless is refused and wrote nothing:\n  {}", refused.join("\n  "));
    for (which, text) in out {
        let path = match &out_dir {
            Some(d) => d.join(format!("emit_planner__{which}.snap")),
            None => snapshot_path(which),
        };
        std::fs::write(&path, text).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    }
}

