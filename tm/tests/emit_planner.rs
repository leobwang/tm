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

mod planner_common;

use chrono::NaiveTime;
use planner_common::{at, basic_state, date, load, load_with_log, BASIC_LOG};
use tm_core::config::Config;
use tm_core::emit;
use tm_core::dayplan::DayPlan;
use tm_core::planner;
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

/// (a) `plan-basic`, early start — the §4.3 day planned at 07:00.
#[test]
fn plan_basic_early_start_section_and_svg() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = basic_state();
    let day = planner::plan(&fx.input(&state, at("2026-09-07", 7, 0)));
    insta::assert_snapshot!(
        "plan_basic_early_emit",
        rendered(&day, &fx.tree, &fx.cfg, 7, 0)
    );
}

/// (b) `plan-basic`, late start with the 12:50 wall.
#[test]
fn plan_basic_late_start_section_and_svg() {
    let fx = load_with_log("plan-basic", Some(BASIC_LOG));
    let state = tm_core::store::RuntimeState {
        date: Some(date("2026-09-07")),
        wake: Some(NaiveTime::from_hms_opt(9, 0, 0).expect("time")),
        arrival: Some(NaiveTime::from_hms_opt(10, 30, 0).expect("time")),
        loc: Some("lounge".to_string()),
        ..tm_core::store::RuntimeState::default()
    };
    let day = planner::plan(&fx.input(&state, at("2026-09-07", 10, 30)));
    insta::assert_snapshot!(
        "plan_basic_late_emit",
        rendered(&day, &fx.tree, &fx.cfg, 10, 30)
    );
}

/// (c) `plan-home-day` — §8.2 step 3's `home_max_ci` cap.
#[test]
fn plan_home_day_section_and_svg() {
    let fx = load("plan-home-day");
    let day = planner::plan(&fx.input(&fx.state, at("2026-09-07", 9, 0)));
    insta::assert_snapshot!("plan_home_day_emit", rendered(&day, &fx.tree, &fx.cfg, 9, 0));
}

/// The renderer's contract with the planner, asserted rather than snapshotted:
/// no row may print the same fact twice.
///
/// `SegFlags::note` is §4.3's *trailing note column* ("due today", "↓ slot 4,
/// item 3"). The planner used to put the item's title there for routines,
/// optionals and the wind-down, and a finished block's actual minutes there
/// too, so every one of those rows printed its title (or its actual) once in
/// its own column and again in the note.
#[test]
fn no_row_repeats_its_own_title_or_actual() {
    for (name, log) in [("plan-basic", Some(BASIC_LOG)), ("plan-recur", None)] {
        let fx = load_with_log(name, log);
        let state = basic_state();
        let day = planner::plan(&fx.input(&state, at("2026-09-07", 7, 0)));
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
