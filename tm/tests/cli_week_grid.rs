//! **`tm review week`'s heat grid draws a meeting's pause as the WALL** — the
//! campaign's D69 call on README gap 3244, under D65's behaviour row (parity
//! P56), and a typed pause as a PAUSE — never a leak (D68, P59).
//!
//! `plan-basic`'s calendar holds `^g1 Meeting w/ host at:2026-09-07T12:50/13:50`.
//! A block started at 12:00 runs into it, and D61 logs a `pause` at 12:50 and an
//! `unpause` at 13:50. `tm plan` draws that hour as the wall alone and `tm review
//! day` counts it lost 0 (D65); until D69 the week grid counted it as an hour of
//! `pause` — a third reading of one span. Now the part of a `Pause` segment a
//! wall of its day covers is the grid's `wall` style, and the rest stays `pause`:
//! the cut `tm plan` makes.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;
use tm_core::review::Style;

/// `^t4` from 12:00, run through the meeting: D61's pause is logged by the
/// first verb inside it and its unpause by the first after it.
fn through_the_meeting() -> Tm {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-07T12:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T13:20:00-05:00", &["now"]);
    tm.ok_at("2026-09-07T14:10:00-05:00", &["now"]);
    tm
}

/// The heat grid's day for 2026-09-07 from `tm --json review week` at `at`.
fn heat(tm: &Tm, at: &str) -> Value {
    let week = tm.json_at(at, &["review", "week"]);
    week["review"]["heat"]
        .as_array()
        .and_then(|d| d.iter().find(|x| x["date"] == "2026-09-07").cloned())
        .unwrap_or_else(|| panic!("{week}"))
}

/// Minutes of one style in one clock hour.
fn cell(day: &Value, hour: usize, style: Style) -> u64 {
    day["hours"][hour][style.index()].as_u64().unwrap_or_default()
}

/// **The drive, pinned.** The meeting's hour is the grid's `wall`, split 10 +
/// 50 across the two clock hours it spans, and no `pause` is counted there;
/// the text line says `wall 1h` and no `pause`.
#[test]
fn a_meetings_pause_is_the_wall_in_the_week_grid() {
    let tm = through_the_meeting();
    let day = heat(&tm, "2026-09-07T14:20:00-05:00");
    assert_eq!((cell(&day, 12, Style::Wall), cell(&day, 13, Style::Wall)), (10, 50), "{day}");
    assert_eq!((cell(&day, 12, Style::Pause), cell(&day, 13, Style::Pause)), (0, 0), "{day}");
    assert_eq!(cell(&day, 12, Style::Block), 50, "the stretch before the meeting: {day}");
    let text = tm.ok_at("2026-09-07T14:21:00-05:00", &["review", "week"]).stdout;
    let heat_line = text.lines().find(|l| l.trim_start().starts_with("heat")).unwrap_or_else(|| panic!("{text}"));
    assert!(heat_line.contains("wall 1h") && !heat_line.contains("pause"), "{heat_line}");
}

/// **A typed pause that straddles the meeting keeps its minutes outside it as
/// a pause** — the cut, not a drop (AGENTS §5.8): paused 12:40, resumed 14:00,
/// so ten minutes of pause before the wall's hour and ten after it.
#[test]
fn a_typed_pause_that_straddles_the_meeting_is_a_pause_outside_it() {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-07T12:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T12:40:00-05:00", &["pause"]);
    tm.ok_at("2026-09-07T14:00:00-05:00", &["pause"]);
    let day = heat(&tm, "2026-09-07T14:10:00-05:00");
    assert_eq!((cell(&day, 12, Style::Pause), cell(&day, 12, Style::Wall)), (10, 10), "{day}");
    assert_eq!((cell(&day, 13, Style::Pause), cell(&day, 13, Style::Wall)), (10, 50), "{day}");
}

/// **A pause no wall touches is a pause**, as before — the rule does not
/// over-bite, and a typed pause is never counted a leak (D68).
#[test]
fn a_pause_no_wall_touches_is_a_pause_in_the_week_grid() {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T09:10:00-05:00", &["pause"]);
    tm.ok_at("2026-09-07T09:30:00-05:00", &["pause"]);
    let day = heat(&tm, "2026-09-07T09:40:00-05:00");
    assert_eq!(cell(&day, 9, Style::Pause), 20, "{day}");
    assert_eq!(cell(&day, 9, Style::Wall) + cell(&day, 9, Style::Leak) + cell(&day, 9, Style::Idle), 0, "{day}");
}

/// Minutes of `tm --json plan`'s `pause`-kind segments in each clock hour of
/// the day, at `at` — the plan's cut of a typed pause.
fn plan_pause_by_hour(tm: &Tm, at: &str) -> Vec<u64> {
    let plan = tm.json_at(at, &["plan"]);
    let min = |s: &str| -> u64 {
        let (h, m) = s.split_once(':').unwrap_or(("0", "0"));
        h.parse::<u64>().unwrap_or(0) * 60 + m.parse::<u64>().unwrap_or(0)
    };
    let mut hours = vec![0u64; 24];
    for s in plan["segments"].as_array().cloned().unwrap_or_default() {
        if s["kind"] != "pause" {
            continue;
        }
        let (a, b) = (min(s["start"].as_str().unwrap_or("0:0")), min(s["end"].as_str().unwrap_or("0:0")));
        for (h, cell) in hours.iter_mut().enumerate() {
            let (lo, hi) = (h as u64 * 60, h as u64 * 60 + 60);
            *cell += b.min(hi).saturating_sub(a.max(lo));
        }
    }
    hours
}

/// **The grid and the plan cut ONE pause alike** (README gap 3528, the W-38
/// repair). P56's cut was written in the week grid (the host's heat_pieces,
/// over `Tree::walls_on` and `capacity::free_intervals`) and in the day plan's
/// past half (the fork's `past_segments` until R3, the kernel's
/// `Planner.pastSpans` after it) — two definitions of one cut. Since W-39
/// track T the grid draws the kernel's cut (`GridCut.segSpans`, which
/// `GridCut.pastSpans_is_segSpans` says is `Planner.pastSpans`), so until R3
/// this compares the kernel's cut with the fork's, and after R3 it compares
/// the kernel's cut with itself through two surfaces. For every clock hour of
/// three days — a typed pause straddling the meeting, D61's pause through it,
/// and a pause no wall touches — the grid's `pause` minutes are the plan's
/// `pause`-kind minutes.
#[test]
fn the_grid_and_the_plan_cut_one_pause_alike() {
    let straddle = {
        let tm = Tm::new();
        tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
        tm.ok_at("2026-09-07T12:00:00-05:00", &["start", "^t4", "--energy", "4"]);
        tm.ok_at("2026-09-07T12:40:00-05:00", &["pause"]);
        tm.ok_at("2026-09-07T14:00:00-05:00", &["pause"]);
        (tm, "2026-09-07T14:10:00-05:00")
    };
    let meeting = (through_the_meeting(), "2026-09-07T14:20:00-05:00");
    let plain = {
        let tm = Tm::new();
        tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
        tm.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
        tm.ok_at("2026-09-07T09:10:00-05:00", &["pause"]);
        tm.ok_at("2026-09-07T09:30:00-05:00", &["pause"]);
        (tm, "2026-09-07T09:40:00-05:00")
    };
    let mut total = 0;
    for (name, (tm, at)) in [("straddle", straddle), ("meeting", meeting), ("plain", plain)] {
        let day = heat(&tm, at);
        let grid: Vec<u64> = (0..24).map(|h| cell(&day, h, Style::Pause)).collect();
        let plan = plan_pause_by_hour(&tm, at);
        assert_eq!(grid, plan, "{name}: the grid's pause minutes by hour are the plan's");
        total += grid.iter().sum::<u64>();
    }
    assert_eq!(total, 20 + 20, "the straddle's 10 + 10 and the plain pause's 20 were compared");
}
