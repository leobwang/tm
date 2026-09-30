//! **The week grid cuts a pause with the kernel's cut** — README gaps 3432 and
//! 3528, stage 6 W-39 track T, parity P63.
//!
//! Until W-39 the grid (`review::heat_of`) cut a `Pause` itself, over the
//! host's own reader of the calendar (`Tree::walls_on`) and its own
//! heat_pieces (deleted), while the day plan cuts it by the kernel's
//! `Planner.pastSpans` — two definitions of one cut (AGENTS §5.3). Now the
//! grid asks the kernel, through the `emit` section's walls form with a
//! `week`, for the cut `Planner.pastSpans` makes (`GridCut.segSpans`), and
//! draws what it answers. These tests read what a user reads: `tm --json
//! review week`'s cells, against `tm --json plan` on the day each pause was
//! drawn, across days of one week, a sealed day included.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;
use tm_core::review::Style;

/// The heat grid's rows from `tm --json review week` at `at` for `date`'s week.
fn heat(tm: &Tm, at: &str, date: &str) -> Vec<Value> {
    let week = tm.json_at(at, &["review", "week", "--date", date]);
    week["review"]["heat"].as_array().cloned().unwrap_or_else(|| panic!("{week}"))
}

/// One row of the grid.
fn row<'a>(rows: &'a [Value], date: &str) -> &'a Value {
    rows.iter().find(|r| r["date"] == date).unwrap_or_else(|| panic!("no row {date}"))
}

/// Minutes of one style in one clock hour of a row.
fn cell(row: &Value, hour: usize, style: Style) -> u64 {
    row["hours"][hour][style.index()].as_u64().unwrap_or_default()
}

/// Minutes of `tm --json plan`'s segments of `kind` in each clock hour, at `at`.
fn plan_by_hour(tm: &Tm, at: &str, kind: &str) -> Vec<u64> {
    let plan = tm.json_at(at, &["plan"]);
    let min = |s: &str| -> u64 {
        let (h, m) = s.split_once(':').unwrap_or(("0", "0"));
        h.parse::<u64>().unwrap_or(0) * 60 + m.parse::<u64>().unwrap_or(0)
    };
    let mut hours = vec![0u64; 24];
    for s in plan["segments"].as_array().cloned().unwrap_or_default() {
        if s["kind"] != kind {
            continue;
        }
        let (a, b) = (min(s["start"].as_str().unwrap_or("0:0")), min(s["end"].as_str().unwrap_or("0:0")));
        for (h, c) in hours.iter_mut().enumerate() {
            let (lo, hi) = (h as u64 * 60, h as u64 * 60 + 60);
            *c += b.min(hi).saturating_sub(a.max(lo));
        }
    }
    hours
}

/// Pause minutes by hour of one grid row.
fn grid_pause(row: &Value) -> Vec<u64> {
    (0..24).map(|h| cell(row, h, Style::Pause)).collect()
}

/// **The drive, pinned: one week, three kinds of stop, two days.** Monday
/// 2026-09-07: `^t4` from 12:00 through the calendar's `^g1` meeting
/// (12:50–13:50), D61 pausing it, and a typed pause 14:10–14:25 after it.
/// Tuesday: a typed pause 09:10–09:30 no wall touches, and an interruption
/// 10:00–10:15. On each day `tm --json plan` is asked for its `pause` minutes;
/// on the Wednesday (the week in the hot answer) and on the Thursday of the
/// week after — when the whole week is SEALED in the replay cache, so the
/// kernel reads it back from the records the request carries — the grid's
/// rows hold the same `pause` minutes, the meeting's hour is the wall, and the
/// interruption is the interruption's.
///
/// **The seal is asserted, not hoped for.** The undo stack pins every line a
/// `tm undo` could reach, and a test tree's whole history is within it, so
/// nothing would fold; `.tm/undo.json` is removed — the state of a history
/// longer than the stack — a day of the next week is logged, and the review
/// on its Thursday reseals: the checkpoint's ledger day passes the week and
/// its manifest names a sealed month.
#[test]
fn the_grid_is_the_plans_cut_on_every_day_of_the_week() {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-07T12:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T13:20:00-05:00", &["now"]);
    tm.ok_at("2026-09-07T14:00:00-05:00", &["now"]);
    tm.ok_at("2026-09-07T14:10:00-05:00", &["pause"]);
    tm.ok_at("2026-09-07T14:25:00-05:00", &["pause"]);
    let monday_plan = plan_by_hour(&tm, "2026-09-07T14:40:00-05:00", "pause");
    tm.ok_at("2026-09-07T15:00:00-05:00", &["done"]);

    tm.ok_at("2026-09-08T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-08T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-08T09:10:00-05:00", &["pause"]);
    tm.ok_at("2026-09-08T09:30:00-05:00", &["pause"]);
    tm.ok_at("2026-09-08T10:00:00-05:00", &["interrupt"]);
    tm.ok_at("2026-09-08T10:15:00-05:00", &["resume"]);
    let tuesday_plan = plan_by_hour(&tm, "2026-09-08T10:30:00-05:00", "pause");
    tm.ok_at("2026-09-08T11:00:00-05:00", &["done"]);

    assert_eq!(monday_plan.iter().sum::<u64>(), 15, "the plan drew Monday's typed pause: {monday_plan:?}");
    assert_eq!(tuesday_plan.iter().sum::<u64>(), 20, "the plan drew Tuesday's typed pause: {tuesday_plan:?}");
    for at in ["2026-09-09T09:00:00-05:00", "2026-09-17T09:00:00-05:00"] {
        if at.starts_with("2026-09-17") {
            let _ = std::fs::remove_file(tm.plan.join(".tm/undo.json"));
            tm.ok_at("2026-09-16T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
            tm.ok_at("2026-09-16T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
            tm.ok_at("2026-09-16T09:30:00-05:00", &["done"]);
            let _ = std::fs::remove_file(tm.plan.join(".tm/undo.json"));
        }
        let rows = heat(&tm, at, "2026-09-07");
        let ckpt: Value = serde_json::from_str(
            &std::fs::read_to_string(tm.plan.join(".tm/cache/replay/ckpt.json")).expect("the checkpoint"),
        )
        .expect("a checkpoint");
        let sealed = ckpt["meta"]["ledgerDay"].as_u64().unwrap_or(0) > 739_871
            && ckpt["manifest"].as_object().is_some_and(|m| !m.is_empty());
        assert_eq!(sealed, at.starts_with("2026-09-17"), "{at}: the week sealed: {}", ckpt["meta"]);
        let (monday, tuesday) = (row(&rows, "2026-09-07"), row(&rows, "2026-09-08"));
        assert_eq!(grid_pause(monday), monday_plan, "{at}: Monday's pause minutes are the plan's");
        assert_eq!(grid_pause(tuesday), tuesday_plan, "{at}: Tuesday's pause minutes are the plan's");
        assert_eq!((cell(monday, 12, Style::Wall), cell(monday, 13, Style::Wall)), (10, 50), "{at}: {monday}");
        assert_eq!(cell(tuesday, 10, Style::Interrupt), 15, "{at}: {tuesday}");
        assert_eq!(cell(tuesday, 10, Style::Wall) + cell(tuesday, 9, Style::Wall), 0, "{at}: {tuesday}");
    }
}

/// **Parity P63, pinned: the plan's cut is the DAY's.** A block run past
/// midnight into a call that crosses midnight with it (Tuesday 23:30 to
/// Wednesday 00:30): D61 pauses the block over the call, and the pause is
/// Tuesday's record. The planner cuts a pause of Tuesday's record by
/// Tuesday's walls clipped to Tuesday, so the grid's Tuesday row draws the
/// call's half before midnight as the wall and its half after midnight as
/// the pause — where the host's own cut, over walls it never clipped, drew
/// both halves as the wall. A pause wholly inside its day is untouched by
/// the change (the test above).
#[test]
fn a_pause_past_midnight_is_cut_by_its_days_walls() {
    let tm = Tm::new();
    let calendar = tm.plan.join("calendar/2026-W37.md");
    let mut text = std::fs::read_to_string(&calendar).expect("the calendar");
    text.push_str("- [ ] 3 Late call            at:2026-09-08T23:30/2026-09-09T00:30 ^g9\n");
    std::fs::write(&calendar, text).expect("the calendar");
    tm.ok_at("2026-09-08T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-08T23:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-08T23:40:00-05:00", &["now"]);
    tm.ok_at("2026-09-09T00:40:00-05:00", &["now"]);
    tm.ok_at("2026-09-09T00:50:00-05:00", &["done"]);
    let rows = heat(&tm, "2026-09-09T09:00:00-05:00", "2026-09-07");
    let tuesday = row(&rows, "2026-09-08");
    assert_eq!(cell(tuesday, 23, Style::Wall), 30, "the call before midnight is the wall: {tuesday}");
    assert_eq!(cell(tuesday, 23, Style::Pause), 0, "{tuesday}");
    assert_eq!(cell(tuesday, 0, Style::Pause), 30, "P63: after midnight the day's walls do not reach: {tuesday}");
    assert_eq!(cell(tuesday, 0, Style::Wall), 0, "{tuesday}");
}
