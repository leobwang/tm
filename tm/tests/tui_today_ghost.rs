//! §12.1's ghost row and the §11 adherence it feeds (tm-spec-v1.md §12.1,
//! §11).
//!
//! "A second row renders the plan as it stood at arrival." That plan is a
//! record — `.tm/arrival_plan.json`, written by `tm arrive` — not something
//! the TUI may recompute: a `plan()` re-run at the arrival instant runs with
//! *today's* runtime state and today's log, so the block running now is
//! reserved at 07:00 and everything closed since is missing.

mod tui_common;

use tui_common::{app_at, arrival};

/// `HH:MM item` for every block of a plan, in order.
fn blocks(plan: &tm_core::planner::DayPlan) -> Vec<String> {
    plan.segments
        .iter()
        .map(|s| {
            format!(
                "{} {}",
                s.start.format("%H:%M"),
                s.item.as_ref().map(|i| i.to_string()).unwrap_or_default()
            )
        })
        .collect()
}

#[test]
fn the_ghost_row_is_the_recorded_arrival_plan() {
    let mut app = app_at(10, 42);
    // §9: one keystroke changes one fact and `plan()` reruns — the ghost must
    // survive that unchanged, because the day only arrives once.
    app.replan();
    let ghost = app.ghost.as_ref().expect("the arrival record is the ghost");
    assert_eq!(
        blocks(ghost),
        vec!["07:00 t1", "08:07 m3", "09:32 t3", "11:50 t4"]
    );
    assert!(
        ghost.segments.iter().all(|s| s.flags.ghost),
        "every ghost segment is marked as one (emit paints the row from it)"
    );
    // A block is never stretched over the next one's start.
    for pair in ghost.segments.windows(2) {
        assert!(pair[0].end <= pair[1].start, "{:?}", blocks(ghost));
    }
}

#[test]
fn adherence_is_measured_against_the_recorded_plan() {
    // §11: "% of planned Blocks started within ±10m of plan". The record has
    // four blocks; the log starts three of them on time (t1 07:02, m3 08:09,
    // t3 09:32) and never reaches t4.
    let mut app = app_at(10, 42);
    app.replan();
    assert_eq!(arrival().len(), 4);
    assert_eq!(app.status.adherence_pct, Some(75));
}

#[test]
fn a_day_with_no_arrival_record_has_no_ghost_and_no_adherence() {
    let mut app = app_at(10, 42);
    app.arrival.clear();
    app.replan();
    assert!(app.ghost.is_none(), "no arrival, no plan it stood at");
    assert_eq!(app.status.adherence_pct, None);
}
