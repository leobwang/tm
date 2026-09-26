//! **`tm now` prints ONE reading of the running block's worked minutes**
//! (stage 6 W-35 track E, README gap 2741).
//!
//! The header's `{elapsed}m of {est}m` was the wall clock since `started`, so
//! after an interruption `tm now` said `55m of 60m` in its header while the `▶`
//! row directly below it said `running · 35m left` — which is 60 − 25, the
//! WORKED minutes: two numbers for one fact on one screen. The `▶` row's
//! `left`, the open-block row's `so far` in `tm plan`, the TUI's
//! `App::active_elapsed_min`, §9.1's overtime prompt and the kernel's
//! `openWorkedMin` all read the log's open block (`OpenBlock::worked_min_at`:
//! pauses, breaks and interruptions stop the timer). The header reads it too
//! now, through the one rule both surfaces share, `Replay::active_worked_min`.

mod cli_common;

use cli_common::Tm;

/// After a 30-minute interruption the header, the JSON, the `▶` row's `left`
/// and `tm plan`'s open-block row all read the same 25 worked minutes of the
/// 55 on the wall clock.
#[test]
fn tm_now_reads_one_worked_minutes_after_an_interruption() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T09:10:00-05:00", &["interrupt"]);
    tm.ok_at("2026-09-07T09:40:00-05:00", &["resume"]);
    let at = "2026-09-07T09:55:00-05:00";

    let json = tm.json_at(at, &["now"]);
    assert_eq!(json["active"]["id"], "t4", "{json}");
    assert_eq!(json["active"]["est_min"], 60, "{json}");
    assert_eq!(
        json["active"]["elapsed_min"], 25,
        "the header's minutes are the worked ones, not the 55 on the wall clock: {json}"
    );

    let out = tm.run_at(at, &["now"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let head = out.stdout.lines().next().unwrap_or_default().to_string();
    assert!(head.starts_with("▶ ^t4 "), "{}", out.stdout);
    assert!(head.ends_with("· 25m of 60m"), "the header: {head}");
    // The `▶` row below it leaves what the header has not used: 60 − 25.
    assert!(
        out.stdout.contains("running · 35m left"),
        "the row and the header agree: {}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("55m"),
        "the wall-clock reading is gone from the screen: {}",
        out.stdout
    );

    // And `tm plan`'s open-block row names the same number as worked so far.
    let plan = tm.run_at(at, &["plan"]);
    assert_eq!(plan.code, 0, "{}{}", plan.stdout, plan.stderr);
    assert!(plan.stdout.contains("25m so far"), "{}", plan.stdout);
}

/// With nothing stopping the timer the two readings are the same number, so the
/// rule changes nothing on an uninterrupted block (`cli_plan`'s own 30).
#[test]
fn an_uninterrupted_block_reads_the_wall_clock_minutes() {
    let tm = Tm::new();
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let json = tm.json_at("2026-09-07T09:30:00-05:00", &["now"]);
    assert_eq!(json["active"]["elapsed_min"], 30, "{json}");
}
