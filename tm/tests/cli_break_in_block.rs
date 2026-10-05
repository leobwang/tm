//! **A break taken inside a block is not block time** — the owner's **D87** (README gap 4137, parity
//! P81), driven through the binary on every surface that reads a block's minutes.
//!
//! The day: `tm init --example`, woken at 07:00, `^m1` started at 09:00, a twenty-minute break from
//! 09:30 to 09:50, `tm stop` at 10:00. `tm stop` says forty minutes, and since D87 so does every other
//! surface: `tm review day`'s block minutes, load and load in blocks, `tm review week`'s block minutes
//! and its heat grid (the 09:00 hour is forty minutes of block and twenty of break, the break counted
//! once), and the item's done minutes the TUI's week pane reads. Fork 4748911's replay credited the
//! block its sixty-minute span and drew it across the break, so the review read 60 and the grid's
//! 09:00 cell held 60 + 20 minutes.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

const WAKE: &str = "2026-09-07T07:00:00-05:00";
const START: &str = "2026-09-07T09:00:00-05:00";
const BREAK_ON: &str = "2026-09-07T09:30:00-05:00";
const BREAK_OFF: &str = "2026-09-07T09:50:00-05:00";
const STOP: &str = "2026-09-07T10:00:00-05:00";
const AFTER: &str = "2026-09-07T10:01:00-05:00";

/// The example tree with the day above written into it, ending with `verb` (`stop` or `done`).
fn the_day(verb: &str) -> (Tm, String) {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(START, &["start", "^m1", "--energy", "3"]);
    tm.ok_at(BREAK_ON, &["break", "20m"]);
    tm.ok_at(BREAK_OFF, &["break"]);
    let out = tm.ok_at(STOP, &[verb]);
    (tm, out.stdout)
}

fn heat_09(week: &Value) -> Vec<u64> {
    week["review"]["heat"][0]["hours"][9]
        .as_array()
        .unwrap_or_else(|| panic!("no heat cell for 09:00: {week}"))
        .iter()
        .map(|m| m.as_u64().expect("minutes"))
        .collect()
}

#[test]
fn a_stopped_block_with_a_break_inside_counts_its_worked_minutes_everywhere() {
    let (tm, said) = the_day("stop");
    assert!(said.contains("after 40m"), "`tm stop` no longer says forty minutes: {said}");
    // The log holds the break inside the block, exactly as the binary writes it: since the owner's
    // D105 (parity P100) `tm break` logs its `break_start` when it begins, then the `break` that ends it.
    let events = tm.events();
    assert_eq!(events[events.len() - 4..], ["start", "break_start", "break", "stop"], "{events:?}");

    let day = tm.json_at(AFTER, &["review", "day"]);
    let r = &day["review"];
    assert_eq!(r["block_min"], 40, "review day's block minutes: {r}");
    assert_eq!(r["load"], 40.0, "review day's load (^m1 is ci 5, attributed from the tree): {r}");
    assert_eq!(r["load_blocks"], 0.67, "review day's load in blocks: {r}");
    assert_eq!(r["mix"]["total_min"], 40, "review day's energy mix: {r}");

    let week = tm.json_at(AFTER, &["review", "week"]);
    assert_eq!(week["review"]["block_min"], 40, "review week's block minutes");
    assert_eq!(week["review"]["load"], 40.0, "review week's load");
    let cell = heat_09(&week);
    assert_eq!((cell[0], cell[1]), (40, 20), "the 09:00 heat cell: block then break, the break counted once: {cell:?}");
    assert_eq!(cell.iter().sum::<u64>(), 60, "the 09:00 cell holds the hour once: {cell:?}");

    let human = tm.ok_at(AFTER, &["review", "week"]).stdout;
    assert!(human.contains("block 40m · break 20m"), "review week's heat line: {human}");
}

#[test]
fn a_done_block_with_a_break_inside_credits_what_it_logs_and_draws_no_block_across_the_break() {
    let (tm, _) = the_day("done");
    let done = tm.last_ev("done");
    assert_eq!(done["actual_min"], 40, "`tm done` logs the worked minutes: {done}");
    let day = tm.json_at(AFTER, &["review", "day"]);
    assert_eq!(day["review"]["block_min"], 40);
    let week = tm.json_at(AFTER, &["review", "week"]);
    let cell = heat_09(&week);
    assert_eq!((cell[0], cell[1]), (40, 20), "a done block is drawn around its break too: {cell:?}");
}

/// **A break taken while a `tm pause` holds the block** — the owner's D87 read ONE way by the host
/// and the kernel (parity **P84**, README gaps 4243 and 4332, the W-42 repair). `^m1` from 09:00,
/// paused at 09:20, a twenty-minute break from 09:30 to 09:50, then `tm pause` at 10:00 and `tm
/// stop` at 10:10. The pause held the block through the break, so ending the break leaves it held
/// and the second `tm pause` RESUMES it (`unpause` in the log); the block worked 09:00-09:20 and
/// 10:00-10:10, thirty minutes, and `tm stop`, `tm now`'s header and `tm review day` all say so.
///
/// Fork 4748911 (and this binary until the repair) said three things at once: the break's end
/// un-paused the block in `.tm/state.json`, so the second `tm pause` PAUSED it and logged a second
/// `pause` the replay read as nothing; `tm stop` subtracted the break's minutes inside the pause a
/// second time and said "after 0m"; and `tm review day` credited 20.
#[test]
fn a_break_inside_a_typed_pause_leaves_the_block_held_and_every_surface_reads_one_count() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(START, &["start", "^m1", "--energy", "3"]);
    tm.ok_at("2026-09-07T09:20:00-05:00", &["pause"]);
    tm.ok_at(BREAK_ON, &["break", "20m"]);
    tm.ok_at(BREAK_OFF, &["break"]);
    let held = tm.json_at("2026-09-07T09:55:00-05:00", &["now"]);
    assert_eq!(held["active"]["paused"], true, "the break's end un-paused a block a `tm pause` held: {held}");
    assert_eq!(held["active"]["elapsed_min"], 20, "the header while held: {held}");
    let second = tm.ok_at("2026-09-07T10:00:00-05:00", &["pause"]).stdout;
    assert!(second.contains("resumed"), "the second `tm pause` did not resume the held block: {second}");
    assert_eq!(tm.last_ev("unpause")["id"], "m1", "the resume is logged as `unpause`");
    let mid = tm.json_at("2026-09-07T10:05:00-05:00", &["now"]);
    assert_eq!(mid["active"]["elapsed_min"], 25, "`tm now`'s header at 10:05: {mid}");
    let said = tm.ok_at("2026-09-07T10:10:00-05:00", &["stop"]).stdout;
    assert!(said.contains("after 30m"), "`tm stop` subtracted the break inside the pause twice: {said}");
    // `tm break` logs its `break_start` when it begins (the owner's D105, parity P100).
    let events = tm.events();
    assert_eq!(
        events[events.len() - 6..],
        ["start", "pause", "break_start", "break", "unpause", "stop"],
        "{events:?}"
    );
    let day = tm.json_at("2026-09-07T10:11:00-05:00", &["review", "day"]);
    assert_eq!(day["review"]["block_min"], 30, "`tm review day` and `tm stop` read the block two ways: {day}");
}

/// **The host's idle minutes are a UNION** (P84): an interruption and a break that overlap stop the
/// block's clock once. `^m1` from 09:00, `tm interrupt` at 09:10, a break logged 09:20-09:40 while
/// the interruption runs, `tm resume` at 09:50, `tm stop` at 10:00: twenty minutes worked
/// (09:00-09:10, 09:50-10:00), which the kernel credits — the sum took the break a second time.
#[test]
fn an_interruption_and_a_break_that_overlap_stop_the_clock_once() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(START, &["start", "^m1", "--energy", "3"]);
    tm.ok_at("2026-09-07T09:10:00-05:00", &["interrupt"]);
    tm.ok_at("2026-09-07T09:20:00-05:00", &["break", "20m"]);
    tm.ok_at("2026-09-07T09:40:00-05:00", &["break"]);
    tm.ok_at("2026-09-07T09:50:00-05:00", &["resume"]);
    let said = tm.ok_at(STOP, &["stop"]).stdout;
    assert!(said.contains("after 20m"), "`tm stop`: {said}");
    let day = tm.json_at(AFTER, &["review", "day"]);
    assert_eq!(day["review"]["block_min"], 20, "`tm review day`: {day}");
}

/// **The rebuild from the log reads the break as the verb does** (P84; the owner's D42: the cache
/// follows the log): with the typed pause and the ended break of the test above, `.tm/state.json`
/// deleted, the block is rebuilt HELD — `ctx::logged_pause`'s `break` arm folds nothing — where
/// until the W-42 repair the rebuild read the break as un-pausing it, the reading the cache no
/// longer holds.
#[test]
fn deleting_the_runtime_state_after_a_break_inside_a_pause_rebuilds_the_block_held() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm.ok_at(START, &["start", "^m1", "--energy", "3"]);
    tm.ok_at("2026-09-07T09:20:00-05:00", &["pause"]);
    tm.ok_at(BREAK_ON, &["break", "20m"]);
    tm.ok_at(BREAK_OFF, &["break"]);
    let cached = tm.json_at("2026-09-07T09:55:00-05:00", &["now"]);
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("the runtime state");
    let rebuilt = tm.json_at("2026-09-07T09:55:00-05:00", &["now"]);
    assert_eq!(rebuilt["active"]["paused"], true, "the rebuild un-paused the held block: {rebuilt}");
    assert_eq!(rebuilt["active"]["paused"], cached["active"]["paused"], "the cache and the log disagree");
    assert_eq!(rebuilt["active"]["elapsed_min"], 20, "{rebuilt}");
}
