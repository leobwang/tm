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
    // The log holds the break inside the block, exactly as the binary writes it.
    let events = tm.events();
    assert_eq!(events[events.len() - 3..], ["start", "break", "stop"], "{events:?}");

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
