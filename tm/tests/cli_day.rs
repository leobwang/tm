//! §13's clock verbs against a temp `plan/` (§17 M5).
//!
//! One test per verb: the exit code, the files it changed (read back), the
//! `.tm/log.jsonl` line it appended (§10.1), the `.tm/state.json` field it
//! set (§10.2) and an `insta` snapshot of the `--json` schema.

mod cli_common;

use cli_common::{scrub, Tm, NOW};

#[test]
fn wake_starts_the_day_and_logs_it() {
    let tm = Tm::new();
    let out = tm.run(&["wake", "06:05", "--slept", "8h10m", "--onset", "25m"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    assert_eq!(tm.state()["wake"], "06:05");
    assert_eq!(tm.state()["date"], "2026-09-07");
    let last = tm.last();
    assert_eq!(last["ev"], "wake");
    assert_eq!(last["slept_min"], 490);
    assert_eq!(last["onset_min"], 25);
    // §10.1: `t` is the wake time, not the moment the command ran.
    assert_eq!(last["t"], "2026-09-07T06:05:00-05:00");

    let tm = Tm::new();
    insta::assert_json_snapshot!(
        "wake_json",
        tm.json(&["wake", "06:05", "--slept", "8h10m"])
    );
}

#[test]
fn arrive_computes_window_and_budget_and_plans() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    let out = tm.run(&["arrive", "lounge"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    // §8.1: end = min(arrival + 8h, 19:00) + walls inside; budget = 6.
    let state = tm.state();
    assert_eq!(state["window"][0], "09:00");
    assert_eq!(state["window"][1], "18:00");
    assert_eq!(state["budget"], 6);
    assert_eq!(state["loc"], "lounge");
    assert_eq!(state["arrival"], "09:00");

    let events = tm.events();
    assert!(events.contains(&"arrive".to_string()), "{events:?}");
    assert!(events.contains(&"plan".to_string()), "{events:?}");

    // The plan was written where §4.3 says.
    assert!(tm.read("day/2026-09-07.md").contains("<!-- tm:plan start"));
    assert!(tm.exists("day/2026-09-07.svg"));
    // The block starts as they stood at arrival (§12.1's ghost row).
    assert!(tm.exists(".tm/arrival_plan.json"));

    let mut json = tm.json_at("2026-09-07T09:30:00-05:00", &["arrive", "home"]);
    scrub(&mut json, "plan_hash", "[hash]");
    insta::assert_json_snapshot!("arrive_json", json);
}

#[test]
fn start_marks_the_line_active_and_logs_energy() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["arrive", "lounge"]);
    let out = tm.run(&["start", "^t4", "--energy", "4"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    assert!(tm.line("week/2026-W37.md", "t4").starts_with("- [>]"));
    let last = tm.last();
    assert_eq!(last["ev"], "start");
    assert_eq!(last["id"], "t4");
    assert_eq!(last["rep"], 4);
    assert_eq!(tm.state()["active"]["id"], "t4");
    assert_eq!(tm.state()["active"]["started"], "09:00");

    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    insta::assert_json_snapshot!("start_json", tm.json(&["start", "^t4", "--energy", "4"]));
}

#[test]
fn done_closes_the_block_and_the_line() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let out = tm.run_at("2026-09-07T10:00:00-05:00", &["done", "--went", "1"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    assert!(tm.line("week/2026-W37.md", "t4").starts_with("- [x]"));
    let last = tm.last();
    assert_eq!(last["ev"], "done");
    assert_eq!(last["id"], "t4");
    assert_eq!(last["actual_min"], 60);
    assert_eq!(last["went"], 1);
    assert_eq!(tm.state()["active"], serde_json::Value::Null);

    insta::assert_json_snapshot!(
        "done_json",
        {
            let tm2 = Tm::new();
            tm2.ok(&["wake", "06:05", "--slept", "8h10m"]);
            tm2.ok(&["start", "^t4", "--energy", "4"]);
            tm2.json_at("2026-09-07T10:00:00-05:00", &["done"])
        }
    );
}

#[test]
fn done_partial_keeps_the_line_open_with_a_remainder() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t3", "--energy", "4"]);
    let json = tm.json_at("2026-09-07T09:30:00-05:00", &["done", "--partial"]);
    assert_eq!(json["partial"], true);

    // ^t3 is `- [>] 4 2b … est:1b`: 60 remaining − 30 worked = 30m left.
    let line = tm.line("week/2026-W37.md", "t3");
    assert!(line.starts_with("- [ ]"), "{line}");
    assert!(line.contains("est:30m"), "{line}");
    assert_eq!(tm.last()["partial"], true);
}

#[test]
fn done_with_an_id_and_no_block_is_retro() {
    let tm = Tm::new();
    let json = tm.json(&["done", "^t1"]);
    assert_eq!(json["actual_min"], 0);
    assert!(tm.line("week/2026-W37.md", "t1").starts_with("- [x]"));
    assert_eq!(tm.last()["ev"], "done");
    assert_eq!(tm.last()["actual_min"], 0);
}

#[test]
fn extend_adds_a_block_to_the_estimate() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let json = tm.json(&["extend", "1b"]);
    assert_eq!(json["by_min"], 60);
    assert_eq!(json["est_min"], 120);
    assert!(tm.line("week/2026-W37.md", "t4").contains("est:2b"));
    assert_eq!(tm.last()["ev"], "extend");
    assert_eq!(tm.last()["by_min"], 60);
    assert_eq!(tm.state()["active"]["est_min"], 120);
    insta::assert_json_snapshot!("extend_json", json);
}

#[test]
fn stop_writes_the_remaining_estimate_back() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let json = tm.json_at("2026-09-07T09:20:00-05:00", &["stop"]);
    assert_eq!(json["worked_min"], 20);
    assert_eq!(json["remaining_min"], 40);

    let line = tm.line("week/2026-W37.md", "t4");
    assert!(line.starts_with("- [ ]"), "{line}");
    assert!(line.contains("est:40m"), "{line}");
    assert_eq!(tm.last()["ev"], "stop");
    assert_eq!(tm.last()["remaining_min"], 40);
    assert_eq!(tm.state()["active"], serde_json::Value::Null);
    insta::assert_json_snapshot!("stop_json", json);
}

#[test]
fn break_starts_then_ends_with_its_actual_length() {
    let tm = Tm::new();
    let start = tm.json(&["break", "20m", "--where", "walk"]);
    assert_eq!(start["action"], "started");
    assert_eq!(tm.state()["break"]["planned_min"], 20);
    assert_eq!(tm.state()["break"]["where"], "walk");

    let end = tm.json_at("2026-09-07T09:25:00-05:00", &["break"]);
    assert_eq!(end["action"], "ended");
    assert_eq!(end["actual_min"], 25);
    let last = tm.last();
    assert_eq!(last["ev"], "break");
    assert_eq!(last["planned_min"], 20);
    assert_eq!(last["actual_min"], 25);
    assert_eq!(last["where"], "walk");
    // §10.1: `t` is the break's start.
    assert_eq!(last["t"], "2026-09-07T09:00:00-05:00");
    assert_eq!(tm.state()["break"], serde_json::Value::Null);
    insta::assert_json_snapshot!("break_json", end);
}

#[test]
fn interrupt_and_resume_account_for_the_lost_minutes() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let i = tm.json_at("2026-09-07T09:10:00-05:00", &["interrupt"]);
    assert_eq!(i["id"], "t4");
    assert_eq!(tm.state()["interrupt"]["id"], "t4");
    assert_eq!(tm.state()["active"]["paused"], true);
    assert_eq!(tm.last()["ev"], "interrupt");

    let r = tm.json_at("2026-09-07T10:05:00-05:00", &["resume"]);
    assert_eq!(r["lost_min"], 55);
    assert_eq!(tm.state()["interrupt"], serde_json::Value::Null);
    assert_eq!(tm.state()["active"]["paused"], false);
    let events = tm.events();
    assert!(events.contains(&"resume".to_string()), "{events:?}");
    insta::assert_json_snapshot!("resume_json", r);

    // §9: "segments after t_r shift; tail drops". §10.1's `resume{dropped}`
    // names what the lost minutes cost — each item once, however many blocks
    // it held (the morning plan gives `^m4` three).
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    tm.ok_at("2026-09-07T09:30:00-05:00", &["interrupt"]);
    let r = tm.json_at("2026-09-07T15:30:00-05:00", &["resume"]);
    let dropped: Vec<&str> = r["dropped"]
        .as_array()
        .expect("dropped")
        .iter()
        .filter_map(|v| v.as_str())
        .collect();
    assert!(!dropped.is_empty(), "six hours cost the day its tail: {r}");
    let mut once = dropped.clone();
    once.sort_unstable();
    once.dedup();
    assert_eq!(dropped.len(), once.len(), "each item once: {r}");
    assert_eq!(tm.last_ev("resume")["dropped"], r["dropped"]);
}

#[test]
fn pause_toggles_the_timer() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let p = tm.json(&["pause"]);
    assert_eq!(p["paused"], true);
    assert_eq!(tm.last()["ev"], "pause");
    assert_eq!(tm.state()["active"]["paused"], true);

    let u = tm.json_at("2026-09-07T09:05:00-05:00", &["pause"]);
    assert_eq!(u["paused"], false);
    assert_eq!(tm.last()["ev"], "unpause");
    insta::assert_json_snapshot!("pause_json", p);
}

#[test]
fn energy_logs_a_report_against_the_prediction() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["arrive", "lounge"]);
    let json = tm.json(&["energy", "3", "--at", "10:30"]);
    assert_eq!(json["rep"], 3);
    assert_eq!(json["at"], "10:30");
    // A non-zero delta re-plans (§8.5), so a `plan` entry follows the report;
    // assert on the `energy` entry itself rather than on the last line.
    let last = tm.last_ev("energy");
    assert_eq!(last["rep"], 3);
    assert_eq!(last["t"], "2026-09-07T10:30:00-05:00");
    assert!(
        tm.events().contains(&"energy".to_string()),
        "the report is logged: {:?}",
        tm.events()
    );
    insta::assert_json_snapshot!("energy_json", json);
}

#[test]
fn energy_above_five_is_an_error() {
    let tm = Tm::new();
    let out = tm.run(&["energy", "9"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("0–5"), "{}", out.stderr);
}

/// `tm start --help` says `--energy` is 0–5, the same §8.5 scale `tm energy`
/// takes and rejects out of range. `start` used to filter an out-of-range
/// value away instead: `--energy 9` fell back to the prediction, logged no
/// `rep` at all, and said nothing — the report the user typed, thrown away.
#[test]
fn start_refuses_an_energy_outside_the_scale() {
    let tm = Tm::new();
    let out = tm.run(&["start", "^t4", "--energy", "9"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("0–5"), "{}", out.stderr);

    // Refused before anything ran: the line is untouched and no block opened.
    assert!(tm.line("week/2026-W37.md", "t4").starts_with("- [ ]"));
    assert!(tm.events().is_empty(), "{:?}", tm.events());

    // The scale itself is unchanged, both ends of it.
    let tm = Tm::new();
    tm.ok(&["start", "^t4", "--energy", "0"]);
    assert_eq!(tm.last_ev("start")["rep"], 0);
    let tm = Tm::new();
    tm.ok(&["start", "^t4", "--energy", "5"]);
    assert_eq!(tm.last_ev("start")["rep"], 5);
}

/// §10.1's `went` is 1, 2 or 3 (§8.5), which is what `tm done --help` says.
/// An out-of-range value used to be filtered out of the log event but *not*
/// out of the day file's `## Log` note, so the two records of one `done`
/// disagreed: `went=7` in `day/2026-09-07.md`, no `went` at all in
/// `.tm/log.jsonl`, and §8.5 never saw the report.
#[test]
fn done_refuses_a_went_outside_the_scale() {
    let tm = Tm::new();
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let out = tm.run_at("2026-09-07T10:00:00-05:00", &["done", "--went", "7"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("--went is 1"), "{}", out.stderr);

    // Refused before anything ran: neither record mentions it, and the block
    // is still running.
    assert!(!tm.read("day/2026-09-07.md").contains("went=7"));
    assert_eq!(tm.last_ev("start")["ev"], "start");
    assert_eq!(tm.state()["active"]["id"], "t4");

    // The scale itself still works, at both ends.
    for went in ["1", "3"] {
        let tm = Tm::new();
        tm.ok(&["start", "^t4", "--energy", "4"]);
        let json = tm.json_at("2026-09-07T10:00:00-05:00", &["done", "--went", went]);
        assert_eq!(json["id"], "t4");
        assert_eq!(tm.last_ev("done")["went"].to_string(), went);
        assert!(tm.read("day/2026-09-07.md").contains(&format!("went={went}")));
    }
}

#[test]
fn idle_attributes_the_gap() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    let json = tm.json_at("2026-09-07T09:14:00-05:00", &["idle", "l"]);
    assert_eq!(json["attributed"], "leak");
    // The gap runs from the last logged event (the wake at 06:05).
    assert_eq!(json["min"], 189);
    let last = tm.last();
    assert_eq!(last["ev"], "idle");
    assert_eq!(last["attributed"], "leak");
    insta::assert_json_snapshot!("idle_json", tm.json(&["idle", "b", "--min", "14"]));
}

#[test]
fn ending_a_break_unpauses_the_block() {
    // §10.2's `active.paused`: the break paused the block, ending it must
    // clear the flag — otherwise the next `tm pause` unpauses.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T10:00:00-05:00", &["break", "20m", "--where", "walk"]);
    assert_eq!(tm.state()["active"]["paused"], true);

    tm.ok_at("2026-09-07T10:22:00-05:00", &["break"]);
    assert_eq!(tm.state()["active"]["paused"], false);
    assert!(!tm.run_at("2026-09-07T10:23:00-05:00", &["now"]).stdout.contains("paused"));

    // …so `tm pause` pauses.
    let p = tm.json_at("2026-09-07T10:24:00-05:00", &["pause"]);
    assert_eq!(p["paused"], true);
}

#[test]
fn stop_ends_a_running_break() {
    // §11's break integrity needs every break in the log; §10.1's `break`
    // entry is written when the break ends, so `tm stop` has to end it.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T10:00:00-05:00", &["break", "20m"]);
    tm.ok_at("2026-09-07T10:30:00-05:00", &["stop"]);

    assert_eq!(tm.state()["break"], serde_json::Value::Null);
    let br = tm
        .log()
        .into_iter()
        .find(|e| e["ev"] == "break")
        .expect("the break reached the log");
    assert_eq!(br["planned_min"], 20);
    assert_eq!(br["actual_min"], 30);
}

#[test]
fn worked_minutes_exclude_interrupted_and_paused_time() {
    // §9: an interruption pauses the block and its minutes are logged once,
    // as `resume{lost_min}`. Counting them in `done.actual_min` too would
    // inflate §8.5's duration multiplier and §11's ledgers.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T10:00:00-05:00", &["interrupt"]);
    tm.ok_at("2026-09-07T10:30:00-05:00", &["resume"]);
    let json = tm.json_at("2026-09-07T11:00:00-05:00", &["done"]);
    // 09:00 → 11:00 is 120 minutes, 30 of them interrupted.
    assert_eq!(json["actual_min"], 90);
    let done = tm
        .log()
        .into_iter()
        .find(|e| e["ev"] == "done")
        .expect("a done");
    assert_eq!(done["actual_min"], 90);

    // The same for a pause and for `tm stop`.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T09:30:00-05:00", &["pause"]);
    tm.ok_at("2026-09-07T09:50:00-05:00", &["pause"]);
    let json = tm.json_at("2026-09-07T10:00:00-05:00", &["stop"]);
    assert_eq!(json["worked_min"], 40);
}

#[test]
fn a_routine_line_is_never_rewritten() {
    // §5.1: "a recurring item never changes its line"; §4.3: in `routines.md`
    // the state is omitted and instances live in the log. A `[x]` there would
    // end the recurrence for good.
    let tm = Tm::new();
    let before = tm.read("routines.md");
    tm.ok(&["start", "lunch", "--energy", "3"]);
    assert_eq!(tm.read("routines.md"), before, "start rewrote routines.md");
    assert_eq!(tm.state()["active"]["id"], "lunch");

    tm.ok_at("2026-09-07T09:40:00-05:00", &["done"]);
    assert_eq!(tm.read("routines.md"), before, "done rewrote routines.md");

    // §10.1: the occurrence is a `routine` event, not a `done{id}`.
    let last = tm.last();
    assert_eq!(last["ev"], "routine");
    assert_eq!(last["item"], "lunch");
    assert_eq!(last["inst"], "2026-09-07");
    assert_eq!(last["status"], "done");
    assert_eq!(last["actual_min"], 40);
    assert!(!tm.events().contains(&"done".to_string()), "{:?}", tm.events());
}

#[test]
fn since_break_min_is_measured_from_the_end_of_the_break() {
    // §10.1's `start{since_break_min}`: `break.t` is when the break *began*
    // (the entry is appended when it ends, carrying `actual_min`), so the
    // working gap starts at `t + actual_min`.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["break", "20m", "--where", "walk"]);
    tm.ok_at("2026-09-07T09:25:00-05:00", &["break"]);
    tm.ok_at("2026-09-07T09:30:00-05:00", &["start", "^t4", "--energy", "4"]);
    let start = tm
        .log()
        .into_iter()
        .find(|e| e["ev"] == "start")
        .expect("a start");
    assert_eq!(start["since_break_min"], 5);

    // With no break all day the gap runs from the first block, not from 0.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T11:00:00-05:00", &["done"]);
    tm.ok_at("2026-09-07T11:00:00-05:00", &["start", "^t5", "--energy", "4"]);
    let second = tm.last_ev("start");
    assert_eq!(second["since_break_min"], 120);
}

#[test]
fn the_block_machine_survives_a_line_another_writer_removed() {
    // §1.3: three writers, one file set. If the running block's line is gone,
    // `tm done` must still close the block — there is no other way out.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);

    let path = tm.plan.join("week/2026-W37.md");
    let text = std::fs::read_to_string(&path).expect("read week");
    let kept: Vec<&str> = text.lines().filter(|l| !l.contains("^t4")).collect();
    std::fs::write(&path, format!("{}\n", kept.join("\n"))).expect("write week");

    let out = tm.run_at("2026-09-07T10:00:00-05:00", &["done"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(tm.state()["active"], serde_json::Value::Null);
    assert_eq!(tm.last()["ev"], "done");
    assert_eq!(tm.last()["actual_min"], 60);
}

#[test]
fn a_non_zero_energy_delta_replans() {
    // §8.5: "Non-zero δ triggers a replan"; §9's table: "slots re-energised".
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["arrive", "lounge"]);
    let plans = tm.events().iter().filter(|e| *e == "plan").count();

    let same = tm.json_at("2026-09-07T10:30:00-05:00", &["energy", "5"]);
    assert_eq!(same["delta"], 0);
    assert_eq!(same["replanned"], false);

    let json = tm.json_at("2026-09-07T10:31:00-05:00", &["energy", "3"]);
    assert_eq!(json["delta"], -2);
    assert_eq!(json["replanned"], true);
    // The plan was rewritten from `now`: §4.3's generated block is re-stamped.
    assert!(
        tm.read("day/2026-09-07.md").contains("<!-- tm:plan start 10:31 -->"),
        "{}",
        tm.read("day/2026-09-07.md")
    );
    assert!(tm.exists(".tm/last_plan.json"));
    // The re-energised slots move the day, so §10.1's `plan` event is appended
    // (a replan that changes nothing does not log one — see the delta-0 case
    // above, which left the count where it was).
    assert_eq!(
        tm.events().iter().filter(|e| *e == "plan").count(),
        plans + 1
    );
}

#[test]
fn the_day_file_carries_the_runtime_front_matter_and_the_log() {
    // §4.3's day file: `wake`, `slept`, `loc`, `window`, `budget` in the
    // front matter and an append-only `## Log`. §14 forbids Claude Code from
    // writing `## Log` and §1.2 gives `emit.rs` only the generated section,
    // so the CLI is the only writer of either.
    let tm = Tm::new();
    tm.ok_at("2026-09-07T08:15:00-05:00", &["wake", "08:15", "--slept", "6h"]);
    tm.ok_at("2026-09-07T08:30:00-05:00", &["arrive", "home"]);
    tm.ok_at("2026-09-07T08:35:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T09:35:00-05:00", &["done", "--went", "1"]);

    let day = tm.read("day/2026-09-07.md");
    let front: Vec<&str> = day
        .split("---")
        .nth(1)
        .unwrap_or_default()
        .lines()
        .filter(|l| !l.trim().is_empty())
        .collect();
    // §4.3's own order: date, wake, slept, loc, window, budget.
    assert_eq!(
        front,
        [
            "date: 2026-09-07",
            "wake: 08:15",
            "slept: 6h",
            "loc: home",
            "window: 08:30..17:30",
            "budget: 6",
        ],
        "{day}"
    );

    let log = day.split("## Log").nth(1).unwrap_or_default();
    assert!(log.contains("08:15 wake slept=6h"), "{day}");
    assert!(log.contains("08:30 arrive home"), "{day}");
    assert!(log.contains("08:35 start ^t4 pred="), "{day}");
    assert!(log.contains("09:35 done ^t4 60m/60m went=1"), "{day}");

    // A day file the CLI creates has the whole §4.3 skeleton.
    let tm = Tm::new();
    tm.ok_at("2026-09-08T08:30:00-05:00", &["arrive", "lounge"]);
    let day = tm.read("day/2026-09-08.md");
    for section in ["# Pinned", "## Log", "## Notes", "<!-- tm:plan start"] {
        assert!(day.contains(section), "missing {section} in {day}");
    }
}

#[test]
fn starting_a_second_block_is_refused() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    let out = tm.run(&["start", "^t5"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("running"), "{}", out.stderr);
}

#[test]
fn an_unknown_id_is_an_error() {
    let tm = Tm::new();
    let out = tm.run_at(NOW, &["start", "^zzzz"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("no such item"), "{}", out.stderr);
}

#[test]
fn an_append_after_a_torn_line_starts_a_new_line() {
    // Parity P19 (G9's writer half, design §14.3 row R10): a log whose last
    // line has no final `\n` (a write cut short, a hand edit) used to have the
    // next event glued onto the fragment, so both lines were lost to every
    // reader. The append now writes the `\n` first.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    let path = tm.plan.join(".tm/log.jsonl");
    let mut text = std::fs::read_to_string(&path).expect("read log");
    let fragment = r#"{"t":"2026-09-07T06:30:00-05:00","ev":"no"#;
    text.push_str(fragment);
    std::fs::write(&path, &text).expect("write log");

    tm.ok(&["start", "^t4", "--energy", "4"]);
    let after = tm.read(".tm/log.jsonl");
    assert!(after.ends_with('\n'), "every appended line is terminated");
    let lines: Vec<&str> = after.strip_suffix('\n').unwrap_or(&after).split('\n').collect();
    let at = lines.iter().position(|l| *l == fragment).expect("the fragment stays a line of its own");
    let appended: Vec<serde_json::Value> = lines[at + 1..]
        .iter()
        .map(|l| serde_json::from_str(l).expect("each appended line is JSON on its own"))
        .collect();
    assert!(appended.iter().any(|e| e["ev"] == "start" && e["id"] == "t4"), "{appended:?}");
    // The reader sees the start (and not the fragment): `tm log --json`.
    assert_eq!(tm.state()["active"]["id"], "t4");
    let shown = tm.json(&["log", "--item", "^t4"]);
    let shown = shown["entries"].as_array().expect("entries").clone();
    assert!(shown.iter().any(|e| e["ev"] == "start" && e["id"] == "t4"), "{shown:?}");
    tm.ok_at("2026-09-07T09:20:00-05:00", &["stop"]);
    assert_eq!(tm.state()["active"], serde_json::Value::Null, "the stop found the block the start opened");
    let parsed: Vec<serde_json::Value> =
        tm.read(".tm/log.jsonl").lines().filter_map(|l| serde_json::from_str(l).ok()).collect();
    assert_eq!(parsed.last().map(|e| e["ev"].clone()), Some(serde_json::json!("stop")));

    // A log that already ends in `\n` gains no blank line.
    let before = tm.read(".tm/log.jsonl");
    tm.ok_at("2026-09-07T09:25:00-05:00", &["start", "^t4", "--energy", "4"]);
    let now = tm.read(".tm/log.jsonl");
    assert!(now.starts_with(&before) && !now[before.len()..].starts_with('\n'), "no repair on a whole line");
}

/// Break `^m1`'s `@parent` so the kernel refuses the whole tree
/// (`itemCheck`/`danglingParent`, the owner's D6). Returns the text as it was.
fn break_tree(tm: &Tm) -> String {
    let path = tm.plan.join("week/2026-W37.md");
    let text = std::fs::read_to_string(&path).expect("read week");
    let broken = text.replace("@O1 ^m1", "@O9 ^m1");
    assert_ne!(broken, text, "the fixture no longer carries `@O1 ^m1`");
    std::fs::write(&path, &broken).expect("write week");
    text
}

fn restore_tree(tm: &Tm, text: &str) {
    std::fs::write(tm.plan.join("week/2026-W37.md"), text).expect("restore week");
}

/// **A tree the kernel refuses stops `arrive`, `resume` and `energy` before
/// they write, and the same verb runs once the tree is fixed** — gap 115,
/// closed here. These three write `state.json` and the log *before* the
/// planning call that sends the tree, so each used to fail *after* its own
/// write. Driven at `89ead46`, each on a copy of `plan-basic` with a typo'd
/// `@parent`: `arrive` left an `arrive` line and a written `state.json`,
/// `energy 3` left an `energy` line, and `resume` left `state.json` with the
/// interruption **cleared** and no log line naming it — the interruption was
/// simply lost. Both orders are checked: refused writes nothing, fixed runs.
#[test]
fn a_refused_tree_stops_the_writing_verbs_before_they_write() {
    // (a) `arrive`, from a fresh tree: it wrote both the log line and the state.
    {
        let tm = Tm::new();
        let text = break_tree(&tm);
        let before = tm.events();
        let out = tm.run(&["arrive", "lounge"]);
        assert_eq!(out.code, 1, "arrive: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("danglingParent"), "arrive: {}", out.stderr);
        assert_eq!(tm.events(), before, "arrive logged on a refused tree");
        assert!(
            !tm.exists(".tm/state.json") || tm.state()["arrival"].is_null(),
            "arrive wrote its arrival on a refused tree"
        );

        restore_tree(&tm, &text);
        let ok = tm.run(&["arrive", "lounge"]);
        assert_eq!(ok.code, 0, "arrive, fixed: {}{}", ok.stdout, ok.stderr);
        assert!(tm.events().contains(&"arrive".to_string()), "arrive did not log once fixed");
        assert_eq!(tm.state()["arrival"], "09:00");
    }

    // (b) `energy`: a non-zero delta replans (§8.5), which is the refused call.
    {
        let tm = Tm::new();
        let text = break_tree(&tm);
        let before = tm.events();
        let out = tm.run(&["energy", "3"]);
        assert_eq!(out.code, 1, "energy: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("danglingParent"), "energy: {}", out.stderr);
        assert_eq!(tm.events(), before, "energy logged on a refused tree");

        restore_tree(&tm, &text);
        let ok = tm.run(&["energy", "3"]);
        assert_eq!(ok.code, 0, "energy, fixed: {}{}", ok.stdout, ok.stderr);
        assert!(tm.events().contains(&"energy".to_string()), "energy did not log once fixed");
    }

    // (c) `resume`: the worst shape — no log line, but the interruption was
    // cleared out of `state.json` by a command that then failed.
    {
        let tm = Tm::new();
        tm.ok(&["arrive", "lounge"]);
        tm.ok(&["start", "^t3"]);
        tm.ok(&["interrupt"]);
        assert!(!tm.state()["interrupt"].is_null(), "the setup left no interruption");
        let state_before = tm.read(".tm/state.json");
        let events_before = tm.events();

        let text = break_tree(&tm);
        let out = tm.run(&["resume"]);
        assert_eq!(out.code, 1, "resume: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("danglingParent"), "resume: {}", out.stderr);
        assert_eq!(tm.events(), events_before, "resume logged on a refused tree");
        assert_eq!(
            tm.read(".tm/state.json"),
            state_before,
            "resume rewrote state.json on a refused tree — the interruption was lost"
        );

        restore_tree(&tm, &text);
        let ok = tm.run(&["resume"]);
        assert_eq!(ok.code, 0, "resume, fixed: {}{}", ok.stdout, ok.stderr);
        assert!(tm.events().contains(&"resume".to_string()), "resume did not log once fixed");
        assert!(tm.state()["interrupt"].is_null(), "the interruption is closed once fixed");
    }
}

/// **One day has ONE window** — the owner's **D45**, README gap **1530**,
/// D9's "a named fact of one reader".
///
/// Two rules existed. The runtime state's window is the day's **last**
/// `arrive` (`tm arrive` overwrites it, and `Ctx::derived_state` rebuilds it
/// that way); `DayReplay::window` is the day's **first**, which is the fork's
/// derivation and `Replay.lean`'s proved C5. `tm plan` and the day file quoted
/// the former, `tm review day` the latter, and **no surface said which**.
///
/// `--at` is §13's own flag and exists precisely so an arrival can be logged
/// out of order. Driven on the shipped binary before the repair, on this
/// fixture: `tm arrive home --at 16:00` then `tm arrive home --at 08:00` left
/// `.tm/state.json`, `tm plan --json` and `day/2026-09-07.md` all saying
/// `08:00..17:00` while `tm review day` said `window 16:00–19:00` — two
/// surfaces of one day, eight hours apart, with nothing to tell a reader which
/// was the answer.
///
/// The bite is asserted first: the two arrivals must disagree, or every line
/// below holds for the wrong reason.
#[test]
fn every_surface_of_one_day_quotes_the_same_window() {
    let tm = Tm::new();
    tm.ok(&["arrive", "home", "--at", "16:00"]);
    tm.ok(&["arrive", "home", "--at", "08:00"]);

    let arrivals: Vec<_> = tm
        .log()
        .into_iter()
        .filter(|e| e["ev"] == "arrive")
        .map(|e| e["window"][0].as_str().unwrap_or_default().to_string())
        .collect();
    assert_eq!(arrivals, vec!["16:00".to_string(), "08:00".to_string()],
        "the two arrivals no longer differ, so this test proves nothing");

    let state = tm.state();
    let want = ["08:00", "17:00"];
    assert_eq!(state["window"][0], want[0], "the cache is not the LAST arrival (D45)");
    assert_eq!(state["window"][1], want[1]);

    let plan = tm.json(&["plan"]);
    assert_eq!(plan["window"][0], want[0], "`tm plan` disagrees with the cache");
    assert_eq!(plan["window"][1], want[1]);

    assert!(
        tm.read("day/2026-09-07.md").contains(&format!("window: {}..{}", want[0], want[1])),
        "the day file disagrees: {}",
        tm.read("day/2026-09-07.md")
    );

    // The one that moved. `DayReview::window` is `NaiveTime`, so `--json`
    // spells it with seconds.
    let review = tm.json(&["review", "day"]);
    assert_eq!(
        review["review"]["window"][0], format!("{}:00", want[0]),
        "`tm review day` quotes a different window from `tm plan` (README gap 1530)"
    );
    assert_eq!(review["review"]["window"][1], format!("{}:00", want[1]));
    assert!(
        tm.run(&["review", "day"]).stdout.contains(&format!("window {}–{}", want[0], want[1])),
        "the rendered review disagrees with its own `--json`"
    );
}

/// The fallback half, so the repair above is not a rule that only ever reads
/// the cache: a review of a day the runtime is **not** about still answers from
/// the replay's own payload, which is the only window the log carries for it.
#[test]
fn a_review_of_another_day_still_reads_the_logs_own_window() {
    let tm = Tm::new();
    tm.ok(&["arrive", "home", "--at", "08:00"]);
    // **Asked on the NEXT day**, where `roll_day` has cleared the runtime's
    // window and `DayExtras::window` is therefore `None`: the answer has to
    // come from `DayReplay::window`, the only window the log carries for a day
    // that is over. A `window_now` that read the runtime alone answers `null`
    // here and loses the field.
    let review = tm.json_at(
        "2026-09-08T09:00:00-05:00",
        &["review", "day", "--date", "2026-09-07"],
    );
    assert_eq!(
        review["review"]["window"][0], "08:00:00",
        "a past day lost its window: {}", review["review"]["window"]
    );
    // And a day the log knows nothing about still has none, so the line above
    // is the fallback firing and not a default.
    let none = tm.json_at(NOW, &["review", "day", "--date", "2026-09-05"]);
    assert!(none["review"]["window"].is_null(), "{}", none["review"]["window"]);
}
