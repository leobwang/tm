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
    let last = tm.last();
    assert_eq!(last["ev"], "energy");
    assert_eq!(last["rep"], 3);
    assert_eq!(last["t"], "2026-09-07T10:30:00-05:00");
    insta::assert_json_snapshot!("energy_json", json);
}

#[test]
fn energy_above_five_is_an_error() {
    let tm = Tm::new();
    let out = tm.run(&["energy", "9"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("0–5"), "{}", out.stderr);
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
