//! `tm plan` and `tm now` (§8, §13) against a temp `plan/`.
//!
//! The §8.2 algorithm is a placeholder until M4, so these tests assert the
//! *structure*: exit codes, the files written, the events appended and the
//! `--json` schema — never which item landed in which slot.

mod cli_common;

use cli_common::{schema, Tm};

#[test]
fn plan_writes_the_generated_section_the_svg_and_the_event() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["arrive", "lounge"]);

    let out = tm.run_at("2026-09-07T10:42:00-05:00", &["plan"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    // §4.3: the plan lives between the markers, and only there.
    let day = tm.read("day/2026-09-07.md");
    assert!(day.contains("<!-- tm:plan start 10:42 -->"), "{day}");
    assert!(day.contains("<!-- tm:plan end -->"), "{day}");
    assert!(day.contains("# Pinned"), "the human sections survive");
    assert!(day.contains("## Log"), "the append-only section survives");
    assert!(tm.exists("day/2026-09-07.svg"));
    assert!(tm.read("day/2026-09-07.svg").starts_with("<svg"));

    assert!(tm.events().contains(&"plan".to_string()));
    assert!(tm.exists(".tm/last_plan.json"));
    assert!(tm.state()["last_plan_hash"].is_string());
}

#[test]
fn a_replan_that_moves_nothing_is_not_logged_twice() {
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    let plans = tm.events().iter().filter(|e| *e == "plan").count();
    tm.ok_at("2026-09-07T11:00:00-05:00", &["plan"]);
    let after = tm.events().iter().filter(|e| *e == "plan").count();
    assert_eq!(plans, after, "the day did not move, so it is not a replan");
}

#[test]
fn plan_json_has_the_documented_shape() {
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    let json = tm.json(&["plan"]);
    for key in [
        "date",
        "window",
        "budget_blocks",
        "blocks_done",
        "hash",
        "segments",
        "diagnostics",
        "priorities",
        "wrote",
    ] {
        assert!(json.get(key).is_some(), "missing {key} in {json}");
    }
    assert_eq!(json["window"].as_array().map(Vec::len), Some(2));
    insta::assert_json_snapshot!("plan_schema", schema(&json));
}

#[test]
fn plan_week_renders_the_capacity_grid() {
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    let json = tm.json(&["plan", "--week"]);
    assert_eq!(json["week"], "2026-W37");
    assert_eq!(json["days"].as_array().map(Vec::len), Some(7));
    assert!(json["grid"].as_str().unwrap_or_default().contains("day"));
    insta::assert_json_snapshot!("plan_week_schema", schema(&json));
}

#[test]
fn plan_diff_compares_against_the_stored_plan() {
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    tm.ok(&["plan"]);
    let json = tm.json_at("2026-09-07T11:00:00-05:00", &["plan", "--diff"]);
    let diff = &json["diff"];
    assert_eq!(diff["had_previous"], true);
    assert_eq!(diff["drift_min"], 0);
    insta::assert_json_snapshot!("plan_diff_schema", schema(diff));
}

#[test]
fn plan_explain_answers_for_one_item_without_writing() {
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    let before = tm.read("day/2026-09-07.md");
    let out = tm.run(&["plan", "--explain", "^d1"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    // §13's example shape: `p = k(3) + bin(u=… → +1) = 4; …`.
    assert!(out.stdout.contains("p = "), "{}", out.stdout);
    assert!(out.stdout.contains("deps"), "{}", out.stdout);
    assert_eq!(tm.read("day/2026-09-07.md"), before, "explain writes nothing");

    let json = tm.json(&["plan", "--explain", "^d1"]);
    assert!(json["explain"].as_str().unwrap_or_default().contains("p = "));
    assert_eq!(json["wrote"].as_array().map(Vec::len), Some(0));
}

#[test]
fn now_reports_the_running_block_and_the_next_segments() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["arrive", "lounge"]);

    let idle = tm.json(&["now"]);
    assert_eq!(idle["active"], serde_json::Value::Null);
    assert_eq!(idle["date"], "2026-09-07");
    insta::assert_json_snapshot!("now_schema", schema(&idle));

    tm.ok(&["start", "^t4", "--energy", "4"]);
    let json = tm.json_at("2026-09-07T09:30:00-05:00", &["now"]);
    assert_eq!(json["active"]["id"], "t4");
    assert_eq!(json["active"]["elapsed_min"], 30);
    assert_eq!(json["active"]["title"], "Claude Code drafts tests");
}

#[test]
fn allow_home_lifts_the_home_energy_cap() {
    // §8.2 step 3: at home slot energy is capped at `home_max_ci` (3) unless
    // `--allow-home` says otherwise, so the week grid gains high-energy
    // minutes today.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["arrive", "home"]);
    let capped = tm.json(&["plan", "--week"]);
    let free = tm.json(&["plan", "--week", "--allow-home"]);
    let high = |v: &serde_json::Value| -> u64 {
        v["days"][0]["minutes_at_level"][4].as_u64().unwrap_or(0)
            + v["days"][0]["minutes_at_level"][5].as_u64().unwrap_or(0)
    };
    assert_eq!(high(&capped), 0, "the home cap holds without the flag");
    assert!(high(&free) > 0, "--allow-home lifts it: {free}");
}

#[test]
fn plan_needs_a_plan_directory() {
    let tm = Tm::empty();
    let out = tm.run(&["plan"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("config.toml"), "{}", out.stderr);
}
