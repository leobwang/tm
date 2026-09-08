//! `close`, `review`, `sync-cal`, `model`, `log`, `check`, `tui` and `init`
//! (§6.3, §11, §13, §14, §15) against a temp `plan/`.

mod cli_common;

use cli_common::{schema, scrub, Tm};

#[test]
fn close_day_reopens_active_lines_and_stamps_the_state() {
    let tm = Tm::new();
    let json = tm.json_at("2026-09-07T21:00:00-05:00", &["close", "day"]);
    assert_eq!(json["period"], "day");
    assert_eq!(json["key"], "2026-09-07");

    // §6.3: `[>]` → `[ ]` with the remaining estimate.
    let t3 = tm.line("week/2026-W37.md", "t3");
    assert!(t3.starts_with("- [ ]"), "{t3}");
    // The pinned item moved to the week with a day stamp.
    assert!(tm.read("week/2026-W37.md").contains("^p1"));
    assert!(tm.read("week/2026-W37.md").contains("demoted:D07"));

    assert!(tm.events().contains(&"close".to_string()));
    assert_eq!(tm.state()["closed"]["day"], "2026-09-07");
    insta::assert_json_snapshot!("close_day_schema", schema(&json));
}

#[test]
fn close_week_archives_into_the_month() {
    let tm = Tm::new();
    let json = tm.json_at("2026-09-13T21:00:00-05:00", &["close", "week"]);
    assert_eq!(json["key"], "2026-W37");
    assert!(!json["report"]["demoted"].as_array().unwrap().is_empty());

    // §6.3: the week file becomes an archive, the month keeps the copies.
    assert!(tm.line("week/2026-W37.md", "m1").starts_with("- [-]"));
    let month = tm.read("month/2026-09.md");
    let demoted = month.split("# Demoted").nth(1).unwrap_or_default();
    assert!(demoted.contains("^m1"), "{month}");
    assert!(demoted.contains("demoted:W37"), "{month}");
    assert_eq!(tm.state()["closed"]["week"], "2026-W37");
    assert!(tm.events().contains(&"close".to_string()));
}

/// §6.3 + §13: the close "runs automatically on the first command after the
/// period ends", and `Ctx::load` runs it — so `tm close week` on the Monday
/// after found its own work done and printed an all-empty report over a tree
/// it had in fact rewritten. It now names the week the auto-close closed and
/// reports what that run did (and does not archive the week you are one day
/// into).
#[test]
fn close_after_the_period_ended_reports_what_the_auto_close_did() {
    let tm = Tm::new();
    let json = tm.json_at("2026-09-14T09:00:00-05:00", &["close", "week"]);
    assert_eq!(json["key"], "2026-W37", "the week that ended, not W38");
    let report = &json["report"];
    let demoted: Vec<&str> = report["demoted"]
        .as_array()
        .expect("demoted")
        .iter()
        .map(|d| d["id"].as_str().expect("id"))
        .collect();
    // ^p1 is there because the same sweep closed the days it skipped first:
    // `day/2026-09-07#Pinned` moved into the week with `demoted:D07` (§6.3's
    // day row) and the week close then demoted it to the month. Before the
    // catch-up covered a tree with no close history, only 2026-09-13 was
    // closed and ^p1 was left behind in the day file.
    assert_eq!(demoted, vec!["m1", "m2", "m3", "m4", "p1"], "{report}");
    let moved: Vec<&str> = report["moved"]
        .as_array()
        .expect("moved")
        .iter()
        .map(|m| m["id"].as_str().expect("id"))
        .collect();
    assert_eq!(moved, vec!["x1", "x2", "d1"], "{report}");
    assert_eq!(report["carried"].as_array().expect("carried").len(), 2);
    assert_eq!(
        report["overdue_to_backlog"]
            .as_array()
            .expect("overdue")
            .len(),
        1
    );
    // W38 is the live week the walls moved into, not an archive.
    assert!(!tm.read("week/2026-W38.md").contains("closed:"));
    assert!(tm.read("week/2026-W38.md").contains("^x1"));

    // And the human line of the same run counts the same work.
    let fresh = Tm::new();
    let out = fresh.run_at("2026-09-14T09:00:00-05:00", &["close", "week"]);
    assert_eq!(
        out.stdout.trim(),
        "closed week 2026-W37 · 3 moved · 5 demoted · 0 reopened · 0 dropped",
        "{}",
        out.stderr
    );
}

/// The same for a day: run on the next morning, `tm close day` closes
/// yesterday and says what moved.
#[test]
fn close_day_after_midnight_reports_yesterday() {
    let tm = Tm::new();
    let json = tm.json_at("2026-09-08T09:00:00-05:00", &["close", "day"]);
    assert_eq!(json["key"], "2026-09-07");
    assert!(
        !json["report"]["moved"].as_array().expect("moved").is_empty(),
        "^p1 moved to the week: {json}"
    );
    assert!(tm.read("week/2026-W37.md").contains("demoted:D07"));
}

#[test]
fn close_month_can_drop_an_outcome() {
    let tm = Tm::new();
    let json = tm.json_at(
        "2026-09-30T21:00:00-05:00",
        &["close", "month", "--drop", "^O3"],
    );
    assert_eq!(json["period"], "month");
    assert_eq!(json["key"], "2026-09");
    assert!(json["report"]["dropped"]
        .as_array()
        .unwrap()
        .iter()
        .any(|d| d == "O3"));
    assert_eq!(tm.state()["closed"]["month"], "2026-09");
}

/// §6.3 + §13: the month close auto-runs from `Ctx::load` before the verb
/// body, with no drop list — so once the month has ended, `tm close month
/// --drop ^id` used to find the line already carried into the next month and
/// do nothing at all, printing a success line. An explicit `--drop` is never
/// discarded: the line comes back and is dropped.
#[test]
fn close_month_drops_an_outcome_the_auto_close_already_carried() {
    let tm = Tm::new();
    let json = tm.json_at(
        "2026-10-01T09:00:00-05:00",
        &["close", "month", "--drop", "^O3"],
    );
    assert_eq!(json["key"], "2026-09", "the month that ended");
    let report = &json["report"];
    let dropped: Vec<&str> = report["dropped"]
        .as_array()
        .expect("dropped")
        .iter()
        .map(|d| d.as_str().expect("id"))
        .collect();
    assert_eq!(dropped, vec!["O3"], "{report}");

    // The line is `[~]` back in the month it was an outcome of, not open in
    // the next one — where a `--drop` before the auto-close leaves it too.
    assert!(tm.line("month/2026-09.md", "O3").starts_with("- [~]"));
    assert!(
        !tm.read("month/2026-10.md").contains("^O3"),
        "{}",
        tm.read("month/2026-10.md")
    );

    // …and the report describes that tree: the carry the drop undid is not
    // counted as a carry.
    let moved: Vec<&str> = report["moved"]
        .as_array()
        .expect("moved")
        .iter()
        .map(|m| m["id"].as_str().expect("id"))
        .collect();
    assert!(!moved.contains(&"O3"), "{report}");
    assert!(moved.contains(&"O1"), "the rest still carried: {report}");
}

/// A `--drop` naming something this close cannot act on fails loudly (§13's
/// exit code 1) rather than being dropped on the floor.
#[test]
fn close_month_refuses_a_drop_it_cannot_honour() {
    let tm = Tm::new();
    let out = tm.run_at(
        "2026-09-30T21:00:00-05:00",
        &["close", "month", "--drop", "^nope"],
    );
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("^nope"), "{}", out.stderr);

    // ^a1 exists, but in `backlog.md` — not this close's business.
    let out = tm.run_at(
        "2026-09-30T21:00:00-05:00",
        &["close", "month", "--drop", "^a1"],
    );
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("tm drop"), "{}", out.stderr);

    // Neither run closed the month: nothing was carried and nothing dropped.
    assert!(!tm.exists("month/2026-10.md"));
    assert!(!tm.read("month/2026-09.md").contains("- [~]"));
    assert!(tm.line("backlog.md", "a1").starts_with("- [ ]"));
}

/// §6.3 gives `--drop` to the month close alone; a day or week close that
/// quietly ignored it discarded what the user asked for.
#[test]
fn close_day_and_week_refuse_a_drop_list() {
    let tm = Tm::new();
    for period in ["day", "week"] {
        let out = tm.run_at("2026-09-07T21:00:00-05:00", &["close", period, "--drop", "^p1"]);
        assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("tm close month"), "{}", out.stderr);
        assert!(!tm.exists(".tm/state.json"), "nothing ran");
    }
}

#[test]
fn the_first_command_after_a_period_ends_closes_it() {
    // §6.3: "runs automatically on the first command after the period ends".
    let tm = Tm::new();
    assert!(!tm.exists(".tm/state.json"));
    tm.ok(&["now"]);
    let closed = tm.state()["closed"].clone();
    assert_eq!(closed["day"], "2026-09-06");
    assert_eq!(closed["week"], "2026-W36");
    assert_eq!(closed["month"], "2026-08");
}

/// §6.3 + §0 principle 6, the fresh-tree case: `tm init` writes week and day
/// files and no `state.json`, so the first command a tree ever runs has no
/// close history behind it. Closing only the *last* period and stamping the
/// rest left the tree's own first week `[ ]` in a file the planner no longer
/// reads — never demoted, absent even from `diagnostics.dropped`, and
/// unreachable afterwards because `state.closed` only moves forward.
#[test]
fn a_first_command_two_weeks_late_closes_the_skipped_periods() {
    let tm = Tm::new();
    assert!(!tm.exists(".tm/state.json"), "a fresh tree has no close history");

    // Nothing has been run since the tree was made; today is a Monday in W39.
    tm.ok_at("2026-09-21T09:00:00-05:00", &["plan"]);

    // The week that was live when the tree was made is an archive now, and
    // its milestones are in the month, not stranded (§6.3).
    let week = tm.read("week/2026-W37.md");
    assert!(week.contains("closed:"), "{week}");
    assert!(tm.line("week/2026-W37.md", "m1").starts_with("- [-]"), "{week}");
    let month = tm.read("month/2026-09.md");
    let demoted = month.split("# Demoted").nth(1).unwrap_or_default();
    for id in ["m1", "m2", "m3", "m4"] {
        assert!(demoted.contains(&format!("^{id}")), "^{id} demoted: {month}");
    }
    assert!(demoted.contains("demoted:W37"), "{month}");

    // The day close ran too: `day/2026-09-07#Pinned` is in the week's archive
    // with its `demoted:D07` stamp, and from there in the month.
    assert!(demoted.contains("demoted:D07"), "{month}");

    assert_eq!(tm.state()["closed"]["week"], "2026-W38");
    assert_eq!(tm.state()["closed"]["day"], "2026-09-20");
}

/// §11 and §12.4: `tm review day` reports the monitors `tm_core::review`
/// computes — not a second, thinner set assembled in the CLI. The verb used
/// to have its own `blocks / leak / lost / MAE / estimates` summary, so the
/// shipped review had no adherence, break integrity, rest debt, sleep panel
/// or plan honesty at all, and §17 M8's hand-computed values validated code
/// the binary never ran.
#[test]
fn review_day_reports_the_monitors_and_can_write_them() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.run_at("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T10:00:00-05:00", &["done", "--went", "1"]);

    let json = tm.json_at("2026-09-07T21:00:00-05:00", &["review", "day"]);
    assert_eq!(json["period"], "day");
    assert_eq!(json["key"], "2026-09-07");
    let r = &json["review"];
    assert_eq!(r["blocks_done"], 1);
    assert_eq!(r["block_min"], 60);
    assert_eq!(r["done"][0], "t4");
    // §11's monitors the old CLI summary had no room for.
    for key in [
        "adherence",
        "breaks",
        "rest_debt_min",
        "slept_min",
        "plan_honesty",
        "mix",
        "leak",
        "energy",
    ] {
        assert!(r.get(key).is_some(), "missing review.{key} in {r}");
    }
    // The ghost row `tm arrive` recorded is the adherence denominator (§11).
    assert!(
        r["adherence"]["planned"].as_u64().unwrap_or(0) > 0,
        "no adherence denominator: {r}"
    );
    assert_eq!(r["slept_min"], 490);
    insta::assert_json_snapshot!("review_day_schema", schema(&json));

    let written = tm.json_at("2026-09-07T21:01:00-05:00", &["review", "day", "--write"]);
    assert_eq!(written["wrote"], "day/2026-09-07.md");
    let day = tm.read("day/2026-09-07.md");
    assert!(day.contains("<!-- tm:review start -->"), "{day}");
    // §12.4's rows, in the file.
    assert!(day.contains("adherence"), "{day}");
    assert!(day.contains("\n breaks    "), "{day}");
    assert!(day.contains("\n sleep     "), "{day}");
}

#[test]
fn review_week_and_month_run() {
    let tm = Tm::new();
    let week = tm.json(&["review", "week"]);
    assert_eq!(week["key"], "2026-W37");
    let month = tm.json(&["review", "month"]);
    assert_eq!(month["key"], "2026-09");
}

#[test]
fn sync_cal_without_feeds_is_a_no_op_with_a_warning() {
    // The fixture has `ics_urls = []` (§16's placeholder is not fetched).
    let tm = Tm::new();
    let json = tm.json(&["sync-cal"]);
    assert_eq!(json["events"], 0);
    assert_eq!(json["files"].as_array().map(Vec::len), Some(0));
    assert!(json["warnings"][0]
        .as_str()
        .unwrap_or_default()
        .contains("no calendar feeds"));
    insta::assert_json_snapshot!("sync_cal_schema", schema(&json));
}

#[test]
fn sync_cal_writes_the_calendar_and_keeps_manual_lines() {
    // §15 / §17 M9: "sync against a fixture `.ics` preserves `manual` lines
    // and stable ids".
    let tm = Tm::new();
    let ics = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../tm-core/tests/fixtures/sample.ics")
        .canonicalize()
        .expect("the fixture feed");
    let cfg = tm.plan.join("config.toml");
    let text = std::fs::read_to_string(&cfg).expect("read config");
    std::fs::write(
        &cfg,
        text.replace(
            "ics_urls       = []",
            &format!("ics_urls       = [\"file://{}\"]", ics.display()),
        ),
    )
    .expect("write config");

    let json = tm.json(&["sync-cal"]);
    assert!(json["events"].as_u64().unwrap_or(0) > 0, "{json}");
    let files: Vec<&str> = json["files"]
        .as_array()
        .expect("files")
        .iter()
        .filter_map(|f| f.as_str())
        .collect();
    assert!(files.contains(&"calendar/2026-W37.md"), "{files:?}");
    assert_eq!(json["weeks"].as_array().map(Vec::len), Some(3));

    let week = tm.read("calendar/2026-W37.md");
    assert!(week.contains("manual"), "the manual line survives: {week}");
    assert!(week.contains("^g4"), "with its id: {week}");
    let ids: Vec<String> = week
        .lines()
        .filter_map(|l| l.split_whitespace().find(|w| w.starts_with('^')))
        .map(str::to_string)
        .collect();
    assert!(ids.len() > 1, "{week}");

    // A re-sync is byte-identical: the ids are stable (§15).
    let again = tm.json_at("2026-09-07T09:05:00-05:00", &["sync-cal"]);
    assert_eq!(again["files"].as_array().map(Vec::len), Some(0), "{again}");
    assert_eq!(tm.read("calendar/2026-W37.md"), week);
    assert_eq!(tm.run(&["check"]).code, 0);
}

#[test]
fn model_show_fit_and_compare() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["arrive", "lounge"]);
    tm.ok(&["energy", "3", "--at", "10:30"]);

    let show = tm.json(&["model", "--show"]);
    assert_eq!(show["action"], "show");
    assert_eq!(show["model"]["n_obs"], 0);

    let fit = tm.json_at("2026-09-07T21:00:00-05:00", &["model", "--fit"]);
    assert_eq!(fit["action"], "fit");
    assert_eq!(fit["wrote"], ".tm/model.json");
    assert!(tm.exists(".tm/model.json"));
    assert_eq!(fit["model"]["fitted"], "2026-09-07");

    let cmp = tm.json_at("2026-09-07T21:01:00-05:00", &["model", "--compare"]);
    assert_eq!(cmp["action"], "compare");
    assert!(cmp["comparison"]["n"].as_u64().unwrap_or(0) >= 1);
    insta::assert_json_snapshot!("model_compare_schema", schema(&cmp["comparison"]));
}

#[test]
fn log_tail_since_and_item() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T10:00:00-05:00", &["done"]);

    let all = tm.json(&["log"]);
    assert_eq!(all["total"], 3);
    assert_eq!(all["entries"].as_array().map(Vec::len), Some(3));

    let tail = tm.json(&["log", "--tail", "1"]);
    assert_eq!(tail["entries"].as_array().map(Vec::len), Some(1));
    assert_eq!(tail["entries"][0]["ev"], "done");

    let item = tm.json(&["log", "--item", "^t4"]);
    assert_eq!(item["entries"].as_array().map(Vec::len), Some(2));

    let since = tm.json(&["log", "--since", "7d"]);
    assert_eq!(since["entries"].as_array().map(Vec::len), Some(3));

    let mut schema_json = tm.json(&["log", "--tail", "1"]);
    scrub(&mut schema_json, "t", "[t]");
    insta::assert_json_snapshot!("log_json", schema_json);
}

#[test]
fn check_passes_on_the_fixture_and_fails_on_a_duplicate_id() {
    let tm = Tm::new();
    let out = tm.run(&["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("no problems"));

    let json = tm.json(&["check"]);
    assert_eq!(json["exit_code"], 0);
    insta::assert_json_snapshot!("check_schema", schema(&json));

    // §13: exit 2 when the tree has errors.
    let path = tm.plan.join("week/2026-W37.md");
    let mut text = std::fs::read_to_string(&path).expect("read week");
    text.push_str("- [ ] 3 1b Duplicate ^t5\n");
    std::fs::write(&path, text).expect("write week");
    let out = tm.run(&["check"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("dup-id"), "{}", out.stdout);

    // The shape of a problem is the half of the contract §14's integration
    // consumes; the clean snapshot above only pins the empty arrays.
    let broken = tm.run(&["--json", "check"]);
    assert_eq!(broken.code, 2, "{}{}", broken.stdout, broken.stderr);
    let json: serde_json::Value =
        serde_json::from_str(&broken.stdout).expect("check --json is JSON");
    assert_eq!(json["exit_code"], 2);
    assert!(json["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .any(|p| p["code"] == "dup-id" && p["severity"] == "error"));
    insta::assert_json_snapshot!("check_problems_schema", schema(&json));
}

#[test]
fn check_fix_ids_appends_missing_ids() {
    let tm = Tm::new();
    let path = tm.plan.join("week/2026-W37.md");
    let mut text = std::fs::read_to_string(&path).expect("read week");
    text.push_str("- [ ] 3 1b No id here\n");
    std::fs::write(&path, text).expect("write week");

    let out = tm.run(&["check"]);
    assert_eq!(out.code, 0);
    assert!(out.stdout.contains("missing-id"), "{}", out.stdout);

    let json = tm.json(&["check", "--fix-ids"]);
    assert_eq!(json["fixed"].as_array().map(Vec::len), Some(1));
    assert_eq!(json["exit_code"], 0);
    let week = std::fs::read_to_string(&path).expect("read week");
    let line = week
        .lines()
        .find(|l| l.contains("No id here"))
        .expect("the line");
    assert!(line.contains(" ^"), "{line}");
}

#[test]
fn the_plan_directory_is_found_by_env_and_by_walking_up() {
    use std::process::Command;
    let tm = Tm::new();

    // $TM_DIR overrides the search.
    let out = Command::new(env!("CARGO_BIN_EXE_tm"))
        .env("TM_DIR", &tm.plan)
        .current_dir(tm.tmp.path())
        .args(["--now", cli_common::NOW, "check"])
        .output()
        .expect("run tm");
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));

    // Without it, the working directory's `plan/` child is found (§2).
    let out = Command::new(env!("CARGO_BIN_EXE_tm"))
        .env_remove("TM_DIR")
        .current_dir(tm.tmp.path())
        .args(["--now", cli_common::NOW, "check"])
        .output()
        .expect("run tm");
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));

    // And from inside it.
    let out = Command::new(env!("CARGO_BIN_EXE_tm"))
        .env_remove("TM_DIR")
        .current_dir(tm.plan.join("week"))
        .args(["--now", cli_common::NOW, "check"])
        .output()
        .expect("run tm");
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
}

#[test]
fn help_succeeds_and_a_usage_error_exits_with_one() {
    // §13's codes: a usage error is an ordinary error, not `check`'s 2.
    let tm = Tm::new();
    let help = tm.run(&["--help"]);
    assert_eq!(help.code, 0);
    assert!(help.stdout.contains("Usage: tm"), "{}", help.stdout);
    let bad = tm.run(&["nosuchverb"]);
    assert_eq!(bad.code, 1);
}

#[test]
fn tui_needs_a_terminal() {
    // §12's TUI is built (see `tm/src/tui/`), but this harness pipes stdout,
    // so `tm tui` refuses rather than putting a pipe into raw mode. The
    // screen itself is tested with `ratatui`'s `TestBackend` in
    // `tui_today_*.rs` (§17 M6).
    let tm = Tm::new();
    let out = tm.run(&["tui"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("needs a terminal"), "{}", out.stderr);
}

#[test]
fn init_produces_a_tree_that_passes_check() {
    // §17 M9's definition of done.
    let tm = Tm::empty();
    let out = tm.run(&["init"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    // §14: config, CLAUDE.md, skills, hooks, files.
    assert!(tm.exists("config.toml"));
    assert!(tm.exists("CLAUDE.md"));
    assert!(tm.exists(".claude/settings.json"));
    assert!(tm.exists(".githooks/pre-commit"));
    for skill in [
        "plan-week",
        "plan-month",
        "triage",
        "capture",
        "replan",
        "review-day",
        "review-week",
        "explain",
    ] {
        assert!(
            tm.exists(&format!(".claude/skills/{skill}/SKILL.md")),
            "missing skill {skill}"
        );
    }
    assert!(tm.exists("inbox.md"));
    assert!(tm.exists("backlog.md"));
    assert!(tm.exists("routines.md"));
    assert!(tm.exists("optional.md"));
    assert!(tm.exists("month/2026-09.md"));
    assert!(tm.exists("week/2026-W37.md"));

    // The hook runs `tm check` (§14) — through `.claude/hooks/tm-check.sh`,
    // which scopes it to this plan tree and reports on stderr — and the rules
    // are §14's, verbatim.
    assert!(tm.read(".claude/settings.json").contains("tm-check.sh"));
    assert!(tm.read(".claude/hooks/tm-check.sh").contains("tm check"));
    assert!(tm.read(".claude/settings.json").contains("PostToolUse"));
    assert!(tm.read(".githooks/pre-commit").contains("tm check"));
    assert!(tm.read("CLAUDE.md").starts_with("# tm — rules for Claude Code"));
    assert!(tm.read("CLAUDE.md").contains("Demote, never delete."));

    let check = tm.run(&["check"]);
    assert_eq!(check.code, 0, "{}{}", check.stdout, check.stderr);
    assert!(check.stdout.contains("no problems"));

    // And the day verbs work in it.
    assert_eq!(tm.run(&["wake", "07:00", "--slept", "8h"]).code, 0);
    assert_eq!(tm.run(&["arrive", "home"]).code, 0);
}

#[test]
fn init_example_writes_the_spec_tree_and_passes_check() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    assert!(tm.read("week/2026-W37.md").contains("^m1"));
    assert!(tm.read("routines.md").contains("- lunch"));
    assert_eq!(tm.run(&["check"]).code, 0);

    let mut json = tm.json(&["init", "--force"]);
    scrub(&mut json, "dir", "[dir]");
    scrub(&mut json, "hook_hint", "[hint]");
    insta::assert_json_snapshot!("init_json", json);
}
