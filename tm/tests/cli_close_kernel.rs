//! §6.3's close through the shipped binary, kernel-backed (stage 4 step 6).
//!
//! AGENTS §8.2's acceptance, CLI half: "close idempotent at library **and
//! CLI** level; a 3-month-stale tree catches up losing nothing". The library
//! half is `close_is_idempotent` (L16), `autoClose_catches_up_in_one_step`
//! (L19b) and `the_stale_tree_catches_up_losing_nothing` in the kernel; these
//! run the built `tm` against temp trees, through `kernel_bridge::apply`.
//!
//! The four `d1_*` tests are the owner's evidence for D1 (2026-09-12: "`close
//! day` targets the week containing *now*"), each asserting the **new**
//! behaviour where the fork-point Rust failed.

mod cli_common;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;

use cli_common::Tm;
use tm_core::grammar::{parse_line, ParseCtx};

/// `plan-basic`'s config: America/Chicago, a 60-minute block.
fn config() -> String {
    fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../tm-core/tests/fixtures/plan-basic/config.toml"),
    )
    .expect("fixture config")
}

/// A plan directory holding exactly `files`, and `state.closed` when given.
fn tree(files: &[(&str, &str)], closed: Option<(&str, &str, &str)>) -> Tm {
    let tm = Tm::empty();
    fs::create_dir_all(tm.plan.join(".tm")).expect("mkdir .tm");
    fs::write(tm.plan.join("config.toml"), config()).expect("config");
    for (rel, text) in files {
        let path = tm.plan.join(rel);
        fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
        fs::write(path, text).expect("write");
    }
    if let Some((day, week, month)) = closed {
        fs::write(
            tm.plan.join(".tm/state.json"),
            format!(r#"{{"closed":{{"day":"{day}","week":"{week}","month":"{month}"}}}}"#),
        )
        .expect("state");
    }
    tm
}

/// Every `*.md` file under the plan directory, path → text.
fn md_files(tm: &Tm) -> BTreeMap<String, String> {
    fn walk(dir: &std::path::Path, prefix: &str, out: &mut BTreeMap<String, String>) {
        let Ok(rd) = fs::read_dir(dir) else { return };
        for e in rd {
            let path = e.expect("entry").path();
            let name = path.file_name().expect("name").to_string_lossy().to_string();
            if name.starts_with('.') {
                continue;
            }
            let rel = format!("{prefix}{name}");
            if path.is_dir() {
                walk(&path, &format!("{rel}/"), out);
            } else if rel.ends_with(".md") {
                out.insert(rel, fs::read_to_string(&path).expect("read"));
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(&tm.plan, "", &mut out);
    out
}

/// One item line as the files hold it.
#[derive(Debug, Clone)]
struct Line {
    path: String,
    text: String,
    /// The box character: ` `, `>`, `x`, `-`, `~`, `?`.
    status: char,
    /// Minutes: `est:` if present, else the leading estimate.
    minutes: Option<u32>,
    stamps: Vec<String>,
}

/// Every item line with an id, grouped by id, in file order.
fn lines(files: &BTreeMap<String, String>) -> BTreeMap<String, Vec<Line>> {
    let mut out: BTreeMap<String, Vec<Line>> = BTreeMap::new();
    for (path, text) in files {
        for raw in text.lines() {
            let Some(id) = raw.split_whitespace().find_map(|w| w.strip_prefix('^')) else {
                continue;
            };
            if !raw.starts_with("- [") {
                continue;
            }
            let item = parse_line(raw, &ParseCtx::new(path, 60))
                .unwrap_or_else(|e| panic!("{path}: {raw}: {e}"));
            out.entry(id.to_string()).or_default().push(Line {
                path: path.clone(),
                text: raw.to_string(),
                status: raw.chars().nth(3).expect("box"),
                minutes: item.est.as_ref().or(item.est_original.as_ref()).map(|d| d.as_minutes()),
                stamps: item.stamps.demoted.iter().map(|s| s.to_string()).collect(),
            });
        }
    }
    out
}

/// The `ev`/`id` pairs of the log.
fn events(tm: &Tm) -> Vec<(String, String)> {
    tm.log()
        .iter()
        .map(|e| {
            (
                e["ev"].as_str().unwrap_or_default().to_string(),
                e["id"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect()
}

// ---------------------------------------------------------------------------
// (a) Closing twice is closing once, through the binary (L16 / L19b at the CLI)
// ---------------------------------------------------------------------------

/// The tree of the kernel's `the_week_close_reports_each_line`: an ended
/// week with an open line, a done line and a wall still ahead.
fn ended_week() -> Tm {
    tree(
        &[
            (
                "week/2026-W36.md",
                "# Tasks\n- [ ] 4 6b Rollback path passes tests ^m2\n- [x] 2 1b Send the draft ^t1\n- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1\n",
            ),
            ("week/2026-W37.md", "# Tasks\n"),
            ("month/2026-09.md", "# Outcomes\n# Demoted\n"),
        ],
        None,
    )
}

#[test]
fn closing_twice_changes_zero_bytes_the_second_time() {
    const AT: &str = "2026-09-07T09:00:00-05:00";
    let tm = ended_week();
    let first = tm.json_at(AT, &["close", "week"]);
    assert_eq!(first["key"], "2026-W36");
    let closes = first["report"]["closes"].as_array().expect("closes");
    let got: Vec<(&str, &str, &str, &str)> = closes
        .iter()
        .map(|c| {
            (
                c["id"].as_str().unwrap(),
                c["did"].as_str().unwrap(),
                c["to"].as_str().unwrap(),
                c["stamp"].as_str().unwrap_or("-"),
            )
        })
        .collect();
    assert_eq!(
        got,
        // Source order (kernel/README.md gap 59): `^m2` above `^x1` in W36.
        vec![
            ("m2", "copy", "month/2026-09.md", "W36"),
            ("x1", "carry", "week/2026-W37.md", "-"),
        ],
        "{first}"
    );
    assert_eq!(closes[0]["min"], serde_json::json!({"num": 360, "den": 1}));
    let after_first = md_files(&tm);
    assert_ne!(after_first["week/2026-W36.md"], "# Tasks\n- [ ] 4 6b Rollback path passes tests ^m2\n- [x] 2 1b Send the draft ^t1\n- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1\n");
    let events_first = events(&tm);

    // Second explicit close at the same instant: the kernel is called again,
    // finds nothing to take, and every plan byte stays where it was.
    let second = tm.json_at(AT, &["close", "week"]);
    assert_eq!(second["report"]["closes"], serde_json::json!([]), "{second}");
    assert_eq!(md_files(&tm), after_first, "the second close changed plan bytes");
    let new_events: Vec<_> = events(&tm)[events_first.len()..].to_vec();
    assert_eq!(
        new_events,
        // Q6(f) (gap 86) does **not** move these bytes: a close line's fields are
        // `period` and `key`, and its primary id is *derived* from them for the
        // header and the undo mask — it is never written into the line. This
        // reads the line's own `id` field, which a close has never had.
        vec![("close".to_string(), String::new())],
        "a close of nothing logs only its own close"
    );

    // And the automatic close with the host's `state.closed` gate removed:
    // one `autoClose` over the caught-up tree is the identity too.
    fs::remove_file(tm.plan.join(".tm/state.json")).ok();
    let out = tm.ok_at(AT, &["now"]);
    assert!(!out.stderr.contains("refused"), "{}", out.stderr);
    assert_eq!(md_files(&tm), after_first, "autoClose over a closed tree changed plan bytes");
}

// ---------------------------------------------------------------------------
// (b) A three-month-stale tree catches up losing nothing
// ---------------------------------------------------------------------------

/// The kernel's `staleWitness` (Boundary.lean) as files: both failure shapes
/// of the fork-point Rust in one tree. Closed through 2026-06-11 / 2026-W23 /
/// 2026-05, first command on Saturday 2026-09-12.
fn stale_tree() -> Tm {
    tree(
        &[
            ("day/2026-06-12.md", "# Pinned\n- [>] 2 20m Call the bank ^p1\n- [x] 1 10m Water the plants ^p2\n"),
            ("day/2026-08-29.md", "# Pinned\n- [>] 3 1h Draft the letter ^p3\n"),
            (
                "week/2026-W24.md",
                "# Tasks\n- [ ] 4 6b Rollback path passes tests ^m2\n- [x] 2 1b Send the draft ^t1\n- [ ] 1 15m Standup every:day ^r1\n",
            ),
            ("week/2026-W35.md", "# Tasks\n- [ ] 3 2b Read chapter four ^m3\n- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1\n"),
            ("week/2026-W37.md", "# Tasks\n- [ ] 3 1b Review the drafts ^t5\n"),
            (
                "month/2026-06.md",
                "# Outcomes\n- [ ] 5 !1 Old outcome ^O7\n- [x] 3 !2 Done outcome ^O8\n# Demoted\n- [-] 4 3b Carried record est:3b demoted:W22 ^m9\n",
            ),
            ("month/2026-09.md", "# Outcomes\n- [ ] 5 !1 Lean through ch.8 ^O1\n# Demoted\n"),
        ],
        Some(("2026-06-11", "2026-W23", "2026-05")),
    )
}

/// The fork-point Rust ran **zero** day closes on this tree: `catch_up`
/// looked only at the sixteen most recent days, none of which but 08-29 had
/// a file, so `^p1` stayed `[>]` in a sealed June day file under a clean
/// `tm check` — and `^p3`, filed into its own closed week W35, was demoted
/// again by the week sweep (`D29,W35`). One `autoClose` call now: every id
/// kept, every taken line in a file the planner reads, one stamp at most per
/// line, and the summed estimate unchanged.
#[test]
fn a_three_month_stale_tree_catches_up_losing_nothing() {
    let tm = stale_tree();
    let before = lines(&md_files(&tm));
    let out = tm.ok_at("2026-09-12T09:00:00-05:00", &["now"]);
    assert!(!out.stderr.contains("refused"), "{}", out.stderr);
    let files = md_files(&tm);
    let after = lines(&files);

    // Every id is still in the tree.
    assert_eq!(
        before.keys().collect::<BTreeSet<_>>(),
        after.keys().collect::<BTreeSet<_>>(),
        "an id was lost"
    );
    // One stamp at most on any line, exactly one on each taken line.
    for (id, ls) in &after {
        for l in ls {
            assert!(l.stamps.len() <= 1, "^{id} double-stamped: {}", l.text);
        }
    }
    let stamp_of = |id: &str, path: &str| -> Vec<String> {
        after[id]
            .iter()
            .find(|l| l.path == path)
            .unwrap_or_else(|| panic!("^{id} is not in {path}: {:?}", after[id]))
            .stamps
            .clone()
    };
    assert_eq!(stamp_of("p1", "week/2026-W37.md"), vec!["D12"]);
    assert_eq!(stamp_of("p3", "week/2026-W37.md"), vec!["D29"]);
    assert_eq!(stamp_of("m2", "month/2026-09.md"), vec!["W24"]);
    assert_eq!(stamp_of("m3", "month/2026-09.md"), vec!["W35"]);

    // Live in the right region: the reopened pinned items and the wall in
    // the week containing now, the records and the carried month lines in
    // the month containing now.
    let live_in = |id: &str| -> (String, char) {
        let l = after[id]
            .iter()
            .find(|l| l.status != '-' || l.path.starts_with("month/2026-09"))
            .unwrap_or_else(|| panic!("^{id}: {:?}", after[id]));
        (l.path.clone(), l.status)
    };
    assert_eq!(live_in("p1"), ("week/2026-W37.md".to_string(), ' '));
    assert_eq!(live_in("p3"), ("week/2026-W37.md".to_string(), ' '));
    assert_eq!(live_in("x1"), ("week/2026-W37.md".to_string(), ' '));
    assert_eq!(live_in("O7"), ("month/2026-09.md".to_string(), ' '));
    assert_eq!(live_in("m9"), ("month/2026-09.md".to_string(), '-'));
    for (id, week) in [("m2", "week/2026-W24.md"), ("m3", "week/2026-W35.md")] {
        let paths: Vec<(&str, char)> = after[id].iter().map(|l| (l.path.as_str(), l.status)).collect();
        assert_eq!(paths, vec![("month/2026-09.md", '-'), (week, '-')], "^{id}");
    }
    let demoted = files["month/2026-09.md"].split("# Demoted").nth(1).unwrap_or_default();
    for id in ["m2", "m3", "m9"] {
        assert!(demoted.contains(&format!("^{id}")), "^{id} not under # Demoted: {demoted}");
    }
    // What §6.3 leaves in the archives stays: settled and recurring lines.
    for (id, path) in [("p2", "day/2026-06-12.md"), ("t1", "week/2026-W24.md"), ("r1", "week/2026-W24.md"), ("O8", "month/2026-06.md")] {
        assert_eq!(after[id].len(), 1, "^{id}");
        assert_eq!(after[id][0].path, path, "^{id}");
    }

    // The summed estimate is unchanged: every line of an id carries the
    // minutes that id had, and the sum over ids is the same number.
    let total = |m: &BTreeMap<String, Vec<Line>>| -> u32 { m.values().map(|ls| ls[0].minutes.unwrap_or(0)).sum() };
    for (id, ls) in &after {
        for l in ls {
            assert_eq!(l.minutes, before[id][0].minutes, "^{id}'s estimate changed: {}", l.text);
        }
    }
    assert_eq!(total(&before), total(&after));
    // p1 20 + p2 10 + p3 60 + m2 360 + t1 60 + r1 15 + m3 120 + x1 120 +
    // t5 60 + m9 180 at a 60-minute block; the outcomes carry none.
    assert_eq!(total(&after), 1005);

    // The host's gate is stamped through the last ended period of each
    // grain, and the log names each taken line once.
    let state = tm.state();
    assert_eq!(state["closed"]["day"], "2026-09-11");
    assert_eq!(state["closed"]["week"], "2026-W36");
    assert_eq!(state["closed"]["month"], "2026-08");
    let demotes: Vec<String> = events(&tm).into_iter().filter(|(e, _)| e == "demote").map(|(_, i)| i).collect();
    // Source order (gap 59): the June day before the August day, W24 before W35.
    assert_eq!(demotes, vec!["p1", "p3", "m2", "m3"]);

    // And the next command at a later hour changes nothing (L19b, and the gate).
    tm.ok_at("2026-09-12T17:00:00-05:00", &["now"]);
    assert_eq!(md_files(&tm), files);
}

// ---------------------------------------------------------------------------
// (c) The fourteen-day case does not double-stamp
// ---------------------------------------------------------------------------

/// A pinned `[>]` of Saturday 2026-08-29 (in W35), first command fourteen
/// days later. The fork-point close filed it into W35 — the closed day's own
/// week — and the week sweep then demoted it: `demoted:D29,W35` on the month
/// review's cut list, off the plan. D1: it lands once, in the week of now.
#[test]
fn a_fourteen_day_late_close_stamps_once() {
    let tm = tree(
        &[
            ("day/2026-08-29.md", "# Pinned\n- [>] 3 1h Draft the letter ^p3\n"),
            ("week/2026-W35.md", "# Tasks\n- [ ] 3 2b Read chapter four ^m3\n"),
            ("week/2026-W37.md", "# Tasks\n"),
            ("month/2026-09.md", "# Outcomes\n# Demoted\n"),
        ],
        Some(("2026-08-28", "2026-W34", "2026-07")),
    );
    tm.ok_at("2026-09-12T09:00:00-05:00", &["now"]);
    let after = lines(&md_files(&tm));
    assert_eq!(after["p3"].len(), 1, "{:?}", after["p3"]);
    assert_eq!(after["p3"][0].path, "week/2026-W37.md");
    assert_eq!(after["p3"][0].text, "- [ ] 3 1h Draft the letter demoted:D29 ^p3");
    assert_eq!(after["p3"][0].stamps, vec!["D29"]);
    // The week close still ran — on W35's own line — and did not re-take it.
    assert_eq!(after["m3"].iter().map(|l| l.path.as_str()).collect::<Vec<_>>(), vec!["month/2026-09.md", "week/2026-W35.md"]);
    let p3_demotes = events(&tm).iter().filter(|(e, i)| e == "demote" && i == "p3").count();
    assert_eq!(p3_demotes, 1);
}

// ---------------------------------------------------------------------------
// (d) The owner's four scenarios (D1, 2026-09-12)
// ---------------------------------------------------------------------------

/// D1, scenario 1 — a day closed late within its own week. Tuesday's pinned
/// item, first command Thursday: the week containing now *is* the day's
/// week, so the old and new rules agree on the file; the item lands there
/// once, reopened and stamped `D08`.
#[test]
fn d1_a_day_closed_late_within_its_week_files_into_the_week_of_now() {
    let tm = tree(
        &[
            ("day/2026-09-08.md", "# Pinned\n- [>] 2 20m Call the bank ^p1\n"),
            ("week/2026-W37.md", "# Tasks\n- [ ] 3 1b Review the drafts ^t5\n"),
            ("month/2026-09.md", "# Outcomes\n# Demoted\n"),
        ],
        Some(("2026-09-07", "2026-W36", "2026-08")),
    );
    tm.ok_at("2026-09-10T09:00:00-05:00", &["now"]);
    let after = lines(&md_files(&tm));
    assert_eq!(after["p1"].len(), 1);
    assert_eq!(after["p1"][0].path, "week/2026-W37.md");
    assert_eq!(after["p1"][0].text, "- [ ] 2 20m Call the bank demoted:D08 ^p1");
    assert_eq!(after["t5"][0].text, "- [ ] 3 1b Review the drafts ^t5", "the live week is not closed");
    assert_eq!(tm.state()["closed"]["day"], "2026-09-09");
}

/// D1, scenario 2 — a Friday closed on Monday. The fork-point close filed
/// Friday's pinned item into Friday's week (W37), which the same sweep then
/// closed: the item was double-stamped `D11,W37` onto the month review's cut
/// list and dropped off Monday's plan. D1: it lands in **W38**, the week
/// containing now — a file the host creates for it — stamped once, and the
/// W37 close does not see it.
#[test]
fn d1_a_friday_closed_on_monday_lands_in_mondays_week_stamped_once() {
    let tm = tree(
        &[
            ("day/2026-09-11.md", "# Pinned\n- [ ] 2 20m Call the bank ^p1\n"),
            ("week/2026-W37.md", "# Tasks\n- [ ] 3 1b Review the drafts ^t5\n"),
            ("month/2026-09.md", "# Outcomes\n# Demoted\n"),
        ],
        Some(("2026-09-10", "2026-W36", "2026-08")),
    );
    assert!(!tm.exists("week/2026-W38.md"));
    tm.ok_at("2026-09-14T09:00:00-05:00", &["now"]);
    let files = md_files(&tm);
    let after = lines(&files);
    assert_eq!(after["p1"].len(), 1, "{:?}", after["p1"]);
    assert_eq!(after["p1"][0].path, "week/2026-W38.md");
    assert_eq!(after["p1"][0].stamps, vec!["D11"]);
    assert!(!files["month/2026-09.md"].contains("^p1"), "p1 was demoted into the month");
    // W37 itself was closed: its open line has its record in the month.
    assert_eq!(after["t5"].iter().map(|l| (l.path.as_str(), l.stamps.clone())).collect::<Vec<_>>(),
        vec![("month/2026-09.md", vec!["W37".to_string()]), ("week/2026-W37.md", vec![])]);
    assert_eq!(tm.state()["closed"]["week"], "2026-W37");
}

/// D1, scenario 3 — an item whose parent is in the closing week. The
/// fork-point close moved Friday's pinned child into W37 beside its parent,
/// and the W37 close then treated it as a child of a demoted milestone:
/// **deleted**, its minutes silently absorbed. D1: the child lands in the
/// week of now with its own estimate, and the parent is demoted — both ids
/// are in the tree, no minute gone. (The kernel folds no children at all
/// yet — gap 22 — so a child still in the closing week is demoted as its own
/// record rather than dropped.)
#[test]
fn d1_an_item_whose_parent_is_in_the_closing_week_is_kept_not_deleted() {
    let tm = tree(
        &[
            ("day/2026-09-11.md", "# Pinned\n- [ ] 3 1b Draft the intro @m1 ^s1\n"),
            ("week/2026-W37.md", "# Milestones\n- [ ] 5 6b Finish the paper ^m1\n"),
            ("month/2026-09.md", "# Outcomes\n# Demoted\n"),
        ],
        Some(("2026-09-10", "2026-W36", "2026-08")),
    );
    let before = lines(&md_files(&tm));
    tm.ok_at("2026-09-14T09:00:00-05:00", &["now"]);
    let after = lines(&md_files(&tm));
    assert_eq!(after["s1"].len(), 1, "{:?}", after["s1"]);
    assert_eq!(after["s1"][0].path, "week/2026-W38.md");
    assert_eq!(after["s1"][0].status, ' ');
    assert_eq!(after["s1"][0].minutes, Some(60), "the child's estimate is its own, not absorbed");
    assert_eq!(after["s1"][0].stamps, vec!["D11"]);
    let m1: Vec<(&str, char)> = after["m1"].iter().map(|l| (l.path.as_str(), l.status)).collect();
    assert_eq!(m1, vec![("month/2026-09.md", '-'), ("week/2026-W37.md", '-')]);
    assert_eq!(after["m1"][0].minutes, before["m1"][0].minutes, "the parent absorbed nothing");
}

/// D1, scenario 4 — a day closed more than sixteen days late. The fork-point
/// catch-up looked at the sixteen most recent days only, stamped the rest
/// closed without running them, and the pinned item stayed in a sealed day
/// file nothing plans from, under a clean `tm check`. One `autoClose` has no
/// window: the item lands in the week of now.
#[test]
fn d1_a_day_closed_more_than_sixteen_days_late_is_not_stranded() {
    let tm = tree(
        &[
            ("day/2026-08-20.md", "# Pinned\n- [>] 2 20m Call the bank ^p1\n"),
            ("week/2026-W37.md", "# Tasks\n"),
            ("month/2026-09.md", "# Outcomes\n# Demoted\n"),
        ],
        Some(("2026-08-19", "2026-W33", "2026-07")),
    );
    tm.ok_at("2026-09-12T09:00:00-05:00", &["now"]);
    let files = md_files(&tm);
    let after = lines(&files);
    assert!(!files["day/2026-08-20.md"].contains("^p1"), "stranded in the day file");
    assert_eq!(after["p1"].len(), 1);
    assert_eq!(after["p1"][0].path, "week/2026-W37.md");
    assert_eq!(after["p1"][0].text, "- [ ] 2 20m Call the bank demoted:D20 ^p1");
    assert_eq!(tm.state()["closed"]["day"], "2026-09-11");
}

/// The upgrade path. A tree the fork-point binary last touched: its
/// catch-up stamped every period closed (row 2 of kernel/README.md stage 4
/// step 6's table, "older periods stamped closed unrun"), so `state.closed`
/// is **current** while `^p1` sits in a sealed day file. Stamps alone would
/// gate the automatic close off and leave it stranded under a clean `tm
/// check`; a `state.closed` no kernel sweep has vouched for (no `swept`) is
/// swept once, and then — the other direction — the gate holds again: the
/// next command does not call the kernel at all.
#[test]
fn an_upgraded_tree_whose_stamps_are_current_is_swept_once() {
    const AT: &str = "2026-09-12T09:00:00-05:00";
    let tm = tree(
        &[
            ("day/2026-08-20.md", "# Pinned\n- [>] 2 20m Call the bank ^p1\n"),
            ("week/2026-W37.md", "# Tasks\n- [ ] 3 1b Review ^t5\n"),
            ("month/2026-09.md", "# Outcomes\n# Demoted\n"),
        ],
        // Exactly what the fork-point binary wrote at its last command.
        Some(("2026-09-11", "2026-W36", "2026-08")),
    );
    tm.ok_at(AT, &["now"]);
    let files = md_files(&tm);
    let after = lines(&files);
    assert!(!files["day/2026-08-20.md"].contains("^p1"), "stranded in the day file");
    assert_eq!(after["p1"].len(), 1);
    assert_eq!(after["p1"][0].path, "week/2026-W37.md");
    assert_eq!(after["p1"][0].text, "- [ ] 2 20m Call the bank demoted:D20 ^p1");
    let state = tm.state();
    assert_eq!(state["closed"]["day"], "2026-09-11");
    assert_eq!(state["closed"]["swept"], true, "{state}");
    let evs = events(&tm);
    assert!(evs.contains(&("demote".to_string(), "p1".to_string())), "{evs:?}");
    assert!(tm.log().iter().any(|e| e["ev"] == "close" && e["period"] == "day"), "{:?}", tm.log());

    // Swept and current: the gate holds, so a kernel fault probe set for the
    // next housekeeping verb is never reached and the verb succeeds. The verb
    // is `triage`, which runs housekeeping and calls the kernel for nothing
    // else: since stage 5 D10 L8 `now` asks the kernel for today's priorities.
    let before = md_files(&tm);
    let out = tm.run_env_at(AT, &[("TM_KERNEL_FAULT_PROBE", "1")], &["triage"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(md_files(&tm), before);

    // A writer that does not know `swept` (the fork-point binary) drops it,
    // and the next command sweeps again — here, over nothing.
    fs::write(
        tm.plan.join(".tm/state.json"),
        r#"{"closed":{"day":"2026-09-11","week":"2026-W36","month":"2026-08"}}"#,
    )
    .expect("state");
    let out = tm.run_env_at(AT, &[("TM_KERNEL_FAULT_PROBE", "1")], &["triage"]);
    assert_eq!(out.code, 1, "an unswept tree must call the kernel: {}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("kernel fault"), "{}", out.stderr);
    tm.ok_at(AT, &["now"]);
    assert_eq!(md_files(&tm), before, "a sweep of a swept tree changed plan bytes");
    assert_eq!(tm.state()["closed"]["swept"], true);
}

// ---------------------------------------------------------------------------
// Both directions: the close bites, by name, and writes nothing
// ---------------------------------------------------------------------------

/// A refused close is named and writes nothing — on a month close whose
/// leftover outcome stands under a heading the current month file does not
/// have (`noSection`: the host hands over only `# Outcomes` and `# Demoted`,
/// kernel/README.md gap 56). This test pinned §4.3's own example tree, whose
/// open dated `^d1` refused the week close `badHorizon` (gap 55), until the
/// owner's D7 and D8 (2026-09-13) routed dated work — past due to
/// `backlog.md # Overdue`, not yet due into `# Demoted` with its date — and
/// that tree closes now
/// (`the_literal_example_tree_closes_on_its_first_command_a_week_after_its_week`).
/// The explicit verb exits 1 with the refusal's name and writes nothing; the
/// automatic close ahead of an unrelated verb prints the same name and lets
/// the verb run, stamping nothing closed so it is tried again.
#[test]
fn a_refused_close_is_named_and_writes_nothing() {
    const AT: &str = "2026-09-14T09:00:00-05:00";
    let tm = tree(
        &[
            (
                "month/2026-08.md",
                "---\nmonth: 2026-08\n---\n# Goals\n- [ ] 5 !1 Old outcome ^O7\n# Demoted\n",
            ),
            ("month/2026-09.md", "---\nmonth: 2026-09\n---\n# Outcomes\n# Demoted\n"),
            ("week/2026-W38.md", "# Tasks\n"),
        ],
        Some(("2026-09-13", "2026-W37", "2026-07")),
    );
    let before = md_files(&tm);

    let out = tm.run_at(AT, &["close", "month"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("noSection"), "{}", out.stderr);
    assert!(out.stderr.contains("gap 56"), "{}", out.stderr);
    assert_eq!(md_files(&tm), before);
    assert!(!tm.events().iter().any(|e| e == "close" || e == "move"), "{:?}", tm.events());

    let json = tm.run_at(AT, &["--json", "close", "month"]);
    assert_eq!(json.code, 1);
    let doc: serde_json::Value = serde_json::from_str(json.stderr.trim()).expect("error document");
    assert_eq!(doc["detail"]["refusal"], "noSection", "{doc}");

    let out = tm.run_at(AT, &["now"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("automatic close"), "{}", out.stderr);
    assert!(out.stderr.contains("noSection"), "{}", out.stderr);
    assert_eq!(md_files(&tm), before);
    assert_eq!(tm.state()["closed"]["month"], "2026-07", "{}", tm.state());
}

/// kernel/README.md gap 55, closed, through the binary — the owner's
/// acceptance, on the **literal** tree: `tm init --example` run a week after
/// §4.3's week, then `tm now`, both at Monday 2026-09-14 09:00. Until D7 and
/// D8 every command printed the automatic close's `badHorizon` refusal and
/// wrote nothing, because `^d1 due:2026-09-11T23:59` was filed into
/// `# Demoted` like any open line and its record broke the month rule. Now
/// the close runs on the first command and prints no refusal: `^d1` is past
/// due with `persist` (§5.3's default for a point), so it is **moved** to the
/// end of `backlog.md`'s `# Overdue` — which the host appends, the file had
/// none (gap 56's overdue half) — as `[ ]`, every byte kept, no stamp, and no
/// `[-]` left in the week; `^m2` merges into its standing record, one line in
/// September; `tm check` is clean; and a second `tm now` does not call the
/// kernel (a fault probe set for it is never reached).
#[test]
fn the_literal_example_tree_closes_on_its_first_command_a_week_after_its_week() {
    const AT: &str = "2026-09-14T09:00:00-05:00";
    const D1: &str = "- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1";
    let tm = Tm::empty();
    let init = tm.run_at(AT, &["init", "--example"]);
    assert_eq!(init.code, 0, "{}{}", init.stdout, init.stderr);
    let backlog_before = tm.read("backlog.md");
    assert!(!backlog_before.contains("# Overdue"), "{backlog_before}");
    assert!(tm.read("week/2026-W37.md").contains(D1));

    let out = tm.run_at(AT, &["now"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("refused"), "{}", out.stderr);
    assert!(!out.stderr.contains("badHorizon"), "{}", out.stderr);

    let files = md_files(&tm);
    let after = lines(&files);
    let d1: Vec<(&str, &str, char)> =
        after["d1"].iter().map(|l| (l.path.as_str(), l.text.as_str(), l.status)).collect();
    assert_eq!(d1, vec![("backlog.md", D1, ' ')], "{d1:?}");
    assert!(after["d1"][0].stamps.is_empty());
    // The backlog is the template's bytes with `# Overdue` and `^d1` appended —
    // and one change that is not the close's: `^a4`'s `waiting:2026-09-05` has
    // lapsed (`on-event:reply/7d`), which §5.1's waiting timeout, run by the
    // same housekeeping, reopens.
    let a4_waiting = "- [?] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4";
    let a4_lapsed = "- [ ] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d ^a4";
    assert!(backlog_before.contains(a4_waiting), "{backlog_before}");
    assert_eq!(
        files["backlog.md"],
        format!("{}# Overdue\n{D1}\n", backlog_before.replace(a4_waiting, a4_lapsed))
    );
    assert!(!files["week/2026-W37.md"].contains("^d1"), "{}", files["week/2026-W37.md"]);

    let m2: Vec<(&str, &str)> = after["m2"].iter().map(|l| (l.path.as_str(), l.text.as_str())).collect();
    assert_eq!(
        m2,
        vec![
            ("month/2026-09.md", "- [-] 4 6b Rollback path passes tests   @O2 demoted:W37 ^m2"),
            ("week/2026-W37.md", "- [-] 4 6b Rollback path passes tests   @O2 ^m2"),
        ]
    );
    assert_eq!(files["month/2026-09.md"].matches("^m2").count(), 1, "{}", files["month/2026-09.md"]);

    let moves: Vec<serde_json::Value> =
        tm.log().into_iter().filter(|e| e["ev"] == "move" && e["id"] == "d1").collect();
    assert_eq!(moves.len(), 1, "{moves:?}");
    assert_eq!(moves[0]["from"], "week/2026-W37.md");
    assert_eq!(moves[0]["to"], "backlog.md");
    assert!(!events(&tm).iter().any(|(ev, id)| ev == "demote" && id == "d1"), "{:?}", events(&tm));
    let state = tm.state();
    assert_eq!(state["closed"]["week"], "2026-W37", "{state}");
    assert_eq!(state["closed"]["swept"], true, "{state}");
    tm.ok_at(AT, &["check"]);

    // Closed and swept: the next command's housekeeping skips the kernel
    // (`triage`: since stage 5 D10 L8 `now` asks the kernel for priorities).
    let out = tm.run_env_at(AT, &[("TM_KERNEL_FAULT_PROBE", "1")], &["triage"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("kernel fault"), "{}", out.stderr);
    assert_eq!(md_files(&tm), files);
}

/// The owner's D8, through the binary, with D7 beside it for contrast: a week
/// close demotes a **not-yet-due** dated task like any unfinished one — `[-]`
/// left in the week file in its own bytes, a record in September's
/// `# Demoted` stamped `W37` that **keeps its `due:`** (a `# Demoted` record
/// is a work item, and the month rule "an outcome carries no date" reads
/// outcomes only) — while the past-due one beside it moves to
/// `backlog.md # Overdue`. The report names the two dispositions, `copy` and
/// `moveOverdue`, and `tm check` accepts the dated record.
#[test]
fn a_not_yet_due_dated_task_is_demoted_keeping_its_date() {
    const AT: &str = "2026-09-14T09:00:00-05:00";
    let tm = tree(
        &[
            (
                "week/2026-W37.md",
                "# Tasks\n- [ ] 3 1b Essay draft due:2026-09-20 ^e1\n- [ ] 2 1b Pset due:2026-09-10 ^e2\n",
            ),
            (
                "month/2026-09.md",
                "---\nmonth: 2026-09\n---\n# Outcomes\n- [ ] 5 !1 Lean through ch.8 ^O1\n# Demoted\n",
            ),
            ("backlog.md", "# Untied\n- [ ] 2 30m Insurance claim ^a1\n"),
        ],
        None,
    );
    let json = tm.json_at(AT, &["close", "week"]);
    let closes = json["report"]["closes"].as_array().expect("closes");
    let did: Vec<(&str, &str, &str)> = closes
        .iter()
        .map(|c| (c["id"].as_str().unwrap(), c["did"].as_str().unwrap(), c["to"].as_str().unwrap()))
        .collect();
    assert_eq!(
        did,
        vec![("e1", "copy", "month/2026-09.md"), ("e2", "moveOverdue", "backlog.md")],
        "{json}"
    );
    assert_eq!(closes[0]["stamp"], "W37");
    assert!(closes[1]["stamp"].is_null(), "{json}");

    assert_eq!(
        tm.read("month/2026-09.md"),
        "---\nmonth: 2026-09\n---\n# Outcomes\n- [ ] 5 !1 Lean through ch.8 ^O1\n# Demoted\n\
         - [-] 3 1b Essay draft due:2026-09-20 demoted:W37 ^e1\n"
    );
    assert_eq!(tm.read("week/2026-W37.md"), "# Tasks\n- [-] 3 1b Essay draft due:2026-09-20 ^e1\n");
    assert_eq!(
        tm.read("backlog.md"),
        "# Untied\n- [ ] 2 30m Insurance claim ^a1\n# Overdue\n- [ ] 2 1b Pset due:2026-09-10 ^e2\n"
    );
    tm.ok_at(AT, &["check"]);
}

/// Goal B3's repair, through the binary (kernel/README.md "Stage 4 final,
/// step 4"): §6.3's week row "Unfinished children are dropped from the week
/// file (their remaining is folded into the parent's `est:`)", by §6.4's
/// `max`. `^m1` (`2b`, 120 minutes at the 60-minute block) has `2b + 1b` of
/// tasks dropped with it, so its record carries `est:3b`; `^m2` (`6b`) covers
/// its `1b` task, so its record is the line with only the stamp set. The three
/// tasks stay in the week file as `[~]` — fork-point `close_week` deleted them;
/// the kernel removes no line — and log nothing; the report names each
/// (`copyFolding`, `dropIntoParent`); `tm check` is clean; and a second close
/// writes nothing (L16 at the CLI).
#[test]
fn a_week_close_folds_dropped_tasks_into_their_milestone_by_max() {
    const AT: &str = "2026-09-14T09:00:00-05:00";
    let tm = tree(
        &[
            (
                "week/2026-W37.md",
                "# Milestones\n- [ ] 5 2b Stale milestone @O1 ^m1\n- [ ] 4 6b Covered milestone @O1 ^m2\n\
                 # Tasks\n- [ ] 3 2b Part one @m1 ^t1\n- [ ] 3 1b Part two @m1 ^t2\n- [ ] 3 1b Covered part @m2 ^t3\n",
            ),
            (
                "month/2026-09.md",
                "---\nmonth: 2026-09\n---\n# Outcomes\n- [ ] 5 !1 Lean through ch.8 ^O1\n# Demoted\n",
            ),
        ],
        None,
    );
    let json = tm.json_at(AT, &["close", "week"]);
    let closes = json["report"]["closes"].as_array().expect("closes");
    let did: Vec<(&str, &str, &str, serde_json::Value, serde_json::Value)> = closes
        .iter()
        .map(|c| {
            (
                c["id"].as_str().unwrap(),
                c["did"].as_str().unwrap(),
                c["to"].as_str().unwrap(),
                c["stamp"].clone(),
                c["min"]["num"].clone(),
            )
        })
        .collect();
    assert_eq!(
        did,
        vec![
            ("m1", "copyFolding", "month/2026-09.md", "W37".into(), 180.into()),
            ("m2", "copyFolding", "month/2026-09.md", "W37".into(), 360.into()),
            ("t1", "dropIntoParent", "week/2026-W37.md", serde_json::Value::Null, 120.into()),
            ("t2", "dropIntoParent", "week/2026-W37.md", serde_json::Value::Null, 60.into()),
            ("t3", "dropIntoParent", "week/2026-W37.md", serde_json::Value::Null, 60.into()),
        ],
        "{json}"
    );
    let month = "---\nmonth: 2026-09\n---\n# Outcomes\n- [ ] 5 !1 Lean through ch.8 ^O1\n# Demoted\n\
                 - [-] 5 2b Stale milestone @O1 est:3b demoted:W37 ^m1\n\
                 - [-] 4 6b Covered milestone @O1 demoted:W37 ^m2\n";
    let week = "# Milestones\n- [-] 5 2b Stale milestone @O1 ^m1\n- [-] 4 6b Covered milestone @O1 ^m2\n\
                # Tasks\n- [~] 3 2b Part one @m1 ^t1\n- [~] 3 1b Part two @m1 ^t2\n- [~] 3 1b Covered part @m2 ^t3\n";
    assert_eq!(tm.read("month/2026-09.md"), month);
    assert_eq!(tm.read("week/2026-W37.md"), week);
    let ev = events(&tm);
    assert!(ev.contains(&("demote".to_string(), "m1".to_string())), "{ev:?}");
    assert!(ev.contains(&("demote".to_string(), "m2".to_string())), "{ev:?}");
    for t in ["t1", "t2", "t3"] {
        assert!(!ev.iter().any(|(_, id)| id == t), "{t} logged: {ev:?}");
    }
    tm.ok_at(AT, &["check"]);

    // L16 through the binary: the same close again writes nothing.
    let before = md_files(&tm);
    let again = tm.json_at(AT, &["close", "week"]);
    assert_eq!(md_files(&tm), before, "{again}");
}

/// **An `NhMm` child is folded at its minutes** — kernel/README.md "Stage 4
/// final, repair", defect 3. The kernel's stage-one estimate reader did not
/// read `2h30m`, so a `6b` milestone with `5h` and `2h30m` of subtasks dropped
/// into it kept a record of 360 minutes — the 150 minutes of the second task
/// silently gone, while the report said 150 for the task itself and `tm check`
/// was clean. Now the record carries §6.4's `max`: 300 + 150 = 450 minutes,
/// written `est:450m` (the fold writes whole blocks, else hours, else minutes).
/// The control `90m` in the same slot was always read.
#[test]
fn a_week_close_folds_an_hours_and_minutes_child_at_its_minutes() {
    const AT: &str = "2026-09-14T09:00:00-05:00";
    for (child, est) in [("2h30m", "est:450m"), ("90m", "est:390m")] {
        let tm = tree(
            &[
                (
                    "week/2026-W37.md",
                    &format!(
                        "# Milestones\n- [ ] 3 6b Parent project @O1 ^pp\n\
                         # Tasks\n- [ ] 3 5h Child one @pp ^c8\n- [ ] 3 {child} Child two @pp ^c9\n"
                    ),
                ),
                (
                    "month/2026-09.md",
                    "---\nmonth: 2026-09\n---\n# Outcomes\n- [ ] 5 !1 Lean through ch.8 ^O1\n# Demoted\n",
                ),
            ],
            None,
        );
        let json = tm.json_at(AT, &["close", "week"]);
        let closes = json["report"]["closes"].as_array().expect("closes");
        let c9 = closes.iter().find(|c| c["id"] == "c9").expect("c9 in the report");
        assert_eq!(c9["did"], "dropIntoParent", "{json}");
        let pp = closes.iter().find(|c| c["id"] == "pp").expect("pp in the report");
        let want: u64 = est.trim_start_matches("est:").trim_end_matches('m').parse().expect("minutes");
        assert_eq!(pp["min"]["num"], want, "{child}: {json}");
        assert!(
            tm.read("month/2026-09.md")
                .contains(&format!("- [-] 3 6b Parent project @O1 {est} demoted:W37 ^pp")),
            "{child}: {}",
            tm.read("month/2026-09.md")
        );
        assert!(tm.line("week/2026-W37.md", "c9").starts_with("- [~]"), "{child}");
        tm.ok_at(AT, &["check"]);
    }
}

/// The owner's D8 reaches the `demote` verb too: `tm demote ^d1` on §4.3's
/// dated line files a `[-]` record into September's `# Demoted` that keeps
/// `due:2026-09-11T23:59`, and `tm check` accepts it. Until D8 the verb's
/// post-state failed the month rule "an outcome carries no date" and was
/// refused `badHorizon` with nothing written — the same rule that refused the
/// week close (kernel/README.md gap 55).
#[test]
fn the_demote_verb_files_a_dated_line_keeping_its_date() {
    const AT: &str = "2026-09-08T09:00:00-05:00";
    let tm = Tm::empty();
    let init = tm.run_at(AT, &["init", "--example"]);
    assert_eq!(init.code, 0, "{}{}", init.stdout, init.stderr);
    tm.ok_at(AT, &["demote", "^d1"]);
    let after = lines(&md_files(&tm));
    let d1: Vec<(&str, &str)> = after["d1"].iter().map(|l| (l.path.as_str(), l.text.as_str())).collect();
    assert_eq!(
        d1,
        vec![
            ("month/2026-09.md", "- [-] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d demoted:W37 ^d1"),
            ("week/2026-W37.md", "- [-] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1"),
        ]
    );
    tm.ok_at(AT, &["check"]);
}

/// kernel/README.md gap 53, closed, through the binary: §4.3's own example
/// week, a week after `tm init --example`, closes. `^m2` is §4.3's pre-close
/// pair — the `[ ]` milestone beside its `[-]` record in September's
/// `# Demoted` — and the week close used to refuse it (`alreadyDemoted`) and
/// retry on every command. It now merges, as fork-point `demote_one` did: the
/// week line stays behind as `[-]` in its own bytes, and September keeps
/// **one** `^m2` record, `[-]`, stamped `W37` once (the record already said
/// `W37`; the merge writes each stamp once), with the live line's own `6b` —
/// the line owns an estimate, so the record's `est:3b` is not a floor over it
/// (`ownsEstimate`, L15's user exception). `^d1` is finished before its week
/// ends, so this test is about the merge alone (an open `^d1` was gap 55's
/// refusal until the owner's D7; it now moves to `backlog.md # Overdue` —
/// `the_literal_example_tree_closes_on_its_first_command_a_week_after_its_week`).
/// The automatic close runs once and prints no refusal, `tm check` is
/// clean, and the next command does not call the kernel (the swept gate: a
/// fault probe set for it is never reached).
#[test]
fn the_example_week_closes_a_week_after_init_merging_m2_into_its_record() {
    const AT: &str = "2026-09-14T09:00:00-05:00";
    let tm = Tm::empty();
    let init = tm.run_at("2026-09-07T09:00:00-05:00", &["init", "--example"]);
    assert_eq!(init.code, 0, "{}{}", init.stdout, init.stderr);
    tm.ok_at("2026-09-11T10:00:00-05:00", &["done", "^d1"]);
    let before = lines(&md_files(&tm));
    assert_eq!(before["m2"].len(), 2, "{:?}", before["m2"]);

    let out = tm.ok_at(AT, &["now"]);
    assert!(!out.stderr.contains("refused"), "{}", out.stderr);
    let files = md_files(&tm);
    let after = lines(&files);
    let m2: Vec<(&str, &str)> = after["m2"].iter().map(|l| (l.path.as_str(), l.text.as_str())).collect();
    assert_eq!(
        m2,
        vec![
            ("month/2026-09.md", "- [-] 4 6b Rollback path passes tests   @O2 demoted:W37 ^m2"),
            ("week/2026-W37.md", "- [-] 4 6b Rollback path passes tests   @O2 ^m2"),
        ]
    );
    assert_eq!(files["month/2026-09.md"].matches("^m2").count(), 1, "{}", files["month/2026-09.md"]);
    assert_eq!(after["m2"][0].stamps, vec!["W37".to_string()]);
    assert_eq!(
        events(&tm).iter().filter(|(ev, id)| ev == "demote" && id == "m2").count(),
        1,
        "{:?}",
        events(&tm)
    );
    let state = tm.state();
    assert_eq!(state["closed"]["week"], "2026-W37", "{state}");
    assert_eq!(state["closed"]["swept"], true, "{state}");
    tm.ok_at(AT, &["check"]);

    // Closed and swept: the next command's housekeeping skips the kernel
    // (`triage`: since stage 5 D10 L8 `now` asks the kernel for priorities).
    let out = tm.run_env_at(AT, &[("TM_KERNEL_FAULT_PROBE", "1")], &["triage"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("kernel fault"), "{}", out.stderr);
    assert_eq!(md_files(&tm), files);
}

/// The stage-4 hardening repair, through the binary: an open line whose
/// item's other line is a `[-]` left in an earlier, already-closed week — not a
/// `# Demoted` record — is not merged. Fork-point `archived_record` reads a
/// record only off a month file's `# Demoted`; the kernel at `0662977` merged
/// into the week line anyway and deleted it from `week/2026-W37.md` without a
/// word. The shape is a hand edit (`readopt` removes both lines) that
/// `tm check` accepts. Now the automatic close and `tm demote` both refuse
/// `alreadyDemoted`, by name, and write nothing.
#[test]
fn a_stray_week_tombstone_is_refused_by_the_close_and_the_verb_and_nothing_is_written() {
    let files: &[(&str, &str)] = &[
        ("week/2026-W37.md", "# Milestones\n- [-] 2 Pick winter courses @O3 demoted:W36 ^m4\n"),
        ("week/2026-W38.md", "# Milestones\n- [ ] 2 Pick winter courses @O3 ^m4\n"),
        ("month/2026-09.md", "# Outcomes\n- [ ] 2 !3 Winter course selection ^O3\n\n# Demoted\n"),
    ];

    // The verb, inside 2026-W38.
    let verb = tree(files, Some(("2026-09-15", "2026-W37", "2026-08")));
    verb.ok_at("2026-09-16T09:00:00-05:00", &["check"]);
    let before = md_files(&verb);
    let out = verb.run_at("2026-09-16T09:00:00-05:00", &["demote", "^m4"]);
    assert_ne!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("alreadyDemoted"), "{}", out.stderr);
    assert_eq!(md_files(&verb), before);

    // The automatic close, a week later: 2026-W38 has ended.
    let close = tree(files, Some(("2026-09-20", "2026-W37", "2026-08")));
    let before = md_files(&close);
    for _ in 0..2 {
        let out = close.run_at("2026-09-21T09:00:00-05:00", &["now"]);
        assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("automatic close"), "{}", out.stderr);
        assert!(out.stderr.contains("alreadyDemoted"), "{}", out.stderr);
        assert_eq!(md_files(&close), before);
    }
    let after = lines(&md_files(&close));
    assert_eq!(after["m4"].len(), 2, "{:?}", after["m4"]);
    assert_eq!(close.state()["closed"]["week"], "2026-W37", "{}", close.state());
}

/// Gap 56's host half: the kernel cannot create a file or a section, so a
/// close request carries the month containing now with §4.3's `# Outcomes`
/// and `# Demoted`, appended when missing — and the file is written only if
/// a line lands in it.
#[test]
fn the_host_hands_over_the_sections_a_close_needs_and_writes_them_only_when_used() {
    const AT: &str = "2026-09-07T09:00:00-05:00";
    let month = "---\nmonth: 2026-09\n---\n# Outcomes\n- [ ] 5 !1 Lean through ch.8 ^O1\n";

    // Nothing to close: the month file is handed over with `# Demoted`
    // appended, the kernel lands nothing, and not a byte is written.
    let idle = tree(&[("week/2026-W37.md", "# Tasks\n"), ("month/2026-09.md", month)], None);
    let json = idle.json_at(AT, &["close", "week"]);
    assert_eq!(json["report"]["closes"], serde_json::json!([]));
    assert_eq!(idle.read("month/2026-09.md"), month);
    // …and the backlog `# Overdue` goes into (the owner's D7) is handed over
    // too — created, with the heading, only if a line lands there.
    assert!(!idle.exists("backlog.md"));

    // A record lands: the section it needed is written with it.
    let busy = tree(
        &[
            ("week/2026-W36.md", "# Tasks\n- [ ] 3 2b Read chapter four ^m3\n"),
            ("week/2026-W37.md", "# Tasks\n"),
            ("month/2026-09.md", month),
        ],
        None,
    );
    busy.json_at(AT, &["close", "week"]);
    assert_eq!(
        busy.read("month/2026-09.md"),
        format!("{month}# Demoted\n- [-] 3 2b Read chapter four demoted:W36 ^m3\n")
    );
    assert_eq!(busy.read("week/2026-W36.md"), "# Tasks\n- [-] 3 2b Read chapter four ^m3\n");
}

/// Kernel/README.md gap 59, through the binary: a close keeps the order of the
/// lines it carries. September's two open outcomes — `!1` above `!2` — land
/// in October's `# Outcomes` in that order, after the outcome October already
/// has; its two `# Demoted` records land in October's `# Demoted` in their
/// order too. Until the kernel sorted its candidates by (document, rank) both
/// pairs arrived reversed, and the `!1` outcome ranked below the `!2` one
/// until `tm rank` restored it (§7.4: rank is priority within a class).
#[test]
fn a_close_keeps_the_order_of_the_lines_it_carries() {
    const AT: &str = "2026-10-01T09:00:00-05:00";
    let tm = tree(
        &[
            (
                "month/2026-09.md",
                "---\nmonth: 2026-09\n---\n# Outcomes\n\
                 - [ ] 5 !1 Lean through ch.8 ^O1\n\
                 - [ ] 4 !2 Soundcode demo runs ^O2\n\
                 - [x] 2 !3 Winter courses done ^O3\n\
                 # Demoted\n\
                 - [-] 4 3b Rollback path passes tests est:3b demoted:W37 ^m2\n\
                 - [-] 3 2b Read chapter four est:2b demoted:W38 ^m3\n",
            ),
            (
                "month/2026-10.md",
                "---\nmonth: 2026-10\n---\n# Outcomes\n- [ ] 3 !2 Already here ^O4\n# Demoted\n",
            ),
        ],
        None,
    );
    let json = tm.json_at(AT, &["close", "month"]);
    assert_eq!(json["key"], "2026-09", "{json}");
    let moved: Vec<&str> = json["report"]["closes"]
        .as_array()
        .expect("closes")
        .iter()
        .map(|c| c["id"].as_str().expect("id"))
        .collect();
    assert_eq!(moved, vec!["O1", "O2", "m2", "m3"], "{json}");
    assert_eq!(
        tm.read("month/2026-10.md"),
        "---\nmonth: 2026-10\n---\n# Outcomes\n\
         - [ ] 3 !2 Already here ^O4\n\
         - [ ] 5 !1 Lean through ch.8 ^O1\n\
         - [ ] 4 !2 Soundcode demo runs ^O2\n\
         # Demoted\n\
         - [-] 4 3b Rollback path passes tests est:3b demoted:W37 ^m2\n\
         - [-] 3 2b Read chapter four est:2b demoted:W38 ^m3\n"
    );
    assert_eq!(
        tm.read("month/2026-09.md"),
        "---\nmonth: 2026-09\n---\n# Outcomes\n- [x] 2 !3 Winter courses done ^O3\n# Demoted\n"
    );
}

/// A refusal of the automatic close lets the verb run; a kernel **fault**
/// does not — it is a bug, not a plan the kernel declined, so the verb
/// fails loudly, nothing is written and nothing is stamped closed.
#[test]
fn a_fault_in_the_automatic_close_fails_the_verb() {
    let tm = stale_tree();
    let before = md_files(&tm);
    let out = tm.run_env_at(
        "2026-09-12T09:00:00-05:00",
        &[("TM_KERNEL_FAULT_PROBE", "1")],
        &["now"],
    );
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("kernel fault"), "{}", out.stderr);
    assert_eq!(md_files(&tm), before);
    assert_eq!(tm.state()["closed"]["day"], "2026-06-11");
}
