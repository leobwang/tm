//! The file verbs — `add`, `edit`, `move`, `rank`, `demote`, `readopt`,
//! `drop`, `event`, `skip`, `routine done`, `triage` (§6.3, §13) — against a
//! temp `plan/`.

mod cli_common;

use cli_common::Tm;

#[test]
fn add_writes_a_line_with_an_id_and_logs_it() {
    let tm = Tm::new();
    let json = tm.json(&[
        "add",
        "2 30m Call the plumber",
        "--to",
        "backlog",
        "--section",
        "Untied",
    ]);
    let id = json["id"].as_str().expect("an id").to_string();
    assert_eq!(json["file"], "backlog.md");

    let backlog = tm.read("backlog.md");
    assert!(
        backlog.contains(&format!("- [ ] 2 30m Call the plumber ^{id}")),
        "{backlog}"
    );
    // The section it was asked for, not the end of the file.
    let untied = backlog.split("# Dated").next().unwrap_or_default();
    assert!(untied.contains("Call the plumber"), "{backlog}");

    // §10.1 has no `add`; the line is recorded as an `edit`.
    let last = tm.last();
    assert_eq!(last["ev"], "edit");
    assert_eq!(last["field"], "add");
    assert_eq!(last["id"], id.as_str());
    insta::assert_json_snapshot!("add_json", json);
}

#[test]
fn add_to_a_state_less_file_keeps_the_convention() {
    let tm = Tm::new();
    let json = tm.json(&["add", "stretch win:07:00-22:00 dur:10m every:day", "--to", "routines"]);
    assert_eq!(json["file"], "routines.md");
    let text = tm.read("routines.md");
    assert!(text.contains("- stretch win:07:00-22:00 dur:10m every:day"), "{text}");
    assert!(!text.contains("- [ ] stretch"), "routines carry no state");
}

/// §13 + §4.1: `tm add` takes the line as written, `- [ ] ` prefix and all —
/// the natural thing to do is copy a line out of a `.md` file, which is what
/// `plan/CLAUDE.md` tells Claude Code to do. clap read the leading `- ` as a
/// flag and exited 1 with `unexpected argument '- ' found`, and the `--`
/// escape it suggests then swallowed `--to`.
#[test]
fn add_accepts_a_line_with_its_grammar_prefix() {
    let tm = Tm::new();
    for (line, to, want) in [
        (
            "- [ ] 4 2b Write the release notes @m1 #soundcode",
            "week",
            "- [ ] 4 2b Write the release notes @m1 #soundcode",
        ),
        ("- [ ] 2 30m Call the bank", "backlog", "- [ ] 2 30m Call the bank"),
        (
            "- meditate win:06:00-08:00 dur:15m every:day",
            "routines",
            "- meditate win:06:00-08:00 dur:15m every:day",
        ),
    ] {
        let out = tm.run(&["add", line, "--to", to]);
        assert_eq!(out.code, 0, "`{line}`: {}{}", out.stdout, out.stderr);
        assert!(out.stdout.contains(want), "`{line}` → {}", out.stdout);
    }
    // The un-prefixed form still works, and the two do not stack prefixes.
    let out = tm.run(&["add", "2 30m Call the vet", "--to", "backlog"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    let backlog = tm.read("backlog.md");
    assert!(!backlog.contains("- - "), "{backlog}");
    assert!(!backlog.contains("- [ ] - "), "{backlog}");
    assert_eq!(tm.run(&["check"]).code, 0);
}

/// §1.3 + §6.3: after a demotion the id names two `[-]` lines — the archive
/// in the week file and the stamped copy under `month/…# Demoted`. `tm edit`
/// read one and wrote its text over the other, so the week archive silently
/// gained the month copy's `est:` and `demoted:` tokens while the record kept
/// its old `ci`, and `tm drop` picked the other copy again.
#[test]
fn editing_a_demoted_item_rewrites_the_line_it_read() {
    let tm = Tm::new();
    tm.ok(&["demote", "^m1"]);
    let week_before = tm.line("week/2026-W37.md", "m1");
    let month_before = tm.line("month/2026-09.md", "m1");
    assert!(week_before.starts_with("- [-] "), "{week_before}");
    assert!(month_before.contains("demoted:W37"), "{month_before}");

    tm.ok(&["edit", "^m1", "ci=2"]);
    assert_eq!(
        tm.line("week/2026-W37.md", "m1"),
        week_before,
        "the week archive was rewritten from the other copy"
    );
    let month_after = tm.line("month/2026-09.md", "m1");
    assert!(month_after.starts_with("- [-] 2 "), "{month_after}");
    assert!(month_after.contains("demoted:W37"), "{month_after}");

    // `tm drop` addresses the same copy.
    tm.ok(&["drop", "^m1"]);
    assert_eq!(tm.line("week/2026-W37.md", "m1"), week_before);
    assert!(tm.line("month/2026-09.md", "m1").starts_with("- [~] "));
}

#[test]
fn edit_changes_fields_byte_faithfully_and_logs_each_one() {
    let tm = Tm::new();
    let before = tm.line("backlog.md", "a1");
    let json = tm.json(&["edit", "^a1", "ci=3", "est=45m", "--set", "loc=out"]);
    assert_eq!(json["changes"].as_array().map(Vec::len), Some(3));

    let after = tm.line("backlog.md", "a1");
    assert_ne!(before, after);
    // §4.1: `est=` is the item's estimate — the *leading* one. `est:` is the
    // tool-written remainder (`tm stop`, a partial `tm done`), so a hand edit
    // must not land there: §6.4's `progress` divides by the leading value and
    // the §4.3 timeline prints it.
    assert!(after.starts_with("- [ ] 3 45m Insurance claim"), "{after}");
    assert!(!after.contains("est:"), "{after}");
    assert!(after.contains("loc:out"), "{after}");

    let edits: Vec<_> = tm
        .log()
        .into_iter()
        .filter(|e| e["ev"] == "edit")
        .collect();
    assert_eq!(edits.len(), 3);
    assert_eq!(edits[0]["field"], "ci");
    assert_eq!(edits[0]["from"], "2");
    assert_eq!(edits[0]["to"], "3");
    // The `est` edit reports the estimate it replaced, not "".
    assert_eq!(edits[1]["field"], "est");
    assert_eq!(edits[1]["from"], "30m");
    insta::assert_json_snapshot!("edit_json", json);
}

#[test]
fn edit_est_reaches_a_line_with_no_positional_slot() {
    // §4.3: a `routines.md` line has no state, so it has no leading-estimate
    // slot; `est:` is where the value goes.
    let tm = Tm::new();
    tm.ok(&["edit", "lunch", "est=45m"]);
    let text = tm.read("routines.md");
    assert!(text.contains("- lunch"), "{text}");
    assert!(text.contains("est:45m"), "{text}");
    assert_eq!(tm.run(&["check"]).code, 0);

    // A line without a leading estimate gains one.
    tm.ok(&["edit", "^a3", "est=1b"]);
    let a3 = tm.line("backlog.md", "a3");
    assert!(a3.starts_with("- [ ] 1 1b Pick up package"), "{a3}");
}

#[test]
fn set_writes_a_raw_token_where_the_typed_edit_would_not() {
    // `--set` is documented as writing a `key:value` token verbatim, which is
    // how the tool-written `est:` remainder is reachable by hand.
    let tm = Tm::new();
    tm.ok(&["edit", "^a1", "--set", "est=45m"]);
    let after = tm.line("backlog.md", "a1");
    assert!(after.starts_with("- [ ] 2 30m Insurance claim"), "{after}");
    assert!(after.contains("est:45m"), "{after}");
}

#[test]
fn edit_refuses_a_priority_outside_the_grammar() {
    // §4.1's EBNF: `token = … | "!" ("1".."4") | …`. Writing `!9` produces a
    // line `tm check` rejects (`bad-ci`) and that the grammar then re-reads
    // as title text, so a second `p=` edit would add a *second* token.
    let tm = Tm::new();
    let before = tm.line("week/2026-W37.md", "t1");
    for bad in ["0", "9", "notanumber"] {
        let out = tm.run(&["edit", "^t1", &format!("p={bad}")]);
        assert_eq!(out.code, 1, "p={bad} was accepted");
        assert!(out.stderr.contains("1–4"), "{}", out.stderr);
    }
    assert_eq!(tm.line("week/2026-W37.md", "t1"), before);
    assert_eq!(tm.run(&["check"]).code, 0);

    tm.ok(&["edit", "^t1", "p=2"]);
    assert!(tm.line("week/2026-W37.md", "t1").contains("!2"));
}

#[test]
fn edit_refuses_a_value_its_own_check_would_reject() {
    // §14 makes the CLI the sanctioned writer; §1.3 means it must never
    // produce a tree `tm check` fails on.
    let tm = Tm::new();
    let t3 = tm.line("week/2026-W37.md", "t3");
    let bad = tm.run(&["edit", "^t3", "due=notadate"]);
    assert_eq!(bad.code, 1, "{}{}", bad.stdout, bad.stderr);
    assert_eq!(tm.line("week/2026-W37.md", "t3"), t3);

    let a1 = tm.line("backlog.md", "a1");
    let bad = tm.run(&["edit", "^a1", "--set", "max=nonsense"]);
    assert_eq!(bad.code, 1, "{}{}", bad.stdout, bad.stderr);
    assert_eq!(tm.line("backlog.md", "a1"), a1);

    // A good value still goes through.
    tm.ok(&["edit", "^t3", "due=2026-09-11T23:59"]);
    assert!(tm.line("week/2026-W37.md", "t3").contains("due:2026-09-11T23:59"));
    assert_eq!(tm.run(&["check"]).code, 0);
}

#[test]
fn add_refuses_a_duplicate_id() {
    // §4.1: "Ids are global across the tree."
    let tm = Tm::new();
    let before = tm.read("backlog.md");
    let out = tm.run(&["add", "3 1b Dup id ^t1", "--to", "backlog"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("already used"), "{}", out.stderr);
    assert_eq!(tm.read("backlog.md"), before);
    assert_eq!(tm.run(&["check"]).code, 0);
}

#[test]
fn add_without_a_section_stays_out_of_a_series() {
    // §5.4: only the head of a `## series:` is active; a captured item that
    // lands behind the head is invisible to the planner. `backlog.md` ends
    // with `## series:cell-bio` in §4.3 and in the `tm init` tree.
    let tm = Tm::new();
    let json = tm.json(&["add", "2 30m Renew the passport", "--to", "backlog"]);
    let id = json["id"].as_str().expect("an id").to_string();
    assert_eq!(json["section"], "Dated, far out");

    let backlog = tm.read("backlog.md");
    let series = backlog.split("## series:").nth(1).unwrap_or_default();
    assert!(!series.contains(&id), "landed inside the series: {backlog}");

    // …and it is a candidate the planner can see.
    let plan = tm.json(&["plan"]);
    let ids: Vec<&str> = plan["priorities"]
        .as_array()
        .expect("priorities")
        .iter()
        .filter_map(|p| p["id"].as_str())
        .collect();
    assert!(ids.contains(&id.as_str()), "{ids:?}");
}

#[test]
fn demote_then_readopt_in_the_same_week_leaves_one_line() {
    // §6.3: the demote marks the week line `[-]` and copies it to the month's
    // `# Demoted`; the readopt brings that stamped copy back. Within one week
    // both land in the same file, and two lines with one id is a `tm check`
    // error (§17 M9: the tree must pass `tm check`).
    let tm = Tm::new();
    tm.ok(&["demote", "^m4"]);
    assert_eq!(tm.run(&["check"]).code, 0);
    tm.ok_at("2026-09-07T09:01:00-05:00", &["readopt", "^m4"]);

    let week = tm.read("week/2026-W37.md");
    assert_eq!(week.matches("^m4").count(), 1, "{week}");
    let line = tm.line("week/2026-W37.md", "m4");
    assert!(line.starts_with("- [ ]"), "{line}");
    assert!(line.contains("demoted:W37"), "the stamp is kept: {line}");
    let check = tm.run(&["check"]);
    assert_eq!(check.code, 0, "{}{}", check.stdout, check.stderr);
}

#[test]
fn edit_unset_removes_a_key() {
    let tm = Tm::new();
    let json = tm.json(&["edit", "^t3", "--unset", "est"]);
    assert_eq!(json["changes"][0]["field"], "est");
    assert_eq!(json["changes"][0]["from"], "1b");
    assert!(!tm.line("week/2026-W37.md", "t3").contains("est:"));
}

#[test]
fn move_takes_a_line_between_horizon_files() {
    let tm = Tm::new();
    let json = tm.json(&["move", "^a1", "week"]);
    assert_eq!(json["from"], "backlog.md");
    assert_eq!(json["to"], "week/2026-W37.md");
    assert!(!tm.read("backlog.md").contains("^a1"));
    assert!(tm.read("week/2026-W37.md").contains("^a1"));
    let last = tm.last();
    assert_eq!(last["ev"], "move");
    assert_eq!(last["id"], "a1");
    insta::assert_json_snapshot!("move_json", json);
}

#[test]
fn move_to_a_day_pins_the_line() {
    let tm = Tm::new();
    tm.ok(&["move", "^a3", "day"]);
    let day = tm.read("day/2026-09-07.md");
    let pinned = day.split("## Log").next().unwrap_or_default();
    assert!(pinned.contains("^a3"), "{day}");
    assert!(pinned.contains("# Pinned"), "{day}");
}

#[test]
fn rank_moves_a_line_within_its_section() {
    let tm = Tm::new();
    let json = tm.json(&["rank", "^m3", "1"]);
    assert_eq!(json["moved"], true);
    let week = tm.read("week/2026-W37.md");
    let milestones: Vec<&str> = week
        .lines()
        .skip_while(|l| !l.starts_with("# Milestones"))
        .filter(|l| l.starts_with("- "))
        .collect();
    assert!(milestones[0].contains("^m3"), "{milestones:?}");
    insta::assert_json_snapshot!("rank_json", json);
}

#[test]
fn demote_copies_the_line_into_the_month_archive() {
    let tm = Tm::new();
    let json = tm.json(&["demote", "^m4"]);
    assert_eq!(json["id"], "m4");
    assert_eq!(json["stamps"][0], "W37");

    assert!(tm.line("week/2026-W37.md", "m4").starts_with("- [-]"));
    let month = tm.read("month/2026-09.md");
    let demoted = month.split("# Demoted").nth(1).unwrap_or_default();
    assert!(demoted.contains("^m4"), "{month}");
    assert!(demoted.contains("demoted:W37"), "{month}");

    let last = tm.last();
    assert_eq!(last["ev"], "demote");
    assert_eq!(last["id"], "m4");
    insta::assert_json_snapshot!("demote_json", json);
}

#[test]
fn readopt_brings_a_demoted_line_back() {
    let tm = Tm::new();
    let json = tm.json(&["readopt", "^m2"]);
    assert_eq!(json["from"], "month/2026-09.md");
    assert_eq!(json["to"], "week/2026-W37.md");
    let last = tm.last();
    assert_eq!(last["ev"], "readopt");
    assert_eq!(last["id"], "m2");
    insta::assert_json_snapshot!("readopt_json", json);
}

/// §4.1 + §17.2: ids are global and unique, so no verb may leave one `^id`
/// on two live lines. `^m2` ships live in `week/2026-W37.md` beside its
/// `[-]` archive copy under `month/…# Demoted`; readopting it into *another*
/// horizon used to carry the copy across and report success, leaving `^m2`
/// live twice and `tm check` at `error[dup-id]`, exit 2 (§17 M9: the tree
/// must pass `tm check`).
#[test]
fn readopt_into_another_horizon_leaves_the_tree_valid() {
    for to in ["week/2026-W38.md", "day"] {
        let tm = Tm::new();
        let json = tm.json(&["readopt", "^m2", "--to", to]);
        assert_eq!(json["from"], "month/2026-09.md");

        let check = tm.run(&["check"]);
        assert_eq!(check.code, 0, "{to}: {}{}", check.stdout, check.stderr);

        // Exactly one live line, in the horizon that was asked for, and the
        // archive copy is gone.
        let dest = json["to"].as_str().expect("a destination").to_string();
        assert_eq!(tm.read(&dest).matches("^m2").count(), 1, "{}", tm.read(&dest));
        assert!(!tm.read("week/2026-W37.md").contains("^m2 "));
        assert!(!tm.read("week/2026-W37.md").ends_with("^m2\n"));
        assert!(!tm.read("month/2026-09.md").contains("^m2"));
        // … carrying the stamp the copy held (§11's demotion churn).
        let line = tm.line(&dest, "m2");
        assert!(line.starts_with("- [ ] "), "{line}");
        assert!(line.contains("demoted:W37"), "{line}");
    }
}

/// §6.3: readopt moves a *demoted* line. `^t1` was never demoted, so there
/// is nothing to readopt — the verb refuses (`tm move` is the verb for that)
/// instead of silently moving the line and logging a `readopt`.
#[test]
fn readopt_refuses_an_item_that_was_never_demoted() {
    let tm = Tm::new();
    let before = tm.read("week/2026-W37.md");
    let out = tm.run(&["readopt", "^t1"]);
    assert_ne!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("not demoted"), "{}", out.stderr);
    assert_eq!(tm.read("week/2026-W37.md"), before);
    assert!(tm.events().is_empty(), "{:?}", tm.events());
}

#[test]
fn drop_marks_the_line_dropped() {
    let tm = Tm::new();
    let json = tm.json(&["drop", "^m4"]);
    assert!(json["line"].as_str().unwrap_or_default().starts_with("- [~]"));
    assert!(tm.line("week/2026-W37.md", "m4").starts_with("- [~]"));
    let last = tm.last();
    assert_eq!(last["ev"], "drop");
    assert_eq!(last["id"], "m4");
    insta::assert_json_snapshot!("drop_json", json);
}

#[test]
fn event_resolves_a_waiting_item() {
    let tm = Tm::new();
    // ^a4 is `[?] … on-event:reply/7d waiting:2026-09-05`.
    assert!(tm.line("backlog.md", "a4").starts_with("- [?]"));
    let json = tm.json(&["event", "reply"]);
    assert_eq!(json["resolved"][0], "a4");

    let line = tm.line("backlog.md", "a4");
    assert!(line.starts_with("- [ ]"), "{line}");
    assert!(!line.contains("waiting:"), "{line}");

    let events = tm.events();
    assert!(events.contains(&"event".to_string()), "{events:?}");
    insta::assert_json_snapshot!("event_json", json);
}

#[test]
fn done_on_an_on_event_item_starts_the_wait() {
    // §5.1: "on `done`, the item's state becomes `[?]` with `waiting:<date>`".
    let tm = Tm::new();
    tm.ok(&["event", "reply"]);
    let json = tm.json_at("2026-09-07T09:10:00-05:00", &["done", "^a4"]);
    assert_eq!(json["state"], "[?]");
    let line = tm.line("backlog.md", "a4");
    assert!(line.starts_with("- [?]"), "{line}");
    assert!(line.contains("waiting:2026-09-07"), "{line}");
    assert_eq!(tm.last()["ev"], "done");
}

#[test]
fn a_waiting_timeout_flips_the_item_back_on_the_next_command() {
    // §5.1: `[?] … on-event:reply/7d waiting:2026-09-05` times out on
    // 2026-09-12; the next command after that puts it back in play.
    let tm = Tm::new();
    assert!(tm.line("backlog.md", "a4").starts_with("- [?]"));
    tm.ok_at("2026-09-13T09:00:00-05:00", &["now"]);

    let line = tm.line("backlog.md", "a4");
    assert!(line.starts_with("- [ ]"), "{line}");
    assert!(!line.contains("waiting:"), "{line}");
    let edits: Vec<_> = tm
        .log()
        .into_iter()
        .filter(|e| e["ev"] == "edit" && e["id"] == "a4")
        .collect();
    assert_eq!(edits.len(), 1);
    assert_eq!(edits[0]["field"], "state");
    assert_eq!(edits[0]["from"], "[?]");
    assert_eq!(edits[0]["to"], "[ ]");
}

#[test]
fn skip_records_todays_instance() {
    let tm = Tm::new();
    let json = tm.json(&["skip", "lunch"]);
    assert_eq!(json["item"], "lunch");
    assert_eq!(json["inst"], "2026-09-07");
    let last = tm.last();
    assert_eq!(last["ev"], "skip");
    assert_eq!(last["item"], "lunch");
    assert_eq!(last["inst"], "2026-09-07");
    insta::assert_json_snapshot!("skip_json", json);
}

#[test]
fn routine_done_records_the_minutes() {
    let tm = Tm::new();
    let json = tm.json(&["routine", "done", "lunch", "--min", "18"]);
    assert_eq!(json["status"], "done");
    let last = tm.last();
    assert_eq!(last["ev"], "routine");
    assert_eq!(last["item"], "lunch");
    assert_eq!(last["status"], "done");
    assert_eq!(last["actual_min"], 18);
    insta::assert_json_snapshot!("routine_done_json", json);
}

#[test]
fn skipping_an_unknown_routine_is_an_error() {
    let tm = Tm::new();
    let out = tm.run(&["skip", "nonesuch"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("no such routine"), "{}", out.stderr);
}

#[test]
fn triage_previews_every_inbox_line() {
    let tm = Tm::new();
    let json = tm.json(&["triage"]);
    assert_eq!(json["file"], "inbox.md");
    let lines = json["lines"].as_array().expect("lines");
    assert_eq!(lines.len(), 4);
    assert!(lines[0]["parsed"].is_string());
    insta::assert_json_snapshot!("triage_json", json);
}

#[test]
fn triage_skips_the_guidance_comment_tm_init_writes() {
    // §14/§17 M9: `tm init` fills `inbox.md` with one HTML comment block.
    // Previewing its lines would have `/triage` `tm add` the guidance — and
    // the terminator `-->` — as items.
    let tm = Tm::new();
    std::fs::write(
        tm.plan.join("inbox.md"),
        "<!--\nCapture, untriaged: one thought per line.\n\n    pset 2 due friday night\n-->\n\
         - a real capture\n",
    )
    .expect("write inbox");
    let json = tm.json(&["triage"]);
    let lines = json["lines"].as_array().expect("lines");
    assert_eq!(lines.len(), 1, "{json}");
    assert_eq!(lines[0]["raw"], "- a real capture");
}
