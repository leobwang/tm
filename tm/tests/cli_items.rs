//! The file verbs — `add`, `edit`, `move`, `rank`, `demote`, `readopt`,
//! `drop`, `event`, `skip`, `routine done`, `triage` (§6.3, §13) — against a
//! temp `plan/`.

mod cli_common;

use std::fs;

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
    // slot; `est:` is where the value goes. Id-less, so it rides the old
    // Rust path (gap 5: the kernel cannot address a line without `^id` —
    // kernel/README.md, 2026-09-12 "the five lifecycle verbs" block).
    let tm = Tm::new();
    tm.ok(&["edit", "lunch", "est=45m"]);
    let text = tm.read("routines.md");
    assert!(text.contains("- lunch"), "{text}");
    assert!(text.contains("est:45m"), "{text}");
    assert_eq!(tm.run(&["check"]).code, 0);

    // Kernel-backed `est=`: the value lands as the canonical `est:` token
    // (in minutes) and the leading slot is never invented — the old path
    // wrote a leading estimate here (kernel/README.md, 2026-09-12 block:
    // `tm edit est=` is the kernel's est op, one reader end to end).
    tm.ok(&["edit", "^a3", "est=1b"]);
    let a3 = tm.line("backlog.md", "a3");
    assert!(a3.starts_with("- [ ] 1 Pick up package"), "{a3}");
    assert!(a3.contains("est:60m"), "{a3}");
    assert_eq!(tm.run(&["check"]).code, 0);
}

/// The minutes `tm plan` gave an item, summed over its segments.
fn planned_minutes(plan: &serde_json::Value, id: &str) -> i64 {
    plan["segments"]
        .as_array()
        .expect("segments")
        .iter()
        .filter(|s| s["item"] == id)
        .filter_map(|s| s["minutes"].as_i64())
        .sum()
}

#[test]
fn edit_est_moves_the_remaining_estimate_not_the_one_as_written() {
    // §4.1: `est:` is "the remaining estimate" and it "overrides the leading
    // estimate"; §3.1 keeps the two apart (`est` against `est_original`, "the
    // leading estimate as written"). So on a line that already carries `est:`
    // — every line `tm stop`, a partial `tm done` or a `tm close` has touched
    // — that token *is* the estimate the user is changing. Writing the leading
    // one instead would leave §6.4's `remaining` exactly where it was (the
    // edit would report success and change nothing) and would rewrite the
    // history §11's estimate calibration measures actual/est against.
    let tm = Tm::new();
    let before = tm.json(&["plan"]);

    let json = tm.json(&["edit", "^t3", "est=3b"]);
    assert_eq!(json["changes"][0]["field"], "est");
    // The value replaced is the remaining estimate, not the leading one (2b).
    assert_eq!(json["changes"][0]["from"], "1b");
    assert_eq!(json["changes"][0]["to"], "3b");

    // Kernel-backed: the kernel writes the field's canonical rendering of
    // the parsed value — minutes, so `3b` lands as `est:180m`
    // (kernel/README.md, 2026-09-12 "the five lifecycle verbs" block).
    let after = tm.line("week/2026-W37.md", "t3");
    assert!(after.contains("est:180m"), "the remainder moved: {after}");
    assert!(!after.contains("est:1b"), "and only once: {after}");
    assert!(
        after.starts_with("- [>] 4 2b Exercises"),
        "the estimate as written is history, not a field to overwrite: {after}"
    );
    assert_eq!(tm.run(&["check"]).code, 0);

    // The parse changed: the item's remaining is 3b, and the planner spends
    // more of the day on it than the 1b it had left before.
    assert!(
        planned_minutes(&tm.json(&["plan"]), "t3") > planned_minutes(&before, "t3"),
        "the new remaining is invisible to `tm plan`"
    );
    // §6.3: the estimate a demotion carries is that same remaining.
    assert_eq!(tm.json(&["demote", "^t3"])["est_min"], 180);
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

    // Dropping the remainder hands `remaining` back to the leading estimate
    // (§3.1's `est_original`, gap 41's fallback). A later `est=` writes the
    // `est:` token again — kernel-backed, the est op always writes the one
    // slot `remaining` reads first, never the leading history
    // (kernel/README.md, 2026-09-12 "the five lifecycle verbs" block).
    tm.ok(&["edit", "^t3", "est=4b"]);
    let after = tm.line("week/2026-W37.md", "t3");
    assert!(after.starts_with("- [>] 4 2b Exercises"), "{after}");
    assert!(after.contains("est:240m"), "{after}");
}

#[test]
fn edit_unset_removes_the_positional_ci() {
    // §4.1 writes the ci in the slot after the state, not as a `key:` token,
    // so removing the token is not enough: `--unset ci` used to report the
    // change and leave the digit standing. §3.1: with no ci of its own the
    // item inherits its parent's again.
    let tm = Tm::new();
    let json = tm.json(&["edit", "^t1", "--unset", "ci"]);
    assert_eq!(json["changes"][0]["field"], "ci");
    assert_eq!(json["changes"][0]["from"], "5");
    let after = tm.line("week/2026-W37.md", "t1");
    assert!(after.starts_with("- [ ] 1b Read ch.6"), "{after}");
    assert_eq!(tm.run(&["check"]).code, 0);

    // A state-less line spells the same fact `ci:` (§4.3), and that goes too.
    tm.ok(&["edit", "sleep", "--unset", "ci"]);
    let routines = tm.read("routines.md");
    assert!(routines.contains("- sleep"), "{routines}");
    assert!(!routines.contains("ci:0"), "{routines}");
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

/// Kernel-backed move places the line itself, at a fresh rank — the end of
/// the destination file — and re-checks the whole plan. §6.2 constrains a
/// day file's items to `# Pinned`, and the shipped day file ends with
/// `## Log`/`## Notes`, so the landing site fails the check and the move is
/// refused **by name** (`badHorizon`) with nothing written — where the old
/// path appended into `# Pinned` by section name (kernel/README.md,
/// 2026-09-12 "the five lifecycle verbs" block records the change).
#[test]
fn move_to_a_day_is_refused_by_name() {
    let tm = Tm::new();
    let day_before = tm.read("day/2026-09-07.md");
    let backlog_before = tm.read("backlog.md");
    let out = tm.run(&["move", "^a3", "day"]);
    assert_ne!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("badHorizon"), "{}", out.stderr);
    assert_eq!(tm.read("day/2026-09-07.md"), day_before);
    assert_eq!(tm.read("backlog.md"), backlog_before);
    assert!(tm.events().is_empty(), "{:?}", tm.events());
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

/// Kernel-backed `tm rank` (kernel/README.md, 2026-09-12 "rank, add and the
/// keyed edit" block): the host compiles the position into a rotation of
/// `rank{id,rank}` wire ops — every line byte-identical, only the order
/// changed, and the whole plan re-checked by the kernel.
#[test]
fn rank_down_rotates_the_section_and_keeps_every_byte() {
    let tm = Tm::new();
    let before = tm.read("week/2026-W37.md");
    let json = tm.json(&["rank", "^t1", "4"]);
    assert_eq!(json["moved"], true);
    let after = tm.read("week/2026-W37.md");
    let tasks: Vec<&str> = after
        .lines()
        .skip_while(|l| !l.starts_with("# Tasks"))
        .filter(|l| l.starts_with("- "))
        .collect();
    let ids: Vec<&str> = tasks
        .iter()
        .map(|l| l.rsplit('^').next().unwrap_or_default())
        .collect();
    assert_eq!(ids, ["t3", "t4", "t5", "t1"], "{tasks:?}");
    // The same lines, byte for byte: a reorder is a permutation, never a
    // rewrite.
    let mut sorted_before: Vec<&str> = before.lines().collect();
    let mut sorted_after: Vec<&str> = after.lines().collect();
    sorted_before.sort_unstable();
    sorted_after.sort_unstable();
    assert_eq!(sorted_before, sorted_after);
    assert_eq!(tm.run(&["check"]).code, 0);

    // The old path's clamp and no-op report survive the wiring: position 99
    // clamps to the last slot, where ^t1 already is.
    let json = tm.json(&["rank", "^t1", "99"]);
    assert_eq!(json["moved"], false);
    assert_eq!(tm.read("week/2026-W37.md"), after);
}

/// Kernel-backed `tm add`: the id is the kernel's own (`freshId` renders the
/// host's seed as digits and bumps past every taken id — freshness is L21,
/// a theorem, not a retry loop), the line lands at the end of the file, and
/// the §10.1 `edit{field:"add"}` event still carries it.
#[test]
fn add_through_the_kernel_assigns_a_digit_id() {
    let tm = Tm::new();
    let json = tm.json(&["add", "4 2b Write the release notes", "--to", "week"]);
    let id = json["id"].as_str().expect("an id").to_string();
    assert!(
        !id.is_empty() && id.chars().all(|c| c.is_ascii_digit()),
        "kernel ids are freshId's digits (gap 13's recorded resolution): {id}"
    );
    assert_eq!(json["file"], "week/2026-W37.md");
    let week = tm.read("week/2026-W37.md");
    assert!(
        week.contains(&format!("- [ ] 4 2b Write the release notes ^{id}")),
        "{week}"
    );
    let last = tm.last();
    assert_eq!(last["ev"], "edit");
    assert_eq!(last["field"], "add");
    assert_eq!(last["id"], id.as_str());
    assert_eq!(tm.run(&["check"]).code, 0);
}

/// The `add` bite reaches the shipped binary (§5.8; the FFI twin is
/// `add_outside_a_day_files_pinned_section_is_refused_by_name`): the kernel
/// appends at the end of the file, §6.2 constrains a day file's items to
/// `# Pinned`, and the shipped day file ends `## Log`/`## Notes` — so the
/// add is refused **by name** with nothing written, where the old path
/// appended an out-of-section line (kernel/README.md, 2026-09-12 "rank, add
/// and the keyed edit" block records the change).
#[test]
fn add_to_a_day_outside_pinned_is_refused_by_name() {
    let tm = Tm::new();
    let before = tm.read("day/2026-09-07.md");
    let out = tm.run(&["add", "2 20m Buy stamps", "--to", "day"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("badItem"), "{}", out.stderr);
    assert_eq!(tm.read("day/2026-09-07.md"), before);
    assert!(tm.events().is_empty(), "{:?}", tm.events());
}

/// The keyed edit, kernel-backed for the nine wired keys (kernel/README.md,
/// 2026-09-12 "rank, add and the keyed edit" block): the value is parsed by
/// the key's own field grammar and written as its canonical rendering —
/// `cap` and `max` are one key and the write lands as `max:`
/// (`set_max_writes_max`) — and an empty value is the wire's unset form.
#[test]
fn edit_keyed_writes_the_fields_canonical_rendering() {
    let tm = Tm::new();
    let json = tm.json(&["edit", "^t1", "pref=07:30"]);
    assert_eq!(json["changes"][0]["field"], "pref");
    let line = tm.line("week/2026-W37.md", "t1");
    assert!(line.contains("pref:07:30"), "{line}");

    tm.ok(&["edit", "^t1", "cap=2b/d"]);
    let line = tm.line("week/2026-W37.md", "t1");
    assert!(line.contains("max:2b/d"), "cap writes max: — {line}");
    assert!(!line.contains("cap:"), "{line}");

    // `tm edit ^id <key>=` — the unset form the wire documents.
    tm.ok(&["edit", "^t1", "pref="]);
    let line = tm.line("week/2026-W37.md", "t1");
    assert!(!line.contains("pref:"), "{line}");
    assert_eq!(tm.run(&["check"]).code, 0);
}

/// The keyed edit's refusals arrive **by name**, in the human line and the
/// `--json` document — `badValue <k>` is the key's field grammar biting
/// through the wire (R10), `keyAbsent` an unset of a key the line does not
/// carry (the old path reported success and removed nothing; recorded in
/// the same README block).
#[test]
fn edit_keyed_refusals_are_named() {
    let tm = Tm::new();
    let before = tm.read("week/2026-W37.md");
    let out = tm.run(&["--json", "edit", "^t1", "dur=zzz"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc: serde_json::Value = serde_json::from_str(&out.stderr).expect("json");
    assert_eq!(doc["kind"], "kernel");
    assert_eq!(doc["detail"]["refusal"], "badValue");
    assert_eq!(doc["detail"]["key"], "dur");

    let out = tm.run(&["--json", "edit", "^t1", "--unset", "buffer"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc: serde_json::Value = serde_json::from_str(&out.stderr).expect("json");
    assert_eq!(doc["detail"]["refusal"], "keyAbsent");

    assert_eq!(tm.read("week/2026-W37.md"), before);
    assert!(tm.events().is_empty(), "{:?}", tm.events());
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

/// Gap 20's remainder (kernel/README.md, stage 4 step 9): `tm demote` files the
/// record at the end of the month's `# Demoted` — ahead of a heading that
/// follows it, where it used to land after that heading, at the end of the
/// file — and a month without `# Demoted` is handed the section with the record,
/// as a close's month is (gap 56).
#[test]
fn demote_files_the_record_at_the_end_of_the_demoted_section() {
    let tm = Tm::new();
    let path = tm.plan.join("month/2026-09.md");
    let month = std::fs::read_to_string(&path).expect("month");
    std::fs::write(&path, format!("{month}\n# Notes\nKeep the review short.\n")).expect("write");
    tm.ok(&["demote", "^m4"]);
    let after = tm.read("month/2026-09.md");
    let (demoted, notes) = after.split_once("# Notes").expect("notes kept");
    assert!(demoted.contains("demoted:W37 ^m2"), "{after}");
    assert!(demoted.contains("demoted:W37 ^m4"), "{after}");
    assert!(
        demoted.find("^m2").unwrap_or(usize::MAX) < demoted.find("^m4").unwrap_or(0),
        "the new record follows the standing one: {after}"
    );
    assert!(!notes.contains("^m4"), "{after}");
    assert_eq!(tm.run(&["check"]).code, 0);

    // No `# Demoted` at all: the host hands the section over and the record
    // lands under it.
    let tm = Tm::new();
    let path = tm.plan.join("month/2026-09.md");
    let month = std::fs::read_to_string(&path).expect("month");
    let head = month.split("# Demoted").next().expect("head").to_string();
    std::fs::write(&path, &head).expect("write");
    tm.ok(&["demote", "^m4"]);
    let after = tm.read("month/2026-09.md");
    assert!(after.starts_with(&head), "{after}");
    let tail = &after[head.len()..];
    assert!(tail.starts_with("# Demoted\n- [-] 2 2b Pick winter courses"), "{after}");
    assert!(tail.trim_end().ends_with("demoted:W37 ^m4"), "{after}");
}

/// A real demote-then-readopt round trip, into a different week: the kernel
/// takes the record into the destination, flips `[-]` back to `[ ]` keeping
/// its stamps, and removes the tombstone (kernel/README.md, 2026-09-12
/// "the five lifecycle verbs" block).
#[test]
fn readopt_brings_a_demoted_line_back() {
    let tm = Tm::new();
    tm.ok(&["demote", "^m4"]);
    let json = tm.json_at("2026-09-07T09:01:00-05:00", &["readopt", "^m4", "--to", "week/2026-W38.md"]);
    assert_eq!(json["id"], "m4");
    assert_eq!(json["to"], "week/2026-W38.md");
    let line = tm.line("week/2026-W38.md", "m4");
    assert!(line.starts_with("- [ ] "), "{line}");
    assert!(line.contains("demoted:W37"), "the stamp is kept: {line}");
    // One line in the whole tree: the tombstone and the record both went.
    assert!(!tm.read("week/2026-W37.md").contains("^m4"));
    assert!(!tm.read("month/2026-09.md").contains("^m4"));
    let check = tm.run(&["check"]);
    assert_eq!(check.code, 0, "{}{}", check.stdout, check.stderr);
    let last = tm.last();
    assert_eq!(last["ev"], "readopt");
    assert_eq!(last["id"], "m4");
}

/// §4.3 ships `^m2` **live** in `week/2026-W37.md` beside its `[-]` record
/// under `month/…# Demoted`. To the kernel that pair is one entity whose
/// live line is `[ ]` — not demoted — so readopt is refused **by name**
/// (`notDemoted`) and nothing is written, where the old Rust path absorbed
/// the record into the live line and moved it (kernel/README.md, 2026-09-12
/// "the five lifecycle verbs" block records the change). The §4.1/§17.2
/// guarantee this test used to check — no verb leaves one id on two live
/// lines — now holds by refusal.
#[test]
fn readopt_into_another_horizon_leaves_the_tree_valid() {
    for to in ["week/2026-W38.md", "day"] {
        let tm = Tm::new();
        let week_before = tm.read("week/2026-W37.md");
        let month_before = tm.read("month/2026-09.md");
        let out = tm.run(&["readopt", "^m2", "--to", to]);
        assert_ne!(out.code, 0, "{to}: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("notDemoted"), "{to}: {}", out.stderr);

        // Nothing was written, no event was logged, the tree is untouched.
        assert_eq!(tm.read("week/2026-W37.md"), week_before);
        assert_eq!(tm.read("month/2026-09.md"), month_before);
        assert!(tm.events().is_empty(), "{:?}", tm.events());
        let check = tm.run(&["check"]);
        assert_eq!(check.code, 0, "{to}: {}{}", check.stdout, check.stderr);
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

/// **A6, closed in the shipped binary** (kernel/README.md, 2026-09-12
/// "the five lifecycle verbs" block). `^m2`'s `[-]` record stands in
/// `month/…# Demoted`; the pre-stage-0 `move_to` appended the week line
/// beside it without ever asking whether the destination already held the
/// id — the hole all 426 violations of the depth-2 sweep reached, 400 of
/// them through exactly this verb. The kernel refuses **by name**
/// (`occupied`), and nothing is written.
#[test]
fn move_into_the_tombstones_file_is_refused_by_name() {
    let tm = Tm::new();
    let week_before = tm.read("week/2026-W37.md");
    let month_before = tm.read("month/2026-09.md");
    let out = tm.run(&["move", "^m2", "month"]);
    assert_ne!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("occupied"), "{}", out.stderr);
    assert_eq!(tm.read("week/2026-W37.md"), week_before);
    assert_eq!(tm.read("month/2026-09.md"), month_before);
    assert!(tm.events().is_empty(), "{:?}", tm.events());
}

/// Demoting an id that already has a standing `# Demoted` record merges into
/// that record, as fork-point `demote_one` did: §6.3 gives an item **one**
/// record, so the month keeps one `^m2` line — the live line's bytes, `[-]`,
/// its stamps merged with the record's (`W37` once) — and the week line stays
/// behind as `[-]`. Until kernel/README.md gap 53 closed the kernel refused
/// this by name (`alreadyDemoted`, 2026-09-12 "the five lifecycle verbs"
/// block), which kept the record safe from a silent overwrite but also from
/// the demotion; the merge keeps its stamps and, under a line with no estimate
/// of its own, its `est:`.
#[test]
fn demote_with_a_standing_record_merges_into_it() {
    let tm = Tm::new();
    let out = tm.run(&["demote", "^m2"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let month = tm.read("month/2026-09.md");
    assert_eq!(month.matches("^m2").count(), 1, "{month}");
    assert_eq!(
        tm.line("month/2026-09.md", "m2"),
        "- [-] 4 6b Rollback path passes tests   @O2 demoted:W37 ^m2"
    );
    assert_eq!(tm.line("week/2026-W37.md", "m2"), "- [-] 4 6b Rollback path passes tests   @O2 ^m2");
    assert_eq!(tm.events(), vec!["demote".to_string()]);
}

/// Gap 32's guard, in the shipped binary: a tab is a word character to the
/// kernel and whitespace to the old Rust tokenizer, so an `est=` written
/// against a tabbed line could land on the wrong token. The kernel refuses
/// the whole edit path by name (`tabbedLine`) instead — kernel/README.md,
/// 2026-09-12 "the five lifecycle verbs" block.
#[test]
fn est_edit_of_a_tabbed_line_is_refused_by_name() {
    let tm = Tm::new();
    let path = tm.plan.join("backlog.md");
    let text = std::fs::read_to_string(&path)
        .expect("read backlog")
        .replace("Insurance claim", "Insurance\tclaim");
    std::fs::write(&path, &text).expect("write backlog");
    let out = tm.run(&["edit", "^a1", "est=45m"]);
    assert_ne!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("tabbedLine"), "{}", out.stderr);
    assert_eq!(std::fs::read_to_string(&path).expect("re-read"), text);
}

/// Kernel-backed verbs demand a loadable tree: a corrupted id **anywhere**
/// refuses the verb by name, even when the verb's own target is a different
/// item in a different file — where the old Rust path edited its one line
/// and left the corruption standing (kernel/README.md, 2026-09-12 block).
/// Two live lines with one id in one file are `dupId`; two live lines with
/// one id in two files are `notADemotion` (the loader tries to read them as
/// a demotion pair and refuses when they are not one).
#[test]
fn a_kernel_backed_verb_refuses_an_unloadable_tree_by_name() {
    for (extra, refusal, target) in [
        ("- [ ] 3 1b A second line claiming a1 ^a1\n", "dupId", "^t1"),
        ("- [ ] 3 1b A second line claiming t1 ^t1\n", "notADemotion", "^a1"),
    ] {
        let tm = Tm::new();
        let path = tm.plan.join("backlog.md");
        let mut text = std::fs::read_to_string(&path).expect("read backlog");
        text.push_str(extra);
        std::fs::write(&path, &text).expect("write backlog");
        let out = tm.run(&["drop", target]);
        assert_ne!(out.code, 0, "{}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains(refusal), "{}", out.stderr);
        assert_eq!(std::fs::read_to_string(&path).expect("re-read"), text);
    }
}

/// Every Markdown file of the plan, by path — what a refused verb must leave
/// byte-identical.
fn plan_md(tm: &Tm) -> std::collections::BTreeMap<String, String> {
    fn walk(dir: &std::path::Path, prefix: &str, out: &mut std::collections::BTreeMap<String, String>) {
        let Ok(rd) = std::fs::read_dir(dir) else { return };
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
                out.insert(rel, std::fs::read_to_string(&path).expect("read"));
            }
        }
    }
    let mut out = std::collections::BTreeMap::new();
    walk(&tm.plan, "", &mut out);
    out
}

/// **A typo'd `@parent` refuses a kernel-backed verb by name, and nothing is
/// written** — the owner's D6 (kernel/README.md gap 22, closed at stage 4 final
/// step 3). A parent is read off its line, and a link to an id no line of the
/// tree carries refuses the **whole** tree: here `^m1`'s `@O1` in the week file
/// becomes `@O9`, and `tm drop ^a1` — an item in another file, with a parent
/// of its own that is fine — exits 1 with `itemCheck` / `danglingParent` in the
/// error document, and every file and the log are as they were. Stricter than
/// fork-point `tm check`, which reported the `@ghost` and let every other
/// command run; the owner chose it knowingly. A parent cycle (`^m1` under `^t3`,
/// which is under `^m1`) is refused the same way as `parentCycle`. Fixing the
/// line is all it takes: the same verb then runs.
#[test]
fn a_typod_parent_refuses_a_kernel_backed_verb_by_name_and_writes_nothing() {
    for (to, fault) in [("@O9 ^m1", "danglingParent"), ("@t3 ^m1", "parentCycle")] {
        let tm = Tm::new();
        let path = tm.plan.join("week/2026-W37.md");
        let text = std::fs::read_to_string(&path).expect("read week");
        let broken = text.replace("@O1 ^m1", to);
        assert_ne!(broken, text, "the fixture no longer carries `@O1 ^m1`");
        std::fs::write(&path, &broken).expect("write week");
        let before = plan_md(&tm);
        let events = tm.events();

        let out = tm.run(&["--json", "drop", "^a1"]);
        assert_eq!(out.code, 1, "{fault}: {}{}", out.stdout, out.stderr);
        // The automatic close ahead of the verb meets the same tree and prints
        // the same refusal as prose first; the verb's document follows it.
        let at = out.stderr.find("\n{").map(|k| k + 1).unwrap_or(0);
        let doc: serde_json::Value = serde_json::from_str(out.stderr[at..].trim())
            .unwrap_or_else(|e| panic!("{fault}: stderr does not end in a document ({e}): {:?}", out.stderr));
        assert!(
            out.stderr[..at].is_empty() || out.stderr[..at].contains(fault),
            "{fault}: the automatic close's prose does not name the fault: {:?}",
            out.stderr
        );
        assert_eq!(doc["kind"], "kernel", "{doc}");
        assert_eq!(doc["detail"]["refusal"], "itemCheck", "{doc}");
        assert_eq!(doc["detail"]["fault"], fault, "{doc}");
        assert!(doc["message"].as_str().unwrap_or_default().contains(fault), "{doc}");
        assert_eq!(plan_md(&tm), before, "{fault}: a refused verb wrote a file");
        assert_eq!(tm.events(), events, "{fault}: a refused verb logged an event");
        assert!(tm.read("backlog.md").contains("^a1"));
        assert!(!tm.line("backlog.md", "a1").starts_with("- [~]"));

        std::fs::write(&path, &text).expect("restore week");
        let fixed = tm.run(&["drop", "^a1"]);
        assert_eq!(fixed.code, 0, "{fault}, fixed: {}{}", fixed.stdout, fixed.stderr);
        assert!(tm.line("backlog.md", "a1").starts_with("- [~]"));
    }
}

/// **A tree refusal names where to look, and is not printed twice** (W-12,
/// README gap 239).
///
/// The kernel's item invariant is a property of the *whole* tree, so its refusal
/// carries a fault name and no position: on a drive of 20 consecutive commands a
/// single malformed line made almost every verb print
/// `itemCheck — … (fileKindShape)` with no file, no line and no suggestion, once
/// for §6.3's automatic close and once for the verb itself. `tm check` answers
/// exactly that question on the same tree, in milliseconds, so the refusal now
/// says so; and the verb no longer repeats the sentence the close printed two
/// lines above it. The error line stays — a failing command must still say it
/// failed — and `--json` is untouched (the test above reads that document).
#[test]
fn a_tree_refusal_points_at_tm_check_and_is_printed_once() {
    let tm = Tm::new();
    let path = tm.plan.join("week/2026-W37.md");
    let text = std::fs::read_to_string(&path).expect("read week");
    let broken = text.replace("@O1 ^m1", "@O9 ^m1");
    assert_ne!(broken, text, "the fixture no longer carries `@O1 ^m1`");
    std::fs::write(&path, &broken).expect("write week");

    // A Monday after the week: §6.3's automatic close runs ahead of the verb,
    // meets the same tree and is refused first.
    let out = tm.run_at("2026-09-14T09:00:00-05:00", &["drop", "^a1"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("run `tm check`"),
        "the refusal does not say where to look: {:?}",
        out.stderr
    );
    assert_eq!(
        out.stderr.matches("the tree fails the kernel's item invariant").count(),
        1,
        "the same refusal is printed more than once: {:?}",
        out.stderr
    );
    assert!(
        out.stderr.contains("the automatic close (\u{a7}6.3) was refused"),
        "the close's own refusal is gone: {:?}",
        out.stderr
    );
    assert!(
        out.stderr.contains("this command's too"),
        "the verb printed no failure line of its own: {:?}",
        out.stderr
    );

    // And `tm check` does answer it: the file and the line.
    let check = tm.run_at("2026-09-14T09:00:00-05:00", &["check"]);
    assert!(
        check.stdout.contains("week/2026-W37.md:") || check.stderr.contains("week/2026-W37.md:"),
        "`tm check` does not name the file and line: {:?}{:?}",
        check.stdout,
        check.stderr
    );
}

/// **A refused tree is not written by the housekeeping ahead of the verb
/// either** — kernel/README.md "Stage 4 final, repair", defect 1. The test
/// above runs at [`cli_common::NOW`], before `^a4`'s `on-event:reply/7d`
/// timeout has elapsed, so §5.1's timeout never tried to write. Here it has,
/// by both roads into it: (a) on the Monday after the week, where the
/// automatic close runs first and is refused, and (b) on a day whose close
/// has already run, where the timeout alone meets the tree and checks it with
/// the kernel first. Before the repair both rewrote `^a4` to `[ ]` and created
/// the log, and then the verb refused saying nothing was written. Now every
/// Markdown file and the log are as they were, stderr names the fault, and
/// fixing the link lets the same verb run — with the timeout applied.
#[test]
fn a_typod_parent_refuses_a_verb_after_a_waiting_timeout_and_writes_nothing() {
    for (road, at) in [("auto close refused", "2026-09-14T09:00:00-05:00"), ("timeout alone", "2026-09-07T10:00:00-05:00")] {
        let tm = Tm::new();
        if road == "timeout alone" {
            // The day's close runs here, on a sound tree; nothing is due at `at`.
            let first = tm.run(&["now"]);
            assert_eq!(first.code, 0, "{road}: {}{}", first.stdout, first.stderr);
            let backlog = tm.read("backlog.md");
            let aged = backlog.replace("waiting:2026-09-05", "waiting:2026-08-01");
            assert_ne!(aged, backlog, "the fixture no longer carries `waiting:2026-09-05`");
            std::fs::write(tm.plan.join("backlog.md"), aged).expect("write backlog");
        }
        let path = tm.plan.join("week/2026-W37.md");
        let text = std::fs::read_to_string(&path).expect("read week");
        let broken = text.replace("@O1 ^m1", "@O9 ^m1");
        assert_ne!(broken, text, "the fixture no longer carries `@O1 ^m1`");
        std::fs::write(&path, &broken).expect("write week");
        assert!(tm.line("backlog.md", "a4").starts_with("- [?]"));
        let before = plan_md(&tm);
        let events = tm.events();
        let log_existed = tm.exists(".tm/log.jsonl");

        let out = tm.run_at(at, &["drop", "^a1"]);
        assert_eq!(out.code, 1, "{road}: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("danglingParent"), "{road}: {}", out.stderr);
        if road == "timeout alone" {
            assert!(out.stderr.contains("waiting timeouts (§5.1) were not applied"), "{road}: {}", out.stderr);
        }
        assert_eq!(plan_md(&tm), before, "{road}: a refused tree was written");
        assert_eq!(tm.events(), events, "{road}: a refused tree was logged");
        assert_eq!(tm.exists(".tm/log.jsonl"), log_existed, "{road}: the log was created");
        assert!(tm.line("backlog.md", "a4").starts_with("- [?]"), "{road}");

        std::fs::write(&path, &text).expect("restore week");
        let fixed = tm.run_at(at, &["drop", "^a1"]);
        assert_eq!(fixed.code, 0, "{road}, fixed: {}{}", fixed.stdout, fixed.stderr);
        assert!(tm.line("backlog.md", "a1").starts_with("- [~]"), "{road}");
        assert!(tm.line("backlog.md", "a4").starts_with("- [ ]"), "{road}: the timeout did not run");
    }
}

/// **`tm add` refuses a line whose `@parent` names no item, on both of its
/// paths, and writes nothing** — the owner's D6. The kernel-backed add would
/// refuse the title by its post-state check; the carve-outs (`--section`, a
/// series-last file, an explicit `^id`) write without the kernel, and before
/// this step they wrote the line and exited 0, leaving a tree every
/// kernel-backed verb then refused `danglingParent` (driven at `6c2dacb`'s
/// successor, kernel/README.md "Stage 4 final", step 3). A parent that resolves
/// is written on both paths.
#[test]
fn add_refuses_a_dangling_parent_on_both_paths_and_writes_nothing() {
    for section in [None, Some("Tasks")] {
        let tm = Tm::new();
        let before = plan_md(&tm);
        let mut args = vec!["add", "3 1b Subtask of nothing @O9", "--to", "week/2026-W37.md"];
        if let Some(s) = section {
            args.extend(["--section", s]);
        }
        let out = tm.run(&args);
        assert_eq!(out.code, 1, "{section:?}: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("danglingParent"), "{section:?}: {}", out.stderr);
        assert!(out.stderr.contains("@O9"), "{section:?}: {}", out.stderr);
        assert_eq!(plan_md(&tm), before, "{section:?}: a refused add wrote a file");

        let mut args = vec!["add", "3 1b Subtask of the midterm @x1", "--to", "week/2026-W37.md"];
        if let Some(s) = section {
            args.extend(["--section", s]);
        }
        let ok = tm.run(&args);
        assert_eq!(ok.code, 0, "{section:?}: {}{}", ok.stdout, ok.stderr);
        assert!(tm.read("week/2026-W37.md").contains("Subtask of the midterm @x1 ^"));
        let later = tm.run(&["drop", "^a1"]);
        assert_eq!(later.code, 0, "{section:?}: {}{}", later.stdout, later.stderr);
    }
}

#[test]
fn drop_marks_the_line_dropped() {
    let tm = Tm::new();
    let json = tm.json(&["drop", "^m4"]);
    assert!(json["line"].as_str().unwrap_or_default().starts_with("- [~]"));
    assert!(tm.line("week/2026-W37.md", "m4").starts_with("- [~]"));
    // A line that already carries an id gains nothing: D33's token is only for
    // the line that had none.
    assert!(json.get("assigned").is_none(), "{json}");
    let last = tm.last();
    assert_eq!(last["ev"], "drop");
    assert_eq!(last["id"], "m4");
    insta::assert_json_snapshot!("drop_json", json);
}

/// **Boxing a title-keyed line writes its `^id`** — the owner's **D33**, gap
/// 477 closed.
///
/// `tm drop lunch` wrote `- [~] lunch …` on a `routines.md` line that carries
/// no `^id`, and D31's grammar refuses exactly that shape (`PErr.noId`, cheat
/// 174) — so one documented one-word command bricked every kernel-backed verb
/// on the tree: `tm check` called it clean and `tm plan`, `tm now` and
/// `tm move` all answered `badLine`. Pre-existing, byte-identical at `d2c0aa6`.
///
/// D33 follows D31 rather than bending it: a boxed line is a **tracked** item
/// and a tracked item needs an id that survives the user editing its title, so
/// the host writes the id — visibly, in the answer — and cheat 174 stays.
#[test]
fn dropping_a_title_keyed_line_writes_its_id_and_the_tree_still_loads() {
    for (file, title) in [
        ("routines.md", "lunch"),
        ("inbox.md", "ask Kun about the dinner place"),
    ] {
        let tm = Tm::new();
        let before = tm.read(file);
        assert!(
            before.lines().any(|l| l.trim_start().starts_with("- ") && l.contains(title)
                && !l.contains(" ^")),
            "{file} has no title-keyed `{title}` line to drop"
        );

        let json = tm.json(&["drop", title]);
        let id = json["assigned"].as_str().expect("D33 writes an id").to_string();
        assert_eq!(json["id"], id, "the answer names the id it wrote: {json}");
        let line = json["line"].as_str().unwrap_or_default();
        assert!(line.starts_with("- [~]"), "{line}");
        assert!(line.ends_with(&format!("^{id}")), "{line}");

        // Written on the line itself, and on **only** that line: the other
        // id-less lines of the same file are untouched (`--fix-ids` still
        // assigns nothing in these files).
        let after = tm.read(file);
        assert_eq!(
            after.lines().filter(|l| l.contains(" ^")).count(),
            before.lines().filter(|l| l.contains(" ^")).count() + 1,
            "{after}"
        );

        // The whole point: the tree the host just wrote is one the kernel can
        // read. `tm check` is clean and a kernel-backed verb answers.
        let check = tm.run(&["check"]);
        assert_eq!(check.code, 0, "{}{}", check.stdout, check.stderr);
        assert!(check.stdout.contains("no problems"), "{}", check.stdout);
        tm.ok(&["plan"]);

        // And `tm undo` takes the token back off with the box it was written
        // for — the id is part of the drop, not a separate edit.
        tm.ok(&["undo"]);
        assert_eq!(tm.read(file), before);
    }
}

/// **`tm edit <title> state=…` writes the `^id` too** — the same D33, the half
/// `tm drop`'s repair left behind (W-16 repair, **gap 575**).
///
/// D33 is a rule about **boxing**, not about `drop`: `ItemLine::set_state`
/// inserts a box after the bullet on a `routines.md` line exactly as
/// `horizon::drop_item` does, and all six state values reach it. Before this,
/// `tm edit lunch 'state=[ ]'` printed the boxed line, exited **0**, and left a
/// tree where `tm check` exits 2 (`badLine … PErr.noId`) and `tm plan`,
/// `tm now` and `tm review day` exit 1 — a command that bricks the tree it just
/// wrote.
///
/// The ledger recorded the opposite as a **driven measurement** (*"no `state`
/// value the edit accepts writes a box"*), which is the W-15 lesson repeating:
/// a user-visibility claim written without driving the path.
#[test]
fn boxing_a_title_keyed_line_through_edit_writes_its_id_and_the_tree_still_loads() {
    for state in ["[ ]", "[x]", "[~]", "[>]", "[?]", "[-]"] {
        let tm = Tm::new();
        let before = tm.read("routines.md");
        assert!(before.lines().any(|l| l.contains("lunch") && !l.contains(" ^")));

        let json = tm.json(&["edit", "lunch", &format!("state={state}")]);
        let id = json["assigned"].as_str().expect("D33 writes an id").to_string();
        assert_eq!(json["id"], id, "{state}: {json}");
        let line = json["line"].as_str().unwrap_or_default();
        assert!(line.starts_with(&format!("- {state}")), "{state}: {line}");
        assert!(line.ends_with(&format!("^{id}")), "{state}: {line}");

        // One new id, on that line only.
        let after = tm.read("routines.md");
        assert_eq!(
            after.lines().filter(|l| l.contains(" ^")).count(),
            before.lines().filter(|l| l.contains(" ^")).count() + 1,
            "{state}: {after}"
        );

        // The tree the host just wrote is one the kernel reads.
        let check = tm.run(&["check"]);
        assert_eq!(check.code, 0, "{state}: {}{}", check.stdout, check.stderr);
        tm.ok(&["now"]);

        // `tm undo` takes the token back off with the box it was written for.
        tm.ok(&["undo"]);
        assert_eq!(tm.read("routines.md"), before, "{state}");
    }
}

/// An edit that boxes nothing writes no id and its `--json` shape does not
/// move: `assigned` is absent, not `null`.
#[test]
fn an_edit_that_boxes_nothing_writes_no_id() {
    let tm = Tm::new();
    // A dated line that already carries a box and an id.
    let json = tm.json(&["edit", "^d1", "ci=3"]);
    assert!(json.get("assigned").is_none(), "{json}");
    // A `routines.md` line whose edit touches no state.
    let json = tm.json(&["edit", "lunch", "ci=2"]);
    assert!(json.get("assigned").is_none(), "{json}");
    assert!(!tm.read("routines.md").lines().any(|l| l.contains("lunch") && l.contains(" ^")));
}

/// **A title that names two lines is refused, never resolved to the first** —
/// W-16 repair, **gap 576**, and the host half of the owner's **D32**.
///
/// D31 keys a box-less, id-less line by its **title**, so two `- laundry …`
/// lines are two lines with one address. `Tree` gives the key to the first and
/// keys the second `file:line`, so every verb that looked an argument up got
/// the first one silently: `tm drop laundry` rewrote `routines.md:7`, wrote an
/// `^id` on it and **exited 0** on a tree the kernel refuses whole (`dupId`,
/// naming both lines), and `tm edit laundry ci=3` did the same. That is
/// disambiguate-by-occurrence, which D32 **declined**, and AGENTS §5.6's "the
/// loader never picks between two readings" applied to the host.
///
/// Every verb that addresses an item by name is driven here, including the
/// three that look the argument up in `self.tree` directly rather than through
/// `Ctx::item` (`done`, `skip`, `routine done`) — a grep would have missed
/// those, which is the lesson W-15 paid for.
#[test]
fn an_ambiguous_title_is_refused_by_every_verb_and_nothing_is_written() {
    let verbs: &[&[&str]] = &[
        &["drop", "laundry"],
        &["edit", "laundry", "ci=3"],
        &["edit", "laundry", "state=[ ]"],
        &["move", "laundry", "week"],
        &["rank", "laundry", "1"],
        &["demote", "laundry"],
        &["readopt", "laundry"],
        &["start", "laundry"],
        &["event", "ping", "laundry"],
        &["done", "laundry"],
        &["skip", "laundry"],
        &["routine", "done", "laundry"],
    ];
    for args in verbs {
        let tm = Tm::new();
        let path = tm.plan.join("routines.md");
        let doubled = format!("{}- laundry    win:09:00-21:00 dur:30m every:week on-miss:persist\n", tm.read("routines.md"));
        fs::write(&path, &doubled).expect("write routines.md");

        let out = tm.run(args);
        assert_eq!(out.code, 1, "{args:?} did not refuse: {}{}", out.stdout, out.stderr);
        // Both placements are named, the way the kernel's own `dupId` names
        // them, and the key is printed bare — a title key is never written into
        // a file, so `^laundry` would be a token to grep for that does not
        // exist.
        assert!(out.stderr.contains("routines.md:7"), "{args:?}: {}", out.stderr);
        assert!(out.stderr.contains("routines.md:9"), "{args:?}: {}", out.stderr);
        assert!(out.stderr.contains("`laundry`"), "{args:?}: {}", out.stderr);
        assert!(!out.stderr.contains("^laundry"), "{args:?}: {}", out.stderr);
        // Nothing written: not the plan file, and not the log either.
        assert_eq!(tm.read("routines.md"), doubled, "{args:?} wrote the plan file");
        assert!(tm.log().is_empty(), "{args:?} appended to the log: {:?}", tm.log());
    }
}

/// **RESTATED under the owner's D35** (gap 584), and the old assertion is
/// refuted rather than deleted.
///
/// As written at the W-16 repair this said: *"the refusal is about **this**
/// key: an unambiguous title on the same tree still works, so the guard is not
/// a blanket refusal of a tree with any duplicate in it"*, and asserted
/// `tm drop groceries` **exits 0** on the collision tree. That is now **false**,
/// deliberately: D35 makes every write path ask the kernel whether the tree
/// still loads, and a tree holding a title collision does not load — so
/// `tm drop groceries` refuses too, and refuses with the *tree's* sentence.
/// Writing to a tree every reading verb refuses is exactly what D35 stopped.
///
/// The property the old assertion was protecting is real and is kept, in the
/// form that still bites: **which refusal fires.** `Ctx::refuse_ambiguous_title`
/// is about *which line an argument names* and runs first, on the argument;
/// the gate is about *the tree* and runs after. So the two verbs below must
/// fail for two different reasons, and a guard that had become a blanket
/// refusal of any tree with a duplicate in it would give both the same one.
#[test]
fn an_unambiguous_title_is_refused_by_the_tree_and_not_by_the_key() {
    let tm = Tm::new();
    let path = tm.plan.join("routines.md");
    let doubled = format!("{}- laundry    win:09:00-21:00 dur:30m every:week on-miss:persist\n", tm.read("routines.md"));
    fs::write(&path, &doubled).expect("write routines.md");

    // The unambiguous key: the gate refuses, naming the *other* two lines.
    let out = tm.run(&["drop", "groceries"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("dupId"), "{}", out.stderr);
    assert!(out.stderr.contains("routines.md:7"), "{}", out.stderr);
    assert!(out.stderr.contains("routines.md:9"), "{}", out.stderr);
    assert!(!out.stderr.contains("groceries"), "the key guard fired on an unambiguous key: {}", out.stderr);

    // The ambiguous key: the argument guard refuses first, naming the key.
    let out = tm.run(&["drop", "laundry"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("`laundry`"), "{}", out.stderr);
    assert!(out.stderr.contains("names 2 lines"), "the key guard did not fire: {}", out.stderr);

    // And neither wrote.
    assert_eq!(tm.read("routines.md"), doubled);
    assert!(tm.log().is_empty(), "{:?}", tm.log());
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

// ---------------------------------------------------------------------------
// The bridge's newline convention, pinned at the byte level (the 2026-09-12
// drive-verification defect: a kernel-path append into a newline-terminated
// file landed after the trailing empty split segment — `…^p1\n\n- [ ] … ^a1`
// with no final newline). These four tests are full-file byte compares, not
// contains-checks: they fail on one wrong byte at either end of the file.
// The convention itself is recorded on `tm/src/cli/kernel_bridge.rs`'s
// module docs (and kernel/README.md's 2026-09-12 block).
// ---------------------------------------------------------------------------

/// (a) `move` into a newline-terminated file: exactly one `\n` between the
/// old last line and the appended line, the file still ends `\n`, the source
/// file is the same bytes minus the moved line — and (d) every file the verb
/// did not change is byte-identical, not just similar.
#[test]
fn move_appends_newline_faithfully_full_byte_compare() {
    let tm = Tm::new();
    let week_before = tm.read("week/2026-W37.md");
    let backlog_before = tm.read("backlog.md");
    assert!(week_before.ends_with('\n'), "fixture week file is newline-terminated");
    assert!(backlog_before.ends_with('\n'), "fixture backlog is newline-terminated");
    let moved_line = backlog_before
        .lines()
        .find(|l| l.ends_with("^a1"))
        .expect("^a1 in backlog")
        .to_string();
    let untouched = [
        "month/2026-09.md",
        "day/2026-09-07.md",
        "calendar/2026-W37.md",
        "inbox.md",
        "optional.md",
        "routines.md",
    ];
    let untouched_before: Vec<String> = untouched.iter().map(|p| tm.read(p)).collect();

    tm.ok(&["move", "^a1", "week"]);

    assert_eq!(
        tm.read("week/2026-W37.md"),
        format!("{week_before}{moved_line}\n"),
        "the appended line follows the old last line after exactly one newline, \
         and the file keeps its final newline"
    );
    assert_eq!(
        tm.read("backlog.md"),
        backlog_before.replace(&format!("{moved_line}\n"), ""),
        "the source file is the original bytes minus the moved line"
    );
    for (p, before) in untouched.iter().zip(&untouched_before) {
        assert_eq!(&tm.read(p), before, "{p} was not part of the move and must not change");
    }
}

/// (b) kernel-path `add --to week`: the file grows exactly the rendered line
/// plus one final newline, byte for byte.
#[test]
fn add_appends_newline_faithfully_full_byte_compare() {
    let tm = Tm::new();
    let before = tm.read("week/2026-W37.md");
    assert!(before.ends_with('\n'), "fixture week file is newline-terminated");
    let json = tm.json(&["add", "4 2b Write the release notes", "--to", "week"]);
    let id = json["id"].as_str().expect("an id");
    assert_eq!(
        tm.read("week/2026-W37.md"),
        format!("{before}- [ ] 4 2b Write the release notes ^{id}\n")
    );
}

/// (c) the recorded convention for a source file that does NOT end in a
/// newline (kernel_bridge module docs): untouched, it is never written and
/// stays byte-identical — missing EOF newline included; rewritten, it comes
/// back newline-terminated (normalized to the POSIX text-file shape).
#[test]
fn a_file_without_a_final_newline_follows_the_recorded_convention() {
    let tm = Tm::new();
    let week_path = tm.plan.join("week/2026-W37.md");
    let stripped = tm
        .read("week/2026-W37.md")
        .strip_suffix('\n')
        .expect("fixture ends with a newline")
        .to_string();
    std::fs::write(&week_path, &stripped).expect("strip the final newline");

    // A kernel-backed verb that changes only backlog.md: the week file is
    // untouched and must keep its exact bytes, missing final newline and all
    // (the write-changed-docs-only rule, asserted at the byte level).
    tm.ok(&["edit", "^a1", "ci=4"]);
    assert_eq!(
        tm.read("week/2026-W37.md"),
        stripped,
        "an untouched file is never rewritten, so its missing final newline survives"
    );

    // A verb that rewrites it: the appended line still lands after exactly
    // one newline, and the rewritten file is newline-terminated.
    let moved_line = tm
        .read("backlog.md")
        .lines()
        .find(|l| l.ends_with("^a1"))
        .expect("^a1 in backlog")
        .to_string();
    tm.ok(&["move", "^a1", "week"]);
    assert_eq!(
        tm.read("week/2026-W37.md"),
        format!("{stripped}\n{moved_line}\n"),
        "a rewritten file is normalized to newline-terminated"
    );
}

// ---------------------------------------------------------------------------
// W-22 track A — README gap 991, REFUTED as written, and the sentence it
// should have been about.
//
// The gap says `tm drop` resolves a ROUTINE title where `tm edit` does not,
// and quotes `tm edit laundry state=[x]` answering "no such item: ^laundry".
// It does not reproduce: on a FRESH tree both verbs resolve the title and both
// exit 0. The refusal the gap quotes comes from running `edit` AFTER `drop`
// has already written an `^id` onto the line — at which point D31's title key
// is gone and BOTH verbs refuse it. The two verbs agree in both directions;
// what the transcript compared was a pre-drop `drop` with a post-drop `edit`.
//
// What is real, and both verbs do it identically, is that boxing a routine
// line converts it into a tracked item: it loses its title address and its
// recurrence, and `tm check` says "no problems". That is what the one boxing
// notice now says, in one spelling (AGENTS §5.3) — and these are the first
// tests to pin either sentence.

/// The `^id` a boxing verb wrote onto `routines.md`'s `laundry` line.
fn boxed_routine_id(tm: &Tm) -> String {
    tm.read("routines.md")
        .lines()
        .find(|l| l.contains("laundry"))
        .and_then(|l| l.rsplit(" ^").next().map(|s| s.trim().to_string()))
        .unwrap_or_else(|| panic!("no boxed laundry line: {}", tm.read("routines.md")))
}

#[test]
fn drop_and_edit_agree_about_a_routine_title_in_both_directions() {
    // Direction 1: on a fresh tree, a routine title is an address for both.
    let by_drop = Tm::new();
    by_drop.ok(&["drop", "laundry"]);
    let by_edit = Tm::new();
    by_edit.ok(&["edit", "laundry", "state=[x]"]);
    let by_field = Tm::new();
    by_field.ok(&["edit", "laundry", "ci=3"]);

    // Direction 2: once the line carries an `^id`, it is an address for
    // neither — which is D31 working, not two verbs disagreeing.
    for tm in [&by_drop, &by_edit] {
        for args in [
            &["drop", "laundry"][..],
            &["edit", "laundry", "ci=3"][..],
        ] {
            let out = tm.run(args);
            assert_eq!(out.code, 1, "{args:?}: {}{}", out.stdout, out.stderr);
            assert!(
                out.stderr.contains("no such item: ^laundry"),
                "{args:?}: {}",
                out.stderr
            );
        }
        // And the routine verbs answer the same way, in their own words.
        let out = tm.run(&["routine", "done", "laundry"]);
        assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("no such routine: laundry"), "{}", out.stderr);
    }

    // `edit laundry ci=3` writes a key, not a box, so it assigns no id and the
    // title still addresses it — the control that keeps the two directions
    // from being one.
    by_field.ok(&["drop", "laundry"]);
}

#[test]
fn boxing_a_routine_says_the_title_is_gone_and_the_recurrence_with_it() {
    for args in [
        &["drop", "laundry"][..],
        &["edit", "laundry", "state=[x]"][..],
    ] {
        let tm = Tm::new();
        let out = tm.ok(args);
        let id = boxed_routine_id(&tm);
        // One sentence, whichever verb typed it.
        assert!(
            out.stdout.contains(&format!(
                "a state box makes it a tracked item, so ^{id} was written on the line, and \
                 `laundry` addressed it only while it carried no `^id` (D31)"
            )),
            "{args:?}: {}",
            out.stdout
        );
        assert!(
            out.stdout.contains("a routine line with a box does not recur"),
            "{args:?}: {}",
            out.stdout
        );
        // And the sentence is true: the plan stops scheduling it.
        let before = Tm::new();
        assert!(
            before.ok(&["plan"]).stdout.contains("laundry"),
            "the fixture does not schedule laundry, so this test measures nothing"
        );
        assert!(
            !tm.ok(&["plan"]).stdout.contains("laundry"),
            "{args:?}: the plan still schedules a boxed routine: {}",
            tm.ok(&["plan"]).stdout
        );
    }
}

#[test]
fn boxing_a_line_that_does_not_recur_says_only_what_happened_to_it() {
    // `optional.md` has no recurrence, so the clause that names `tm routine
    // done` must not appear — the note is keyed on the file, not on the box.
    let tm = Tm::new();
    let out = tm.ok(&["drop", "Severance S3E4"]);
    assert!(
        out.stdout.contains("`Severance S3E4` addressed it only while it carried no `^id`"),
        "{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("does not recur"),
        "an optional line was told it stopped recurring: {}",
        out.stdout
    );
}

#[test]
fn dropping_by_id_says_nothing_about_boxing() {
    // The other direction (AGENTS §5.8): a line that already has an `^id`
    // gains no note at all.
    let tm = Tm::new();
    let out = tm.ok(&["drop", "^m4"]);
    assert_eq!(out.stdout.trim(), "dropped ^m4", "{}", out.stdout);
}
