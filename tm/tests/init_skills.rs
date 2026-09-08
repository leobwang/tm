//! What the generated skills tell Claude to do, run against the real binary
//! (tm-spec-v1.md §14's skill table; §17 M9).
//!
//! A `SKILL.md` is executable documentation: every fenced line that starts a
//! `tm` command is a command Claude will run verbatim, and every field named
//! after a `→` is a field it will quote. Both are checked here against the
//! CLI itself, so a skill cannot document a command the parser rejects (the
//! `tm add "- [ ] …"` form did exactly that) or a number `--json` never
//! emits.

mod cli_common;

use std::collections::BTreeSet;

use cli_common::Tm;
use serde_json::Value;

/// §14's skills, in table order.
const SKILLS: &[&str] = &[
    "plan-week",
    "plan-month",
    "triage",
    "capture",
    "replan",
    "review-day",
    "review-week",
    "explain",
];

/// Late enough on Monday 2026-09-07 that [`worked_day`]'s events are past.
const EVENING: &str = "2026-09-07T18:00:00-05:00";

/// One command a skill documents, with the JSON fields it promises.
#[derive(Debug)]
struct Documented {
    /// The skill that documents it.
    skill: String,
    /// The command, as written (placeholders included).
    command: String,
    /// The `→ a b c` field paths, if the line declares any.
    fields: Vec<String>,
}

/// A fresh §4.3 tree.
fn example_tree() -> Tm {
    let tm = Tm::empty();
    let out = tm.run(&["init", "--example"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    tm
}

/// The same tree after a worked Monday, so `days[]`, `estimates[]` and the
/// energy calibration in a review are not empty.
fn worked_day() -> Tm {
    let tm = example_tree();
    tm.ok_at("2026-09-07T07:00:00-05:00", &["wake"]);
    tm.ok_at("2026-09-07T08:00:00-05:00", &["arrive", "lounge"]);
    tm.ok_at("2026-09-07T09:00:00-05:00", &["energy", "4"]);
    tm.ok_at("2026-09-07T09:05:00-05:00", &["start", "^t1"]);
    tm.ok_at("2026-09-07T10:05:00-05:00", &["done"]);
    tm.ok_at("2026-09-07T10:10:00-05:00", &["idle", "l", "--min", "25"]);
    tm
}

/// Every `tm …` line in a fenced block of `text`.
fn documented(skill: &str, text: &str) -> Vec<Documented> {
    let mut out = Vec::new();
    let mut fenced = false;
    for line in text.lines() {
        if line.starts_with("```") {
            fenced = !fenced;
            continue;
        }
        if !fenced || !line.starts_with("tm ") {
            continue;
        }
        let (command, fields) = match line.split_once('→') {
            Some((c, f)) => (c, f.split_whitespace().map(str::to_string).collect()),
            None => (line, Vec::new()),
        };
        // A trailing `  # …` is a comment for the reader, not an argument.
        let command = match command.find("  #") {
            Some(i) => &command[..i],
            None => command,
        };
        out.push(Documented {
            skill: skill.to_string(),
            command: command.trim().to_string(),
            fields,
        });
    }
    out
}

/// Every command every generated skill documents.
fn all_documented(tm: &Tm) -> Vec<Documented> {
    let mut out = Vec::new();
    for skill in SKILLS {
        let text = tm.read(&format!(".claude/skills/{skill}/SKILL.md"));
        out.extend(documented(skill, &text));
    }
    assert!(out.len() > 10, "no commands were extracted: {out:?}");
    out
}

/// Resolve the `<this week>`-style placeholders against `cli_common::NOW`
/// (Monday 2026-09-07, week 2026-W37).
fn concrete(command: &str) -> String {
    command
        .replace("<next week>", "2026-W38")
        .replace("<this week>", "2026-W37")
        .replace("<next month>", "2026-10")
        .replace("<this month>", "2026-09")
        .replace("<date>", "2026-09-07")
        // `^m2` is the example tree's demoted milestone: an id every verb the
        // skills document (`plan --explain`, `close --drop`) accepts.
        .replace("^id", "^m2")
}

/// Split a command line the way a shell would: `"…"` is one argument.
fn argv(command: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut quoted = false;
    let mut started = false;
    for ch in command.chars() {
        match ch {
            '"' => {
                quoted = !quoted;
                started = true;
            }
            c if c.is_whitespace() && !quoted => {
                if started {
                    out.push(std::mem::take(&mut cur));
                    started = false;
                }
            }
            c => {
                cur.push(c);
                started = true;
            }
        }
    }
    if started {
        out.push(cur);
    }
    assert_eq!(out.first().map(String::as_str), Some("tm"), "{command}");
    out.remove(0);
    out
}

/// The value at `days[].blocks`-style path, if the document really has it.
fn resolve<'a>(doc: &'a Value, path: &str) -> Option<&'a Value> {
    let mut cur = doc;
    for segment in path.split('.') {
        let (key, indexed) = match segment.strip_suffix("[]") {
            Some(key) => (key, true),
            None => (segment, false),
        };
        cur = cur.get(key)?;
        if indexed {
            // An empty array proves nothing about the row's fields, so the
            // fixture must produce at least one.
            cur = cur.as_array()?.first()?;
        }
    }
    Some(cur)
}

#[test]
fn every_documented_command_runs() {
    // The `- [ ] ` prefix regression: `tm add "- [ ] …"` exits 1 with a clap
    // usage error, so a skill that documents it sends Claude into a loop of
    // failing writes. Nothing here is asserted about the prose — only that
    // each command the skills print actually runs.
    let commands: Vec<String> = {
        let tm = example_tree();
        all_documented(&tm)
            .iter()
            .map(|d| format!("{}\t{}", d.skill, d.command))
            .collect()
    };
    let mut adds = 0;
    for entry in &commands {
        let (skill, command) = entry.split_once('\t').expect("skill and command");
        let tm = example_tree();
        let args = argv(&concrete(command));
        let args: Vec<&str> = args.iter().map(String::as_str).collect();
        let out = tm.run(&args);
        assert_eq!(
            out.code, 0,
            "{skill} documents `{command}`, which exits {}: {}{}",
            out.code, out.stdout, out.stderr
        );

        // A documented `tm add` must also leave the tree clean — a flag in
        // the wrong place (§4.1: flags count only after a `@ # ! ^ key:`
        // token) is a `tm check` warning, not an error, so exit 0 alone
        // would not catch it.
        if args.first() == Some(&"add") {
            adds += 1;
            let check = tm.run(&["check", "--json"]);
            let doc: Value = serde_json::from_str(&check.stdout)
                .unwrap_or_else(|e| panic!("check --json ({e}): {}", check.stdout));
            let problems = doc["problems"].as_array().expect("problems");
            assert!(
                problems.is_empty(),
                "{skill}'s `{command}` leaves the tree with problems: {problems:?}"
            );
        }
    }
    assert!(adds >= 4, "the skills document only {adds} `tm add` commands");
}

#[test]
fn every_documented_json_field_exists() {
    // §14 has the review skills turn `--json` into prose; a field that is not
    // in the document is a number Claude would have to invent.
    let tm = worked_day();
    let docs = all_documented(&tm);
    let mut checked = BTreeSet::new();
    for doc in docs.iter().filter(|d| !d.fields.is_empty()) {
        let args = argv(&concrete(&doc.command));
        let args: Vec<&str> = args.iter().map(String::as_str).collect();
        assert!(
            args.contains(&"--json"),
            "{}: `{}` declares fields but is not a --json command",
            doc.skill,
            doc.command
        );
        let out = tm.run_at(EVENING, &args);
        assert_eq!(
            out.code, 0,
            "{}: `{}` exits {}: {}{}",
            doc.skill, doc.command, out.code, out.stdout, out.stderr
        );
        let json = out.json();
        for path in &doc.fields {
            assert!(
                resolve(&json, path).is_some(),
                "{}: `{}` reports no `{}` — the skill would have to invent it\n{}",
                doc.skill,
                doc.command,
                path,
                out.stdout
            );
            checked.insert(format!("{} {path}", doc.command));
        }
    }
    assert!(
        checked.len() > 40,
        "only {} fields were checked",
        checked.len()
    );
}

#[test]
fn the_review_skills_declare_the_fields_they_quote() {
    // The two skills §14 defines as "`tm review … --json` → prose" are the
    // ones that must not free-hand a metric.
    let tm = example_tree();
    for skill in ["review-day", "review-week", "plan-month", "replan", "explain"] {
        let text = tm.read(&format!(".claude/skills/{skill}/SKILL.md"));
        assert!(
            text.contains("<!-- json fields -->"),
            "{skill} quotes numbers without declaring where they come from"
        );
        let declared: Vec<Documented> = documented(skill, &text)
            .into_iter()
            .filter(|d| !d.fields.is_empty())
            .collect();
        assert!(!declared.is_empty(), "{skill} declares no fields");
    }
}
