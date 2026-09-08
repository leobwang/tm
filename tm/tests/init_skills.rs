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

/// Every backticked field name in a skill's **prose** is a field one of the
/// documents that skill runs actually carries.
///
/// The `→` declarations were checked above; the prose was not, and it had
/// drifted from them: `/review-day` told Claude to read `days[].done`,
/// `leak_min`, `energy_mae` and `energy_bias`, and `/review-week` the same
/// plus `days[].blocks`, four paragraphs below its own list of the fields
/// that exist. Nothing in `tm review … --json` is called any of those, so the
/// numbers could only have been invented.
#[test]
fn every_field_the_prose_quotes_exists_too() {
    let tm = worked_day();
    let mut checked = 0usize;
    for skill in SKILLS {
        let text = tm.read(&format!(".claude/skills/{skill}/SKILL.md"));
        // The documents this skill actually reads.
        let mut docs: Vec<(String, Value)> = Vec::new();
        let commands = documented(skill, &text)
            .into_iter()
            .map(|d| d.command)
            // A skill may also name a `--json` command inline (`/plan-week`
            // sends you to `tm model --show --json` for the multipliers).
            .chain(inline_commands(&text));
        for command in commands {
            let args = argv(&concrete(&command));
            if !args.iter().any(|a| a == "--json") {
                continue;
            }
            let args: Vec<&str> = args.iter().map(String::as_str).collect();
            let out = tm.run_at(EVENING, &args);
            assert_eq!(out.code, 0, "{skill}: `{command}` exits {}", out.code);
            docs.push((command, out.json()));
        }
        if docs.is_empty() {
            continue; // `/capture` reads nothing
        }
        for name in prose_fields(&text) {
            assert!(
                docs.iter()
                    .any(|(_, doc)| resolve(doc, &name).is_some() || has_key(doc, &name)),
                "{skill}'s prose quotes `{name}`, which none of the documents \
                 it runs ({}) carries",
                docs.iter()
                    .map(|(c, _)| c.as_str())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            checked += 1;
        }
    }
    assert!(checked > 20, "only {checked} prose fields were checked");
}

/// Backticked `tm … --json` commands in the prose — a skill may point at a
/// document without putting it in its "Run" block.
fn inline_commands(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut fenced = false;
    for line in text.lines() {
        if line.starts_with("```") {
            fenced = !fenced;
            continue;
        }
        if fenced {
            continue;
        }
        for token in line.split('`').skip(1).step_by(2) {
            if token.starts_with("tm ") && token.contains("--json") {
                out.push(token.to_string());
            }
        }
    }
    out
}

/// The backticked names in `text` outside fenced blocks that are meant to be
/// `--json` fields: a dotted/indexed path under one of the document roots
/// (`review.leak.total_min`, `days[].total`), or a bare `snake_case` metric
/// (`budget_blocks`, `a_capacity_lost`). Prose about the *files* (`est:`,
/// `backlog.md`, `week.plan_ratio` — a config key) is not a field claim.
fn prose_fields(text: &str) -> BTreeSet<String> {
    const ROOTS: &[&str] = &[
        "review",
        "diagnostics",
        "model",
        "comparison",
        "segments",
        "priorities",
        "days",
        "lines",
        "diff",
    ];
    let mut out = BTreeSet::new();
    let mut fenced = false;
    for line in text.lines() {
        if line.starts_with("```") {
            fenced = !fenced;
            continue;
        }
        if fenced {
            continue;
        }
        for token in line.split('`').skip(1).step_by(2) {
            let name = token.trim();
            if name.is_empty()
                || !name.chars().all(|c| {
                    c.is_ascii_lowercase() || c.is_ascii_digit() || "._[]".contains(c)
                })
            {
                continue;
            }
            let root = name.split(['.', '[']).next().unwrap_or_default();
            let dotted = name.contains('.') && ROOTS.contains(&root);
            let bare = !name.contains('.') && !name.contains('[') && name.contains('_');
            if dotted || bare {
                out.insert(name.to_string());
            }
        }
    }
    out
}

/// Whether `key` — a bare field name — appears anywhere in the document.
fn has_key(doc: &Value, key: &str) -> bool {
    match doc {
        Value::Object(map) => {
            map.contains_key(key) || map.values().any(|v| has_key(v, key))
        }
        Value::Array(items) => items.iter().any(|v| has_key(v, key)),
        _ => false,
    }
}
