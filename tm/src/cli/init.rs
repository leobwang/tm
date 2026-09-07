//! `tm init` — the skeleton of tm-spec-v1.md §14 (and §2's layout).
//!
//! # API overview
//!
//! [`run`] writes, into the directory it is given (default `./plan`):
//!
//! * `config.toml` — [`tm_core::config::Config::default_toml`], i.e. §16
//!   verbatim;
//! * `CLAUDE.md` — §14's rules for Claude Code, word for word;
//! * `.claude/skills/<name>/SKILL.md` for each row of §14's skill table
//!   (`plan-week`, `plan-month`, `triage`, `capture`, `replan`, `review-day`,
//!   `review-week`, `explain`);
//! * `.claude/settings.json` — the `PostToolUse` hook that runs `tm check`
//!   after an edit under the plan directory (§14);
//! * `.githooks/pre-commit` — the same check as a git hook (§1.3), plus the
//!   one-line instruction to enable it;
//! * `inbox.md`, `backlog.md`, `routines.md`, `optional.md`, this month's and
//!   this week's file, and `.tm/`.
//!
//! Empty files carry §4.3's examples as HTML comments; `--example` writes the
//! §4.3 tree itself instead. The result passes `tm check` (§17 M9).

use std::fs;
use std::path::{Path, PathBuf};

use serde::Serialize;
use tm_core::config::Config;
use tm_core::model::{Horizon, IsoWeek, YearMonth};
use tm_core::store;

use super::ctx::Globals;
use super::out::{emit, CliError};

/// §14's `plan/CLAUDE.md`, verbatim.
const CLAUDE_MD: &str = r#"# tm — rules for Claude Code
Files: month/ week/ day/ backlog.md routines.md optional.md calendar/ inbox.md. Horizon = file. Rank = line order.
Grammar: `- [ ] <ci 0-5> <est> Title @parent #tag key:value ^id`. Fields: due at win dur pref every after-done on-event on-miss min max after loc est. Flags: open atomic manual travel-day hot.
Always: add items with `tm add "..."` (or write the grammar exactly, then run `tm check`). Read `tm plan --json` before reasoning about today. Use `tm model --show` multipliers when estimating.
Never: edit between `<!-- tm:plan start/end -->`; edit `## Log`; mark blocks done; change an existing item's ci, est, or priority unless asked; reorder `month/` outcomes without confirmation; touch `.tm/`.
Demote, never delete. Explain the diff after `tm plan --diff`.
"#;

/// `.claude/settings.json`: the §14 `PostToolUse` hook.
const SETTINGS_JSON: &str = r#"{
  "hooks": {
    "PostToolUse": [
      {
        "matcher": "Edit|MultiEdit|Write",
        "hooks": [
          {
            "type": "command",
            "command": "tm check"
          }
        ]
      }
    ]
  }
}
"#;

/// `.githooks/pre-commit` (§1.3: `tm check` runs as a pre-commit hook).
const PRE_COMMIT: &str = r#"#!/bin/sh
# tm — validate the plan tree before every commit (tm-spec-v1.md §1.3).
# Enable with:  git config core.hooksPath <this directory>
plan="$(cd "$(dirname "$0")/.." && pwd)"
exec tm check --dir "$plan"
"#;

/// The §14 skills: `(name, description, body)`.
fn skills() -> Vec<(&'static str, &'static str, String)> {
    vec![
        (
            "plan-week",
            "Propose next week's milestones from the month outcomes, the backlog and the capacity grid. Use at the weekly planning conversation.",
            [
                "Read, in this order:",
                "",
                "1. `month/<this month>.md` — the outcomes and everything under `# Demoted`.",
                "2. `backlog.md` — dated items whose due falls in or near the week.",
                "3. `calendar/<week>.md` — the walls the week already has.",
                "4. `tm plan --week --json` — the capacity grid (minutes per day per energy level).",
                "5. `tm review week --json` — last week's blocks, carry-over and calibration.",
                "",
                "Then propose **3–5 milestones** with calibrated estimates (`tm model --show`",
                "gives the duration multipliers; state `est × multiplier`). Pre-select the",
                "demoted items — they already lost a week — and show carry-over and plan",
                "honesty (planned blocks ÷ budget; warn above 1.1).",
                "",
                "Write `week/<next week>.md` **only after the user confirms**. Use `tm add`",
                "for each line, or write the §4.1 grammar exactly and run `tm check`.",
            ]
            .join("\n"),
        ),
        (
            "plan-month",
            "Propose next month's outcomes and the cuts for repeatedly demoted work. Use at the monthly planning conversation.",
            [
                "Read last month's review (`tm review month --json`) and",
                "`month/<last month>.md`.",
                "",
                "Propose outcomes with an explicit priority (`!1`–`!4`; only roots carry one)",
                "and a cut list: anything with **two or more demotion stamps** is a candidate",
                "to cut or re-scope (§11's demotion churn). Say what each cut costs.",
                "",
                "Write `month/<next month>.md` only after the user confirms; carry the rest",
                "with `tm close month` (`--drop ^id` for the cuts).",
            ]
            .join("\n"),
        ),
        (
            "triage",
            "Turn inbox captures into well-formed items. Use when inbox.md has lines waiting.",
            [
                "Run `tm triage --json`: each line comes back with a parse preview.",
                "",
                "For every line decide `ci` (min-energy 0–5), an estimate, a parent (`@id`)",
                "and the file it belongs in (`week/`, `backlog.md`, `routines.md`,",
                "`optional.md`). Ask when the answer is ambiguous rather than guessing.",
                "",
                "Add each item with `tm add \"<line>\" --to <file> [--section <name>]`, then",
                "remove the raw line from `inbox.md`. Finish with `tm check`.",
            ]
            .join("\n"),
        ),
        (
            "capture",
            "Turn one sentence of natural language into a tm item line. Use for quick capture.",
            [
                "Translate the sentence into the §4.1 grammar, then run `tm add`.",
                "",
                "\"pset 2 is due Friday night, six blocks, two a day max\" becomes",
                "`- [ ] 4 6b pset 2 due:2026-09-11T23:59 max:2b/d`.",
                "",
                "Rules: the leading number is `ci`, the second is the estimate (`Nb|Nm|Nh`);",
                "deadlines are `due:`, appointments `at:`, windows `win:` + `dur:`;",
                "recurrence is `every:`, `after-done:` or `on-event:`. Show the line and the",
                "target file, then `tm add \"<line>\" --to <file>`.",
            ]
            .join("\n"),
        ),
        (
            "replan",
            "Replan the day and explain what moved. Use after an interruption, a late start or an estimate change.",
            [
                "Run `tm plan --diff --json`.",
                "",
                "Say in **two sentences** what moved and why: which items shifted, what fell",
                "off the tail, and which constraint caused it (lost minutes, a new wall, a",
                "downgraded energy prediction). Never edit the generated section yourself —",
                "`tm plan` writes it.",
            ]
            .join("\n"),
        ),
        (
            "review-day",
            "Write the day review prose. Use at the end of a day.",
            [
                "Run `tm review day --json`.",
                "",
                "Write a short paragraph into `## Notes` of `day/<date>.md`: what got done,",
                "where the time went (leak and lost minutes), how the estimates held, and one",
                "thing to change tomorrow. Flag repeated demotions and estimate drift.",
                "",
                "Never touch `## Log` or anything between `<!-- tm:… -->` markers.",
            ]
            .join("\n"),
        ),
        (
            "review-week",
            "Write the week review prose. Use at the end of a week.",
            [
                "Run `tm review week --json` (and `tm model --compare` when the log is long",
                "enough).",
                "",
                "Cover: milestones hit and demoted, blocks per day, lounge rate, estimate and",
                "energy calibration, plan honesty. Name every item with two or more demotion",
                "stamps and propose a cut or a re-scope. Write the prose into the week file's",
                "`## Notes`.",
            ]
            .join("\n"),
        ),
        (
            "explain",
            "Explain in plain language why an item sits where it does. Use when a priority is surprising.",
            [
                "Run `tm plan --explain ^id --json`.",
                "",
                "Translate it: what `k` the root gives it, what `u = need / capacity` says",
                "about the deadline, which bin that lands in, which slot it got and why (the",
                "energy filter `ci ≤ slot`), and what would change it — a smaller `est:`, a",
                "later `due:`, or a different rank (line order).",
            ]
            .join("\n"),
        ),
    ]
}

/// The guidance an empty file carries: §4.3's example, commented out.
fn guidance(kind: &str) -> String {
    let body = match kind {
        "inbox" => vec![
            "Capture, untriaged: one thought per line, any wording.",
            "`tm triage` previews each line; /triage turns them into items.",
            "",
            "    pset 2 due friday night, six blocks, two a day max",
        ],
        "backlog" => vec![
            "Horizon = none: finite undated items, far-out dated items, series.",
            "",
            "    # Untied",
            "    - [ ] 2 30m Insurance claim for the bike  ^a1",
            "    - [ ] 1 Pick up package  win:2026-09-07T09:00/21:00 dur:20m ^a3",
            "",
            "    # Dated, far out",
            "    - [ ] 5 10b Workshop paper draft  @O2 due:2026-11-20 #soundcode ^d2",
            "",
            "    ## series:cell-bio",
            "    - [ ] 4 4b Cell Biology vol. 1 ^c1",
            "    - [ ] 4 4b Cell Biology vol. 2 ^c2",
        ],
        "routines" => vec![
            "Open recurring windows. No checkbox: instances live in the log.",
            "Every line has a window (win: + dur:) or after-done:, and ci defaults to 1.",
            "",
            "    - sleep      win:22:00-08:00 dur:8h30m every:day ci:0",
            "    - breakfast  win:06:00-09:00 dur:30m  every:day pref:wake+10m",
            "    - lunch      win:11:30-13:30 dur:30m  every:day",
            "    - workout    win:16:00-19:00 dur:1h   every:Mon,Wed,Fri",
            "    - shower     win:07:00-23:00 dur:20m  after-done:2d~1d",
            "    - laundry    win:09:00-21:00 dur:30m  every:week on-miss:persist",
        ],
        "optional" => vec![
            "Never displaces work: rest slots only, priority 5, ci 0.",
            "",
            "    - Severance S3E4  dur:1h",
            "    - Factorio        dur:2h max:4h/w",
        ],
        _ => vec![],
    };
    let mut out = String::from("<!--\n");
    for line in body {
        out.push_str(line);
        out.push('\n');
    }
    out.push_str("-->\n");
    out
}

/// §4.3's `month/2026-09.md`.
const EX_MONTH: &str = "---\nmonth: 2026-09\n---\n# Outcomes\n\
- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1\n\
- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2\n\
- [ ] 2 !3 Winter course selection + admin done        ^O3\n\n\
# Demoted\n\
- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2\n";

/// §4.3's `week/2026-W37.md`.
const EX_WEEK: &str = "---\nweek: 2026-W37\nwindow: 2026-09-07..2026-09-13\nbudget: 25\nplanned: 20\n---\n\
# Milestones\n\
- [ ] 5 6b Finish ch.5 exercises        @O1 ^m1\n\
- [ ] 4 6b Rollback path passes tests   @O2 ^m2\n\
- [ ] 5 3b Read ch.6                    @O1 ^m3\n\
- [ ] 2 2b Pick winter courses          @O3 ^m4\n\
- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1\n\
- [ ] 5 2h Midterm                      @O3 at:2026-10-20T10:00/12:00 loc:JCL ^x1\n\
- [ ] 5 8b Midterm review               @x1 ^x2\n\n\
# Tasks\n\
- [ ] 5 1b Read ch.6 §1–2               @m3 ^t1\n\
- [>] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3\n\
- [ ] 3 1b Claude Code drafts tests     @m2 ^t4\n\
- [ ] 3 1b Review the drafts            @m2 after:^t4 ^t5\n";

/// §4.3's `backlog.md`.
const EX_BACKLOG: &str = "# Untied\n\
- [ ] 2 30m Insurance claim for the bike  ^a1\n\
- [ ] 1 Pick up package  win:2026-09-07T09:00/21:00 dur:20m ^a3\n\
- [?] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4\n\n\
# Dated, far out\n\
- [ ] 5 10b Workshop paper draft  @O2 due:2026-11-20 #soundcode ^d2\n\n\
## series:cell-bio\n\
- [x] 4 4b Cell Biology vol. 1 ^c1\n\
- [ ] 4 4b Cell Biology vol. 2 ^c2\n\
- [ ] 4 4b Cell Biology vol. 3 ^c3\n";

/// §4.3's `routines.md`.
const EX_ROUTINES: &str = "- sleep      win:22:00-08:00 dur:8h30m every:day ci:0\n\
- breakfast  win:06:00-09:00 dur:30m  every:day pref:wake+10m\n\
- lunch      win:11:30-13:30 dur:30m  every:day\n\
- dinner     win:17:30-19:30 dur:30m  every:day\n\
- workout    win:16:00-19:00 dur:1h   every:Mon,Wed,Fri\n\
- shower     win:07:00-23:00 dur:20m  after-done:2d~1d\n\
- laundry    win:09:00-21:00 dur:30m  every:week on-miss:persist\n\
- groceries  win:10:00-20:00 dur:45m  every:week loc:out\n";

/// §4.3's `optional.md`.
const EX_OPTIONAL: &str = "- Severance S3E4  dur:1h\n- Factorio        dur:2h max:4h/w\n";

/// `tm init --json`.
#[derive(Debug, Serialize)]
pub struct InitOut {
    /// The directory created.
    pub dir: String,
    /// Files written.
    pub created: Vec<String>,
    /// Files that already existed and were left alone.
    pub skipped: Vec<String>,
    /// How to enable the git pre-commit hook (§1.3).
    pub hook_hint: String,
}

/// Write `rel` unless it exists (or `force`).
fn write(
    root: &Path,
    rel: &str,
    text: &str,
    force: bool,
    out: &mut InitOut,
) -> Result<(), CliError> {
    let path = root.join(rel);
    if path.exists() && !force {
        out.skipped.push(rel.to_string());
        return Ok(());
    }
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| CliError::io(parent.display().to_string(), e))?;
    }
    fs::write(&path, text).map_err(|e| CliError::io(path.display().to_string(), e))?;
    out.created.push(rel.to_string());
    Ok(())
}

/// `tm init [dir] [--example]` (§14, §17 M9).
pub fn run(g: &Globals, args: &super::InitArgs) -> Result<i32, CliError> {
    let root: PathBuf = args
        .dir
        .clone()
        .or_else(|| g.dir.clone())
        .unwrap_or_else(|| PathBuf::from("plan"));
    fs::create_dir_all(&root).map_err(|e| CliError::io(root.display().to_string(), e))?;
    fs::create_dir_all(root.join(".tm")).map_err(|e| CliError::io(".tm", e))?;

    let mut out = InitOut {
        dir: root.display().to_string(),
        created: Vec::new(),
        skipped: Vec::new(),
        hook_hint: format!(
            "git config core.hooksPath {}",
            root.join(".githooks").display()
        ),
    };
    let force = args.force;

    write(&root, store::CONFIG_PATH, Config::default_toml(), force, &mut out)?;
    write(&root, "CLAUDE.md", CLAUDE_MD, force, &mut out)?;
    write(&root, ".claude/settings.json", SETTINGS_JSON, force, &mut out)?;
    for (name, description, body) in skills() {
        let text = format!(
            "---\nname: {name}\ndescription: {description}\n---\n\n# /{name}\n\n{body}\n"
        );
        write(
            &root,
            &format!(".claude/skills/{name}/SKILL.md"),
            &text,
            force,
            &mut out,
        )?;
    }
    write(&root, ".githooks/pre-commit", PRE_COMMIT, force, &mut out)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let hook = root.join(".githooks/pre-commit");
        if hook.exists() {
            let mut perms = fs::metadata(&hook)
                .map_err(|e| CliError::io(hook.display().to_string(), e))?
                .permissions();
            perms.set_mode(0o755);
            fs::set_permissions(&hook, perms)
                .map_err(|e| CliError::io(hook.display().to_string(), e))?;
        }
    }

    let now = g
        .now
        .map(|t| t.date_naive())
        .unwrap_or_else(|| chrono::Local::now().date_naive());
    let month = Horizon::Month(YearMonth::from_date(now));
    let week = Horizon::Week(IsoWeek::from_date(now));

    if args.example {
        write(&root, "inbox.md", "", force, &mut out)?;
        write(&root, "backlog.md", EX_BACKLOG, force, &mut out)?;
        write(&root, "routines.md", EX_ROUTINES, force, &mut out)?;
        write(&root, "optional.md", EX_OPTIONAL, force, &mut out)?;
        write(&root, "month/2026-09.md", EX_MONTH, force, &mut out)?;
        write(&root, "week/2026-W37.md", EX_WEEK, force, &mut out)?;
    } else {
        write(&root, "inbox.md", &guidance("inbox"), force, &mut out)?;
        write(&root, "backlog.md", &guidance("backlog"), force, &mut out)?;
        write(&root, "routines.md", &guidance("routines"), force, &mut out)?;
        write(&root, "optional.md", &guidance("optional"), force, &mut out)?;
        write(
            &root,
            &month.path(),
            &store::initial_text(&month),
            force,
            &mut out,
        )?;
        write(
            &root,
            &week.path(),
            &store::initial_text(&week),
            force,
            &mut out,
        )?;
    }

    emit(
        g.json,
        || {
            format!(
                "created {} file(s) in {}\n\
                 enable the pre-commit hook with:\n  {}",
                out.created.len(),
                out.dir,
                out.hook_hint
            )
        },
        &out,
    )?;
    Ok(0)
}
