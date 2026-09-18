//! **A damaged `.tm/log.jsonl`, and what `tm check` says about it** — the
//! owner's D18 (i) and (ii), and design
//! `kernel/design/stage5/stage5-D9-D10-design.md` §14.6's item 7 and two of
//! its nine T9 names.
//!
//! D18 answers OWNER Q9: malformed log lines and lines dated more than two
//! days after `now` are **warnings**, listed with the exit code unchanged;
//! and every verb *except* `tm check` fails by name on `reachTooFar`, which
//! makes `tm check` precisely the verb that must keep working on a damaged
//! log, because it is how the bad line is found.
//!
//! W-6's independent audit drove three damaged trees and found none of that
//! wired: a truncated line and a line of nonsense got `no problems, exit 0`;
//! a line dated 2027 went unmentioned; and **one invalid UTF-8 byte killed
//! every verb, `tm check` included**, with the raw I/O message
//! `stream did not contain valid UTF-8` naming no line at all. These tests
//! are that audit's cases, kept.
//!
//! The UTF-8 half is design §17's parity **P13** — "a log line that is not
//! UTF-8: the kernel warns per line and the verb runs; the fork's
//! `read_to_string` fails the whole command" — answered on the host side,
//! through the same single reader (`Ctx::replay_of` reads bytes and
//! `Log::parse_bytes` splits before decoding). The row's kernel column
//! reached before the switch; the switch still owes everything else.

mod cli_common;

#[allow(dead_code)]
#[path = "support/loggen.rs"]
mod loggen;

use std::fs::OpenOptions;
use std::io::Write;

use cli_common::Tm;

/// `tm/src/cli/kernel_log.rs`'s `CHUNK_LINES`, spelled out rather than
/// imported: a CLI test drives the binary and must not pull a `tm::cli`
/// module into its own crate (`kernel_call_counts.rs` spells out
/// `TM_TRACE_REPLAY_SCOPE` for the same reason). If the constant moves, this
/// test's own assertion that the log spans several chunks is what fails.
const CHUNK_LINES: usize = 4_096;

/// The day after the log's last dated line, as an instant: a `now` that makes
/// no line future-dated, so `tm check`'s D18 (ii) half stays quiet and the
/// line warnings are the only thing under test.
fn day_after(text: &str) -> String {
    let last = text
        .lines()
        .rev()
        .find_map(|l| {
            let v: serde_json::Value = serde_json::from_str(l).ok()?;
            chrono::DateTime::parse_from_rfc3339(v.get("t")?.as_str()?).ok()
        })
        .expect("a dated line");
    format!("{}T12:00:00-05:00", last.date_naive() + chrono::Duration::days(1))
}

/// Append raw bytes to the log, as a hand edit or a torn write would.
fn append_bytes(tm: &Tm, bytes: &[u8]) {
    let path = tm.plan.join(".tm/log.jsonl");
    let mut f = OpenOptions::new().create(true).append(true).open(&path).expect("open the log");
    f.write_all(bytes).expect("append to the log");
}

/// The log's physical line count — the line number the last appended line has.
fn log_lines(tm: &Tm) -> usize {
    let bytes = std::fs::read(tm.plan.join(".tm/log.jsonl")).unwrap_or_default();
    let newlines = bytes.iter().filter(|b| **b == b'\n').count();
    newlines + usize::from(!bytes.is_empty() && !bytes.ends_with(b"\n"))
}

/// Every problem `tm check --json` reported, as `(code, severity, file, line)`.
fn problems(tm: &Tm) -> Vec<(String, String, String, u64)> {
    problems_at(tm, cli_common::NOW)
}

/// [`problems`] at an explicit instant — the stall tests check a tree weeks
/// after the block they are about was opened.
fn problems_at(tm: &Tm, now: &str) -> Vec<(String, String, String, u64)> {
    problems_of(&tm.json_at(now, &["check"]))
}

/// The same, off a `tm check --json` document the caller already has — for the
/// D32 case, where the tree deliberately exits 2 and `Tm::json_at`'s exit-0
/// assertion would fire first.
fn problems_of(doc: &serde_json::Value) -> Vec<(String, String, String, u64)> {
    doc["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .map(|p| {
            (
                p["code"].as_str().unwrap_or_default().to_string(),
                p["severity"].as_str().unwrap_or_default().to_string(),
                p["file"].as_str().unwrap_or_default().to_string(),
                p["line"].as_u64().unwrap_or_default(),
            )
        })
        .collect()
}

/// A tree with a log: one `wake`, one started block.
fn with_a_log() -> Tm {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["start", "^t4", "--energy", "4"]);
    tm
}

/// **T9**: one byte of invalid UTF-8 is one warning at its own line, the exit
/// code does not move, and every verb still runs.
#[test]
fn invalid_utf8_line_is_a_warning_and_tm_check_names_it() {
    let tm = with_a_log();
    let clean = tm.run(&["check"]);
    assert_eq!(clean.code, 0, "{}{}", clean.stdout, clean.stderr);
    assert!(clean.stdout.contains("no problems"), "{}", clean.stdout);

    append_bytes(&tm, b"{\"t\":\"2026-09-07T08:30:00-05:00\",\"ev\":\"note\",\"text\":\"\xff\xfe\"}\n");
    let line = log_lines(&tm) as u64;

    // D18 (i): a warning, the exit code unchanged.
    let out = tm.run(&["check"]);
    assert_eq!(out.code, 0, "the exit code must not move: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains(".tm/log.jsonl"), "{}", out.stdout);
    assert!(out.stdout.contains("log-line"), "{}", out.stdout);
    assert!(out.stdout.contains("invalid UTF-8"), "{}", out.stdout);
    assert!(out.stdout.contains(&format!(":{line}:")), "it names the line: {}", out.stdout);
    assert!(
        problems(&tm).contains(&("log-line".into(), "warning".into(), ".tm/log.jsonl".into(), line)),
        "{:?}",
        problems(&tm)
    );

    // And the point of the whole row: the verbs still run. Every one of these
    // exited 1 with `stream did not contain valid UTF-8` before the repair.
    // Each gets its own damaged tree, so one verb's writes cannot disturb the
    // next one's (`tm plan` rewrites the day file `tm undo` snapshotted).
    for args in [
        vec!["now"],
        vec!["log", "--tail", "3"],
        vec!["plan"],
        vec!["review", "day"],
        vec!["model"],
        vec!["undo"],
        vec!["close", "day"],
    ] {
        let tm = with_a_log();
        append_bytes(&tm, b"{\"t\":\"2026-09-07T08:30:00-05:00\",\"ev\":\"note\",\"text\":\"\xff\xfe\"}\n");
        let out = tm.run_at("2026-09-07T11:00:00-05:00", &args);
        assert_eq!(out.code, 0, "`tm {}`: {}{}", args.join(" "), out.stdout, out.stderr);
        assert!(
            !out.stderr.contains("valid UTF-8"),
            "`tm {}` still dies on the byte: {}",
            args.join(" "),
            out.stderr
        );
    }
}

/// D18 (i)'s other half: a truncated line and a line of nonsense. The audit's
/// first damaged tree, which reported `no problems`.
#[test]
fn a_malformed_line_is_a_warning_and_tm_check_names_it() {
    let tm = with_a_log();
    append_bytes(&tm, b"{\"t\":\"2026-09-07T08:40:00-05:00\",\"ev\":\"wake\"\n");
    let truncated = log_lines(&tm) as u64;
    append_bytes(&tm, b"not json at all\n");
    let nonsense = log_lines(&tm) as u64;

    let out = tm.run(&["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("no problems"), "{}", out.stdout);
    let found = problems(&tm);
    for line in [truncated, nonsense] {
        assert!(
            found.contains(&("log-line".into(), "warning".into(), ".tm/log.jsonl".into(), line)),
            "line {line} is not named: {found:?}"
        );
    }
    // A warning is advice: `tm check`'s exit code is the tree's alone.
    assert_eq!(tm.json(&["check"])["exit_code"], 0);
}

/// **T9**: a line dated next year is named, and it changes nothing about
/// today (D18 (ii)).
#[test]
fn a_line_dated_next_year_changes_nothing_about_today_and_tm_check_names_it() {
    let tm = with_a_log();
    let before = tm.json(&["now"]);

    append_bytes(&tm, b"{\"t\":\"2027-11-30T10:00:00-05:00\",\"ev\":\"wake\",\"slept_min\":400}\n");
    let line = log_lines(&tm) as u64;

    let after = tm.json(&["now"]);
    assert_eq!(before, after, "a line dated next year changed something about today");

    let out = tm.run(&["check"]);
    assert_eq!(out.code, 0, "the exit code must not move: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("log-future"), "{}", out.stdout);
    assert!(out.stdout.contains("2027-11-30"), "{}", out.stdout);
    assert!(
        problems(&tm).contains(&("log-future".into(), "warning".into(), ".tm/log.jsonl".into(), line)),
        "{:?}",
        problems(&tm)
    );

    // Two days after `now` is inside the fence and is not named: the rule is
    // "more than 2 days", and a `tm wake` typed for tomorrow is ordinary.
    let tm = with_a_log();
    append_bytes(&tm, b"{\"t\":\"2026-09-09T06:00:00-05:00\",\"ev\":\"wake\",\"slept_min\":400}\n");
    let codes: Vec<String> = problems(&tm).into_iter().map(|p| p.0).collect();
    assert!(!codes.contains(&"log-future".to_string()), "{codes:?}");
}

/// W-6's audit defect: `tm close <grain> --date <an older ended period>` was
/// accepted, ignored, and reported as a close of the period it really took —
/// and it appended a `close` event for a key already closed. It is now
/// refused by name, and nothing is written.
#[test]
fn a_close_date_naming_a_period_it_does_not_take_is_refused_by_name() {
    // Tuesday 2026-09-15: the last ended day is 2026-09-14, week 2026-W37,
    // month 2026-08.
    const NOW: &str = "2026-09-15T09:00:00-05:00";
    for (grain, date, takes) in [
        ("day", "2026-08-26", "2026-09-14"),
        ("week", "2026-W25", "2026-W37"),
        ("month", "2026-07", "2026-08"),
    ] {
        let tm = Tm::new();
        let out = tm.run_at(NOW, &["close", grain, "--date", date]);
        assert_eq!(out.code, 1, "`tm close {grain} --date {date}`: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("periodNotTaken"), "{}", out.stderr);
        assert!(out.stderr.contains(takes), "it does not name what it takes: {}", out.stderr);
        assert!(!out.stdout.contains("closed"), "it said it closed something: {}", out.stdout);
        assert!(
            !tm.events().contains(&"close".to_string()),
            "a refused close appended a close event: {:?}",
            tm.events()
        );
    }
}

/// The `--date` help says `2026-09-13`, `2026-W37` or `2026-08`, and a
/// calendar date names the period containing it. Before the repair
/// `tm review week --date 2026-06-15` — the spelling the old `<DATE>` help
/// invited — came back `invalid iso-week` and left the ISO-week form to be
/// guessed from the error message.
#[test]
fn review_reads_a_calendar_date_for_a_week_or_a_month() {
    let tm = Tm::new();
    const NOW: &str = "2026-09-15T09:00:00-05:00";

    let by_key = tm.json_at(NOW, &["review", "week", "--date", "2026-W25"]);
    let by_date = tm.json_at(NOW, &["review", "week", "--date", "2026-06-15"]);
    assert_eq!(by_key["key"], "2026-W25");
    assert_eq!(by_date, by_key, "a Monday of W25 must review W25");
    let sunday = tm.json_at(NOW, &["review", "week", "--date", "2026-06-21"]);
    assert_eq!(sunday, by_key, "a Sunday of W25 must review W25");

    let m_key = tm.json_at(NOW, &["review", "month", "--date", "2026-07"]);
    let m_date = tm.json_at(NOW, &["review", "month", "--date", "2026-07-15"]);
    assert_eq!(m_key["key"], "2026-07");
    assert_eq!(m_date, m_key);

    // A value that is neither still fails by the period parser's own name.
    let bad = tm.run_at(NOW, &["review", "week", "--date", "garbage"]);
    assert_eq!(bad.code, 1, "{}{}", bad.stdout, bad.stderr);
    assert!(bad.stderr.contains("iso-week"), "{}", bad.stderr);

    // And the help no longer promises what the parser refuses.
    let help = tm.run(&["review", "--help"]);
    assert!(help.stdout.contains("2026-W37"), "{}", help.stdout);
}

/// **Gap 134**: `tm check` names every unreadable line of a log long enough to
/// span several genesis chunks — including one in the **first** chunk.
///
/// The kernel's `log` answer carries a `warnings` array that is **per call**
/// (`Boundary.logBody` over `logVerdicts`), and `kernel_log::genesis` returns
/// only its **last chunk's** answer. A `tm check` wired to that array would
/// name the final chunk's lines and silently drop every earlier one — at every
/// scope, `All` included. The verb asks the kernel for the lines directly
/// instead (`kernel_log::line_warnings`, a read-only sweep of the whole file
/// in chunks), which is what this test pins: the damage is put in the first
/// chunk, the middle and the last, and all three must be named.
///
/// Before the wiring this test could not fail for the right reason — the
/// in-tree Rust reader reads the whole file in one pass — so its value is that
/// it fails the moment the sweep is replaced by an answer's array.
#[test]
fn tm_check_names_an_unreadable_line_in_every_chunk_of_a_multi_chunk_log() {
    let tm = Tm::new();
    let mut lines = loggen::log(loggen::Rate::SixtyOne, 200);
    assert!(
        lines.len() > 2 * CHUNK_LINES,
        "the log must span more than two chunks, else this test proves nothing: {} lines",
        lines.len()
    );
    // One in the first chunk, one in the middle, one in the last.
    let (early, middle, late) = (10, CHUNK_LINES + 500, lines.len() - 3);
    for i in [early, middle, late] {
        lines[i] = "not json at all".to_string();
    }
    let text = loggen::text(&lines);
    // `plan-basic` has no `.tm/` until a verb writes one; this log is written
    // straight in, so the damaged lines keep the numbering the test asserts.
    std::fs::create_dir_all(tm.plan.join(".tm")).expect("mkdir .tm");
    std::fs::write(tm.plan.join(".tm/log.jsonl"), &text).expect("write the log");
    let now = day_after(&text);

    let out = tm.run_at(&now, &["check"]);
    assert_eq!(out.code, 0, "a damaged log must not move the exit code: {}{}", out.stdout, out.stderr);

    let doc = tm.json_at(&now, &["check"]);
    let named: Vec<u64> = doc["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .filter(|p| p["code"] == "log-line" && p["file"] == ".tm/log.jsonl")
        .map(|p| p["line"].as_u64().expect("a line"))
        .collect();
    assert_eq!(
        named,
        vec![early as u64 + 1, middle as u64 + 1, late as u64 + 1],
        "every damaged line is named, whichever chunk it fell in"
    );
    eprintln!(
        "tm check swept {} lines / {} bytes over {} chunks and named {} lines",
        lines.len(),
        text.len(),
        lines.len().div_ceil(CHUNK_LINES),
        named.len()
    );
}

/// **Gap 119 / design §9.4's "Stalls", §18.7 and design gap 88** — a block
/// left open holds the replay checkpoint's **ledger day** back, and until now
/// `tm check` said `no problems` about it.
///
/// Three runs before the switch found this unreachable and said so honestly:
/// the ledger day is a fact of the kernel's checkpoint, and no verb read one.
/// S made it reachable, so this is the test that can finally fail.
///
/// **Both directions, because the obvious check is a trapdoor** (§5.8). The
/// natural rule — "the ledger day is more than seven days behind `now`" — is
/// true of trees with nothing wrong with them: §9.4 folds only up to
/// `min(T, M) - keepDays`, so `L` trails the log's own last activity, and the
/// **control tree below runs about twelve days behind while perfectly
/// healthy**. It is the open block that must be named, with its age. So this
/// asserts the warning bites on a stall *and* stays silent on a tree that is
/// merely quiet — which is the assertion that would have caught the rule I
/// first wrote.
#[test]
fn a_stalled_ledger_day_is_named_and_a_healthy_one_is_not() {
    const LATE: &str = "2026-10-10T09:00:00-05:00";
    // Days a verb runs on between the stall and the check, so the checkpoint
    // reseals more than once and the ledger day has every chance to move on.
    const BETWEEN: &[&str] = &["2026-09-12", "2026-09-21", "2026-09-30"];

    // (1) The stall: `with_a_log` starts a block on ^t4 and nothing closes it.
    let tm = with_a_log();
    for day in BETWEEN {
        tm.ok_at(&format!("{day}T09:00:00-05:00"), &["now"]);
    }
    let start_line = tm.log().iter().position(|e| e["ev"] == "start").expect("a `start`") as u64 + 1;

    let out = tm.run_at(LATE, &["check"]);
    assert_eq!(out.code, 0, "a stall is a warning, not an error: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("log-stall"), "the stall is not named: {}", out.stdout);
    assert!(out.stdout.contains("^t4"), "the stall does not name the block: {}", out.stdout);
    // The consequence §9.4 names, not just the cause.
    assert!(out.stdout.contains("ledger day"), "the stall does not name what it holds: {}", out.stdout);
    let found = problems_at(&tm, LATE);
    assert!(
        found.contains(&("log-stall".into(), "warning".into(), ".tm/log.jsonl".into(), start_line)),
        "the stall is not at the `start`'s own line {start_line}: {found:?}"
    );
    // D18's rule for the whole family: the exit code is the tree's alone.
    assert_eq!(tm.json_at(LATE, &["check"])["exit_code"], 0);

    // (2) The control: the same tree, the same days, the block **closed**. Its
    // ledger day still trails `now` by far more than the seven-day bound, so a
    // lag test would name it. Nothing is wrong with it and nothing is said.
    let tm = with_a_log();
    tm.ok_at("2026-09-07T10:05:00-05:00", &["done", "--went", "1"]);
    for day in BETWEEN {
        tm.ok_at(&format!("{day}T09:00:00-05:00"), &["now"]);
    }
    let out = tm.run_at(LATE, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(
        !out.stdout.contains("log-stall"),
        "a tree whose block was closed was named as stalled: {}",
        out.stdout
    );
}

/// **The bound is `> 7` days, and it is asserted on both sides of itself**
/// (`check::LOG_STALL_DAYS`; design §9.4's "a stall longer than 7 days").
///
/// A block open for exactly seven days is not a stall; one open for eight is.
/// Without this, `>=` and `>` both pass the test above, and the sentence the
/// design wrote would not be the sentence the code means.
#[test]
fn a_block_open_exactly_seven_days_is_not_yet_a_stall() {
    // `with_a_log` starts its block on 2026-09-07 (`cli_common::NOW`).
    let seven = "2026-09-14T09:00:00-05:00";
    let eight = "2026-09-15T09:00:00-05:00";

    let tm = with_a_log();
    let out = tm.run_at(seven, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(
        !out.stdout.contains("log-stall"),
        "a block open exactly 7 days was named a stall: {}",
        out.stdout
    );

    let tm = with_a_log();
    let out = tm.run_at(eight, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("log-stall"),
        "a block open 8 days was not named a stall: {}",
        out.stdout
    );
    assert!(out.stdout.contains("^t4"), "{}", out.stdout);
}

/// **The second stall cause design §9.4 names**: "an open block holding an
/// observation, a `stop` never followed by a `start`, or an **open
/// interruption** holds `L'` back."
///
/// `tm interrupt` leaves both at once — the block is still open and the
/// interruption sits on top of it — and both really do hold the ledger day,
/// so both are named, each at its own line with the verb that clears it. This
/// exists because an arm that is built and never exercised is the shape §9.2
/// calls a disguised gap: it would have passed review and named nothing.
#[test]
fn an_interruption_never_resumed_is_named_beside_its_block() {
    const LATE: &str = "2026-10-10T09:00:00-05:00";
    let tm = with_a_log();
    tm.ok_at("2026-09-07T09:30:00-05:00", &["interrupt"]);
    for day in ["2026-09-12", "2026-09-21", "2026-09-30"] {
        tm.ok_at(&format!("{day}T09:00:00-05:00"), &["now"]);
    }
    let line_of = |ev: &str| {
        tm.log().iter().position(|e| e["ev"] == ev).unwrap_or_else(|| panic!("a `{ev}`")) as u64 + 1
    };

    let out = tm.run_at(LATE, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let stalls: Vec<_> = problems_at(&tm, LATE).into_iter().filter(|p| p.0 == "log-stall").collect();
    assert_eq!(stalls.len(), 2, "both stalls should be named, got {stalls:?}");
    for ev in ["start", "interrupt"] {
        let line = line_of(ev);
        assert!(
            stalls.contains(&("log-stall".into(), "warning".into(), ".tm/log.jsonl".into(), line)),
            "the `{ev}` at line {line} is not named: {stalls:?}"
        );
    }
    // Each names the verb that actually clears it — the point of naming them
    // separately rather than as one "something is open".
    assert!(out.stdout.contains("an interruption of ^t4"), "{}", out.stdout);
    assert!(out.stdout.contains("`tm resume`"), "{}", out.stdout);
    assert!(out.stdout.contains("`tm done`"), "{}", out.stdout);
}

/// **D18 survives D32**: the one verb that loads tolerantly still does.
///
/// D32 (gap 476) gave `tm check` sight of a kernel **load** refusal, and gap
/// 145's whole point is that `tm check` must keep working on a log no rebuild
/// can window — it is how the bad line is found. The two do not collide,
/// because the request `tm check` now sends carries **no `log` section**:
/// `{"docs":…,"cmds":[]}`, the corpus round trip's own shape.
///
/// So, on one tree with both faults at once: the log's bad line is still a
/// **warning** naming its line, the tree's collision is an **error** naming
/// both of its lines, and the exit code is 2 because of the second and never
/// because of the first — which is exactly D18's requirement that a damaged
/// log move no exit code.
#[test]
fn a_damaged_log_stays_a_warning_while_a_refused_tree_is_an_error() {
    let tm = with_a_log();
    append_bytes(&tm, b"this is not json at all\n");
    let bad_line = log_lines(&tm) as u64;
    let now = day_after(
        &std::fs::read_to_string(tm.plan.join(".tm/log.jsonl")).expect("read the log"),
    );

    // The log alone: warning, exit 0 — gap 145, unchanged.
    let out = tm.run_at(&now, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(
        problems_at(&tm, &now).contains(&(
            "log-line".into(),
            "warning".into(),
            ".tm/log.jsonl".into(),
            bad_line
        )),
        "{:?}",
        problems_at(&tm, &now)
    );
    let json_of = |out: &cli_common::Out| -> serde_json::Value {
        serde_json::from_str(&out.stdout).expect("check --json is JSON")
    };

    // …and now a tree the kernel refuses as well.
    let path = tm.plan.join("routines.md");
    let text = std::fs::read_to_string(&path).expect("read routines");
    let first = text.lines().next().expect("a routine line").to_string();
    std::fs::write(&path, format!("{text}{first}\n")).expect("write routines");

    let out = tm.run_at(&now, &["check"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let ps = problems_of(&json_of(&tm.run_at(&now, &["--json", "check"])));
    // The log line is still named, still a warning.
    assert!(
        ps.contains(&("log-line".into(), "warning".into(), ".tm/log.jsonl".into(), bad_line)),
        "the damaged log stopped being named: {ps:?}"
    );
    // The tree's collision is an error, at both of its lines.
    let n = text.lines().count() as u64;
    for line in [1, n + 1] {
        assert!(
            ps.contains(&("kernel-load".into(), "error".into(), "routines.md".into(), line)),
            "routines.md:{line} is not named: {ps:?}"
        );
    }
}
