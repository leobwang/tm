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

use std::fs::OpenOptions;
use std::io::Write;

use cli_common::Tm;

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
    let doc = tm.json(&["check"]);
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
