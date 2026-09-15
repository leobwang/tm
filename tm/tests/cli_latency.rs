//! Latency acceptance: one kernel-backed verb on a tree with months of history
//! (kernel/README.md gap 62, closed by the stage-4 hardening block).
//!
//! Before the fast checker, every kernel call re-rendered the whole plan once per
//! document and looked every id up through a chain of one closure per item, so
//! a history-shaped tree of about 2,750 lines and 225 files took 59-83 s per
//! verb. The tree below is that shape — six months of day files, a half-year of
//! week files, six month files, a long backlog — with open lines left in the
//! last forty days and eight weeks, so the verb's automatic close really lands
//! lines (one plan check per landing), not just loads the tree.
//!
//! The bounds are generous on purpose: measured on the development machine
//! (debug profile, the binary this test runs) the first verb — the automatic
//! close taking 120 lines, then the drop — took 0.61-0.63 s and the second
//! verb, one kernel call on the swept tree, 0.05 s. `FIRST_VERB` is 8x the
//! first and `LATER_VERB` 20x the second, so a busy machine does not flake
//! them, while the quadratic kernel they guard against misses both by minutes.

mod cli_common;

#[path = "support/loggen.rs"]
#[allow(dead_code)]
mod loggen;

use std::fs;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use cli_common::Tm;

/// Held while a test times its verbs.
static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// The Monday after W37: the last ended day is 2026-09-13.
const AT: &str = "2026-09-14T09:00:00-05:00";
/// The first verb: an automatic close that lands every open line, then a drop.
const FIRST_VERB: Duration = Duration::from_secs(5);
/// A later verb on the swept tree: the drop's kernel call alone.
const LATER_VERB: Duration = Duration::from_secs(1);

fn write(tm: &Tm, rel: &str, text: &str) {
    let path = tm.plan.join(rel);
    fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
    fs::write(path, text).expect("write");
}

/// Monday of ISO week `w` of 2026 (2026-W01 starts on 2025-12-29).
fn monday(w: u32) -> chrono::NaiveDate {
    chrono::NaiveDate::from_isoywd_opt(2026, w, chrono::Weekday::Mon).expect("iso week")
}

/// 190 day files of eight done lines, 27 week files of twenty, six month files
/// of ten outcomes and 300 backlog lines — 226 files, about 2,960 lines — with
/// two open lines in each of the last 40 days and five in each of the last 8
/// weeks.
fn history_tree() -> Tm {
    let tm = Tm::empty();
    fs::create_dir_all(tm.plan.join(".tm")).expect("mkdir .tm");
    let config = fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../tm-core/tests/fixtures/plan-basic/config.toml"),
    )
    .expect("fixture config");
    write(&tm, "config.toml", &config);

    let mut backlog = String::from("# Untied\n- [ ] 2 30m Insurance claim for the bike ^a1\n");
    for k in 0..300 {
        backlog.push_str(&format!("- [ ] 2 30m Synthetic task {k} ^z{k}\n"));
    }
    write(&tm, "backlog.md", &backlog);

    write(
        &tm,
        "month/2026-09.md",
        "---\nmonth: 2026-09\n---\n# Outcomes\n- [ ] 3 !2 Ship the paper ^O1\n\n# Demoted\n",
    );
    for (n, m) in (3..=8).enumerate() {
        let mut body = format!("---\nmonth: 2026-{m:02}\n---\n# Outcomes\n");
        for j in 0..10 {
            let k = n * 10 + j;
            body.push_str(&format!("- [x] 3 !2 Outcome {k} ^o{k}\n"));
        }
        write(&tm, &format!("month/2026-{m:02}.md"), &body);
    }

    let mut open = 0;
    for (n, w) in (11..=37).enumerate() {
        let mon = monday(w);
        let sun = mon + chrono::Duration::days(6);
        let mut body = format!(
            "---\nweek: 2026-W{w:02}\nwindow: {mon}..{sun}\nbudget: 25\nplanned: 20\n---\n# Milestones\n"
        );
        for j in 0..20 {
            let k = n * 20 + j;
            body.push_str(&format!("- [x] 3 1b Week task {k} ^w{k}\n"));
        }
        if w >= 30 {
            for _ in 0..5 {
                body.push_str(&format!("- [ ] 3 1b Open week task {open} ^v{open}\n"));
                open += 1;
            }
        }
        write(&tm, &format!("week/2026-W{w:02}.md"), &body);
    }
    write(
        &tm,
        "week/2026-W38.md",
        "---\nweek: 2026-W38\nwindow: 2026-09-14..2026-09-20\nbudget: 25\nplanned: 0\n---\n# Tasks\n",
    );

    let last = chrono::NaiveDate::from_ymd_opt(2026, 9, 13).expect("date");
    let mut open = 0;
    for d in 0..190 {
        let day = last - chrono::Duration::days(189 - d);
        let mut body = String::from("# Pinned\n");
        for j in 0..8 {
            let k = d * 8 + j;
            body.push_str(&format!("- [x] 1 30m Done thing {k} ^y{k}\n"));
        }
        if d >= 150 {
            for _ in 0..2 {
                body.push_str(&format!("- [ ] 2 20m Open thing {open} ^q{open}\n"));
                open += 1;
            }
        }
        write(&tm, &format!("day/{day}.md"), &body);
    }
    tm
}

/// Run the binary at [`AT`], killing it once `limit` has passed — a regression
/// to the quadratic kernel must fail this test in seconds, not hang it for an
/// hour. Returns the exit code, stdout and stderr together, and the wall time.
fn timed(tm: &Tm, args: &[&str], limit: Duration) -> (i32, String, Duration) {
    let log = tm.tmp.path().join(format!("latency-{}.out", args.join("-").replace('^', "")));
    let file = fs::File::create(&log).expect("output file");
    let start = Instant::now();
    let mut child = Command::new(env!("CARGO_BIN_EXE_tm"))
        .arg("--dir")
        .arg(&tm.plan)
        .arg("--now")
        .arg(AT)
        .args(args)
        .stdout(Stdio::from(file.try_clone().expect("clone")))
        .stderr(Stdio::from(file))
        .spawn()
        .expect("spawn tm");
    loop {
        if let Some(status) = child.try_wait().expect("wait") {
            let took = start.elapsed();
            let text = fs::read_to_string(&log).unwrap_or_default();
            return (status.code().unwrap_or(-1), text, took);
        }
        if start.elapsed() > limit {
            let _ = child.kill();
            let _ = child.wait();
            panic!("`tm {}` was still running after {limit:?}", args.join(" "));
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

fn plan_lines(tm: &Tm) -> (usize, usize) {
    fn walk(dir: &std::path::Path, acc: &mut (usize, usize)) {
        for e in fs::read_dir(dir).expect("read dir") {
            let path = e.expect("entry").path();
            let name = path.file_name().expect("name").to_string_lossy().to_string();
            if name.starts_with('.') {
                continue;
            }
            if path.is_dir() {
                walk(&path, acc);
            } else if name.ends_with(".md") {
                acc.0 += 1;
                acc.1 += fs::read_to_string(&path).expect("read").lines().count();
            }
        }
    }
    let mut acc = (0, 0);
    walk(&tm.plan, &mut acc);
    acc
}

#[test]
fn a_verb_on_a_tree_with_months_of_history_takes_well_under_a_second() {
    let tm = history_tree();
    history_verbs(&tm, "");
}

/// The two verbs every test here times, with the work the bounds are about
/// checked: `label` names the log behind them in the printed figures.
fn history_verbs(tm: &Tm, label: &str) -> (Duration, Duration) {
    // One timed pair at a time: the harness runs tests on parallel threads, and
    // two trees closing at once would time each other.
    let _serial = SERIAL.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let (files, lines) = plan_lines(tm);
    assert!(files >= 220 && lines >= 2_700, "not history-shaped: {files} files, {lines} lines");

    // The first verb: unswept, so the automatic close runs over the whole tree
    // and lands 120 open lines, one plan check per landing; then the drop.
    let (code, out, first) = timed(tm, &["drop", "^a1"], FIRST_VERB);
    eprintln!("latency{label}: first verb {first:?} ({files} files, {lines} lines)");
    assert_eq!(code, 0, "{out}");
    assert!(
        first < FIRST_VERB,
        "the automatic close and a drop on {files} files / {lines} lines took {first:?} (bound {FIRST_VERB:?})"
    );
    // It did the work the bound is about: the lines were landed and the tree swept.
    let w38 = fs::read_to_string(tm.plan.join("week/2026-W38.md")).expect("W38");
    assert_eq!(w38.matches("Open thing").count(), 80, "{w38}");
    let september = fs::read_to_string(tm.plan.join("month/2026-09.md")).expect("month");
    assert_eq!(september.matches("Open week task").count(), 40, "{september}");
    assert!(
        !fs::read_to_string(tm.plan.join("day/2026-09-13.md")).expect("day").contains("[ ]"),
        "an open line stayed in an ended day"
    );
    assert!(fs::read_to_string(tm.plan.join("backlog.md")).expect("backlog").contains("[~] 2 30m Insurance claim"));
    assert_eq!(tm.state()["closed"]["swept"], true);

    // A later verb: the gate holds, so this is the drop's one kernel call.
    let (code, out, later) = timed(tm, &["drop", "^z1"], LATER_VERB);
    eprintln!("latency{label}: later verb {later:?}");
    assert_eq!(code, 0, "{out}");
    assert!(later < LATER_VERB, "a drop on the swept tree took {later:?} (bound {LATER_VERB:?})");
    assert!(fs::read_to_string(tm.plan.join("backlog.md")).expect("backlog").contains("[~] 2 30m Synthetic task 1 ^z1"));
    (first, later)
}

/// The history tree's last ended day: the log below ends on it.
const LAST_LOGGED: (i32, u32, u32) = (2026, 9, 13);

/// `.tm/log.jsonl` on the history tree: `days` days of loggen's 61-events-a-day
/// log (seed 7, the design pass's generator), dated so the last day is
/// [`LAST_LOGGED`], the day before [`AT`]. Returns its lines and bytes.
fn write_log(tm: &Tm, days: u32) -> (usize, usize) {
    let (y, m, d) = LAST_LOGGED;
    let last = chrono::NaiveDate::from_ymd_opt(y, m, d).expect("date");
    let first = last - chrono::Duration::days(i64::from(days) - 1);
    use chrono::Datelike;
    let start = loggen::Date::from_ymd(first.year(), first.month(), first.day());
    let lines = loggen::LogGen::new(loggen::Rate::SixtyOne, loggen::SEED).days_from(start, days);
    assert!(lines.last().expect("a line").contains(&format!("{last}T")), "the log ends on {last}");
    let text = loggen::text(&lines);
    write(tm, ".tm/log.jsonl", &text);
    (lines.len(), text.len())
}

/// Design §14.3 row R14: the same two verbs with a year of log behind them
/// (365 days at 61 events a day, about 2.3 MiB). Every verb
/// reads the whole log through `Ctx::replay_with`; this is the Rust reader's
/// baseline, which the switch's T11 is compared with.
#[test]
fn a_verb_with_a_year_of_log_takes_well_under_a_second() {
    let tm = history_tree();
    let (lines, bytes) = write_log(&tm, 365);
    let (first, later) = history_verbs(&tm, &format!(" (1y log: {lines} lines, {bytes} bytes)"));
    assert!(first < FIRST_VERB && later < LATER_VERB);
    // The verbs appended after the year, not over it.
    let text = fs::read_to_string(tm.plan.join(".tm/log.jsonl")).expect("log");
    assert!(text.len() > bytes && text.starts_with("{\"t\":\"2025-09-14T"), "{}", &text[..80]);
}

/// The three-year variant (1,095 days, about 6.9 MiB), run by hand
/// (`cargo test --test cli_latency -- --ignored --nocapture`); its figures
/// are recorded in kernel/README.md (step R14), not asserted beyond the bounds.
#[test]
#[ignore]
fn a_verb_with_three_years_of_log_takes_well_under_a_second() {
    let tm = history_tree();
    let (lines, bytes) = write_log(&tm, 1_095);
    let (first, later) = history_verbs(&tm, &format!(" (3y log: {lines} lines, {bytes} bytes)"));
    assert!(first < FIRST_VERB && later < LATER_VERB);
}

/// **T14** (stage 5 D10 L8, design §14.8's L8 row and §18.8): since L8 `tm plan`
/// asks the kernel for its priorities over a lookahead that reaches the furthest
/// deadline, so a `due:` three years out makes the kernel simulate about 1,100
/// days and one ten years out about 3,650 (just inside the 3,660-day cap, gap
/// 98). On the history-shaped tree, once swept, both plans stay inside
/// `LATER_VERB`.
#[test]
fn a_plan_with_a_due_three_and_ten_years_out_stays_a_later_verb() {
    let tm = history_tree();
    // Timed one at a time with the other latency tests (R14's rule).
    let _serial = SERIAL.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let (code, out, _) = timed(&tm, &["drop", "^a1"], FIRST_VERB);
    assert_eq!(code, 0, "{out}");
    // The first capacity request probes the zone and caches it (D13); time the plans after it.
    let (code, out, _) = timed(&tm, &["plan"], FIRST_VERB);
    assert_eq!(code, 0, "{out}");
    let backlog = fs::read_to_string(tm.plan.join("backlog.md")).expect("backlog");
    for (years, due, days) in [(3, "2029-09-14", 1097), (10, "2036-09-12", 3652)] {
        write(&tm, "backlog.md", &format!("{backlog}- [ ] 3 2h A deadline {years} years out due:{due} ^far{years}\n"));
        let (code, out, took) = timed(&tm, &["plan"], LATER_VERB);
        eprintln!("latency: plan with a due {years} years out ({days} lookahead days) {took:?}");
        assert_eq!(code, 0, "{out}");
        assert!(!out.contains("clamped"), "{out}");
        assert!(took < LATER_VERB, "a plan with a due {years} years out took {took:?} (bound {LATER_VERB:?})");
    }
}
