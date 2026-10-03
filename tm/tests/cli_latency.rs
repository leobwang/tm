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
    timed_at(tm, AT, args, limit)
}

/// [`timed`] at an explicit instant — T11's rows that move `--now` forward.
fn timed_at(tm: &Tm, now: &str, args: &[&str], limit: Duration) -> (i32, String, Duration) {
    let log = tm.tmp.path().join(format!("latency-{}-{now}.out", args.join("-").replace('^', "")));
    let file = fs::File::create(&log).expect("output file");
    let start = Instant::now();
    let mut child = Command::new(env!("CARGO_BIN_EXE_tm"))
        .arg("--dir")
        .arg(&tm.plan)
        .arg("--now")
        .arg(now)
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

/// The three verbs every test here times, with the work the bounds are about
/// checked: `label` names the log behind them in the printed figures.
///
/// **The third row is the owner's D35 instrument** (gap 584): a *host-only*
/// write — `tm edit ^z2 'title=…'`, a typed non-key edit, which gap 41 keeps
/// off the wire — now asks the kernel whether the tree still loads before it
/// writes. That is a whole-tree kernel load on a path that never had one, and
/// D35 made measuring it a condition of landing it. It is timed here, on the
/// same tree, in the same serial section, one line below the `tm drop` row it
/// has to be compared with: the drop is a verb whose write **is** a kernel
/// call, so it is what one whole-tree load costs on this tree, and the gated
/// edit must land in the same band rather than in a new one.
fn history_verbs(tm: &Tm, label: &str) -> (Duration, Duration, Duration) {
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

    // The gated host-only write (D35, gap 584), beside the drop it is compared
    // with. `title=` is a typed non-key edit: it never reaches the kernel's
    // `edit` op (gap 41), so before D35 this verb wrote without the kernel
    // seeing the tree at all, and its whole cost is now one `tree_refusal`.
    let (code, out, gated) =
        timed(tm, &["edit", "^z2", "title=Synthetic task 2 renamed"], LATER_VERB);
    eprintln!("latency{label}: gated host-only write (D35) {gated:?}");
    assert_eq!(code, 0, "{out}");
    assert!(
        gated < LATER_VERB,
        "a gated host-only edit took {gated:?} (bound {LATER_VERB:?})"
    );
    // It did the work the bound is about: the line really was rewritten.
    assert!(
        fs::read_to_string(tm.plan.join("backlog.md"))
            .expect("backlog")
            .contains("Synthetic task 2 renamed ^z2"),
        "the gated edit did not rewrite its line"
    );
    (first, later, gated)
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
    let (first, later, gated) = history_verbs(&tm, &format!(" (1y log: {lines} lines, {bytes} bytes)"));
    assert!(first < FIRST_VERB && later < LATER_VERB && gated < LATER_VERB);
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
    let (first, later, gated) = history_verbs(&tm, &format!(" (3y log: {lines} lines, {bytes} bytes)"));
    assert!(first < FIRST_VERB && later < LATER_VERB && gated < LATER_VERB);
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

// ---------------------------------------------------------------------------
// T11 (design §14.6): the seven latency rows the switch must not regress.

/// Row 3's bound: a `--now` + 1 day verb, which is a reseal after the switch.
const RESEAL_VERB: Duration = LATER_VERB;

/// **The replay cache's files** (`kernel_log::CACHE_DIR`): `ckpt.json` plus
/// every immutable generation file under `sealed/`.
///
/// **Before the switch this was always 0** — nothing under `tm/src` called
/// `kernel_log::`, so no cache was ever written, and every "does not rebuild"
/// and "at most one checkpoint write a day" assertion below was measured
/// against 0 and could not bite. **README gap 140 clears here**: since S the
/// directory holds `ckpt.json` and the sealed month files, the counts below are
/// real, and the first assertion in the test is turned around to say so — a
/// switched binary that wrote *no* cache would mean the replay was being
/// rebuilt from scratch on every verb, which is the regression these rows
/// exist to catch.
fn cache_files(tm: &Tm) -> usize {
    fn walk(dir: &std::path::Path) -> usize {
        let Ok(entries) = fs::read_dir(dir) else { return 0 };
        let mut n = 0;
        for e in entries.flatten() {
            let path = e.path();
            if path.is_dir() {
                n += walk(&path);
            } else {
                n += 1;
            }
        }
        n
    }
    let dir = tm.plan.join(".tm/cache/replay");
    if dir.is_dir() { walk(&dir) } else { 0 }
}

/// **The distinct checkpoint _generations_ under the replay cache.**
///
/// A generation is what one reseal writes: `ckpt.json` plus an immutable
/// `sealed/YYYY-MM.g<gen>.json` per month it sealed — so at three years a
/// single generation is **~37 files**, and month files of the previous
/// generation stay until the collector takes them (`kernel_log::COLLECT_AFTER`,
/// ten minutes — far longer than this test runs).
///
/// The rows below claim "at most one checkpoint write", and this counts that
/// claim. [`cache_files`] counts *files*, which is the right measure for "a
/// cache exists at all" and "the routine did not rebuild" and the wrong one
/// here: `cache_files <= before + 1` was vacuously true before S (the count was
/// always 0) and cannot hold after it.
fn cache_generations(tm: &Tm) -> usize {
    let dir = tm.plan.join(".tm/cache/replay/sealed");
    let Ok(entries) = fs::read_dir(&dir) else { return 0 };
    let mut gens = std::collections::BTreeSet::new();
    for e in entries.flatten() {
        let name = e.file_name().to_string_lossy().to_string();
        if let Some((_, rest)) = name.split_once(".g") {
            gens.insert(rest.trim_end_matches(".json").to_string());
        }
    }
    gens.len()
}

/// The id whose most recent `done` in `text` is closest to 30 days before
/// `last`, searched inside 28..=32 days, with that date.
///
/// Row 4 hand-appends an `undo` naming this id, so the undo's target is about
/// a month old and the next call cannot resume from a checkpoint past it.
/// Chosen from the generated log rather than hard-coded, so it cannot rot when
/// the generator's draws move; `expect` rather than a skip, so a log that stops
/// containing such an id fails the test instead of quietly weakening it.
///
/// The caveat, stated: loggen writes its own `undo{of:"done"}` lines, and one
/// of them may already have cancelled this `done`. That can only push the
/// mask's target *further* back, which is still a far undo — so the row keeps
/// its meaning, and what is asserted is what is controlled: the id's last
/// `done` line is 28-32 days before the log's end.
fn undo_target_about_30_days_back(text: &str, last: chrono::NaiveDate) -> (String, chrono::NaiveDate) {
    let mut last_done: std::collections::BTreeMap<String, chrono::NaiveDate> = std::collections::BTreeMap::new();
    for line in text.lines() {
        if !line.contains(r#""ev":"done""#) {
            continue;
        }
        let Some(date) = line.strip_prefix(r#"{"t":""#).and_then(|r| r.get(..10)) else { continue };
        let Ok(day) = date.parse::<chrono::NaiveDate>() else { continue };
        let Some(rest) = line.split_once(r#""id":""#).map(|(_, r)| r) else { continue };
        let Some((id, _)) = rest.split_once('"') else { continue };
        let slot = last_done.entry(id.to_string()).or_insert(day);
        if day > *slot {
            *slot = day;
        }
    }
    let want = last - chrono::Duration::days(30);
    let mut best: Option<(String, chrono::NaiveDate)> = None;
    for (id, day) in last_done {
        let age = (last - day).num_days();
        if !(28..=32).contains(&age) {
            continue;
        }
        let closer = match &best {
            None => true,
            Some((_, b)) => (want - day).num_days().abs() < (want - *b).num_days().abs(),
        };
        if closer {
            best = Some((id, day));
        }
    }
    best.expect("a 3-year loggen log holds an id whose last `done` is 28-32 days before its end")
}

/// **T11** (design §14.6's latency table): the seven rows the switch must not
/// regress, measured on a three-year log through the **unswitched** binary.
/// Every figure this prints is a number S is compared with, so it runs in the
/// default suite rather than behind `#[ignore]` — R14's three-year variant
/// stays ignored beside it, because that one is a by-hand measurement and this
/// one is a guard.
#[test]
fn a_verb_on_a_tree_with_three_years_of_log_takes_well_under_a_second() {
    let tm = history_tree();
    let (lines, bytes) = write_log(&tm, 1_095);
    let label = format!(" (T11 3y log: {lines} lines, {bytes} bytes)");

    // Rows 1 and 2: the first verb (genesis + the automatic close + a drop) and
    // a later verb on the swept tree. `history_verbs` takes the serial lock,
    // times both and checks the work the bounds are about really happened.
    let (first, later, gated) = history_verbs(&tm, &label);
    assert!(first < FIRST_VERB && later < LATER_VERB && gated < LATER_VERB);
    // **Gap 140, turned around at S.** The switched binary persists its
    // checkpoint; 0 here would mean every verb paid a genesis.
    let cached = cache_files(&tm);
    assert!(cached > 0, "the switched binary wrote no replay cache — every verb is rebuilding");
    eprintln!("latency{label}: {cached} replay-cache file(s) after the first two verbs");

    // The remaining rows are timed one at a time, like the pair above.
    let _serial = SERIAL.lock().unwrap_or_else(|poisoned| poisoned.into_inner());

    // Row 4, in two halves — and the first half is a **finding**, recorded
    // where it was measured (README gap 180).
    //
    // §14.6's row 4 reads "after hand-appending an `undo` whose target is 30
    // days old (one rebuild) < 5 s". On *this* tree that is not reachable, and
    // it is not a defect: a three-year log at ~60 events a day puts the pop
    // that undo forces **9,039 lines** behind the cut, past the resend cap
    // (`kernel_log::RESEND_LINES` = 8,192 lines / `RESEND_BYTES` = 1,536 KiB,
    // gap 102's memory gate). So the answer is the named fault `reachTooFar`,
    // exactly as the owner's D18 (iii) and parity **P31** require — and **the
    // memory cap is never raised to make a bound reachable** (D18).
    //
    // Both halves are therefore measured: the 30-day undo must fail **by name
    // and fast** (a fault that took a genesis to discover would still be a
    // latency regression), and the row's actual latency claim — one rebuild,
    // then no rebuild — is measured on an undo the gate can window.
    let log_text = fs::read_to_string(tm.plan.join(".tm/log.jsonl")).expect("log");
    let last_logged = chrono::NaiveDate::from_ymd_opt(LAST_LOGGED.0, LAST_LOGGED.1, LAST_LOGGED.2).expect("date");
    let (target, done_on) = undo_target_about_30_days_back(&log_text, last_logged);
    let age = (last_logged - done_on).num_days();
    assert!((28..=32).contains(&age), "the undo target is {age} days old");
    let appended = |id: &str| {
        let mut t = log_text.clone();
        if !t.ends_with('\n') {
            t.push('\n');
        }
        t.push_str(&format!(
            "{{\"t\":\"{last_logged}T23:59:00-05:00\",\"ev\":\"undo\",\"of\":\"done\",\"id\":\"{id}\"}}\n"
        ));
        t
    };

    // Half one: the 30-day-old target. Past the gate, so it is the named fault
    // — and it must be named **fast**: a fault discovered only after a full
    // genesis would still be the latency regression this row exists to catch.
    write(&tm, ".tm/log.jsonl", &appended(&target));
    let (code, out, faulted) = timed(&tm, &["now"], FIRST_VERB);
    eprintln!("latency{label}: a {age}-day-old hand undo (target ^{target}, done {done_on}) {faulted:?}");
    assert_ne!(code, 0, "a log past the resend cap was answered instead of refused: {out}");
    assert!(out.contains("reachTooFar"), "the fault is not named: {out}");
    assert!(faulted < FIRST_VERB, "naming the fault took {faulted:?} (bound {FIRST_VERB:?})");

    // Half two: the row's latency claim, on an undo the gate *can* window — the
    // most recent `done` in the log. One rebuild is allowed FIRST_VERB; the
    // verb after it must not rebuild again, which is what the LATER_VERB bound
    // on the next verb measures.
    let recent = log_text
        .lines()
        .rev()
        .find(|l| l.contains(r#""ev":"done""#))
        .and_then(|l| l.split_once(r#""id":""#).map(|(_, r)| r))
        .and_then(|r| r.split_once('"').map(|(id, _)| id.to_string()))
        .expect("the log has a `done`");
    write(&tm, ".tm/log.jsonl", &appended(&recent));

    let before = cache_generations(&tm);
    let (code, out, rebuild) = timed(&tm, &["drop", "^z2"], FIRST_VERB);
    eprintln!("latency{label}: the verb after a windowable hand undo (target ^{recent}) {rebuild:?}");
    assert_eq!(code, 0, "{out}");
    assert!(rebuild < FIRST_VERB, "the rebuild after a far undo took {rebuild:?} (bound {FIRST_VERB:?})");
    let (code, out, settled) = timed(&tm, &["drop", "^z3"], LATER_VERB);
    eprintln!("latency{label}: the verb after that one {settled:?}");
    assert_eq!(code, 0, "{out}");
    assert!(
        settled < LATER_VERB,
        "the verb after the rebuild took {settled:?} (bound {LATER_VERB:?}) — it rebuilt again"
    );
    assert!(
        cache_generations(&tm) <= before + 1,
        "the far undo wrote more than one checkpoint generation"
    );

    // Row 5: a routine logged for an instance three days old, and no rebuild.
    // On the Monday `AT` names, `every:Fri on-miss:persist` has its pending
    // instance on Friday 2026-09-11 — measured through the binary, and the
    // instance's age is asserted below rather than assumed.
    write(&tm, "routines.md", "- fridaything win:09:00-21:00 dur:30m every:Fri on-miss:persist\n");
    let before = cache_files(&tm);
    let (code, out, routine) = timed(&tm, &["--json", "routine", "done", "fridaything"], LATER_VERB);
    eprintln!("latency{label}: a routine for a 3-day-old instance {routine:?}");
    assert_eq!(code, 0, "{out}");
    assert!(routine < LATER_VERB, "a routine done took {routine:?} (bound {LATER_VERB:?})");
    let inst = tm.last_ev("routine")["inst"].as_str().expect("an inst").to_string();
    let inst_date = inst.parse::<chrono::NaiveDate>().expect("inst is a date");
    let at_date = chrono::NaiveDate::from_ymd_opt(2026, 9, 14).expect("date");
    assert_eq!((at_date - inst_date).num_days(), 3, "the routine's instance is {inst}, not three days old");
    assert_eq!(cache_files(&tm), before, "the routine rebuilt the cache");

    // Row 7: `tm review week` — the `All` scope, which after the switch merges
    // every month's sealed records.
    let (code, out, review) = timed(&tm, &["review", "week"], LATER_VERB);
    eprintln!("latency{label}: review week (the All scope) {review:?}");
    assert_eq!(code, 0, "{out}");
    assert!(review < LATER_VERB, "`tm review week` took {review:?} (bound {LATER_VERB:?})");

    // Row 3: `--now` + 1 day, a reseal after the switch. Run after the rows
    // above so that time only ever moves forward: a verb at `AT` following one
    // at `AT + 1 day` would be reading a log with a line dated after `now`,
    // which is a different measurement (D9-22's future-line fence).
    let day1 = "2026-09-15T09:00:00-05:00";
    let before = cache_generations(&tm);
    let (code, out, reseal) = timed_at(&tm, day1, &["drop", "^z4"], RESEAL_VERB);
    eprintln!("latency{label}: --now +1 day (a reseal) {reseal:?}");
    assert_eq!(code, 0, "{out}");
    assert!(reseal < RESEAL_VERB, "the +1 day verb took {reseal:?} (bound {RESEAL_VERB:?})");
    assert!(
        cache_generations(&tm) <= before + 1,
        "the reseal wrote more than one checkpoint generation ({} -> {})",
        before,
        cache_generations(&tm)
    );

    // **Close what row 4 reopened, before row 6 opens its own.** That row
    // hand-appends an `undo` of the last `done`, which puts `^224`'s `start`
    // back in the log with no `done` after it — and since the owner's **D42**
    // `.tm/state.json` is a cache of the log, so the log is what decides which
    // block is open. `tm start ^z5` is then correctly refused *"^224 is
    // running"*. This is a **behaviour change**, recorded here beside the line
    // it moved: before D42 the two readers disagreed in silence, and `tm plan`
    // drew `^224` with `▶` on this very tree while `tm now` said nothing was
    // running.
    let (code, out, _) = timed_at(&tm, "2026-09-15T09:04:00-05:00", &["stop"], LATER_VERB);
    assert_eq!(code, 0, "closing the block row 4's hand undo reopened: {out}");

    // Row 6: a block left open, then ten successive `--now` days. The stall
    // holds the ledger day back (design §18.7), so each day's verb carries one
    // more open day than the last; each must stay a later verb, and each day
    // may write at most one checkpoint.
    let (code, out, _) = timed_at(&tm, "2026-09-15T09:05:00-05:00", &["start", "^z5"], LATER_VERB);
    assert_eq!(code, 0, "{out}");
    let mut worst = Duration::from_millis(0);
    let before = cache_generations(&tm);
    for d in 0..10 {
        let day = chrono::NaiveDate::from_ymd_opt(2026, 9, 16).expect("date") + chrono::Duration::days(d);
        let now = format!("{day}T09:00:00-05:00");
        let (code, out, took) = timed_at(&tm, &now, &["drop", &format!("^z{}", 10 + d)], LATER_VERB);
        assert_eq!(code, 0, "{out}");
        assert!(took < LATER_VERB, "day {day} of a stall took {took:?} (bound {LATER_VERB:?})");
        worst = worst.max(took);
    }
    // `saturating_sub`: the collector may take the generations this run
    // superseded, so the count can legitimately fall.
    let writes = cache_generations(&tm).saturating_sub(before);
    eprintln!("latency{label}: 10 stalled days, worst {worst:?}, {writes} checkpoint generation(s)");
    assert!(writes <= 10, "a stalled run wrote {writes} checkpoint generations over 10 days");
}

/// **Gap 129, measured rather than assumed** — a plain `tm log` asks the `All`
/// scope (§11.1), which since the switch merges **every** month's sealed
/// records, on one of the verbs users run most often.
///
/// Gap 129 item 4 set the condition for closing it in advance: "if a bare
/// `tm log` at three years sits inside `LATER_VERB` on the `All` scope, the
/// narrowing is not worth its second call and this gap closes as *measured,
/// not needed*; if it does not, S builds the two-step." This is that
/// measurement, on the same three-year tree T11 uses.
///
/// **And it is the behavioural test gap 117 could not carry.** Before S every
/// scope answered with the whole log, so `tm log --tail n` returned *n*
/// whatever scope it asked for and no test could fail. The scope is real now:
/// a tail whose scope could not hold the last *n* headers would come out
/// **short**, silently, which is the failure gap 117 took `All` to avoid. A
/// three-year log is the case where that can actually happen, and a tail far
/// longer than the default is asked for here on purpose.
#[test]
fn tm_log_on_three_years_of_log_stays_a_later_verb_and_returns_its_whole_tail() {
    let tm = history_tree();
    let (lines, bytes) = write_log(&tm, 1_095);
    let label = format!(" (gap 129 3y log: {lines} lines, {bytes} bytes)");
    let _serial = SERIAL.lock().unwrap_or_else(|poisoned| poisoned.into_inner());

    // Genesis first, so what follows is a later verb and not the one-off
    // rebuild every upgrade pays (gap 99). Its own bound is FIRST_VERB.
    let (code, out, first) = timed(&tm, &["drop", "^z2"], FIRST_VERB);
    assert_eq!(code, 0, "{out}");
    eprintln!("latency{label}: the first verb (genesis) {first:?}");

    // Every `tm log` spelling, each at the scope §11.1 gives it: a bare tail
    // and `--item` ask `All`, `--since` asks `Dates`.
    for (what, args) in [
        ("tm log (bare, the default tail of 20; All)", vec!["log"]),
        ("tm log --tail 200 (All)", vec!["log", "--tail", "200"]),
        ("tm log --item ^y1 (All)", vec!["log", "--item", "^y1"]),
        ("tm log --since 7d (Dates)", vec!["log", "--since", "7d"]),
        ("tm --json log --tail 200 (All)", vec!["--json", "log", "--tail", "200"]),
    ] {
        let (code, out, took) = timed(&tm, &args, LATER_VERB);
        assert_eq!(code, 0, "`tm {}`: {out}", args.join(" "));
        eprintln!("latency{label}: {what} {took:?}");
        assert!(took < LATER_VERB, "`tm {}` took {took:?} (bound {LATER_VERB:?})", args.join(" "));
    }

    // **The behavioural half.** The tail comes back whole, and `total` is the
    // log's all-time entry count rather than the row count of the scope it
    // asked for (gap 136's settlement, §11.4 step 5).
    let doc = tm.json_at(AT, &["log", "--tail", "200"]);
    let entries = doc["entries"].as_array().expect("entries");
    assert_eq!(
        entries.len(),
        200,
        "a `--tail 200` over three years came back with {} entries — the scope could not hold it",
        entries.len()
    );
    let total = doc["total"].as_u64().expect("total");
    assert!(
        total >= lines as u64,
        "`total` is {total}, below the {lines} lines written: it is the scope's rows, not the log's count"
    );
    // The rows really are the newest ones, in order: a tail that came back
    // whole but stale would pass the count assertion alone.
    let first_t = entries[0]["t"].as_str().expect("a t").to_string();
    let last_t = entries[199]["t"].as_str().expect("a t").to_string();
    assert!(first_t < last_t, "the tail is not in order: {first_t} then {last_t}");
    eprintln!("latency{label}: --tail 200 returned 200 entries, total {total}, {first_t}..{last_t}");
}

// ---------------------------------------------------------------------------
// T18 (stage 6 W-42 track S; the owner's D82, README gaps 4150 and 4152): the
// PLANNER call itself.
//
// R3 puts one kernel call on `tm plan`, `tm now` and every TUI reload: the
// ranked capacity request `tm plan` sends today with the `planner` section the
// body swap adds — `kernel_capacity::planner_request`, which `tm check` already
// sends (parity P78).  T17 (`kernel/tm-kernel-ffi/tests/stack.rs`) times the
// capacity call and not this one, so nothing here measured the call R3 adds
// until this row.  It is timed INSIDE THE BINARY, on the request the binary
// itself builds — the planner call is `tm check`'s last kernel call, and the FFI
// writes one `kernel call: <kinds>` line before every call
// (`tm_kernel_ffi::TRACE_CALLS_ENV`), so the call is the stretch from its trace
// line to the next one or, when it is the verb's last, to the end of the verb's
// stderr.  That stretch also holds the bridge's parse of the response, which R3
// pays as well.
//
// The trees are this file's own: §4.3's example tree (`tm init --example`), T11's
// three-year tree (`history_tree` + `write_log(1_095)`, swept by its first verb)
// and T14's two far-deadline trees (a due three and ten years out, so the
// lookahead runs to 1,097 and 3,652 days).  `tm plan`'s own wall time is
// printed beside each, because R3's `tm plan` is today's `tm plan` with its
// capacity call carrying the planner section.

/// What one traced verb did: its exit code and stdout, its wall time, the
/// `kernel call:` lines it wrote, and the duration of each call that carried a
/// `planner` section.
struct Traced {
    code: i32,
    out: String,
    wall: Duration,
    calls: Vec<String>,
    planner: Vec<Duration>,
}

/// Run the binary at `now` with `TM_TRACE_KERNEL_CALLS` set and its stderr read
/// line by line as it is written, killing it once `limit` has passed (as
/// [`timed_at`] does).
fn traced_at(tm: &Tm, now: &str, args: &[&str], limit: Duration) -> Traced {
    use std::io::BufRead;
    let log = tm.tmp.path().join(format!("traced-{}-{now}.out", args.join("-").replace('^', "")));
    let file = fs::File::create(&log).expect("output file");
    let start = Instant::now();
    let mut child = Command::new(env!("CARGO_BIN_EXE_tm"))
        .arg("--dir")
        .arg(&tm.plan)
        .arg("--now")
        .arg(now)
        .args(args)
        .env(tm_kernel_ffi::TRACE_CALLS_ENV, "1")
        .stdout(Stdio::from(file))
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn tm");
    let stderr = child.stderr.take().expect("the child's stderr");
    let reader = std::thread::spawn(move || {
        let mut lines = Vec::new();
        for line in std::io::BufReader::new(stderr).lines() {
            match line {
                Ok(l) => lines.push((Instant::now(), l)),
                Err(_) => break,
            }
        }
        (lines, Instant::now())
    });
    let code = loop {
        if let Some(status) = child.try_wait().expect("wait") {
            break status.code().unwrap_or(-1);
        }
        if start.elapsed() > limit {
            let _ = child.kill();
            let _ = child.wait();
            panic!("`tm {}` was still running after {limit:?}", args.join(" "));
        }
        std::thread::sleep(Duration::from_millis(1));
    };
    let wall = start.elapsed();
    let (lines, eof) = reader.join().expect("the stderr reader");
    let calls: Vec<(Instant, String)> = lines
        .into_iter()
        .filter_map(|(t, l)| l.strip_prefix("kernel call: ").map(|k| (t, k.to_string())))
        .collect();
    let planner = calls
        .iter()
        .enumerate()
        .filter(|(_, (_, k))| k.split('+').any(|s| s == "planner"))
        .map(|(i, (t, _))| calls.get(i + 1).map_or(eof, |(next, _)| *next).duration_since(*t))
        .collect();
    let out = fs::read_to_string(&log).unwrap_or_default();
    Traced { code, out, wall, calls: calls.into_iter().map(|(_, k)| k).collect(), planner }
}

/// One tree's T18 figures: `tm check` (which carries the planner call) and
/// `tm plan`, at `now`, printed under `label`.
fn t18_row(tm: &Tm, now: &str, label: &str) -> (Duration, Duration, Duration) {
    let (code, out, plan) = timed_at(tm, now, &["plan"], FIRST_VERB);
    assert_eq!(code, 0, "{label}: `tm plan`: {out}");
    // `tm check` is held to the band every first verb here is held to, REUSED
    // (W-42 repair, README gap 4335): this read `Duration::from_secs(600)`, a
    // kill limit minted for one row, while every other row reuses `FIRST_VERB`
    // or `LATER_VERB` — and a limit nothing else answers to is a bound no
    // measurement can move.
    let check = traced_at(tm, now, &["check"], FIRST_VERB);
    assert_eq!(check.code, 0, "{label}: `tm check`: {}", check.out);
    assert_eq!(check.out.trim(), "no problems", "{label}: {}", check.out);
    // It IS the day R3 asks for: exactly one call carried a `planner` section,
    // and it was the capacity call with its log (P78's request).
    assert_eq!(check.planner.len(), 1, "{label}: kernel calls {:?}", check.calls);
    assert!(
        check.calls.iter().any(|k| k == "capacity+log+planner"),
        "{label}: kernel calls {:?}",
        check.calls
    );
    let planner = check.planner[0];
    eprintln!(
        "T18 {label}: the planner call {planner:?}; `tm check` {:?} over {} kernel call(s); `tm plan` {plan:?}",
        check.wall,
        check.calls.len()
    );
    // **The owner's D82, held where R3 will pay it.**  R3's `tm plan` is today's
    // `tm plan` with its capacity call carrying the `planner` section, so today's
    // `tm plan` plus the planner call bounds it from above — and that sum must sit
    // inside the band every later verb here is held to, `LATER_VERB`, UNCHANGED.
    // A tree that cannot meet it is a measurement to report, never a band to move.
    assert!(
        plan + planner < LATER_VERB,
        "{label}: `tm plan` {plan:?} plus the planner call {planner:?} is past {LATER_VERB:?} — R3's `tm plan` would be"
    );
    // **And the WHAT-IF R3 puts on the TUI** (the W-42 repair, README gaps 4200
    // and 4335): `App::extend_drops` asks the same request with §9.1's
    // `overtime` key (`planwire::overtime_json`), which no shipped verb sends
    // before the swap, so no row here timed it — and it ran the SPECIFICATION
    // twice, because `PlanDiff.lean` did not import the `@[csimp]` twin:
    // 2.0-2.8 s on the example tree and 19-22 s on T14's ten-year tree, against
    // the day's 8-190 ms.  Taken as `tm check` built it (the request is traced
    // once more, untimed: printing it is not the call), asked again in this
    // process with the what-if spliced in as text — the section order is the
    // log section's build order, so it is never re-serialised — and held to the
    // band `tm plan` plus the day is held to, `LATER_VERB`, UNCHANGED.
    let (day, whatif) = t18_whatif(tm, now, label);
    eprintln!("T18 {label}: the day asked in-process {day:?}; the what-if (overtime +1 block) {whatif:?}");
    assert!(
        whatif < LATER_VERB,
        "{label}: the overtime what-if took {whatif:?}, past {LATER_VERB:?} — R3's TUI overtime box would pay it"
    );
    (planner, check.wall, plan)
}

/// `tm check`'s planner request, read off the FFI's request trace
/// (`tm_kernel_ffi::TRACE_REQUESTS_ENV`).
fn t18_planner_request(tm: &Tm, now: &str, label: &str) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_tm"))
        .arg("--dir")
        .arg(&tm.plan)
        .arg("--now")
        .arg(now)
        .arg("check")
        .env(tm_kernel_ffi::TRACE_CALLS_ENV, "1")
        .env(tm_kernel_ffi::TRACE_REQUESTS_ENV, "1")
        .output()
        .expect("spawn tm");
    let err = String::from_utf8_lossy(&out.stderr);
    let mut planners = err
        .lines()
        .filter_map(|l| l.strip_prefix("kernel request: "))
        .filter(|r| r.contains("\"planner\":{"));
    let request = planners.next().unwrap_or_else(|| panic!("{label}: `tm check` traced no planner request"));
    assert!(planners.next().is_none(), "{label}: `tm check` traced two planner requests");
    request.to_string()
}

/// The day and the what-if, each one in-process call of the request `tm check`
/// built (the what-if extends the running block, else the first candidate, by
/// one block), on a thread with the binary's own main-thread stack.
fn t18_whatif(tm: &Tm, now: &str, label: &str) -> (Duration, Duration) {
    let request = t18_planner_request(tm, now, label);
    let parsed: serde_json::Value = serde_json::from_str(&request).expect("the traced request parses");
    let id = parsed["planner"]["state"]["active"]["id"]
        .as_str()
        .or_else(|| parsed["capacity"]["candidates"]["items"][0]["id"].as_str())
        .unwrap_or_else(|| panic!("{label}: no running block and no candidate to extend"))
        .to_string();
    let whatif = request.replacen(
        "\"planner\":{",
        &format!("\"planner\":{{\"overtime\":{{\"id\":\"{id}\",\"blocks\":1}},"),
        1,
    );
    let label = label.to_string();
    std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || {
            let ask = |req: &str| {
                let t = Instant::now();
                let resp = tm_kernel_ffi::call(req).expect("the kernel answers");
                (t.elapsed(), resp)
            };
            let (day, resp) = ask(&request);
            let v: serde_json::Value = serde_json::from_str(&resp).expect("the day's response parses");
            assert!(v["ok"]["plan"]["day"].is_string(), "{label}: the day: {resp:.300}");
            let (took, resp) = ask(&whatif);
            let w: serde_json::Value = serde_json::from_str(&resp).expect("the what-if's response parses");
            assert!(w["ok"]["plan"]["overtime"].is_object(), "{label}: the what-if: {resp:.300}");
            assert_eq!(
                w["ok"]["plan"]["segments"], v["ok"]["plan"]["segments"],
                "{label}: the what-if moved the day it was asked beside"
            );
            (day, took)
        })
        .expect("a thread")
        .join()
        .expect("the in-process kernel call")
}

/// **T18: the planner call R3 adds, on the example tree and on T11's and T14's
/// trees** (the owner's D82, README gaps 4150 and 4152).
#[test]
fn t18_the_planner_call_on_the_example_three_year_and_far_deadline_trees() {
    let _serial = SERIAL.lock().unwrap_or_else(|poisoned| poisoned.into_inner());

    // §4.3's example tree, at the instant it is dated for.
    let ex = Tm::empty();
    let out = ex.run_at(cli_common::NOW, &["init", "--example"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    t18_row(&ex, cli_common::NOW, "example tree");

    // T11's tree: three years of log, swept by its first verb.
    let t11 = history_tree();
    let (lines, bytes) = write_log(&t11, 1_095);
    let (code, out, _) = timed(&t11, &["drop", "^a1"], FIRST_VERB);
    assert_eq!(code, 0, "{out}");
    t18_row(&t11, AT, &format!("T11 tree (3y log: {lines} lines, {bytes} bytes)"));

    // T14's trees: a due three and ten years out.
    let t14 = history_tree();
    let (code, out, _) = timed(&t14, &["drop", "^a1"], FIRST_VERB);
    assert_eq!(code, 0, "{out}");
    let backlog = fs::read_to_string(t14.plan.join("backlog.md")).expect("backlog");
    for (years, due, days) in [(3, "2029-09-14", 1097), (10, "2036-09-12", 3652)] {
        write(&t14, "backlog.md", &format!("{backlog}- [ ] 3 2h A deadline {years} years out due:{due} ^far{years}\n"));
        t18_row(&t14, AT, &format!("T14 tree, a due {years} years out ({days} lookahead days)"));
    }
}
