//! **Every verb that ends a running break writes `tm break`'s journal line** — the owner's **D97**
//! (README gap 4391, parity **P95**, W-44 track H), driven through the binary for every member of
//! the class.
//!
//! The class is read off the code, not listed: a running break is ended in exactly one place
//! (`day::end_break_at`, the one function that takes `.tm/state.json`'s break and logs its line),
//! which only `end_break` and `end_break_first_at` call; the verbs reach it through
//! `end_break_first` and `end_break_first_at`, and each writes the journal line through the one
//! writer, `note_break_ended`. [`the_class_of_verbs_that_end_a_break_is_read_off_the_code`] holds
//! that shape, so a seventh verb that ends a break without saying so fails it by name.
//!
//! Fork 4748911 wrote the line from `tm break`'s ending arm alone; the owner's D90 and the W-43
//! repair gave it to `tm interrupt` and `tm resume`; `tm start`, `tm stop` and `tm done`, which
//! end a running break the same way, wrote only their own line, so the day file's journal said
//! when a break ended for three verbs of the six.

mod cli_common;

use cli_common::Tm;

const WAKE: &str = "2026-09-07T07:00:00-05:00";

/// `HH:MM` on Monday 2026-09-07, Chicago.
fn at(hhmm: &str) -> String {
    format!("2026-09-07T{hhmm}:00-05:00")
}

/// The example tree, woken at 07:00.
fn woken() -> Tm {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at(WAKE, &["wake", "07:00"]);
    tm
}

/// `^m1` running from 09:00 and a thirty-minute break from 09:20.
fn a_block_and_a_break() -> Tm {
    let tm = woken();
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    tm.ok_at(&at("09:20"), &["break", "30m"]);
    assert!(!tm.state()["break"].is_null(), "the break is running: {}", tm.state());
    tm
}

/// The day file's journal lines (`## Log`), as written.
fn journal(tm: &Tm) -> Vec<String> {
    tm.read("day/2026-09-07.md")
        .lines()
        .skip_while(|l| *l != "## Log")
        .skip(1)
        .take_while(|l| !l.starts_with("## "))
        .filter(|l| !l.trim().is_empty())
        .map(str::to_string)
        .collect()
}

/// The journal holds `ended` exactly once, immediately followed by a line beginning `then` — the
/// break's end, then the verb that ended it.
fn says_once_then(tm: &Tm, ended: &str, then: &str) {
    let j = journal(tm);
    let hits: Vec<usize> = j.iter().enumerate().filter(|(_, l)| l.contains("break ended")).map(|(i, _)| i).collect();
    assert_eq!(hits.len(), 1, "one `break ended` line: {j:?}");
    assert_eq!(j[hits[0]], ended, "{j:?}");
    assert!(j.get(hits[0] + 1).is_some_and(|l| l.starts_with(then)), "then `{then}`: {j:?}");
}

/// The log's `break` line: its stamp, its planned and actual minutes.
fn logged_break(tm: &Tm) -> (String, u64, u64) {
    let b = tm.last_ev("break");
    (
        b["t"].as_str().unwrap_or_default().to_string(),
        b["planned_min"].as_u64().unwrap_or(0),
        b["actual_min"].as_u64().unwrap_or(0),
    )
}

/// **`tm start` over a running break** — the behaviour row D97 names: the break's line (ten
/// minutes), then `tm break`'s journal line at 09:10, then the start's.
#[test]
fn tm_start_ends_a_running_break_and_says_so() {
    let tm = woken();
    tm.ok_at(&at("09:00"), &["break", "20m"]);
    tm.ok_at(&at("09:10"), &["start", "^m1", "--energy", "3"]);
    assert_eq!(logged_break(&tm), (at("09:00"), 20, 10));
    says_once_then(&tm, "09:10 break ended 10m/20m", "09:10 start ^m1 pred=");
    assert!(tm.state()["break"].is_null(), "{}", tm.state());
}

#[test]
fn tm_stop_ends_a_running_break_and_says_so() {
    let tm = a_block_and_a_break();
    let out = tm.ok_at(&at("09:35"), &["stop"]);
    assert!(out.stdout.contains("after 20m"), "{}", out.stdout);
    assert_eq!(logged_break(&tm), (at("09:20"), 30, 15));
    says_once_then(&tm, "09:35 break ended 15m/30m", "09:35 stop ^m1 20m · 340m left");
}

#[test]
fn tm_done_ends_a_running_break_and_says_so() {
    let tm = a_block_and_a_break();
    tm.ok_at(&at("09:35"), &["done"]);
    assert_eq!(logged_break(&tm), (at("09:20"), 30, 15));
    says_once_then(&tm, "09:35 break ended 15m/30m", "09:35 done ^m1 20m/360m");
}

/// **A stated end (the owner's D79) ends the break there**, and the journal says so at that
/// instant — `tm stop --at 09:30` at 09:35: the break's ten minutes, both lines at 09:30.
#[test]
fn a_stated_end_ends_the_break_there_and_says_so_there() {
    let tm = a_block_and_a_break();
    let out = tm.ok_at(&at("09:35"), &["stop", "--at", "09:30"]);
    assert!(out.stdout.contains("after 20m"), "{}", out.stdout);
    assert_eq!(logged_break(&tm), (at("09:20"), 30, 10));
    says_once_then(&tm, "09:30 break ended 10m/30m", "09:30 stop ^m1 20m · 340m left");

    let tm = a_block_and_a_break();
    tm.ok_at(&at("09:35"), &["done", "--at", "09:30"]);
    assert_eq!(logged_break(&tm), (at("09:20"), 30, 10));
    says_once_then(&tm, "09:30 break ended 10m/30m", "09:30 done ^m1 20m/360m");
}

/// The three verbs that already said it say it once, through the one writer (no second line).
#[test]
fn the_verbs_that_already_said_it_say_it_once() {
    let tm = a_block_and_a_break();
    tm.ok_at(&at("09:35"), &["interrupt"]);
    says_once_then(&tm, "09:35 break ended 15m/30m", "09:35 interrupt ^m1");

    let tm = woken();
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    tm.ok_at(&at("09:10"), &["interrupt"]);
    tm.ok_at(&at("09:20"), &["break", "30m"]);
    tm.ok_at(&at("09:35"), &["resume"]);
    says_once_then(&tm, "09:35 break ended 15m/30m", "09:35 resume lost=25m");

    let tm = a_block_and_a_break();
    tm.ok_at(&at("09:35"), &["break"]);
    let j = journal(&tm);
    assert_eq!(j.iter().filter(|l| l.contains("break ended")).count(), 1, "{j:?}");
    assert_eq!(j.last().map(String::as_str), Some("09:35 break ended 15m/30m"), "{j:?}");
}

/// **No over-bite**: with no break running, none of the six writes the line.
#[test]
fn with_no_break_running_nothing_says_a_break_ended() {
    let tm = woken();
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    tm.ok_at(&at("09:10"), &["interrupt"]);
    tm.ok_at(&at("09:15"), &["resume"]);
    tm.ok_at(&at("09:30"), &["stop"]);
    tm.ok_at(&at("09:40"), &["start", "^m1", "--energy", "3"]);
    tm.ok_at(&at("09:50"), &["done"]);
    let j = journal(&tm);
    assert!(!j.iter().any(|l| l.contains("break ended")), "{j:?}");
}

/// **`tm undo` takes the journal line back with the verb**: the day file, the log's compensation
/// and the running break, as before the start.
#[test]
fn undo_takes_the_line_back_with_the_start() {
    let tm = woken();
    tm.ok_at(&at("09:00"), &["break", "20m"]);
    let before = tm.read("day/2026-09-07.md");
    tm.ok_at(&at("09:10"), &["start", "^m1", "--energy", "3"]);
    tm.ok_at(&at("09:11"), &["undo"]);
    assert_eq!(tm.read("day/2026-09-07.md"), before);
    assert!(!tm.state()["break"].is_null(), "the break runs again: {}", tm.state());
}

/// Every function of a source file, `(name, body)`, cut at its `fn` lines, `//` comments dropped.
fn bodies(text: &str) -> Vec<(String, String)> {
    let lines: Vec<&str> = text.lines().map(|l| l.find("//").map_or(l, |i| &l[..i])).collect();
    let starts: Vec<(usize, String)> = lines
        .iter()
        .enumerate()
        .filter_map(|(i, l)| {
            let t = l.trim_start();
            let rest = ["pub(crate) fn ", "pub fn ", "fn "].iter().find_map(|p| t.strip_prefix(p))?;
            Some((i, rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect()))
        })
        .collect();
    starts
        .iter()
        .enumerate()
        .map(|(n, (i, name))| {
            let end = starts.get(n + 1).map_or(lines.len(), |(j, _)| *j);
            (name.clone(), lines[*i + 1..end].join("\n"))
        })
        .collect()
}

/// **The class, read off the code** (the body shapes, not a list of verbs): over every source
/// file of the binary and of `tm-core`,
///
/// * a running break is TAKEN out of the state (`.break_.take()`) in `end_break_at` alone, and set
///   to nothing (`.break_ = None`) only where no break can be running — `tm wake`, which refuses
///   over one first (D76, D81) — or where a state is built afresh;
/// * `end_break_at` is called by `end_break` and `end_break_first_at` alone, `end_break` by
///   `end_break_first` alone — so every verb ends a break through the two bodies;
/// * every function that calls `end_break_first` or `end_break_first_at` writes the line through
///   `note_break_ended`.
#[test]
fn the_class_of_verbs_that_end_a_break_is_read_off_the_code() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut takes = Vec::new();
    let mut clears = Vec::new();
    let mut calls_at = Vec::new();
    let mut calls_now = Vec::new();
    let mut silent = Vec::new();
    let mut enders = Vec::new();
    let mut stack = vec![root.join("tm/src"), root.join("tm-core/src")];
    while let Some(dir) = stack.pop() {
        for e in std::fs::read_dir(&dir).expect("a source directory").flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
                continue;
            }
            if p.extension().is_none_or(|x| x != "rs") {
                continue;
            }
            let rel = p.strip_prefix(&root).expect("inside").to_string_lossy().replace('\\', "/");
            let text = std::fs::read_to_string(&p).expect("a source file");
            for (name, body) in bodies(&text) {
                let here = format!("{rel}:{name}");
                if body.contains(".break_.take()") {
                    takes.push(here.clone());
                }
                if body.contains(".break_ = None") {
                    clears.push(here.clone());
                }
                if body.contains("end_break_at(") {
                    calls_at.push(here.clone());
                }
                if body.contains("end_break(") {
                    calls_now.push(here.clone());
                }
                if body.contains("end_break_first(") || body.contains("end_break_first_at(") {
                    enders.push(here.clone());
                    if !body.contains("note_break_ended(") && name != "end_break_first" {
                        silent.push(here);
                    }
                }
            }
        }
    }
    takes.sort();
    clears.sort();
    calls_at.sort();
    calls_now.sort();
    enders.sort();
    assert_eq!(takes, ["tm/src/cli/day.rs:end_break_at"], "a second place takes a running break");
    assert_eq!(clears, ["tm/src/cli/day.rs:wake"], "a running break set to nothing outside `tm wake`");
    assert_eq!(calls_at, ["tm/src/cli/day.rs:end_break", "tm/src/cli/day.rs:end_break_first_at"]);
    assert_eq!(calls_now, ["tm/src/cli/day.rs:end_break_first"]);
    assert!(silent.is_empty(), "a verb that ends a running break and writes no journal line: {silent:?}");
    // The six members, by name — read off the code above, and printed so a reader sees the class.
    let verbs: Vec<&str> = enders
        .iter()
        .map(|e| e.rsplit(':').next().unwrap_or_default())
        .filter(|n| *n != "end_break_first")
        .collect();
    assert_eq!(verbs, ["done", "interrupt", "resume", "start", "stop", "take_break"], "{enders:?}");
}
