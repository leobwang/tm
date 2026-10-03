//! **One reading of a date for the kernel and the host: the signed-year worlds** — stage 6 W-43
//! track G (README gap 4346).
//!
//! `tm-core` reads an item line's dates with chrono 0.4.45's generic parser through
//! `model::parse_date` (`due:`'s date and `waiting:`, ten UTF-8 bytes, `%Y-%m-%d`),
//! `model::parse_datetime` (`due:`'s date-time, `at:` and an absolute `win:`, sixteen bytes,
//! `%Y-%m-%dT%H:%M`) and `model::parse_time` (five bytes, `%H:%M`), and fork 4748911 reads with the
//! same three.  chrono's `%Y` is SIGNED, so `+2026-9-07T12:50` is 2026-09-07 12:50 and
//! `+2026-9-05` is 2026-09-05 to the host.  Until W-43 the kernel's line grammar read a date with a
//! reader of its own (four digits, two, two) and read NO date from a signed spelling: the host and the
//! kernel planned the same tree from two readings of one wall.  Since W-43 the line reads through
//! chrono's readers (`Log.instDate?`, `Field.parseDT`, `Field.parseTime`), one reading of a date.
//!
//! **The world**: `plan-basic` with four of its dated lines respelled with a sign and the same value —
//!
//! | line | `plan-basic` | the signed world |
//! |---|---|---|
//! | `^g1`, today's meeting | `at:2026-09-07T12:50/13:50` | `at:+2026-9-07T12:50/13:50` |
//! | `^a3`, a window | `win:2026-09-07T09:00/21:00` | `win:+2026-9-07T09:00/21:00` |
//! | `^d1`, a deadline | `due:2026-09-11T23:59` | `due:+2026-9-11T23:59` |
//! | `^a4`, a wait | `waiting:2026-09-05` | `waiting:+2026-9-05` |
//!
//! * [`the_host_reads_each_signed_line_as_its_unsigned_twin`] — the host's own reader, by value.
//! * [`tm_check_says_nothing_on_the_signed_world`] — `tm check`, which asks the kernel for R3's
//!   day (P78), says `no problems`, as on `plan-basic`.
//! * [`the_kernel_plans_the_signed_world_as_its_unsigned_twin`] — the kernel's planned day on the
//!   signed world EQUALS `plan-basic`'s, by value.  Both sides are the kernel, so it survives R3;
//!   what makes it a comparison with the fork is the first test, which is the fork's own reader.
//!   Against the kernel at `0984304` it FAILS: the kernel read no `at:` on `^g1`'s calendar line and
//!   refused the whole tree, `itemCheck: fileKindShape` (README W-43 track G, §5).
//! * [`a_date_before_year_one_is_read_by_the_host_and_not_by_the_kernel`] — parity P88, the
//!   reading that stays: `due:0000-01-01` is the year 0 to the host and no date to the kernel.
//! * [`a_deadline_outside_the_calendar_is_named_by_tm_check`] — P88 as the binary shows it: a
//!   deadline in the year 0 or past 9999 is refused on the planner's wire, and `tm check` names it.

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[allow(dead_code)]
#[path = "support/planreq.rs"]
mod planreq;

#[allow(dead_code)]
#[path = "support/forkday.rs"]
mod forkday;

#[allow(dead_code)]
#[path = "support/forkclass.rs"]
mod forkclass;

#[allow(dead_code)]
#[path = "support/plangen.rs"]
mod plangen;

#[allow(dead_code)]
#[path = "support/forkplan.rs"]
mod forkplan;

#[allow(dead_code)]
#[path = "support/forkgrid.rs"]
mod forkgrid;

mod cli_common;

use std::path::Path;

use chrono::DateTime;
use chrono_tz::Tz;

use tm_core::grammar::{parse_line, ParseCtx};
use tm_core::model::{Item, Shape};
use tm_core::planwire::KernelDay;
use tm_core::store::RuntimeState;

use cli_common::Tm;
use forkclass::{Built, ClassWorld};

/// `(file, the line in plan-basic, the same line with a signed date)`.
const EDITS: [(&str, &str, &str); 4] = [
    (
        "calendar/2026-W37.md",
        "- [ ] 3 Meeting w/ host      at:2026-09-07T12:50/13:50 loc:zoom ^g1",
        "- [ ] 3 Meeting w/ host      at:+2026-9-07T12:50/13:50 loc:zoom ^g1",
    ),
    (
        "backlog.md",
        "- [ ] 1 Pick up package  win:2026-09-07T09:00/21:00 dur:20m ^a3",
        "- [ ] 1 Pick up package  win:+2026-9-07T09:00/21:00 dur:20m ^a3",
    ),
    (
        "week/2026-W37.md",
        "- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1",
        "- [ ] 4 6b CS 234 pset 2                @O3 due:+2026-9-11T23:59 max:2b/d ^d1",
    ),
    (
        "backlog.md",
        "- [?] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4",
        "- [?] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d waiting:+2026-9-05 ^a4",
    ),
];

/// The files `plan-basic` holds, in the order the separator worlds read them.
const FILES: [&str; 8] = [
    "month/2026-09.md",
    "week/2026-W37.md",
    "backlog.md",
    "routines.md",
    "optional.md",
    "calendar/2026-W37.md",
    "day/2026-09-07.md",
    "inbox.md",
];

fn tz() -> Tz {
    tm_core::config::Config::default().tz
}

/// `text` with every edit of `file` applied (`signed`), or untouched.
fn edited(file: &str, text: String, signed: bool) -> String {
    let mut text = text;
    if signed {
        for (f, from, to) in EDITS {
            if f == file {
                assert!(text.contains(from), "the fixture's line: {from}");
                text = text.replacen(from, to, 1);
            }
        }
    }
    text
}

/// `plan-basic`'s documents as `(path, text)`, signed or not.
fn texts(signed: bool) -> Vec<(String, String)> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-core/tests/fixtures/plan-basic");
    FILES
        .iter()
        .map(|rel| {
            let text = std::fs::read_to_string(dir.join(rel)).unwrap_or_else(|e| panic!("{rel}: {e}"));
            (rel.to_string(), edited(rel, text, signed))
        })
        .collect()
}

/// The world planned at [`cli_common::NOW`]: no log, the default state — the tree `tm check` asks
/// about.
fn world(signed: bool) -> Built {
    let now = DateTime::parse_from_rfc3339(cli_common::NOW).expect("NOW").with_timezone(&tz());
    Built::of(ClassWorld { docs: texts(signed), log: String::new(), state: RuntimeState::default(), now, mult: None, ratio: None })
}

/// **The kernel's day on a world**, asked as R3's host asks it (`forkplan::request_with_loc`).
fn kernel_of(b: &Built) -> Result<KernelDay, String> {
    let (req, order) = forkplan::request_with_loc(b, None);
    planreq::kernel_day_of(&planreq::call(&req), &b.request_world(), &order).map(|(k, _)| k)
}

/// The host's reader on one line of `file`.
fn host_item(file: &str, line: &str) -> Item {
    parse_line(line, &ParseCtx::new(file, 60)).expect("the host reads the line as an item")
}

/// The dated half of what the host reads on a line: its shape and its wait.
fn dates(i: &Item) -> String {
    let shape = match &i.shape {
        Shape::None => "none".to_string(),
        Shape::Point { due } => format!("point {due}"),
        Shape::Interval { start, end } => format!("interval {start} {end}"),
        Shape::Window { range, dur } => format!("window {range} {dur:?}"),
    };
    format!("{shape} waiting {:?} problems {:?}", i.stamps.waiting_since, i.problems)
}

/// `plan-basic` as a binary-driven tree, signed or not.
fn tree(signed: bool) -> Tm {
    let tm = Tm::new();
    let mut files: Vec<&str> = EDITS.iter().map(|(f, _, _)| *f).collect();
    files.sort();
    files.dedup();
    for file in files {
        let path = tm.plan.join(file);
        let text = std::fs::read_to_string(&path).expect("the fixture file");
        std::fs::write(&path, edited(file, text, signed)).expect("the hand edit");
    }
    tm
}

/// **The host reads each signed line as its unsigned twin**, by value — the fork's own reader.
#[test]
fn the_host_reads_each_signed_line_as_its_unsigned_twin() {
    for (file, plain, signed) in EDITS {
        let (p, s) = (host_item(file, plain), host_item(file, signed));
        assert_ne!(dates(&p), "none waiting None problems []", "{plain}: the control reads a date");
        assert_eq!(dates(&s), dates(&p), "{signed}: the host reads the signed spelling as the plain one");
    }
}

/// **`tm check` says nothing on the signed world**, as on `plan-basic`.
#[test]
fn tm_check_says_nothing_on_the_signed_world() {
    for signed in [false, true] {
        let out = tree(signed).run_at(cli_common::NOW, &["check"]);
        assert_eq!((out.code, out.stdout.trim()), (0, "no problems"), "signed {signed}: {}", out.stderr);
    }
}

/// **The kernel plans the signed world as its unsigned twin**, by value — the wall `^g1` stands
/// in, the window `^a3` is offered in, `^d1`'s deadline and `^a4`'s wait, each read once.
#[test]
fn the_kernel_plans_the_signed_world_as_its_unsigned_twin() {
    let base = kernel_of(&world(false)).expect("plan-basic's day");
    let bv = serde_json::to_value(&base.day).expect("a day serialises");
    assert!(
        bv["segments"].as_array().expect("rows").iter().any(|r| r["item"] == "g1"),
        "the control: plan-basic's day draws ^g1's meeting: {bv}"
    );
    let k = kernel_of(&world(true)).unwrap_or_else(|e| panic!("the kernel refused the signed world: {e}"));
    assert_eq!(serde_json::to_value(&k.day).expect("a day serialises"), bv, "the kernel's day on the signed world");
}

/// **What stays read otherwise — parity P88.**  A date before 0001-01-01 is a date to chrono
/// (`due:0000-01-01` is the year 0, `due:-001-01-01` the year −1) and no `Cal.Day` (`Day := Nat`,
/// AGENTS §4), so the host reads a deadline and the kernel reads none.  The host's half is held
/// here; the kernel's is `Field.a_date_before_year_one_is_no_date_on_the_line`.
#[test]
fn a_date_before_year_one_is_read_by_the_host_and_not_by_the_kernel() {
    for (line, year) in [
        ("- [ ] 1b Ancient deadline due:0000-01-01 ^z1", "0000-01-01"),
        ("- [ ] 1b Ancient deadline due:-001-01-01 ^z1", "-0001-01-01"),
    ] {
        let i = host_item("backlog.md", line);
        assert_eq!(dates(&i), format!("point {year} waiting None problems []"), "{line}");
    }
}

/// **P88, as the binary shows it**: a deadline outside the kernel's calendar — the year 0, or past 9999
/// (which the line reads since W-43) — reaches the planner's wire on the host's candidate, whose `due` the
/// kernel reads with RFC 3339's date and refuses by name, so `tm check` names the day R3's `tm plan`
/// would refuse.  Fork 4748911 says "no problems" on both trees (README W-43 track G, §4, driven).  This
/// pins the departure: a step that moves either bound fails here and is seen.
#[test]
fn a_deadline_outside_the_calendar_is_named_by_tm_check() {
    let plain = "- [ ] 5 10b Workshop paper draft  @O2 due:2026-11-20 #soundcode ^d2";
    for spelled in ["due:0000-01-01", "due:+10000-1-7"] {
        let tm = Tm::new();
        let path = tm.plan.join("backlog.md");
        let text = std::fs::read_to_string(&path).expect("backlog.md");
        assert!(text.contains(plain), "the fixture's ^d2 line");
        std::fs::write(&path, text.replacen("due:2026-11-20", spelled, 1)).expect("the hand edit");
        let out = tm.run_at(cli_common::NOW, &["check"]);
        assert_eq!(out.code, 2, "{spelled}: {}{}", out.stdout, out.stderr);
        assert!(
            out.stdout.contains("planner-refusal") && out.stdout.contains("badCandidate") && out.stdout.contains(" due"),
            "{spelled}: {}",
            out.stdout
        );
        // **At the line** (README gap 4503, the W-43 repair): the kernel names the candidate by its
        // position in the request, and `tm check` reads the record's id back and prints the item's
        // file and line — `badCandidate 13 due` alone named no line a user could find.
        let line = text.lines().position(|l| l == plain).expect("the line") + 1;
        assert!(
            out.stdout.starts_with(&format!("backlog.md:{line}: error[planner-refusal]")),
            "{spelled}: {}",
            out.stdout
        );
        let doc = tm.run_at(cli_common::NOW, &["--json", "check"]);
        let doc: serde_json::Value = serde_json::from_str(&doc.stdout).expect("JSON");
        let p = doc["problems"]
            .as_array()
            .and_then(|ps| ps.iter().find(|p| p["code"] == "planner-refusal"))
            .unwrap_or_else(|| panic!("{spelled}: {doc}"));
        assert_eq!((p["file"].as_str(), p["line"].as_u64(), p["id"].as_str()), (Some("backlog.md"), Some(line as u64), Some("d2")), "{p}");
    }
}
