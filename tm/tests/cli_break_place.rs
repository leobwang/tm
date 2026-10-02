//! **`tm break --where` names a place of the ONE table, or is refused by
//! name** — the campaign's D81 call on README gap 3903, parity P75, stage 6
//! W-41 track T, in D20's shape (`cli_break_args.rs`: the arguments are read
//! in both arms).
//!
//! `tm break 20m --where hammock` exited 0 and stored the word, while the
//! planner's request refuses any word but the four (`PlanWire.placeOf?`,
//! `badBreak place`) — so after R3 a typo in `--where` would stop `tm plan`.
//! The four live in one host table, `tm_core::store::BreakPlace`, which the
//! TUI's `b` then `w`/`s`/`b`/`p` reads too; fork 4748911 kept them in the TUI
//! alone and `tm break` stored any word.

mod cli_common;

use cli_common::Tm;
use tm_core::store::BreakPlace;

const AT: &str = "2026-09-08T10:00:00-05:00";

fn woken() -> Tm {
    let tm = Tm::new();
    tm.ok_at("2026-09-08T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm
}

/// **An unknown place is refused by name, in both arms, and writes nothing**;
/// `--json` carries the same sentence.
#[test]
fn an_unknown_place_is_refused_in_both_arms() {
    let tm = woken();
    let log = tm.read(".tm/log.jsonl");
    let out = tm.run_at(AT, &["break", "20m", "--where", "hammock"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        out.stderr.trim(),
        "tm: unknown break place \"hammock\" — `--where` is one of walk, seat, bed, phone (§12.6)"
    );
    assert!(tm.state()["break"].is_null(), "no break began: {}", tm.state());
    assert_eq!(tm.read(".tm/log.jsonl"), log);
    let out = tm.run_at(AT, &["--json", "break", "--where", "Walk"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc: serde_json::Value = serde_json::from_str(&out.stderr).expect("a JSON error document");
    assert!(doc["message"].as_str().is_some_and(|m| m.contains("unknown break place \"Walk\"")), "{doc}");

    // The running arm reads `--where` too (D20): refused, the break untouched.
    tm.ok_at(AT, &["break", "20m", "--where", "walk"]);
    let out = tm.run_at("2026-09-08T10:05:00-05:00", &["break", "--where", "hammock"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(tm.state()["break"]["where"], "walk", "{}", tm.state());
    assert_eq!(tm.state()["break"]["started"], "10:00", "{}", tm.state());
}

/// **Every word of the table is taken, and is what the break carries** — into
/// `.tm/state.json` and onto the `break` line it logs when it ends.
#[test]
fn every_place_of_the_table_is_taken() {
    for place in BreakPlace::all() {
        let tm = woken();
        tm.ok_at(AT, &["break", "20m", "--where", place.as_str()]);
        assert_eq!(tm.state()["break"]["where"], place.as_str());
        tm.ok_at("2026-09-08T10:20:00-05:00", &["break"]);
        assert_eq!(tm.last()["where"], place.as_str(), "{}", tm.last());
    }
}

/// **`tm break --help` lists the table's words** — the one place the four are
/// written again, as prose, held to the table here.
#[test]
fn the_help_lists_the_tables_words() {
    let tm = Tm::new();
    let out = tm.run(&["break", "--help"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    let line = out
        .stdout
        .lines()
        .find(|l| l.contains("--where"))
        .unwrap_or_else(|| panic!("no --where in {}", out.stdout));
    let help = out.stdout.split(line).nth(1).unwrap_or_default().lines().next().unwrap_or_default();
    let listed = format!("{line} {help}");
    for place in BreakPlace::all() {
        assert!(listed.contains(place.as_str()), "{} missing from {listed:?}", place.as_str());
    }
    assert!(listed.contains(&BreakPlace::words()), "{listed:?}");
}

/// **Every word of the host's table is a word the kernel's planner reads** —
/// the claim `tm_core::store::BreakPlace`'s doc makes ("a word the verb wrote is
/// a word the planner reads"), held by nothing until the W-41 repair (README gap
/// 4145). `tm check` asks the kernel for the day R3's `tm plan` sends
/// (`kernel_capacity::planner_request`, P78), whose `planner.state.break.place`
/// is the cache's word: for each of the table's words, with the break running,
/// the day is planned (`no problems`). And it bites: the same cache hand-edited
/// to a word outside the table is named `badBreak place` at exit 2.
#[test]
fn every_place_of_the_table_is_one_the_planner_reads() {
    let at = "2026-09-08T10:05:00-05:00";
    for place in BreakPlace::all() {
        let tm = woken();
        tm.ok_at(AT, &["break", "20m", "--where", place.as_str()]);
        let out = tm.run_at(at, &["check"]);
        assert_eq!((out.code, out.stdout.trim()), (0, "no problems"), "`{}`: {}{}", place.as_str(), out.stdout, out.stderr);
    }
    let tm = woken();
    tm.ok_at(AT, &["break", "20m", "--where", "walk"]);
    let path = tm.plan.join(".tm/state.json");
    let mut state: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&path).expect("state")).expect("JSON");
    state["break"]["where"] = serde_json::Value::from("hammock");
    std::fs::write(&path, serde_json::to_string(&state).expect("JSON")).expect("the hand edit");
    let out = tm.run_at(at, &["check"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("error[planner-refusal]: kernel refusal: badBreak place"), "{}", out.stdout);
}
