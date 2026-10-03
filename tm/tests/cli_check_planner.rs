//! **`tm check` names a refusal of the day `tm plan` will ask the kernel for** —
//! the W-41 repair (README gaps 4130 and 4142; parity P78), restated at W-42
//! track G when the owner's D83 closed gap 32.
//!
//! The W-41 repair wrote this file over the world that motivated P78: a tab (or
//! a no-break space) after a line's `ci` digit was a separator to the host and
//! part of a word to the kernel, so the two read the line's `ci` differently and
//! the owner's D80 refused the day BY NAME (`ciDisagrees`, parity P72), while
//! fork 4748911 planned it. D83 made the kernel read separators as the host
//! does, and that world now names nothing (`kernel_separator_worlds.rs` holds
//! it and its three siblings). What P78 names since is a disagreement in what
//! the two readers DERIVE from a line they tokenise alike — `ci:+5`, which the
//! host read `5` (`u8::from_str` takes a leading `+`) and the kernel's
//! `Field.parseCi` did not, so the kernel fell back to the positional `3`
//! (README gap 4162). The W-42 repair closed that too: the kernel reads a
//! `ci:` value as `u8::from_str` does (`Text.readRustNat`, README gap 4330), so
//! the world names only the host's own warning now, and the refusal `tm check`
//! names is shown on a day the kernel refuses for its own reason.

mod cli_common;

use cli_common::Tm;

const LINE: &str = "- [ ] 3 1b Claude Code drafts tests     @m2 ^t4";

/// `plan-basic` with `^t4`'s line edited by hand to carry `ci:+5` beside its
/// positional `3`.
fn edited() -> Tm {
    let tm = Tm::new();
    let path = tm.plan.join("week/2026-W37.md");
    let text = std::fs::read_to_string(&path).expect("the week file");
    assert!(text.contains(LINE), "the fixture's ^t4 line");
    std::fs::write(&path, text.replace(LINE, &LINE.replacen("@m2", "ci:+5 @m2", 1))).expect("the hand edit");
    tm
}

/// **`ci:+5` beside a positional `3` is read alike** (the W-42 repair, README
/// gaps 4162 and 4330): both readers take the key's `5` (`ci:` wins), so `tm
/// check` names the host's own warning that the line gives `ci` twice and NO
/// planner refusal — until the repair it named `ciDisagrees t4 wire 5 plan 3`, a
/// refusal of a day fork 4748911 plans. The unedited tree has no problems.
#[test]
fn a_signed_ci_beside_a_positional_one_is_read_alike_and_named_by_the_host_alone() {
    let tm = edited();
    let out = tm.run_at(cli_common::NOW, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        out.stdout.trim_end(),
        "week/2026-W37.md:19: warning[bad-value]: ci given twice (ci: wins)\n0 errors, 1 warning",
        "{}",
        out.stdout
    );
    let tm = Tm::new();
    let out = tm.run_at(cli_common::NOW, &["check"]);
    assert_eq!((out.code, out.stdout.trim()), (0, "no problems"), "{}", out.stderr);
}

/// **`--json` carries a planner refusal** as a problem with its code — on the
/// last day the calendar holds, where the kernel refuses the day R3's `tm plan`
/// asks for (`badCandidate`, a candidate's `due` past its bound there: README
/// gap 4330 records it beside P71's `eveningPastTheCalendar`, a day fork 4748911
/// never reaches either).
#[test]
fn the_json_carries_the_planner_refusal() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    let out = tm.run_at("9999-12-31T09:00:00+00:00", &["--json", "check"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let doc: serde_json::Value = serde_json::from_str(&out.stdout).expect("JSON");
    let p = doc["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .find(|p| p["code"] == "planner-refusal")
        .unwrap_or_else(|| panic!("no planner refusal: {doc}"));
    assert!(p["message"].as_str().is_some_and(|m| m.starts_with("kernel refusal: ")), "{doc}");
}
