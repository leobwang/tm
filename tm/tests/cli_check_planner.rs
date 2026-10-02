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
//! host reads `5` (`u8::from_str` takes a leading `+`) and the kernel's
//! `Field.parseCi` does not, so the kernel falls back to the positional `3`
//! (README gap 4162). P72 still refuses it, and `tm check` still names it.

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

/// **Named at the line, an error, exit 2** — beside the host's own warning that
/// the line gives `ci` twice; the unedited tree has no problems.
#[test]
fn a_ci_the_kernel_reads_otherwise_is_named_at_its_line() {
    let tm = edited();
    let out = tm.run_at(cli_common::NOW, &["check"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.starts_with(
            "week/2026-W37.md:19: warning[bad-value]: ci given twice (ci: wins)\n\
             week/2026-W37.md:19: error[planner-refusal]: kernel refusal: ciDisagrees t4 wire 5 plan 3"
        ),
        "{}",
        out.stdout
    );
    assert!(out.stdout.trim_end().ends_with("1 error, 1 warning"), "{}", out.stdout);
    let tm = Tm::new();
    let out = tm.run_at(cli_common::NOW, &["check"]);
    assert_eq!((out.code, out.stdout.trim()), (0, "no problems"), "{}", out.stderr);
}

/// **`--json` carries it** as a problem with its code, file, line and id.
#[test]
fn the_json_carries_the_planner_refusal() {
    let tm = edited();
    let out = tm.run_at(cli_common::NOW, &["--json", "check"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let doc: serde_json::Value = serde_json::from_str(&out.stdout).expect("JSON");
    let p = doc["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .find(|p| p["code"] == "planner-refusal")
        .unwrap_or_else(|| panic!("no planner refusal: {doc}"));
    assert_eq!((p["file"].as_str(), p["line"].as_u64()), (Some("week/2026-W37.md"), Some(19)), "{doc}");
}
