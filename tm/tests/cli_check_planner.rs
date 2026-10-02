//! **`tm check` names a refusal of the day `tm plan` will ask the kernel for** —
//! the W-41 repair (README gaps 4130 and 4142; parity P78).
//!
//! A tab (or a no-break space) after a line's `ci` digit is a separator to the
//! host and part of a word to the kernel (README gap 32), so the two read the
//! line's `ci` differently and the owner's D80 refuses the day BY NAME
//! (`ciDisagrees`). Fork 4748911 plans it; until this repair `tm check` printed
//! "no problems" while R3's `tm plan` would refuse it.

mod cli_common;

use cli_common::Tm;

const LINE: &str = "- [ ] 3 1b Claude Code drafts tests";

/// `plan-basic` with `^t4`'s line edited by hand: `sep` after the `ci` digit.
fn edited(sep: &str) -> Tm {
    let tm = Tm::new();
    let path = tm.plan.join("week/2026-W37.md");
    let text = std::fs::read_to_string(&path).expect("the week file");
    assert!(text.contains(LINE), "the fixture's ^t4 line");
    std::fs::write(&path, text.replace(LINE, &LINE.replacen("3 1b", &format!("3{sep}1b"), 1))).expect("the hand edit");
    tm
}

/// **Named at the line, an error, exit 2** — for a tab and for a no-break space;
/// the unedited tree has no problems.
#[test]
fn a_ci_the_kernel_reads_otherwise_is_named_at_its_line() {
    for sep in ["\t", "\u{a0}"] {
        let tm = edited(sep);
        let out = tm.run_at(cli_common::NOW, &["check"]);
        assert_eq!(out.code, 2, "{sep:?}: {}{}", out.stdout, out.stderr);
        assert!(
            out.stdout.starts_with("week/2026-W37.md:19: error[planner-refusal]: kernel refusal: ciDisagrees t4 wire 3 plan 4"),
            "{sep:?}: {}",
            out.stdout
        );
        assert!(out.stdout.trim_end().ends_with("1 error, 0 warnings"), "{}", out.stdout);
    }
    let tm = Tm::new();
    let out = tm.run_at(cli_common::NOW, &["check"]);
    assert_eq!((out.code, out.stdout.trim()), (0, "no problems"), "{}", out.stderr);
}

/// **`--json` carries it** as a problem with its code, file, line and id.
#[test]
fn the_json_carries_the_planner_refusal() {
    let tm = edited("\t");
    let out = tm.run_at(cli_common::NOW, &["--json", "check"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let doc: serde_json::Value = serde_json::from_str(&out.stdout).expect("JSON");
    let p = &doc["problems"][0];
    assert_eq!((p["code"].as_str(), p["file"].as_str(), p["line"].as_u64()), (Some("planner-refusal"), Some("week/2026-W37.md"), Some(19)), "{doc}");
}
