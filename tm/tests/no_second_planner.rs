//! **No second planner: the fork's planner is reached only where R3 removes it, and once R3 has
//! deleted it nothing plans a day in Rust** (stage 6 W-45 track C; README gap 4683).
//!
//! R3 swaps the shipped binary's day from fork 4748911's `tm-core/src/planner.rs` to the kernel's
//! and deletes the fork. `planner_classes.rs`' region guard holds the TEST tree to that (every test
//! that reaches the fork keeps it in one region, and a region holds nothing but the fork); this holds
//! everything else under `tm/` and the shipped library to it — [`files`]: the shipped crates' sources
//! (`srcwalk::sources`: `tm/src`, `tm-core/src`, `kernel/tm-kernel-ffi/src`) and every other `.rs` file
//! under `tm/` but its tests (`tm/examples`, `tm/build.rs`) — in `one_padder.rs`' shape, a property over
//! body shapes, measured, never a list of names:
//!
//! * **A planner, by its shape**: a source file that BUILDS a day (`DayPlan::empty(` or a `DayPlan {`
//!   literal) and CUTS a day into slots (a call of `cut_slots`, `cut_slots_from` or
//!   `cut_slots_around`, §8.2 step 3's cut a planner assigns work into). Measured at W-45: one file,
//!   `tm-core/src/planner.rs`. The decoder of the kernel's day (`planwire::read_plan`), the ghost row's
//!   rebuild of a stored plan (`cli/ghost.rs`) and the TUI's placeholder day build a `DayPlan` and cut
//!   nothing; `capacity.rs` cuts slots for the old capacity lookahead and builds no day.
//!   [`there_is_one_planner_and_it_is_the_forks_until_r3_deletes_it`]: at most one, it is the fork's
//!   own file while that file exists, and there is none once it is gone — so a planner copied under
//!   another name, or written again in the binary after R3, fails by its shape.
//! * **Who names the fork's planner** (its module path in code, or the module in a `use` statement —
//!   a grouped or renamed import included): while the fork's file exists, its own file and the
//!   binary's crate (`tm/src`: the call sites R3's body swap replaces — measured at W-45,
//!   `cli/planning.rs` and `tui/app.rs`); no other module of `tm-core` and nothing of the FFI crate
//!   ever. Once the file is gone, nothing names it
//!   ([`the_forks_planner_is_named_only_where_r3_removes_it`]).
//!
//! So the guard is green on both sides of R3 and the switch has nothing in it to rewrite: before it,
//! the one planner is the fork's and the binary calls it; after it, there is no planner in Rust and no
//! name of one.
//!
//! **What it cannot see**, declared: a planner that reimplements the slot cut by hand (it builds a
//! day and calls no cutter), one that builds its day through a helper another file defines, a name
//! assembled by a macro, a glob import of a module that re-exports the fork's items (`use
//! crate::*;`), and `tm-core/tests` or the FFI crate's tests and examples (the test tree under
//! `tm/tests` is the region guard's).

#[allow(dead_code)]
#[path = "support/srcwalk.rs"]
mod srcwalk;

use std::path::Path;

/// The fork's planner, the file R3 deletes.
const FORK: &str = "tm-core/src/planner.rs";

/// The cuts of §8.2 step 3 a planner assigns work into.
const CUTTERS: [&str; 3] = ["cut_slots", "cut_slots_from", "cut_slots_around"];

/// A source's code: comments dropped and string contents blanked, one string.
fn code(text: &str) -> String {
    srcwalk::code_lines(text).into_iter().map(|(_, c)| blank_strings(&c)).collect::<Vec<_>>().join("\n")
}

/// A code line with every string literal's content removed (its quotes kept).
fn blank_strings(line: &str) -> String {
    let (mut out, mut in_str, mut escaped) = (String::new(), false, false);
    for c in line.chars() {
        if in_str {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_str = false;
                out.push(c);
            }
            continue;
        }
        if c == '"' {
            in_str = true;
        }
        out.push(c);
    }
    out
}

/// Whether `code` CALLS the function `name` — `name(` as a whole identifier, not after `fn `.
fn calls(code: &str, name: &str) -> bool {
    let needle = format!("{name}(");
    code.match_indices(&needle).any(|(i, _)| {
        let before = &code[..i];
        !before.chars().next_back().is_some_and(ident) && !before.trim_end().ends_with("fn")
    })
}

/// Whether `code` builds a day: `DayPlan::empty(` or a `DayPlan {` struct literal.
fn builds_a_day(code: &str) -> bool {
    code.contains("DayPlan::empty(") || code.match_indices("DayPlan {").any(|(i, _)| !code[..i].trim_end().ends_with("struct"))
}

/// **The planners among `files`, by their shape**: the labels of the files that build a day and cut
/// a day into slots.
fn planners(files: &[(String, String)]) -> Vec<String> {
    files
        .iter()
        .filter(|(_, text)| {
            let c = code(text);
            builds_a_day(&c) && CUTTERS.iter().any(|n| calls(&c, n))
        })
        .map(|(label, _)| label.clone())
        .collect()
}

/// An identifier character.
fn ident(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Whether `text` holds `w` as a whole word: no identifier character on either side.
fn whole(text: &str, w: &str) -> bool {
    text.match_indices(w).any(|(i, _)| !text[..i].chars().next_back().is_some_and(ident) && !text[i + w.len()..].chars().next().is_some_and(ident))
}

/// Every `use` statement of `code`, from the keyword to its `;`.
fn use_statements(code: &str) -> Vec<&str> {
    code.match_indices("use")
        .filter(|(i, _)| !code[..*i].chars().next_back().is_some_and(ident) && code[i + 3..].chars().next().is_some_and(char::is_whitespace))
        .map(|(i, _)| &code[i..code[i..].find(';').map_or(code.len(), |e| i + e)])
        .collect()
}

/// Whether `code` names the fork's planner module, in code: `tm_core::planner` or `crate::planner` as
/// whole words; a `planner::` path whose first segment is the module (no identifier character before
/// it); or the word `planner` anywhere in a `use` statement rooted at `tm_core`, `crate`, `super` or
/// `self` — a grouped or renamed import (`use tm_core::{config, planner};`, `use crate::{planner as p};`)
/// names the module by neither path.
fn names_the_fork(code: &str) -> bool {
    whole(code, "tm_core::planner")
        || whole(code, "crate::planner")
        || code.match_indices("planner::").any(|(i, _)| !code[..i].chars().next_back().is_some_and(ident))
        || use_statements(code).iter().any(|u| {
            let root = u["use".len()..].trim_start().trim_start_matches("::");
            ["tm_core", "crate", "super", "self"].iter().any(|r| root.starts_with(r)) && whole(u, "planner")
        })
}

/// **Every finding of the two properties over `files`**, given whether the fork's file exists.
fn findings(files: &[(String, String)], fork_exists: bool) -> Vec<String> {
    let mut out = Vec::new();
    let found = planners(files);
    if found.len() > 1 {
        out.push(format!("{} files plan a day by the planner's shape — a second planner: {found:?}", found.len()));
    }
    for p in &found {
        if !fork_exists {
            out.push(format!("{p} plans a day by the planner's shape, and the fork's planner is gone — the kernel is the binary's one planner (R3)"));
        } else if p != FORK {
            out.push(format!("{p} plans a day by the planner's shape, and the one planner is the fork's own file, {FORK} — a second planner"));
        }
    }
    for (label, text) in files {
        if label == FORK || !names_the_fork(&code(text)) {
            continue;
        }
        if !fork_exists {
            out.push(format!("{label} names the fork's planner, and {FORK} is gone"));
        } else if !label.starts_with("tm/src/") {
            out.push(format!("{label} names the fork's planner: only the binary's call sites may, which R3's body swap replaces"));
        }
    }
    out
}

/// **The files this guard reads**: the shipped crates' sources and every other `.rs` file under `tm/`
/// but `tm/tests` (which the region guard holds), as `(label, text)`.
fn files() -> Vec<(String, String)> {
    let mut out = srcwalk::sources();
    out.extend(srcwalk::every_rust_file().into_iter().filter(|(l, _)| l.starts_with("tm/") && !l.starts_with("tm/src/") && !l.starts_with("tm/tests/")));
    out.sort();
    out
}

/// The fork's planner file exists in this tree.
fn fork_exists() -> bool {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join(FORK).exists()
}

/// **There is one planner, and it is the fork's own file until R3 deletes it** — then none. A file
/// that builds a day and cuts slots (the planner's shape) anywhere else is a second planner.
#[test]
fn there_is_one_planner_and_it_is_the_forks_until_r3_deletes_it() {
    let files = files();
    let found = planners(&files);
    let here = fork_exists();
    println!("planners by their shape: {found:?} (the fork's planner file {})", if here { "exists" } else { "is gone" });
    let bad: Vec<String> = findings(&files, here).into_iter().filter(|f| f.contains("shape")).collect();
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    if here {
        assert_eq!(found, vec![FORK.to_string()], "the fork's planner is not seen by its shape — the guard is reading nothing");
    }
}

/// **The fork's planner is named only where R3 removes it**: while its file exists, by its own file
/// and the binary's crate (the call sites the body swap replaces); never by another module of
/// `tm-core` or by the FFI crate; and by nothing once it is gone.
#[test]
fn the_forks_planner_is_named_only_where_r3_removes_it() {
    let files = files();
    let here = fork_exists();
    let naming: Vec<&String> = files.iter().filter(|(l, t)| l != FORK && names_the_fork(&code(t))).map(|(l, _)| l).collect();
    println!("files naming the fork's planner in code, its own aside: {naming:?}");
    let bad: Vec<String> = findings(&files, here).into_iter().filter(|f| f.contains("names the fork")).collect();
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// **The shapes bite, and do not over-bite** (AGENTS §5.8), on sources written here: a second
/// planner-shaped file, a planner-shaped file outside the fork's, a planner after the fork is gone,
/// a library module or the FFI crate naming the fork, a grouped or renamed import of it, and a binary
/// file naming it once the fork is gone are each found; a file that builds a day and cuts nothing, one
/// that DEFINES a cutter, one that names the fork only in a comment or a string, a longer name ending
/// in `planner::`, and a local or a module whose name merely contains the word are not.
#[test]
fn the_planner_shapes_bite() {
    let planner = "pub fn plan() -> DayPlan {\n    let cut = capacity::cut_slots_around(a, b);\n    let day = DayPlan::empty(d, w, 6);\n    day\n}\n";
    let ghost = "fn ghost() -> Option<DayPlan> {\n    Some(DayPlan { date, window, budget_blocks: 0 })\n}\n";
    let defines = "pub fn cut_slots(a: u8) -> Cut {\n    cut_slots_from(a, 0)\n}\npub struct DayPlan {\n    date: u8,\n}\n";
    let caller = "use tm_core::planner::{self, PlanInput};\nfn f() { let d = planner::plan(&i); }\n";
    let prose = "// tm_core::planner::plan is named here\nfn f() { let s = \"planner::plan\"; let x = myplanner::y(); }\n";
    let f = |label: &str, text: &str| (label.to_string(), text.to_string());
    assert_eq!(planners(&[f(FORK, planner), f("tm/src/cli/ghost.rs", ghost), f("tm-core/src/capacity.rs", defines)]), vec![FORK.to_string()]);
    assert!(findings(&[f(FORK, planner), f("tm/src/cli/planning.rs", caller), f("tm/src/cli/ghost.rs", ghost), f("tm-core/src/x.rs", prose)], true).is_empty(), "the tree as it stands was refused");
    assert!(findings(&[f("tm/src/cli/ghost.rs", ghost), f("tm-core/src/x.rs", prose)], false).is_empty(), "the tree after R3 was refused");
    let second = findings(&[f(FORK, planner), f("tm-core/src/copy.rs", planner)], true);
    assert!(second.iter().any(|x| x.contains("a second planner")), "a second planner passed: {second:?}");
    let elsewhere = findings(&[f("tm/src/cli/day.rs", planner)], true);
    assert!(elsewhere.iter().any(|x| x.contains("tm/src/cli/day.rs plans a day")), "a planner outside the fork's file passed: {elsewhere:?}");
    let after = findings(&[f("tm/src/cli/day.rs", planner)], false);
    assert!(after.iter().any(|x| x.contains("the fork's planner is gone")), "a planner after R3 passed: {after:?}");
    let library = findings(&[f(FORK, planner), f("tm-core/src/review.rs", "use crate::planner::plan;\n")], true);
    assert!(library.iter().any(|x| x.starts_with("tm-core/src/review.rs names the fork")), "a library module naming the fork passed: {library:?}");
    for (label, import) in [
        ("tm-core/src/a.rs", "use crate::{planner as fork, store};\nfn f() { fork::plan(&i); }\n"),
        ("tm-core/src/b.rs", "pub use super::planner as p;\n"),
        ("tm/src/cli/c.rs", "use tm_core::{config, planner};\n"),
    ] {
        let gone = findings(&[f(label, import)], false);
        assert!(gone.iter().any(|x| x.starts_with(&format!("{label} names the fork"))), "a grouped or renamed import passed: {import:?} {gone:?}");
    }
    let not_the_fork = "use crate::planwire::with_planner;\nuse tm_core::{config, planning};\nfn f() { let planner = 1; let day_planner = planner; }\n";
    assert!(findings(&[f("tm-core/src/x.rs", not_the_fork)], false).is_empty(), "a name that is not the fork's module was refused");
    let ffi = findings(&[f(FORK, planner), f("kernel/tm-kernel-ffi/src/lib.rs", caller)], true);
    assert!(ffi.iter().any(|x| x.starts_with("kernel/tm-kernel-ffi/src/lib.rs names the fork")), "the FFI crate naming the fork passed: {ffi:?}");
    let gone = findings(&[f("tm/src/cli/planning.rs", caller)], false);
    assert!(gone.iter().any(|x| x.contains("is gone")), "a call site left after R3 passed: {gone:?}");
}
