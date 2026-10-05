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
//!   literal) and CUTS a day into slots — §8.2 step 3's cut a planner assigns work into, seen two
//!   ways: a CALL of one of the fork's three cutters by name ([`CUTTERS`]), and since R3 deleted
//!   them with the class it orphans (README gaps 4752 and 4815, W-46), a cut written by hand into
//!   the cut's own surviving types, a `Slot {` or `Cut {` struct LITERAL ([`CUT_TYPES`]). Measured
//!   at W-45: one file, `tm-core/src/planner.rs`; after R3, none. The decoder of the kernel's day
//!   (`planwire::read_plan`), the ghost row's rebuild of a stored plan (`cli/ghost.rs`) and the
//!   TUI's placeholder day build a `DayPlan` and cut nothing; `capacity.rs` declares the cut's types
//!   and builds no day.
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
//! **What it cannot see**, declared: a planner that reimplements the slot cut by hand into types of
//! its own (it builds a day, calls no cutter and writes no `Slot` or `Cut` literal), one that builds
//! its day through a helper another file defines, a name
//! assembled by a macro, a glob import of a module that re-exports the fork's items (`use
//! crate::*;`), and `tm-core/tests` or the FFI crate's tests and examples (the test tree under
//! `tm/tests` is the region guard's).

#[allow(dead_code)]
#[path = "support/srcwalk.rs"]
mod srcwalk;

use std::path::Path;

/// The fork's planner, the file R3 deleted.
const FORK: &str = "tm-core/src/planner.rs";

/// The cuts of §8.2 step 3 a planner assigns work into — fork 4748911's three cutters, which R3
/// deleted (README gap 4752): a function of one of these names written again is a cutter again.
const CUTTERS: [&str; 3] = ["cut_slots", "cut_slots_from", "cut_slots_around"];

/// **The cut's own types** (README gap 4815): §8.2 step 3's cut is `Slot`s gathered in a `Cut`, and
/// both types outlive R3 in `tm-core/src/capacity.rs` (the frozen fork answers read slots into
/// them). With the cutters deleted, [`CUTTERS`] alone sees only a planner that brings one back by
/// name; a cut written by hand into these types is seen by its LITERAL.
const CUT_TYPES: [&str; 2] = ["Slot", "Cut"];

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

/// Whether `code` writes a struct LITERAL of the type `ty`: `ty {` with `ty` a whole identifier, and
/// not its declaration (`struct ty {`), an `impl` block (`impl ty {`, `for ty {`) or a function's
/// return type before its body (`-> ty {`).
fn constructs(code: &str, ty: &str) -> bool {
    let needle = format!("{ty} {{");
    code.match_indices(&needle).any(|(i, _)| {
        let before = code[..i].trim_end();
        !code[..i].chars().next_back().is_some_and(ident)
            && !["struct", "enum", "impl", "for", "->"].iter().any(|k| before.ends_with(k))
    })
}

/// Whether `code` cuts a day into slots: a call of a [`CUTTERS`] name, or a [`CUT_TYPES`] literal.
fn cuts(code: &str) -> bool {
    CUTTERS.iter().any(|n| calls(code, n)) || CUT_TYPES.iter().any(|t| constructs(code, t))
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
            builds_a_day(&c) && cuts(&c)
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

/// **There is one planner, and it is the fork's own file until R3 deleted it** — then none. A file
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
/// a planner that cuts by hand into the cut's own types (README gap 4815),
/// a library module or the FFI crate naming the fork, a grouped or renamed import of it, and a binary
/// file naming it once the fork is gone are each found; a file that builds a day and cuts nothing, one
/// that DEFINES a cutter or DECLARES the cut's types (and returns one), one that names the fork only
/// in a comment or a string, a longer name ending in `planner::`, and a local or a module whose name
/// merely contains the word are not.
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
    let by_hand = "pub fn plan() -> DayPlan {\n    let s = Slot { start, end, energy: 3, kind: SlotKind::Block };\n    let mut day = DayPlan::empty(d, w, 6);\n    day\n}\n";
    let by_hand_cut = "fn day() -> DayPlan {\n    let c = Cut { slots: vec![], breaks: vec![] };\n    DayPlan { date, window, budget_blocks: 0 }\n}\n";
    for (label, text) in [("tm/src/cli/again.rs", by_hand), ("tm-core/src/again.rs", by_hand_cut)] {
        let after = findings(&[f(label, text)], false);
        assert!(after.iter().any(|x| x.contains(&format!("{label} plans a day"))), "a planner cutting by hand passed: {after:?}");
    }
    let types = "pub struct Slot {\n    start: u8,\n}\nimpl Slot {\n    fn fits(&self) -> bool { true }\n}\npub struct Cut {\n    slots: Vec<Slot>,\n}\nimpl Default for Cut {\n    fn default() -> Cut {\n        todo()\n    }\n}\nfn ghost() -> Option<DayPlan> {\n    Some(DayPlan { date, window, budget_blocks: 0 })\n}\n";
    assert!(planners(&[f("tm-core/src/capacity.rs", types)]).is_empty(), "declaring the cut's types and returning one was read as a cut");
    let not_the_fork = "use crate::planwire::with_planner;\nuse tm_core::{config, planning};\nfn f() { let planner = 1; let day_planner = planner; }\n";
    assert!(findings(&[f("tm-core/src/x.rs", not_the_fork)], false).is_empty(), "a name that is not the fork's module was refused");
    let ffi = findings(&[f(FORK, planner), f("kernel/tm-kernel-ffi/src/lib.rs", caller)], true);
    assert!(ffi.iter().any(|x| x.starts_with("kernel/tm-kernel-ffi/src/lib.rs names the fork")), "the FFI crate naming the fork passed: {ffi:?}");
    let gone = findings(&[f("tm/src/cli/planning.rs", caller)], false);
    assert!(gone.iter().any(|x| x.contains("is gone")), "a call site left after R3 passed: {gone:?}");
}

/// **What adds a segment to a day, or builds one**, counted in one file's code (README gap 4881, the
/// W-46 repair): a `Segment {` literal, a `DayPlan {` literal, `DayPlan::empty(`, and a push, insert
/// or extend into a `segments` vector. A planner is a day with segments in it; the shape test above
/// reads one cut, and the reuse critic's two plants — a cloned day given rest rows by hand, and a day
/// built through a helper defined elsewhere — cut nothing and passed it.
fn day_builds(code: &str) -> usize {
    let literals = ["Segment", "DayPlan"]
        .iter()
        .map(|t| {
            let needle = format!("{t} {{");
            code.match_indices(&needle)
                .filter(|(i, _)| {
                    let before = code[..*i].trim_end();
                    !code[..*i].chars().next_back().is_some_and(ident)
                        && !["struct", "enum", "impl", "for", "->"].iter().any(|k| before.ends_with(k))
                })
                .count()
        })
        .sum::<usize>();
    let calls = ["DayPlan::empty(", "segments.push(", "segments.insert(", "segments.extend("]
        .iter()
        .map(|n| code.matches(n).count())
        .sum::<usize>();
    literals + calls
}

/// **Every site that builds a day or adds a segment to one, MEASURED after R3, with why it is not a
/// planner** — the files of [`files`] and their [`day_builds`] counts, exactly. A new site anywhere,
/// a second one in a file below, or one that left, fails by name: an enumeration a site joins to be
/// EXEMPT, never to be covered (W-27's shape), and it may only shrink.
const DAY_BUILDERS: [(&str, usize, &str); 4] = [
    ("tm-core/src/dayplan.rs", 1, "`DayPlan::empty`'s own body: the type's constructor"),
    ("tm-core/src/planwire.rs", 7, "the codec: `read_plan` decodes the kernel's day (a `Segment` and a `DayPlan` literal) and its unit tests build the days they decode"),
    ("tm/src/cli/ghost.rs", 3, "the ghost rows: a stored plan's past re-drawn from `.tm/last_plan.json`, its blocks as they were"),
    ("tm/src/tui/app.rs", 5, "the TUI's placeholder day before the kernel answers, and its ghost rows (`ghost_block_min`)"),
];

/// **Nothing builds a day or adds a segment to one but the measured sites** (README gap 4881): after
/// R3 the kernel plans every day, so a Rust site that lays segments into a day is a second planner
/// whatever it cuts.
#[test]
fn the_only_day_builders_are_the_measured_ones() {
    let mut found: Vec<(String, usize)> =
        files().iter().map(|(l, t)| (l.clone(), day_builds(&code(t)))).filter(|(_, n)| *n > 0).collect();
    found.sort();
    let mut want: Vec<(String, usize)> = DAY_BUILDERS.iter().map(|(l, n, _)| (l.to_string(), *n)).collect();
    want.sort();
    println!("day builders: {found:?}");
    assert_eq!(found, want, "a day is built, or a segment added to one, somewhere the census does not name (or a named site left): README gap 4881");
}

/// **The census bites** on the reuse critic's two plants (README gap 4881).
#[test]
fn the_day_builder_census_bites() {
    let cloned = "fn plan(d: &DayPlan) -> DayPlan {\n    let mut day = d.clone();\n    for m in (0..300).step_by(50) { day.segments.push(rest(m)); }\n    day\n}\n";
    let helper = "fn plan() -> DayPlan {\n    let mut day = DayPlan::empty(date, w, 6);\n    cut_one(&mut day);\n    day\n}\n";
    assert_eq!(day_builds(&code(cloned)), 1, "a cloned day given segments by hand");
    assert_eq!(day_builds(&code(helper)), 1, "a day built through a helper");
    assert_eq!(day_builds(&code("pub struct DayPlan {\n    date: u8,\n}\nimpl DayPlan {\n}\n")), 0, "a declaration is not a build");
}
