//! **The test harness computes FNV-1a-64 in ONE place** (stage 6 W-44 track C, README gap 4581).
//!
//! The W-43 repair (README gap 4504) made the three copies an auditor named one function in
//! `cli_common`, and the class still had three members — that function, `loggen`'s and the fold
//! inside `forkplan::day_hash` — a LIST repaired where the rule is a CLASS.  W-44 made them one
//! body, `support/fnv.rs`, and this file is the gate that remembers it: a fourth body written
//! anywhere in the harness fails here by name, as `one_padder.rs` and `one_renderer.rs` hold the
//! binary to one padder and one renderer.
//!
//! **The rule, as a property.**  The harness is every `.rs` file under a `tests` directory of the
//! workspace (`srcwalk::every_rust_file`, the walk with a prune rule, not a list of roots).  A file
//! of it that spells FNV-1a-64's offset basis — in hex, with or without `_` separators, in either
//! case, or in decimal — holds an FNV body, and the one file that may is `tm/tests/support/fnv.rs`.
//! The binary's own `kernel_log::fnv1a64`, `tm-core`'s two and `tm-kernel-ffi/build.rs`'s are the
//! code under test or the build's, outside every `tests` directory, and stay apart on purpose: a
//! test's reading of the rule is independent of the code under test.
//!
//! **What it cannot see** is what a text walk never can: a body whose basis is computed rather than
//! spelled, or assembled by a macro.  This file is the one other harness file that spells the basis
//! — to search for it — and is set aside by its own path, `file!()`.

#[allow(dead_code)]
#[path = "support/srcwalk.rs"]
mod srcwalk;

/// The offset basis of FNV-1a-64, in the spellings a body could carry, normalised as [`spells_the_basis`]
/// reads a file (no `_`, lowercase).
const BASIS_SPELLINGS: [&str; 2] = ["cbf29ce484222325", "14695981039346656037"];

/// Does `text` spell FNV-1a-64's offset basis, in any of [`BASIS_SPELLINGS`]?
fn spells_the_basis(text: &str) -> bool {
    let normal: String = text.chars().filter(|c| *c != '_').flat_map(char::to_lowercase).collect();
    BASIS_SPELLINGS.iter().any(|b| normal.contains(b))
}

/// Is `rel` (a path relative to the workspace root) part of the test harness: under a `tests`
/// directory?
fn in_the_harness(rel: &str) -> bool {
    std::path::Path::new(rel).components().any(|c| c.as_os_str() == "tests")
}

#[test]
fn the_harness_computes_fnv_1a_64_in_one_place() {
    let this = std::path::Path::new(file!()).file_name().and_then(|n| n.to_str()).expect("this file's name");
    let bodies: Vec<String> = srcwalk::every_rust_file()
        .into_iter()
        .filter(|(rel, _)| in_the_harness(rel))
        .filter(|(rel, _)| !rel.ends_with(&format!("tests/{this}")))
        .filter(|(_, text)| spells_the_basis(text))
        .map(|(rel, _)| rel)
        .collect();
    assert_eq!(
        bodies,
        vec!["tm/tests/support/fnv.rs".to_string()],
        "the test harness carries an FNV-1a-64 body outside support/fnv.rs — include that file by #[path] instead"
    );
}

/// **The guard bites** (AGENTS §5.8): each spelling of the basis is seen, a separator or a case
/// does not hide it, and a file under no `tests` directory is not the harness.
#[test]
fn the_fnv_guard_sees_every_spelling_and_only_the_harness() {
    for body in [
        "let mut h: u64 = 0xcbf2_9ce4_8422_2325;",
        "let mut h = 0xCBF29CE484222325u64;",
        "let basis: u64 = 14695981039346656037;",
        "let b = 14_695_981_039_346_656_037_u64;",
    ] {
        assert!(spells_the_basis(body), "the guard does not see {body:?}");
    }
    assert!(!spells_the_basis("let h: u64 = 0x811c_9dc5; // FNV-1a-32"), "FNV-1a-32 is not the 64-bit body");
    assert!(in_the_harness("tm/tests/support/fnv.rs") && in_the_harness("tm-core/tests/x.rs"));
    assert!(!in_the_harness("tm/src/cli/kernel_log.rs") && !in_the_harness("kernel/tm-kernel-ffi/build.rs"));
}
