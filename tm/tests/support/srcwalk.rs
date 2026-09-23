//! **One walk of the shipped crates' sources, and one code/prose split.**
//!
//! `one_padder.rs` and `one_renderer.rs` are the two guards that enforce AGENTS
//! §5.3 — *two definitions of one concept is the bug* — and until README gap
//! **1419** each carried its **own** copy of this walk and its own copy of
//! [`code_lines`]. The copies were not equivalent, and the difference was the
//! defect §5.3 names:
//!
//! * `sources()` was the same walk twice, differing only in `rustfmt`'s line
//!   breaks. Only `one_renderer`'s copy carried the blind-spot sentence, so a
//!   reader of `one_padder` could not learn the hole, and widening one root
//!   list did not widen the other. That is the half an auditor reported.
//! * `code_lines()` had **diverged**. `one_padder`'s copy learned Rust's
//!   char-literal rule at W-23 (README gap **1201**: a `'` opens a literal only
//!   when it is one, and is otherwise a lifetime or a loop label);
//!   `one_renderer`'s did not. DRIVEN at the W-24 repair step, in the real
//!   tree: one line appended to `tm/src/cli/day.rs` —
//!   `fn w24_probe(x: &'static str) -> usize { x.len() } // SegKind::Break is
//!   "break" in prose` — put `no_second_set_of_row_words` **RED on a comment**
//!   (`1 failed`) while `one_padder` stayed `8 passed`. A guard that fails on
//!   prose is AGENTS §5.8's trapdoor, and the fix that was applied to one copy
//!   and not the other is exactly why there is now one copy.
//!
//! The same lesson landed in `kernel/citations.py` in the same step, for the
//! same reason and at the same `'`: `rust_code` and `rust_prose` were two
//! scanners of one grammar and only one had the rule (README gap **1416**).
//! Two instruments, one defect, found in one run.
//!
//! # What this walk cannot see
//!
//! It reads the **source** trees of the crates the binary is built from. A
//! padder or a renderer written in a `tests/`, `examples/` or `build.rs` file
//! is invisible to it, and so is one assembled by a macro (it reads *text*).
//! `kernel/tm-kernel-ffi/src` **is** read since gap 1419 — it is linked into
//! the binary (`tm/Cargo.toml`'s `tm-kernel-ffi` path dependency) and the old
//! two-root list omitted it while its blind-spot sentence named only tests,
//! examples and build scripts. It holds no padder and no renderer today, so it
//! costs no adjudication; what it costs is the sentence's accuracy.

use std::fs;
use std::path::{Path, PathBuf};

/// Every `.rs` file of the crates the binary is built from, as
/// `(label, text)` sorted by label.
///
/// The label is the path a human can paste into `grep`, so it is what every
/// allow-list in the two guards keys on.
#[allow(dead_code)]
pub fn sources() -> Vec<(String, String)> {
    fn walk(label: &str, root: &Path, dir: &Path, acc: &mut Vec<(String, String)>) {
        for entry in fs::read_dir(dir).expect("read_dir").flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(label, root, &path, acc);
            } else if path.extension().is_some_and(|e| e == "rs") {
                let rel = path.strip_prefix(root).expect("under src").display().to_string();
                acc.push((
                    format!("{label}/{rel}"),
                    fs::read_to_string(&path).expect("read source"),
                ));
            }
        }
    }
    let tm = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace = tm.parent().expect("workspace root").to_path_buf();
    let ffi = workspace.join("kernel").join("tm-kernel-ffi").join("src");
    let mut acc = Vec::new();
    for (label, dir) in [
        ("tm/src", tm.join("src")),
        ("tm-core/src", workspace.join("tm-core").join("src")),
        ("kernel/tm-kernel-ffi/src", ffi),
    ] {
        walk(label, &dir, &dir, &mut acc);
    }
    acc.sort();
    assert!(acc.len() > 20, "the walk found {} files; it is not reading the tree", acc.len());
    acc
}

/// **Every `.rs` file in the repository**, as `(label, text)` sorted by label,
/// where the label is the path relative to the workspace root.
///
/// [`sources()`] above is a three-entry ROOT LIST on purpose — it answers "what
/// is linked into the shipped binary" — and its own blind-spot sentence says a
/// `tests/`, `examples/` or `build.rs` file is invisible to it. That is the
/// wrong set for a guard about a TEST GENERATOR, and a fourth root typed in
/// beside the three would be the name list this campaign has now paid for six
/// times (`kernel/leanfiles.py`'s header is the record). So this is a walk with
/// a PRUNE RULE, and the rule is `leanfiles.py`'s own, ported rather than
/// invented: a directory is derived output if its name starts with `.` or it
/// holds a CACHEDIR.TAG. Nothing else is skipped.
///
/// What it cannot see is what a text walk never can: a strategy assembled by a
/// macro, or one in a crate outside this checkout.
#[allow(dead_code)]
pub fn every_rust_file() -> Vec<(String, String)> {
    fn derived(dir: &Path) -> bool {
        dir.file_name().is_some_and(|n| n.to_string_lossy().starts_with('.'))
            || dir.join("CACHEDIR.TAG").is_file()
    }
    fn walk(root: &Path, dir: &Path, acc: &mut Vec<(String, String)>) {
        for entry in fs::read_dir(dir).expect("read_dir").flatten() {
            let path = entry.path();
            if path.is_dir() {
                if !derived(&path) {
                    walk(root, &path, acc);
                }
            } else if path.extension().is_some_and(|e| e == "rs") {
                let rel = path.strip_prefix(root).expect("under root").display().to_string();
                acc.push((rel, fs::read_to_string(&path).expect("read source")));
            }
        }
    }
    let tm = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace = tm.parent().expect("workspace root").to_path_buf();
    let mut acc = Vec::new();
    walk(&workspace, &workspace, &mut acc);
    acc.sort();
    assert!(acc.len() > 100, "the walk found {} files; it is not reading the tree", acc.len());
    acc
}

/// Is the `'` at the head of `rest` opening a **char literal** rather than a
/// lifetime or a loop label? (README gap **1201**.)
///
/// `'\n'`, `'\u{2007}'` and `'x'` are literals; `'static`, `'a` and `'outer`
/// are not. The rule is the whole of Rust's: a literal is either an escape
/// (`'\`) or exactly one character closed by a second `'`. Nothing else can
/// be, because a lifetime is an identifier and an identifier of one character
/// followed by `'` would be a literal anyway.
#[allow(dead_code)]
pub fn is_char_literal(rest: &str) -> bool {
    let mut cs = rest.chars();
    if cs.next() != Some('\'') {
        return false;
    }
    match cs.next() {
        Some('\\') => true,
        Some(_) => cs.next() == Some('\''),
        None => false,
    }
}

/// Lines that are code rather than prose: `//` comments name the functions
/// that were deleted, and a guard that could not tell a comment from a call
/// would fail on its own explanation of itself.
///
/// **It strips comments; it does not guess from the first character** (the W-22
/// repair step). The old rule dropped every line whose first non-space
/// character was `*`, so that a `/* … */` block's continuation lines would not
/// be read as code — and `*acc += ratatui::text::Span::raw(s).width();` is a
/// deref-assign, ordinary Rust, dropped with them. An auditor planted exactly
/// that and the guard reported `6 passed; 0 failed`. So the block-comment state
/// is tracked, string literals are respected (a `"//"` inside one is not a
/// comment), and what comes back is each line's **code**, which may be empty.
///
/// **A `'` is a quote only when it opens a literal** ([`is_char_literal`],
/// README gap 1201). `one_renderer.rs` held a copy of this function that never
/// got that rule and went RED on a comment sitting after a `&'static str`;
/// gap **1419** is why there is one copy.
#[allow(dead_code)]
pub fn code_lines(text: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut in_block = false;
    for (i, line) in text.lines().enumerate() {
        let mut code = String::new();
        let mut chars = line.char_indices().peekable();
        let mut in_str: Option<char> = None;
        let mut escaped = false;
        while let Some((i, c)) = chars.next() {
            if in_block {
                if c == '*' && chars.peek().is_some_and(|(_, n)| *n == '/') {
                    chars.next();
                    in_block = false;
                }
                continue;
            }
            if let Some(quote) = in_str {
                code.push(c);
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == quote {
                    in_str = None;
                }
                continue;
            }
            match c {
                '"' => {
                    in_str = Some(c);
                    code.push(c);
                }
                '\'' if is_char_literal(&line[i..]) => {
                    in_str = Some(c);
                    code.push(c);
                }
                '/' if chars.peek().is_some_and(|(_, n)| *n == '/') => break,
                '/' if chars.peek().is_some_and(|(_, n)| *n == '*') => {
                    chars.next();
                    in_block = true;
                }
                _ => code.push(c),
            }
        }
        out.push((i + 1, code));
    }
    out
}
