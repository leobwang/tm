//! **One item-line generator, and every reader of item lines draws from it**
//! (AGENTS §5.3: two definitions of one concept is the bug).
//!
//! Three programs sample random item lines and ask three different questions
//! about them:
//!
//! * `tm-core/tests/grammar_proptest.rs` — do the fork's own two readers,
//!   `parse_line` and `ItemLine`, agree with each other?
//! * `tm/tests/kernel_item_grammar.rs` — does the kernel's `Line.lean` read the
//!   line the way the fork reads it? (§14.4's **R2**.)
//! * `kernel/tm-kernel-ffi/examples/oracle/src/main.rs` — what does the
//!   **fork-point** Rust say about it, built outside this tree against
//!   `4748911` (owner **D21/D22**)?
//!
//! The answers are only comparable if the three draw the *same* lines, so the
//! strategies live in `tm-core/tests/grammar_common/mod.rs` and nowhere else.
//!
//! # Why this file exists — the defect it was written for
//!
//! W-25 moved the strategies out of `grammar_proptest.rs` into
//! `grammar_common/`, and `grammar_common`'s own header says the move makes
//! *"the kernel sees what the fork's proptest sees"* **a fact about one file
//! rather than a claim about two that drift**. That sentence was false when it
//! was written: a **third** copy of the same ten strategies was sitting in the
//! oracle, byte-identical but for one comment line, and both of the comments
//! pointing at it (`main.rs`'s module header and the banner over the copy) now
//! named a file that held no strategy at all. Nothing had diverged; what was
//! gone was the trail that would have made a divergence visible.
//!
//! The copy is deleted — `build-oracle.sh` copies the shared module into the
//! fork-point checkout, and **fails** if it is not there — and the oracle's
//! output is byte-identical across the change (`gen 5 1` and `gen 512 7`, same
//! md5 before and after). This file is what stops a fourth copy.
//!
//! # What each test can see, and what it cannot
//!
//! * [`one_file_defines_the_item_line_strategies`] walks **every** `.rs` file
//!   in the repository ([`srcwalk::every_rust_file`], `leanfiles.py`'s prune
//!   rule) and reads *code*, not prose ([`srcwalk::code_lines`]). It cannot see
//!   a strategy assembled by a macro, one written under a different name, or
//!   one in a crate outside this checkout.
//! * [`the_oracle_is_built_from_the_shared_module`] reads
//!   `build-oracle.sh` as text. It cannot run it: the script extracts the fork
//!   point and builds a second workspace, which is not `cargo test`'s job
//!   (AGENTS §7.3). So it pins the *wiring* — the one thing that rotted — and
//!   not the build.
//! * Neither can see the oracle **binary** on someone's disk, which may have
//!   been built before this change. That is what the script's re-extraction
//!   stamp is for.
//!
//! # Driven RED on its own class before it was kept
//!
//! A guard that has never failed is a claim, so each of these was planted in
//! the real tree and reverted, and the result of each is recorded rather than
//! assumed:
//!
//! | plant | result |
//! |---|---|
//! | `fn ws() -> impl Strategy<…>` appended to `tm/tests/kernel_item_grammar.rs` | **caught** |
//! | the same line as a `//` comment | green — it is prose, and a guard that failed on its own explanation would be AGENTS §5.8's trapdoor |
//! | `pub fn line() -> impl Strategy<…>` put back in `grammar_proptest.rs` | **caught** |
//! | `pub fn token` renamed in [`HOME`] | **caught**, by the second half — the vocabulary goes stale rather than empty |
//! | the `cp "$common"` line deleted from `build-oracle.sh` | **WENT GREEN** on the first draft, and that is why the script is read as code: `script.contains(HOME)` found the *comment above* the command. Caught now, and so is deleting the `common=` guard with it |
//! | `pub fn ws()` in a file under `.claude/` | green, and declared: the walk prunes a dot-directory, which is how a worktree stays out of the tree's own guards |

#[path = "support/srcwalk.rs"]
mod srcwalk;

use srcwalk::{code_lines, every_rust_file};

/// The one module that may define them.
const HOME: &str = "tm-core/tests/grammar_common/mod.rs";

/// The script that carries [`HOME`] into the fork-point checkout.
const SCRIPT: &str = "kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh";

/// The ten strategies, by the names they are defined under.
///
/// A **vocabulary**, and AGENTS §5.2's warning applies: a strategy added under
/// an eleventh name is invisible here until it is added, which is why the test
/// below also asserts that every name on this list is still found in [`HOME`].
/// A rename that empties this list fails rather than passing quietly.
const STRATEGIES: &[&str] =
    &["ws", "state", "est", "word", "title", "date", "time", "dur", "token", "line"];

/// A definition of one of [`STRATEGIES`]: `fn <name>(` returning `impl
/// Strategy`, with or without `pub`, at the start of a code line.
fn defines(code: &str) -> Option<&'static str> {
    let body = code.trim_start();
    let body = body.strip_prefix("pub ").unwrap_or(body);
    let body = body.strip_prefix("fn ")?;
    let name = STRATEGIES.iter().find(|n| {
        body.strip_prefix(**n).is_some_and(|rest| rest.starts_with("()"))
    })?;
    body.contains("impl Strategy").then_some(*name)
}

/// **Exactly one file defines the item-line strategies**, and it is [`HOME`].
#[test]
fn one_file_defines_the_item_line_strategies() {
    let mut elsewhere = Vec::new();
    let mut at_home = Vec::new();
    for (label, text) in every_rust_file() {
        for (line, code) in code_lines(&text) {
            if let Some(name) = defines(&code) {
                if label == HOME {
                    at_home.push(name);
                } else {
                    elsewhere.push(format!("{label}:{line}: a second `{name}()`"));
                }
            }
        }
    }
    assert!(
        elsewhere.is_empty(),
        "a second definition of an item-line strategy (AGENTS §5.3; the one is \
         `{HOME}`):\n  {}",
        elsewhere.join("\n  ")
    );
    // The other direction, so a rename cannot empty the needle and pass.
    let missing: Vec<_> = STRATEGIES.iter().filter(|n| !at_home.contains(n)).collect();
    assert!(
        missing.is_empty(),
        "{HOME} no longer defines {missing:?} — this file's vocabulary is stale, \
         not satisfied (AGENTS §5.2)"
    );
}

/// **The oracle's generator comes from [`HOME`], and its absence is fatal.**
///
/// The fork-point checkout `build-oracle.sh` extracts predates `grammar_common`
/// and cannot supply it, so the script copies it in. Both halves are asserted:
/// that it is copied, and that a missing one exits rather than building a
/// binary that samples something else.
#[test]
fn the_oracle_is_built_from_the_shared_module() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .to_path_buf();
    let script = std::fs::read_to_string(root.join(SCRIPT))
        .unwrap_or_else(|e| panic!("{SCRIPT}: {e}"));
    // **The SCRIPT's code, not its prose.** The first draft of this assertion
    // was `script.contains(HOME)`, and deleting the `cp` line left it GREEN:
    // the comment above that line names the path, so the needle found the
    // explanation instead of the command. That is the shape W-24's track P
    // recorded as gap 1324 about its own new wire, and it is why a `#` line is
    // dropped here before anything is matched.
    let code: String = script
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        code.contains(HOME),
        "{SCRIPT} no longer names {HOME} in its code; the oracle's generator is \
         the trail that rotted once already"
    );
    assert!(
        code.contains("cp \"$common\""),
        "{SCRIPT} names {HOME} but does not copy it into the fork-point checkout"
    );
    assert!(
        code.contains("exit 1"),
        "{SCRIPT} copies {HOME} without failing when it is missing"
    );

    let main = root.join("kernel/tm-kernel-ffi/examples/oracle/src/main.rs");
    let main = std::fs::read_to_string(&main).unwrap_or_else(|e| panic!("{main:?}: {e}"));
    assert!(
        main.contains("mod grammar_common;") && main.contains("use grammar_common::line;"),
        "the oracle no longer draws from the shared module"
    );
}
