//! **A workspace suite that overlaps the mutation gate is not a fact about
//! HEAD** (stage 6 W-29 repair step, kernel/README.md gap 2011).
//!
//! `kernel/mutate.py` plants a constant-folded definition in the SHARED working
//! tree, builds the kernel, and restores the file. While a plant is live the
//! tree holds a library file nobody committed, and `tm-kernel-ffi`'s `build.rs`
//! runs `lake build TmKernel:static` on whatever is there — so a
//! `cargo test --workspace` started by another session links the MUTATED kernel
//! and reports `0 failed` about it.
//!
//! OBSERVED LIVE by an auditor at W-29: ` M kernel/TmKernel/TmKernel/Boundary.lean`
//! carrying `def readState (sec : JVal) : Except Refusal (...) := default`, at the
//! same instant as `python3 mutate.py --gate` and a `lake build` whose parent was
//! `cargo test -p tm --test planner_invariants`.
//!
//! `mutate.py` writes the original bytes to `kernel/.mutate-in-flight` BEFORE it
//! writes the mutation and removes the sidecar after it restores, so the
//! sidecar's existence is exactly the dangerous window. This test reads it and
//! FAILS, which turns a silent false green into a named one. It is the half of
//! the race that can be seen from inside the suite; the other half — two
//! mutation runs interleaving their plants — is `mutate.py`'s own `flock`.
//!
//! **It cannot see** a plant that is live in the seconds between `mutate.py`
//! restoring one file and writing the next, nor a mutation run in a clone whose
//! sidecar is that clone's. The first is the loud direction (the window is
//! smaller, never larger); the second is what a clone is for.

use std::path::PathBuf;

/// `kernel/` of this repository, from this test's own manifest.
fn kernel_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("tm/ has a parent")
        .join("kernel")
}

#[test]
fn no_mutation_is_live_in_the_tree_this_suite_is_testing() {
    let sidecar = kernel_dir().join(".mutate-in-flight");
    let live = std::fs::read_to_string(&sidecar).ok();
    assert!(
        live.is_none(),
        "kernel/.mutate-in-flight exists: `mutate.py` has a constant-folded \
         definition planted in {} right now, and `build.rs` compiles whatever is \
         in the tree — so this run's result is about a kernel nobody committed. \
         Wait for the mutation gate to finish (or run the suite in a clone), \
         then re-run. The planted file is: {}",
        kernel_dir().display(),
        live.as_deref()
            .and_then(|t| t.lines().next().map(str::to_string))
            .unwrap_or_default()
    );
}
