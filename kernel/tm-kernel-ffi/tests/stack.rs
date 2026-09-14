//! **T0, design §14.1 and D9-21: every recursion over a list the wire can make
//! large runs in constant stack per element.**  Its own test binary, not
//! `tests/kernel.rs`: `check.sh` check 5 runs only that one, and these requests
//! are megabytes each, so keeping them out keeps `check.sh`'s wall time inside
//! design §14.0 item 4's 10% budget.  `cargo test` in this crate runs both.
//!
//! Stage 5 step A1 (gap 44 closed).  T0 (b) and (c) join this file at W3 and L5.

use tm_kernel_ffi::call;

/// Runs `f` on a thread whose stack is exactly 2 MiB, so a test does not lean
/// on the harness's default (`RUST_MIN_STACK` can raise it).
fn on_a_2mib_thread<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

/// **T0 (a), design §14.1: gap 44 is closed.**  `jarr`/`jtail`, `jobj`/`jotail`,
/// `jemitTail`/`jemitOTail` and `splitDoc` recursed once per element, so before
/// A1 an array of 22,000 strings aborted a 2 MiB thread.  They now run as proved
/// `@[csimp]` accumulator twins (`jtail_eq_jtailAcc`, `jotail_eq_jotailAcc`,
/// `jemitTail_eq_jemitTailAcc`, `jemitOTail_eq_jemitOTailAcc`,
/// `splitDoc_eq_splitDocAcc`).  Arrays of strings: a 200,000-line document is
/// read, split, loaded, written and emitted back byte for byte.  Arrays of
/// objects: 200,000 objects are parsed to the end (the refusal is `run`'s, not
/// the parser's, and the same bytes with the closing `]` removed are refused by
/// the parser at the last element).  The objects sit in a key `run` never reads
/// because `run` appends each document with `++`, quadratic in the document
/// count (README "Stage 5 A1", gap 100).
#[test]
fn a_200000_element_array_reads_on_a_2mib_thread() {
    on_a_2mib_thread(|| {
        let lines: Vec<String> = (0..200_000).map(|i| format!("\"x{i}\"")).collect();
        let lines = lines.join(",");
        let out = call(&format!(r#"{{"docs":[{{"path":"w.md","lines":[{lines}]}}],"cmds":[]}}"#))
            .unwrap();
        assert_eq!(
            out,
            format!(r#"{{"ok":{{"docs":[{{"path":"w.md","lines":[{lines}]}}],"report":{{"closes":[]}}}}}}"#)
        );
    });
    on_a_2mib_thread(|| {
        let objs: Vec<String> =
            (0..200_000).map(|i| format!(r#"{{"path":"d{i}.md","lines":["x"]}}"#)).collect();
        let objs = objs.join(",");
        let out = call(&format!(r#"{{"docs":7,"pad":[{objs}]}}"#)).unwrap();
        assert_eq!(out, r#"{"err":"array expected"}"#);
        let out = call(&format!(r#"{{"docs":7,"pad":[{objs}}}"#)).unwrap();
        assert_eq!(out, r#"{"err":"bad json: expectedCommaOrBracket }"}"#);
    });
}
