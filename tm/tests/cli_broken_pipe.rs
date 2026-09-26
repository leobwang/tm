//! **A reader that stops reading is not a crash** (stage 6 W-35 repair,
//! README gap 2927).
//!
//! `tm plan | head -9` panicked — `failed printing to stdout: Broken pipe
//! (os error 32)`, exit 101 — because `cli::out::emit` wrote with `println!`,
//! which panics on a closed pipe (fork 4748911's `emit` did the same). The verb
//! had already done its work; the panic was the whole failure. `emit` writes
//! through `stdout_line` now, and a closed pipe ends the output quietly.

mod cli_common;

use std::process::{Command, Stdio};

use cli_common::Tm;

/// The read end of `tm`'s stdout is closed before the verb writes anything, so
/// its first write meets a broken pipe. The verb exits by its own code — not a
/// panic's 101 — and says nothing about a panic.
#[test]
fn a_closed_stdout_is_not_a_panic() {
    let tm = Tm::new();
    for args in [&["plan"][..], &["--json", "plan"][..], &["now"][..]] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_tm"))
            .arg("--dir")
            .arg(&tm.plan)
            .arg("--now")
            .arg("2026-09-07T09:00:00-05:00")
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn tm");
        // Close the read end at once: every byte `tm` writes meets EPIPE.
        drop(child.stdout.take());
        let out = child.wait_with_output().expect("wait for tm");
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(!stderr.contains("panicked"), "tm {args:?} panicked on a closed pipe: {stderr}");
        assert_eq!(out.status.code(), Some(0), "tm {args:?}: {stderr}");
    }
}
