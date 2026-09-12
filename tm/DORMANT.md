# `tm/` was dormant on this branch; the workspace is restored

This directory holds the frontend of the Rust `tm`: the CLI verbs (§13), the
ratatui TUI (§12), and `tm init`'s generated content (§14). It was dormant
while `tm-core` was absent from the branch. That is over: the workspace —
`tm-core/`, the root `Cargo.toml` and `Cargo.lock` — is restored at the
in-clone fork point `4748911` (the owner discarded `main`; see the
`kernel/README.md` 2026-09-12 block), and this crate builds again.

The restored code is **pre-stage-0**: `move_to` lacks the destination/occupied
precondition, so the A6 duplicate-id hole is open in the Rust until the
kernel-backed wiring lands — `move` and `readopt` are the verbs that reach it.
Do not drive this binary as if it were the old `main`.

Stage 3's rewiring against `kernel/tm-kernel-ffi` is underway: the UI becomes a
wrapper that converts between text files and the kernel, and the parts that
never belonged to the kernel stay in Rust — the terminal handling, the day-bar
rendering, file I/O, the calendar fetch, and the learned energy model, which is
statistics and has no soundness theorem worth proving.
