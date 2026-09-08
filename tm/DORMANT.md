# `tm/` is dormant on this branch

This directory holds the frontend of the Rust `tm`: the CLI verbs (§13), the
ratatui TUI (§12), and `tm init`'s generated content (§14). None of it builds
here, because it depends on `tm-core`, which this branch removed in favour of
the Lean kernel under `kernel/`.

It is kept rather than deleted because the architecture in `PLAN-lean-kernel.md`
keeps this layer: the UI becomes a wrapper that converts between text files and
the kernel, and the parts that never belonged to the kernel stay in Rust — the
terminal handling, the day-bar rendering, file I/O, the calendar fetch, and the
learned energy model, which is statistics and has no soundness theorem worth
proving.

Stage 3 of the plan rewires it against `kernel/tm-kernel-ffi`. Until then it is
reference material, not code.

To see it working, use `main`:

    git checkout main            # the Rust tm, 957 tests, exhaustive sweep clean

To restore the Rust kernel onto this branch:

    git checkout main -- tm-core Cargo.toml Cargo.lock
