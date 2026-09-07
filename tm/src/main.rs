//! `tm` — the command line frontend of tm-spec-v1.md §13.
//!
//! # API overview
//!
//! The binary is a thin shell around [`cli::main`]: it parses the command
//! line, runs one verb against a plan directory and turns the result into a
//! process exit code (§13: `0` ok, `1` error, `2` validation problems,
//! `3` a write conflict). Everything else lives in [`cli`]:
//!
//! * `cli::Cli` / `cli::Command` — the clap derive tree, one variant per
//!   §13 verb, with the global `--json`, `--dir` and (hidden) `--now` flags.
//! * `cli::ctx::Ctx` — one loaded plan directory: config, store, tree, log,
//!   replay, model and `.tm/state.json`, plus the housekeeping (§6.3
//!   auto-close, §5.1 waiting timeouts) that runs before every verb.
//! * `cli::out` — `--json` vs human output and the `cli::out::CliError`
//!   → exit code mapping.
//! * `cli::undo` — the undo stack every mutating verb pushes to (§13
//!   `tm undo`).
//!
//! One sibling module sits outside `cli` because it is content, not command
//! handling: [`init`] carries everything `tm init` generates (§14's
//! `CLAUDE.md`, skills and hooks, §16's config, §2's starting files),
//! embedded from `tm/templates/`.

#![warn(missing_docs)]

mod cli;
mod init;

fn main() {
    std::process::exit(cli::main());
}
