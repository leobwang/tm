//! Output and errors for the CLI (tm-spec-v1.md §13).
//!
//! # API overview
//!
//! * [`CliError`] — every failure a verb can produce, with
//!   [`CliError::exit_code`] implementing §13's table: `1` for an ordinary
//!   error, `3` for a [`StoreError::Conflict`] (a write race, whose two
//!   texts are printed by [`CliError::report`]). `2` is not an error at all —
//!   it is what `tm check` *returns* when the tree has problems.
//! * [`emit`] — the one output path: with `--json` it prints
//!   `serde_json::to_string_pretty(value)`, otherwise the human string the
//!   closure builds (which is never computed in JSON mode).
//! * [`fmt_dur`] and [`fmt_time`] — the small formatting helpers the
//!   human output shares.

use std::io;

use serde::Serialize;
use thiserror::Error;
use tm_core::store::StoreError;

/// Exit code for an ordinary failure (§13).
pub const EXIT_ERROR: i32 = 1;
/// Exit code for a write conflict (§13).
pub const EXIT_CONFLICT: i32 = 3;

/// Anything a verb can fail with.
#[derive(Debug, Error)]
pub enum CliError {
    /// A plain message (bad argument, unknown id, nothing running…).
    #[error("{0}")]
    Msg(String),
    /// The plan files.
    #[error(transparent)]
    Store(#[from] StoreError),
    /// A horizon operation (§6.3).
    #[error(transparent)]
    Horizon(#[from] tm_core::horizon::HorizonError),
    /// The append-only log (§10.1).
    #[error(transparent)]
    Log(#[from] tm_core::log::LogError),
    /// Calendar sync (§15).
    #[error(transparent)]
    Ics(#[from] tm_core::ics::IcsError),
    /// A value that does not parse (`est=2b`, `due=…`).
    #[error(transparent)]
    Model(#[from] tm_core::model::ModelError),
    /// A byte-faithful line edit that cannot be made (§4.1).
    #[error(transparent)]
    Edit(#[from] tm_core::grammar::EditError),
    /// `tm check --fix-ids`.
    #[error(transparent)]
    Check(#[from] tm_core::check::CheckError),
    /// The learned model (§8.5).
    #[error(transparent)]
    Energy(#[from] tm_core::energy::EnergyError),
    /// Reading or writing a file outside the store (`tm init`, the SVG).
    #[error("{path}: {source}")]
    Io {
        /// The path involved.
        path: String,
        /// What went wrong.
        source: io::Error,
    },
    /// JSON output or a `.tm/` sidecar.
    #[error(transparent)]
    Json(#[from] serde_json::Error),
}

impl CliError {
    /// A message error from anything displayable.
    pub fn msg(m: impl Into<String>) -> CliError {
        CliError::Msg(m.into())
    }

    /// An I/O error against a named path.
    pub fn io(path: impl Into<String>, source: io::Error) -> CliError {
        CliError::Io {
            path: path.into(),
            source,
        }
    }

    /// The [`StoreError::Conflict`] behind this error, however deeply it is
    /// wrapped — §1.3's write race, which §13 gives its own exit code.
    pub fn conflict(&self) -> Option<&StoreError> {
        let store = match self {
            CliError::Store(e) => e,
            CliError::Horizon(tm_core::horizon::HorizonError::Store(e)) => e,
            CliError::Check(tm_core::check::CheckError::Store(e)) => e,
            _ => return None,
        };
        store.is_conflict().then_some(store)
    }

    /// §13: `3` for a write conflict, `1` for everything else.
    pub fn exit_code(&self) -> i32 {
        if self.conflict().is_some() {
            EXIT_CONFLICT
        } else {
            EXIT_ERROR
        }
    }

    /// Print the error on stderr — a conflict prints both versions of the
    /// line so the two writers can be reconciled (§1.3, §17.2).
    pub fn report(&self) {
        if let Some(StoreError::Conflict {
            id,
            file,
            ours,
            theirs,
        }) = self.conflict()
        {
            let what = if id.is_empty() {
                file.clone()
            } else {
                format!("{file}: {}", id.token())
            };
            eprintln!("tm: conflict in {what} — the file changed under us");
            eprintln!("  ours:   {}", ours.trim_end());
            eprintln!("  theirs: {}", theirs.trim_end());
            return;
        }
        eprintln!("tm: {self}");
    }
}

/// Print one verb's result: the JSON document with `--json`, else the human
/// text. `human` is only called when it is needed.
pub fn emit<T: Serialize>(
    json: bool,
    human: impl FnOnce() -> String,
    value: &T,
) -> Result<(), CliError> {
    if json {
        println!("{}", serde_json::to_string_pretty(value)?);
    } else {
        let text = human();
        if !text.is_empty() {
            println!("{text}");
        }
    }
    Ok(())
}

/// Minutes as the compact human form: `20m`, `1h`, `1h20m`.
pub fn fmt_dur(minutes: u32) -> String {
    match (minutes / 60, minutes % 60) {
        (0, m) => format!("{m}m"),
        (h, 0) => format!("{h}h"),
        (h, m) => format!("{h}h{m}m"),
    }
}

/// `HH:MM`.
pub fn fmt_time(t: chrono::NaiveTime) -> String {
    t.format("%H:%M").to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use tm_core::model::Id;

    /// The §1.3 write race cannot be provoked from outside the process (it
    /// needs a writer between the store's read and its verified write, which
    /// is what `FsStore::with_before_write_hook` is for in `tm-core`'s own
    /// tests). What the CLI owns is the mapping, so that is what is tested
    /// here: a `Conflict`, however deeply wrapped, is §13's exit code 3.
    fn conflict() -> StoreError {
        StoreError::Conflict {
            id: Id::new("t3"),
            file: "week/2026-W37.md".to_string(),
            ours: "- [x] 4 2b Exercises 5.3–5.5 @m1 ^t3".to_string(),
            theirs: "- [>] 4 2b Exercises 5.3–5.5 @m1 est:1b ^t3".to_string(),
        }
    }

    #[test]
    fn a_write_conflict_exits_with_three() {
        let e = CliError::from(conflict());
        assert!(e.conflict().is_some());
        assert_eq!(e.exit_code(), EXIT_CONFLICT);
    }

    #[test]
    fn a_conflict_wrapped_by_horizon_exits_with_three() {
        let e = CliError::from(tm_core::horizon::HorizonError::Store(conflict()));
        assert!(e.conflict().is_some());
        assert_eq!(e.exit_code(), EXIT_CONFLICT);
    }

    #[test]
    fn a_conflict_wrapped_by_check_exits_with_three() {
        let e = CliError::from(tm_core::check::CheckError::Store(conflict()));
        assert_eq!(e.exit_code(), EXIT_CONFLICT);
    }

    #[test]
    fn every_other_error_exits_with_one() {
        assert_eq!(CliError::msg("nope").exit_code(), EXIT_ERROR);
        let missing = CliError::from(StoreError::NotFound(Id::new("zzzz")));
        assert!(missing.conflict().is_none());
        assert_eq!(missing.exit_code(), EXIT_ERROR);
    }

    #[test]
    fn durations_read_the_way_the_spec_writes_them() {
        assert_eq!(fmt_dur(20), "20m");
        assert_eq!(fmt_dur(60), "1h");
        assert_eq!(fmt_dur(90), "1h30m");
    }
}
