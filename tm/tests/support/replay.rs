//! **The test chokepoint** (design D9-18, step R12): the one place a test turns
//! log text into what the reader derives from it.
//!
//! Every test in both crates that needs a [`Replay`] builds it here, from the
//! text of a log, never from `Log` directly: [`replay_of_text`] is the whole
//! reader, [`replay_of_entries`] writes entries with the Rust writer first and
//! reads the text back. Until the switch the body is the in-tree Rust reader,
//! as `Ctx::replay_of` is for the binary. At S the tm-core suites move to
//! `tm/tests/` and this body calls the kernel; no caller changes.
//!
//! Included by path (`#[path = ".../tm/tests/support/replay.rs"]`) from
//! `tm-core/tests` and `tm/tests` alike, so it names only `tm_core` and
//! `chrono_tz`.

use chrono_tz::Tz;
use tm_core::log::{LogEntry, Replay};

/// The replay of the log `text` (JSONL, one entry per line) in `tz`, over
/// every day: what `Ctx::replay_of` derives from `.tm/log.jsonl`.
pub fn replay_of_text(text: &str, tz: Tz) -> Replay {
    tm_core::log::Log::parse(text).replay(None, tz)
}

/// `entries` as the Rust writer appends them: one `LogEntry::to_json` line
/// each, every line ending in `\n`.
pub fn text_of(entries: &[LogEntry]) -> String {
    entries
        .iter()
        .map(|e| e.to_json().expect("a log entry serialises") + "\n")
        .collect()
}

/// [`replay_of_text`] of [`text_of`]`(entries)`: a hand-built log, written and
/// read back.
pub fn replay_of_entries(entries: &[LogEntry], tz: Tz) -> Replay {
    replay_of_text(&text_of(entries), tz)
}

/// The 1-based physical lines of `text` the reader refuses (malformed JSON,
/// an unknown field type, a bad timestamp, invalid UTF-8): the log's line
/// warnings, by line.
pub fn warning_lines_of_text(text: &str) -> Vec<u64> {
    tm_core::log::Log::parse(text)
        .warnings
        .iter()
        .map(|w| w.line as u64)
        .collect()
}

/// Every entry of `text` in file order as `(tag, primary id)`: the kernel's
/// headers (design §11.4), what a writer test checks it appended.
pub fn headers_of_text(text: &str) -> Vec<(String, Option<String>)> {
    tm_core::log::Log::parse(text)
        .entries
        .iter()
        .map(|e| (e.ev.name().to_string(), e.ev.primary_id().map(str::to_string)))
        .collect()
}
