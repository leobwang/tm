//! **The test chokepoint** (design D9-18, step R12): the one place a test turns
//! log text into what the reader derives from it.
//!
//! Every test in both crates that needs a [`Replay`] builds it here, from the
//! text of a log, never from `Log` directly: [`replay_of_text`] is the whole
//! reader, [`replay_of_entries`] writes entries with the Rust writer first and
//! reads the text back.
//!
//! **This body is the kernel's, since S** (design §14.6 items 1 and 3). Until
//! the switch it was the in-tree Rust reader, as `Ctx::replay_of` was for the
//! binary; design §12 deleted that reader, so there is one reader left and this
//! is it — the same `kernel_log::replay_scoped` the shipped `Ctx::replay_with`
//! calls, over a scratch plan root, in the `All` scope.
//!
//! **What this file is NOT, and it matters** (README gap 146). It is a
//! *convenience* for the consumer suites — `recur`, `priority`, `planner`,
//! `review`, `tui`, `energy_fit` — which ask "given this log, what does the
//! planner do?" and never compared the reader against anything. It is **not**
//! a comparand, and no differential may be built on it: since the deletion,
//! both sides of anything compared through here would be the kernel. The
//! differentials read fork point `4748911` instead, frozen into
//! `tests/fixtures/` and reached through `support/fork.rs` — see
//! `kernel_replay_parity.rs` (T5) and `kernel_log_door.rs`.
//!
//! The move is done (design §14.6 item 3, landed before S under D19). Every
//! consumer suite that reads a log lives in `tm/tests/`, so this file is
//! included only from its own crate, by `#[path = "support/replay.rs"]` (or
//! `"../support/replay.rs"` from `planner_common/` and `review_common/`). The
//! fixture tree it reads stays where it is, so the moved suites reach it as
//! `../tm-core/tests/fixtures`.

#[allow(dead_code)]
#[path = "../../src/cli/tz_table.rs"]
mod tz_table;

#[allow(dead_code)]
#[path = "../../src/cli/kernel_log.rs"]
mod kernel_log;

use chrono::{DateTime, FixedOffset, NaiveDate};
use chrono_tz::Tz;
use serde_json::Value;
use tm_core::log::{LogEntry, OpenBlock, Replay};

/// A day later than every line of `text`, so no line is future-dated and every
/// day of the log is a day that has ended — which is what makes the `All` scope
/// the whole log. A text with no dated line gets a fixed late date.
fn day_after(text: &str, tz: Tz) -> NaiveDate {
    text.lines()
        .filter_map(|l| {
            let v: Value = serde_json::from_str(l).ok()?;
            DateTime::parse_from_rfc3339(v.get("t")?.as_str()?).ok()
        })
        .map(|t| t.with_timezone(&tz).date_naive())
        .max()
        .unwrap_or_else(|| NaiveDate::from_ymd_opt(2030, 1, 1).expect("date"))
        + chrono::Duration::days(1)
}

/// The kernel's answer for `text`, over a scratch plan root.
///
/// A fresh root per call is deliberate: these helpers are called with unrelated
/// logs from one process, and a checkpoint built for one of them must never be
/// resumed for another. (It would not be *wrong* — §9.8's prefix digest refuses
/// it and rebuilds — but "the test passed because the digest caught it" is not
/// a thing to leave to chance.)
fn kernel_read(text: &str, tz: Tz) -> kernel_log::Read {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = dir.path();
    let wire = tz_table::wire_for(Some(&root.join(kernel_log::CACHE_DIR)), tz);
    kernel_log::replay_scoped(
        root,
        text.as_bytes(),
        tz,
        &wire,
        day_after(text, tz),
        kernel_log::Scope::All,
        None,
    )
    .unwrap_or_else(|e| panic!("the kernel could not replay this log: {e:?}"))
}

/// **The open block's worked minutes as of `now`**, read off the reader's facts: its closed
/// sub-segments (`worked_min`) and the stretch running since `since`, which accrues nothing while
/// the block is paused or interrupted (`since` is then `None`).  It is the reading tm-core's
/// `OpenBlock::worked_min_at` made — the kernel replay's `Replay.openOf` is what fills the two
/// fields — and lives here since stage 6 W-46 track C because R3 leaves that method with no
/// caller outside the tests and deletes it (README gap 4752, the class).
pub fn open_worked_min_at(b: &OpenBlock, now: DateTime<FixedOffset>) -> u32 {
    b.worked_min + b.since.map_or(0, |s| now.signed_duration_since(s).num_minutes().max(0) as u32)
}

/// The replay of the log `text` (JSONL, one entry per line) in `tz`, over
/// every day: what `Ctx::replay_with` derives from `.tm/log.jsonl`.
pub fn replay_of_text(text: &str, tz: Tz) -> Replay {
    kernel_read(text, tz).replay
}

/// [`replay_of_text`], but handing back the kernel's **named refusal** instead
/// of panicking on it.
///
/// Design §17's parity list has rows where the kernel refuses by name what the
/// fork computed anyway — **P17** is the one with a test: a minute or count sum
/// above `2^32 − 1` is `minutesOverflow`, where the fork's `saturating_add`
/// pinned it at `u32::MAX`. A test about *that* wants the refusal, not a
/// panic.
pub fn try_replay_of_text(text: &str, tz: Tz) -> Result<Replay, String> {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = dir.path();
    let wire = tz_table::wire_for(Some(&root.join(kernel_log::CACHE_DIR)), tz);
    kernel_log::replay_scoped(
        root,
        text.as_bytes(),
        tz,
        &wire,
        day_after(text, tz),
        kernel_log::Scope::All,
        None,
    )
    .map(|r| r.replay)
    .map_err(|e| format!("{e:?}"))
}

/// `entries` as the Rust writer appends them: one `LogEntry::to_json` line
/// each, every line ending in `\n`.
///
/// The writer is **not** deleted at S — design §12 keeps it, and D16's S2 is
/// where it moves into the kernel — so this half of the chokepoint is
/// unchanged.
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
///
/// This is `tm check`'s own read-only sweep ([`kernel_log::line_warnings`]),
/// not the replay's `warnings` array, for the reason gap 134 gives: an answer
/// carries only its own call's warnings, and genesis returns only its last
/// chunk's.
pub fn warning_lines_of_text(text: &str) -> Vec<u64> {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let tz = chrono_tz::America::Chicago;
    let wire = tz_table::wire_for(Some(&dir.path().join(kernel_log::CACHE_DIR)), tz);
    let now = day_after(text, tz).format("%Y-%m-%d").to_string();
    kernel_log::line_warnings(text.as_bytes(), &now, &wire)
        .unwrap_or_else(|e| panic!("the kernel could not sweep this log: {e}"))
        .iter()
        .map(|w| w.line as u64)
        .collect()
}

/// Every entry of `text` in file order as `(tag, primary id)`: the kernel's
/// headers (design §11.4), what a writer test checks it appended.
pub fn headers_of_text(text: &str) -> Vec<(String, Option<String>)> {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let tz = chrono_tz::America::Chicago;
    let wire = tz_table::wire_for(Some(&dir.path().join(kernel_log::CACHE_DIR)), tz);
    let now = day_after(text, tz).format("%Y-%m-%d").to_string();
    kernel_log::headers_after(text.as_bytes(), &now, &wire, 0)
        .unwrap_or_else(|e| panic!("the kernel could not read these headers: {e}"))
        .into_iter()
        .map(|(_, tag, id)| (tag, id))
        .collect()
}
