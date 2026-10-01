//! Store — tm-spec-v1.md §1.2 `store.rs`, §1.3 (three writers, one file
//! set), §2 (repository layout), §4.2/§4.3 (file conventions), §10.2
//! (`state.json`).
//!
//! # API overview
//!
//! * [`Store`] — the object-safe trait every reader/writer of `plan/` goes
//!   through. Implementors supply the primitives (`list_files`, `read_text`,
//!   `write_file`, `exists`, `abs_path`, `read_config`; `read_bytes` has a
//!   default over `read_text` that [`FsStore`] overrides) and the one
//!   id-addressed edit primitive [`Store::modify_line`]; everything else is a
//!   provided method built on the pure text transforms in [`edit`], so every
//!   store behaves identically and bytes outside the edited line are never
//!   touched:
//!   - [`Store::read_tree`]`() -> `[`PlanFiles`] (every `*.md` under the root
//!     in deterministic order — month, week, backlog, routines, optional,
//!     calendar, day, inbox, then anything else — plus `config.toml`; a file
//!     that is not valid UTF-8 becomes an empty [`ParsedFile`] carrying that
//!     problem rather than failing the whole read);
//!     [`Store::read_file`]`(rel)`.
//!   - [`Store::write_line`]`(id, new_text)` — replace exactly the line
//!     carrying `^id` (§1.3). On [`FsStore`] the file's mtime *and* content
//!     hash are checked between the read and the atomic write; on a mismatch
//!     the store re-reads and retries once, then fails with
//!     [`StoreError::Conflict`] carrying both texts.
//!   - [`Store::replace_generated`]`(rel, name, body)` /
//!     [`Store::replace_generated_stamped`]`(rel, name, info, body)` — the
//!     block between `<!-- tm:<name> start … -->` and `<!-- tm:<name> end -->`
//!     (markers kept; inserted after the front matter / `![day](…)` line when
//!     missing). A block whose end marker was lost is *closed* under its
//!     start marker, never run to the end of the file, so `# Pinned`, the
//!     append-only `## Log` and `## Notes` survive; a body that contains a
//!     marker-shaped line is refused.
//!   - [`Store::append_to_section`]`(rel, "## Log", line)`,
//!     [`Store::insert_line`]`(rel, Some("Tasks") | None, text)` (a missing
//!     section is created at the end as `# Section`; a missing horizon file
//!     is created with its front matter), [`Store::remove_line`]`(id)`,
//!     [`Store::move_line`]`(id, to_rel, section)` (guarded removal first,
//!     so the text that lands in the destination is the line as it stood
//!     when it left the source), [`Store::reorder_line`]`(id, delta)` (TUI `J`/`K`, within
//!     the section). [`Store::write_line_in`], [`Store::remove_line_in`] and
//!     [`Store::move_line_from`] take the file to look in, which is how the
//!     `# Demoted` copy of a duplicated id is addressed (§6.3).
//!   - [`Store::ensure_file`] / [`Store::ensure_horizon_file`],
//!     [`Store::load_state`] / [`Store::save_state`] (`.tm/state.json`,
//!     missing → default).
//! * [`StoreExt`] — `read_json<T>` / `write_json<T>` for `.tm/model.json`
//!   and friends (blanket impl for every `Store`, `dyn Store` included);
//!   [`Store::append_text`] extends the append-only `.tm/log.jsonl`.
//! * [`FsStore`]`::new(root)` — `root` is the `plan/` directory. Writes are
//!   atomic (temp file in the same directory + rename) and every mutation is
//!   guarded: the id-addressed ones through [`Store::modify_line`], the
//!   whole-file ones (appends, generated blocks) through
//!   [`Store::modify_file`], which re-applies the edit to a racing writer's
//!   version rather than clobbering it.
//!   [`FsStore::with_before_write_hook`] injects a closure run between the
//!   read and the verified write (the race test of §17 M1).
//! * [`MemStore`] — the same trait over an in-memory `path → text` map, for
//!   tests and the planner's purity tests ([`MemStore::from_dir`] loads a
//!   fixture tree).
//! * [`PlanFiles`] — `config` + `files: Vec<ParsedFile>` with
//!   [`PlanFiles::locate`]`(id) -> Option<`[`Location`]`>`
//!   (file index, line index), [`PlanFiles::find`], [`PlanFiles::ids`],
//!   [`PlanFiles::tree`].
//! * [`RuntimeState`] — §10.2 `state.json`, serde-exact.
//! * Path helpers: [`horizon_path`], [`initial_text`], [`file_rank`],
//!   [`sort_files`], [`is_plan_file`], [`is_safe_rel`] (every path a store
//!   touches must stay inside `plan/`: no `..`, no absolute path), and the
//!   `.tm/` constants [`STATE_PATH`], [`MODEL_PATH`], [`LOG_PATH`],
//!   [`CONFIG_PATH`].
//! * [`StoreError`] — `Io`, `Parse`, `NotFound(id)`, `Conflict {…}`, `Json`,
//!   `Toml`.
//!
//! Ids: a line is addressed by its `^id`; an id-less line (routines,
//! optional, inbox) by the key `tree.rs` gives it (its title). When an id is
//! on several lines (the §6.3 `# Demoted` copy), the copy outside
//! `# Demoted` is the one edited.

use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, HashSet};
use std::fmt;
use std::fs::{self, File};
use std::hash::{Hash, Hasher};
use std::io::{ErrorKind, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, MutexGuard};
use std::time::SystemTime;

use chrono::{DateTime, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::config::{hhmm, Config, ConfigError};
use crate::grammar::{parse_file, ItemLine, ParsedFile, Problem};
use crate::model::{Horizon, Id, IsoWeek, Item, YearMonth};
use crate::tree::{self, Tree};

/// `config.toml`, relative to the plan root.
pub const CONFIG_PATH: &str = "config.toml";
/// `.tm/state.json` (§10.2).
pub const STATE_PATH: &str = ".tm/state.json";
/// `.tm/model.json` (§8.5).
pub const MODEL_PATH: &str = ".tm/model.json";
/// `.tm/log.jsonl` (§10.1).
pub const LOG_PATH: &str = ".tm/log.jsonl";

/// How many times [`Store::modify_file`] re-applies a whole-file edit to a
/// racing writer's version before giving up with [`StoreError::Conflict`].
/// (§1.3 asks for one retry on a line write; a whole-file edit — an append,
/// a generated block — merges cleanly, so it is worth going round again.)
pub const MAX_FILE_ATTEMPTS: usize = 3;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from a [`Store`].
#[derive(Debug, Error)]
pub enum StoreError {
    /// A file could not be read or written.
    #[error("{path}: {source}")]
    Io {
        /// Path (relative to the plan root when known).
        path: String,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// Text that cannot go into a plan file (a line break in a line, a
    /// replacement that is not an item line or changes the `^id`, invalid
    /// UTF-8).
    #[error("{}{}: {}", path, at_line(*line), message)]
    Parse {
        /// File.
        path: String,
        /// 1-based line, or 0 for the whole file.
        line: usize,
        /// What was wrong.
        message: String,
    },
    /// No line carries the id (or, for id-less lines, the title key).
    #[error("no line carries ^{0}")]
    NotFound(Id),
    /// The file kept changing underneath the write (§1.3). Carries both
    /// versions so the TUI can show a diff: the lines for an id-addressed
    /// edit, the whole file texts (with an empty `id`) for a whole-file one.
    #[error("{file} changed underneath the write of ^{id} (ours: {ours:?}, theirs: {theirs:?})")]
    Conflict {
        /// The id being written; empty for a whole-file edit.
        id: Id,
        /// The file holding it.
        file: String,
        /// The text we wanted to write.
        ours: String,
        /// The text as it is in the file now (empty when the line
        /// disappeared).
        theirs: String,
    },
    /// A `.tm/*.json` file did not parse or serialize.
    #[error("{path}: {source}")]
    Json {
        /// File.
        path: String,
        /// Underlying error.
        #[source]
        source: serde_json::Error,
    },
    /// `config.toml` could not be loaded.
    #[error(transparent)]
    Toml(#[from] ConfigError),
}

impl StoreError {
    /// True for [`StoreError::Conflict`] (CLI exit code 3).
    pub fn is_conflict(&self) -> bool {
        matches!(self, StoreError::Conflict { .. })
    }
    /// True for [`StoreError::NotFound`].
    pub fn is_not_found(&self) -> bool {
        matches!(self, StoreError::NotFound(_))
    }
}

fn io_err(path: &str, source: std::io::Error) -> StoreError {
    StoreError::Io {
        path: path.to_string(),
        source,
    }
}

/// `":12"` for a line, and nothing at all for the whole file.
///
/// `StoreError::Parse`'s own field doc says "1-based line, **or 0 for the
/// whole file**", and the format string printed the 0 anyway — so a plan file
/// that is not UTF-8 came out as `inbox.md:0: not valid UTF-8`, and line 0 is
/// not a line (W-16 repair, gap 579).
fn at_line(line: usize) -> String {
    if line == 0 { String::new() } else { format!(":{line}") }
}

fn parse_err(path: &str, line: usize, message: impl Into<String>) -> StoreError {
    StoreError::Parse {
        path: path.to_string(),
        line,
        message: message.into(),
    }
}

/// The 1-based line of the first run of bytes in `rel` that is not UTF-8, or
/// `0` when the bytes cannot be read at all (which the caller prints as "the
/// whole file").
///
/// The same split-then-decode the log's reader does
/// ([`Store::read_bytes`]' own doc comment says why it exists), applied to a
/// plan file. It is a *diagnostic*: the file is still skipped whole, because a
/// tree half-decoded would be a tree the kernel and the host disagreed about.
fn first_bad_utf8_line<S: Store + ?Sized>(store: &S, rel: &str) -> usize {
    let Ok(bytes) = store.read_bytes(rel) else {
        return 0;
    };
    bad_utf8_line(&bytes)
}

/// **The one reader of "which line is the bad byte on"**, over bytes already in
/// hand — [`first_bad_utf8_line`] is this through a store, and the two strict
/// readers ([`FsStore::read_text`] and `Snapshot::read`) call it directly with
/// the bytes their own failed decode was handed (AGENTS §5.3: one definition,
/// and the strict path had **none**, which is why it printed a line-less
/// message where `tm check` and the write gate both named the line — W-17
/// repair, README gap 676).
///
/// `0` when every line decodes (a decode that failed for a reason the split
/// cannot localise) — which [`at_line`] renders as "the whole file".
pub fn bad_utf8_line(bytes: &[u8]) -> usize {
    bytes
        .split(|b| *b == b'\n')
        .position(|line| std::str::from_utf8(line).is_err())
        .map_or(0, |i| i + 1)
}

/// Why a file in the tree could not be turned into text.
enum Unreadable {
    /// Not valid UTF-8 — the tree keeps going without it.
    NotUtf8,
    /// It disappeared between the listing and the read.
    Gone,
}

/// Classify an error from [`Store::read_text`]: `None` for errors that must
/// still abort a whole-tree read.
impl StoreError {
    /// **This file's bytes are not text.** The one answer to that question:
    /// `read_tree`'s tolerance and `tm check`'s kernel load both ask it here
    /// rather than each matching on an `ErrorKind` (AGENTS §5.3).
    pub fn is_not_utf8(&self) -> bool {
        matches!(unreadable(self), Some(Unreadable::NotUtf8))
    }
}

fn unreadable(e: &StoreError) -> Option<Unreadable> {
    match e {
        StoreError::Parse { message, .. } if message.contains("UTF-8") => Some(Unreadable::NotUtf8),
        StoreError::Io { source, .. } => match source.kind() {
            ErrorKind::InvalidData => Some(Unreadable::NotUtf8),
            ErrorKind::NotFound => Some(Unreadable::Gone),
            _ => None,
        },
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Paths
// ---------------------------------------------------------------------------

/// The relative path of a horizon file: `backlog.md`, `month/2026-09.md`,
/// `week/2026-W37.md`, `day/2026-09-07.md`, `calendar/2026-W37.md`,
/// `routines.md`, `optional.md`, `inbox.md`.
pub fn horizon_path(h: &Horizon) -> String {
    h.path()
}

/// The text a horizon file starts with: front matter for month
/// (`month:`), week (`week:` + `window:`) and day (`date:`, plus the
/// `![day](…)` image line of §4.3); empty for the others.
pub fn initial_text(h: &Horizon) -> String {
    match h {
        Horizon::Month(m) => format!("---\nmonth: {m}\n---\n"),
        Horizon::Week(w) => {
            let (a, b) = w.range();
            format!(
                "---\nweek: {w}\nwindow: {}..{}\n---\n",
                a.format("%Y-%m-%d"),
                b.format("%Y-%m-%d")
            )
        }
        Horizon::Day(d) => {
            let ds = d.format("%Y-%m-%d");
            format!("---\ndate: {ds}\n---\n![day]({ds}.svg)\n")
        }
        _ => String::new(),
    }
}

/// Ordering rank of a plan file: month 0, week 1, backlog 2, routines 3,
/// optional 4, calendar 5, day 6, inbox 7, unknown 8. Files of one rank
/// sort by path, so dated files come out chronologically.
pub fn file_rank(rel: &str) -> u8 {
    match Horizon::from_path(rel) {
        Some(Horizon::Month(_)) => 0,
        Some(Horizon::Week(_)) => 1,
        Some(Horizon::Backlog) => 2,
        Some(Horizon::Routine) => 3,
        Some(Horizon::Optional) => 4,
        Some(Horizon::Calendar(_)) => 5,
        Some(Horizon::Day(_)) => 6,
        Some(Horizon::Inbox) => 7,
        None => 8,
    }
}

/// Sort relative paths into the deterministic tree order (see
/// [`file_rank`]) and drop duplicates.
pub fn sort_files(files: &mut Vec<String>) {
    files.sort_by(|a, b| file_rank(a).cmp(&file_rank(b)).then_with(|| a.cmp(b)));
    files.dedup();
}

/// True when `rel` names a file *inside* the plan root: a non-empty
/// relative path with no `..` component, no leading `/` and no drive
/// prefix. The store is scoped to `plan/` (§2), so every path that reaches
/// the filesystem is checked with this first — a `tm move ^id --to …` with
/// a hand-typed destination can otherwise read and write anywhere.
pub fn is_safe_rel(rel: &str) -> bool {
    let norm = rel.replace('\\', "/");
    if norm.is_empty() || norm.starts_with('/') {
        return false;
    }
    // A Windows prefix (`C:`, `\\server\share`) or a bare drive-relative path.
    if norm.split('/').next().is_some_and(|c| c.contains(':')) {
        return false;
    }
    let mut any = false;
    for part in norm.split('/') {
        match part {
            "" | "." => continue,
            ".." => return false,
            _ => any = true,
        }
    }
    any
}

fn check_rel(rel: &str) -> Result<(), StoreError> {
    if is_safe_rel(rel) {
        Ok(())
    } else {
        Err(parse_err(rel, 0, "path leaves the plan root"))
    }
}

/// True for a relative path the tree reader takes: a `.md` file outside
/// hidden directories (`.tm/`, `.claude/`, `.git/`) and not `CLAUDE.md`.
pub fn is_plan_file(rel: &str) -> bool {
    let norm = rel.replace('\\', "/");
    let mut parts = norm.split('/').filter(|p| !p.is_empty()).peekable();
    let mut name = "";
    while let Some(p) = parts.next() {
        if p.starts_with('.') {
            return false;
        }
        if parts.peek().is_none() {
            name = p;
        }
    }
    name.ends_with(".md") && name != "CLAUDE.md"
}

// ---------------------------------------------------------------------------
// The parsed tree
// ---------------------------------------------------------------------------

/// Where a line is inside a [`PlanFiles`]: indexes into `files` and into
/// that file's `lines`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Location {
    /// Index into [`PlanFiles::files`].
    pub file: usize,
    /// 0-based index into `ParsedFile::lines` (line number − 1).
    pub line: usize,
}

/// Every plan file, parsed, plus the config.
#[derive(Clone, Debug)]
pub struct PlanFiles {
    /// `config.toml` (defaults when missing).
    pub config: Config,
    /// Files in tree order (see [`file_rank`]).
    pub files: Vec<ParsedFile>,
}

/// **The one spelling of "these bytes are not text", as a tree problem.**
///
/// [`Store::read_tree`] writes it, [`PlanFiles::undecodable`] reads it back
/// and `tm check`'s `bad-value` row prints it. `StoreError::is_not_utf8` is the
/// same verdict about an *error*; this is the verdict about a *file already in
/// the tree*, which is a different question with the same answer, and neither
/// is spelled twice (AGENTS §5.3).
pub const NOT_UTF8: &str = "not valid UTF-8; the file was skipped";

/// **The verdict alone**, without what `read_tree` did about it: what a
/// *strict* reader says, which cannot honestly add "the file was skipped"
/// because the command is about to fail instead.
///
/// [`NOT_UTF8`] is this sentence plus its consequence clause, and
/// `the_two_not_utf8_spellings_are_one_sentence` pins that so the pair cannot
/// drift into two verdicts (AGENTS §5.3). Before the W-17 repair the strict
/// path had **three** spellings between `fs::read_to_string`'s *"stream did not
/// contain valid UTF-8"* and `Snapshot::read`'s line-less *"not valid UTF-8"*,
/// and neither carried a position.
pub const NOT_UTF8_VERDICT: &str = "not valid UTF-8";

impl PlanFiles {
    /// **The first file whose bytes are not text, with the line the bad byte
    /// is on** — `None` when every file decoded.
    ///
    /// [`Store::read_tree`] tolerates such a file (it becomes an empty
    /// [`ParsedFile`] carrying the problem) so that `tm check` can name the
    /// line rather than dying on it. Every verb that reads the tree *strictly*
    /// still fails on it, which is why a **write** has to be able to ask:
    /// nothing else in the binary can tell the difference between a tree the
    /// kernel would load and one no reading verb can open.
    pub fn undecodable(&self) -> Option<(&str, usize)> {
        self.files.iter().find_map(|f| {
            f.problems
                .iter()
                .find(|p| p.message == NOT_UTF8)
                .map(|p| (f.path.as_str(), p.line))
        })
    }

    /// The file at a relative path.
    pub fn file(&self, rel: &str) -> Option<&ParsedFile> {
        self.files.iter().find(|f| f.path == rel)
    }
    /// Every item of every file, in tree order.
    pub fn items(&self) -> impl Iterator<Item = &Item> {
        self.files.iter().flat_map(|f| f.items())
    }
    /// Where the line for `id` is (the copy outside `# Demoted` when the id
    /// is duplicated; id-less lines match by their title key).
    pub fn locate(&self, id: &Id) -> Option<Location> {
        choose(self.files.iter().enumerate(), id).map(|(file, line)| Location { file, line })
    }
    /// The item for `id`.
    pub fn find(&self, id: &Id) -> Option<&Item> {
        let loc = self.locate(id)?;
        self.files[loc.file].lines[loc.line].item()
    }
    /// The relative path of the file holding `id`.
    pub fn file_of(&self, id: &Id) -> Option<&str> {
        self.locate(id).map(|l| self.files[l.file].path.as_str())
    }
    /// Every `^id` in the tree (for `IdGen::next_id`).
    pub fn ids(&self) -> HashSet<String> {
        self.items()
            .filter(|i| i.has_id())
            .map(|i| i.id.as_str().to_string())
            .collect()
    }
    /// Build the [`Tree`] over these files.
    pub fn tree(&self) -> Tree {
        Tree::build(&self.files, &self.config)
    }
}

/// The preferred `(file index, line index)` for `id` among several parsed
/// files: the **record** copy, ranked by [`tree::record_rank`] — the live
/// line, else the archive copy with the most `demoted:` stamps, else the
/// `month/…# Demoted` copy — with ties going to the file that comes first.
///
/// This is deliberately the rank `Tree::get` resolves an id with. When the
/// two disagree, `tm edit ^id` reads one copy of a duplicated id and writes
/// its text over the other (§1.3: writers address items by id).
fn choose<'a>(files: impl Iterator<Item = (usize, &'a ParsedFile)>, id: &Id) -> Option<(usize, usize)> {
    let mut best: Option<(tree::RecordRank, (usize, usize))> = None;
    for (fi, f) in files {
        let Some(li) = edit::find_line(f, id) else {
            continue;
        };
        let Some(item) = f.lines[li].item() else {
            continue;
        };
        let rank = tree::record_rank(item);
        if best.as_ref().is_none_or(|(b, _)| rank < *b) {
            best = Some((rank, (fi, li)));
        }
    }
    best.map(|(_, loc)| loc)
}

// ---------------------------------------------------------------------------
// Pure text transforms
// ---------------------------------------------------------------------------

/// Pure transforms on a parsed file. Each returns the new file text; nothing
/// outside the touched lines changes (line endings included). The stores
/// call these; they are public so previews (`tm add`, the TUI) can show the
/// result without writing.
pub mod edit {
    use super::*;

    /// A heading line outside the front matter and generated ranges.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Heading {
        /// 0-based line index.
        pub index: usize,
        /// Number of `#`.
        pub level: usize,
        /// Text after the `#`s, trimmed.
        pub text: String,
    }

    /// Lines as `(text, eol)` with the file's dominant line ending.
    struct Doc {
        lines: Vec<(String, String)>,
        eol: String,
    }

    impl Doc {
        fn new(parsed: &ParsedFile) -> Doc {
            let lines: Vec<(String, String)> =
                parsed.lines.iter().map(|l| (l.text(), l.eol.clone())).collect();
            let eol = lines
                .iter()
                .map(|(_, e)| e.as_str())
                .find(|e| !e.is_empty())
                .unwrap_or("\n")
                .to_string();
            Doc { lines, eol }
        }

        fn len(&self) -> usize {
            self.lines.len()
        }

        /// Insert a line; every line but the last gets a line ending, and a
        /// file that had no final newline keeps that convention.
        fn insert(&mut self, idx: usize, text: &str) {
            let idx = idx.min(self.lines.len());
            let at_end = idx == self.lines.len();
            let eol = if at_end && self.lines.last().is_some_and(|(_, e)| e.is_empty()) {
                String::new()
            } else {
                self.eol.clone()
            };
            self.lines.insert(idx, (text.to_string(), eol));
            self.fix_eols();
        }

        fn remove(&mut self, idx: usize) -> String {
            self.lines.remove(idx).0
        }

        fn fix_eols(&mut self) {
            let n = self.lines.len();
            let eol = self.eol.clone();
            for (i, (_, e)) in self.lines.iter_mut().enumerate() {
                if i + 1 < n && e.is_empty() {
                    *e = eol.clone();
                }
            }
        }

        /// Index of the last non-blank line in `start..end`.
        fn last_nonblank(&self, start: usize, end: usize) -> Option<usize> {
            (start..end.min(self.lines.len()))
                .rev()
                .find(|&i| !self.lines[i].0.trim().is_empty())
        }

        fn text(&self) -> String {
            let mut out = String::new();
            for (t, e) in &self.lines {
                out.push_str(t);
                out.push_str(e);
            }
            out
        }
    }

    /// `(level, text)` for a `# Heading` line.
    fn heading_of(line: &str) -> Option<(usize, &str)> {
        let hashes = line.bytes().take_while(|b| *b == b'#').count();
        if hashes == 0 {
            return None;
        }
        let rest = &line[hashes..];
        if rest.is_empty() || rest.starts_with(' ') || rest.starts_with('\t') {
            Some((hashes, rest.trim()))
        } else {
            None
        }
    }

    /// `(level if given, text)` for a requested section: `"## Log"` →
    /// `(Some(2), "Log")`, `"Tasks"` → `(None, "Tasks")`.
    fn split_request(heading: &str) -> (Option<usize>, &str) {
        let h = heading.trim();
        match heading_of(h) {
            Some((level, text)) => (Some(level), text),
            None => (None, h),
        }
    }

    /// Number of lines the front matter occupies (0 when there is none):
    /// `---` on line 1 through the next `---`.
    pub fn front_matter_len(parsed: &ParsedFile) -> usize {
        let texts: Vec<String> = parsed.lines.iter().map(|l| l.text()).collect();
        front_len(&texts)
    }

    fn front_len(texts: &[String]) -> usize {
        if texts.first().is_some_and(|l| l.trim_end() == "---") {
            if let Some(rel) = texts[1..].iter().position(|l| l.trim_end() == "---") {
                return rel + 2;
            }
        }
        0
    }

    /// `(name, is the start marker)` for a `<!-- tm:<name> start … -->` or
    /// `<!-- tm:<name> end -->` line. Mirrors the parser's recogniser, so a
    /// line this accepts is exactly a line `grammar::parse_file` would turn
    /// into a marker.
    pub fn marker_of(line: &str) -> Option<(String, bool)> {
        let inner = line.trim().strip_prefix("<!--")?.strip_suffix("-->")?.trim();
        let mut words = inner.strip_prefix("tm:")?.splitn(3, char::is_whitespace);
        let name = words.next()?.to_string();
        match words.next()? {
            "start" => Some((name, true)),
            "end" => Some((name, false)),
            _ => None,
        }
    }

    /// The `[start, end]` 1-based line range a generated block covers. An
    /// **unterminated** block (its `<!-- tm:… end -->` was lost to a stray
    /// edit or a bad merge) covers only its start marker line: with no end
    /// marker there is nothing "between the markers", so everything below is
    /// ordinary text that §1.3 forbids touching. `ParsedFile::in_generated`
    /// takes the opposite view (unterminated runs to the end of the file),
    /// which is right for *parsing* — the parser must not read stale rows as
    /// items — but would make every edit here eat the rest of the file.
    fn generated_span(g: &crate::grammar::GeneratedRange) -> (usize, usize) {
        (g.start_line, g.end_line.unwrap_or(g.start_line))
    }

    /// True when 1-based line `n` sits inside a generated block (see
    /// [`generated_span`] for unterminated ones).
    pub fn in_generated(parsed: &ParsedFile, n: usize) -> bool {
        parsed.generated.iter().any(|g| {
            let (start, end) = generated_span(g);
            n >= start && n <= end
        })
    }

    /// The headings of a file, in order, skipping the front matter and
    /// generated ranges.
    pub fn headings(parsed: &ParsedFile) -> Vec<Heading> {
        let front = front_matter_len(parsed);
        parsed
            .lines
            .iter()
            .enumerate()
            .skip(front)
            .filter(|(i, l)| l.item().is_none() && !in_generated(parsed, i + 1))
            .filter_map(|(i, l)| {
                heading_of(&l.text()).map(|(level, text)| Heading {
                    index: i,
                    level,
                    text: text.to_string(),
                })
            })
            .collect()
    }

    /// The `[start, end)` line range of the section containing line
    /// `idx`: after its heading up to the next heading (or the end); lines
    /// before the first heading form the unnamed leading section.
    pub fn section_range(parsed: &ParsedFile, idx: usize) -> (usize, usize) {
        let hs = headings(parsed);
        let len = parsed.lines.len();
        match hs.iter().rposition(|h| h.index < idx) {
            Some(k) => (hs[k].index + 1, hs.get(k + 1).map(|h| h.index).unwrap_or(len)),
            None => (
                front_matter_len(parsed),
                hs.first().map(|h| h.index).unwrap_or(len),
            ),
        }
    }

    /// True when the item on line `idx` sits in a `# Demoted` section.
    pub fn is_demoted(parsed: &ParsedFile, idx: usize) -> bool {
        parsed.lines[idx]
            .item()
            .is_some_and(|it| it.src.section.as_deref() == Some("Demoted"))
    }

    /// The line index carrying `id`: an item whose `^id` is `id`, or an
    /// id-less item whose title key (`Tree::key_of`) is `id`. Prefers a
    /// match outside `# Demoted`.
    pub fn find_line(parsed: &ParsedFile, id: &Id) -> Option<usize> {
        let mut fallback = None;
        for (i, l) in parsed.lines.iter().enumerate() {
            let Some(it) = l.item() else { continue };
            let matches = if it.has_id() {
                it.id == *id
            } else {
                Tree::key_of(it) == *id
            };
            if !matches {
                continue;
            }
            if !is_demoted(parsed, i) {
                return Some(i);
            }
            fallback.get_or_insert(i);
        }
        fallback
    }

    /// Replace line `idx` with `new_text` (one line, no ending).
    pub fn replace_line(parsed: &ParsedFile, idx: usize, new_text: &str) -> String {
        let mut doc = Doc::new(parsed);
        doc.lines[idx].0 = new_text.to_string();
        doc.text()
    }

    /// Remove line `idx`; returns `(new text, removed line)`.
    pub fn remove_line(parsed: &ParsedFile, idx: usize) -> (String, String) {
        let mut doc = Doc::new(parsed);
        let removed = doc.remove(idx);
        (doc.text(), removed)
    }

    /// Move the item on line `idx` `delta` positions down (up when
    /// negative) among the item lines of its section, clamped to the
    /// section; prose and blank lines stay where they are. `None` when
    /// nothing moves.
    pub fn reorder_line(parsed: &ParsedFile, idx: usize, delta: i32) -> Option<String> {
        let (start, end) = section_range(parsed, idx);
        let items: Vec<usize> = (start..end)
            .filter(|&i| parsed.lines[i].item().is_some())
            .collect();
        let pos = items.iter().position(|&i| i == idx)?;
        let last = items.len().checked_sub(1)? as i64;
        let new_pos = (pos as i64 + delta as i64).clamp(0, last) as usize;
        if new_pos == pos {
            return None;
        }
        let mut doc = Doc::new(parsed);
        let text = doc.remove(idx);
        // Moving down: the target shifted up by one, so inserting at its old
        // index lands right after it. Moving up: the target did not move, so
        // the same index lands right before it.
        doc.insert(items[new_pos], &text);
        Some(doc.text())
    }

    /// Append `line` at the end of the section `heading` (given as `"Log"`
    /// or `"## Log"`; matched by text): after its last non-blank line, so a
    /// blank separator before the next heading stays. A missing section is
    /// created at the end of the file (after the last non-blank line, with
    /// a blank line before it) as the given heading, or `# <text>` when no
    /// `#`s were given.
    pub fn append_to_section(parsed: &ParsedFile, heading: &str, line: &str) -> String {
        let (level, name) = split_request(heading);
        let hs = headings(parsed);
        let mut doc = Doc::new(parsed);
        match hs.iter().position(|h| h.text == name) {
            Some(k) => {
                let start = hs[k].index + 1;
                let end = hs.get(k + 1).map(|h| h.index).unwrap_or(doc.len());
                let at = doc.last_nonblank(start, end).map(|j| j + 1).unwrap_or(start);
                doc.insert(at, line);
            }
            None => {
                let heading_line = format!("{} {}", "#".repeat(level.unwrap_or(1)), name);
                let front = front_matter_len(parsed);
                let mut at = doc.last_nonblank(0, doc.len()).map(|j| j + 1).unwrap_or(front);
                // A blank line separates the new section from the content
                // above it — but not from the front matter, which the files of
                // §4.3 have a heading directly under.
                if at > front {
                    doc.insert(at, "");
                    at += 1;
                }
                doc.insert(at, &heading_line);
                doc.insert(at + 1, line);
            }
        }
        doc.text()
    }

    /// Append `line` at the end of the file (after its last non-blank
    /// line; trailing blank lines stay trailing).
    pub fn append_to_end(parsed: &ParsedFile, line: &str) -> String {
        let mut doc = Doc::new(parsed);
        let at = doc.last_nonblank(0, doc.len()).map(|j| j + 1).unwrap_or(doc.len());
        doc.insert(at, line);
        doc.text()
    }

    /// The `<!-- tm:<name> start [info] -->` marker line.
    pub fn start_marker(name: &str, info: Option<&str>) -> String {
        match info.map(str::trim).filter(|s| !s.is_empty()) {
            Some(info) => format!("<!-- tm:{name} start {info} -->"),
            None => format!("<!-- tm:{name} start -->"),
        }
    }

    /// The `<!-- tm:<name> end -->` marker line.
    pub fn end_marker(name: &str) -> String {
        format!("<!-- tm:{name} end -->")
    }

    fn body_lines(body: &str) -> Vec<String> {
        if body.is_empty() {
            return Vec::new();
        }
        let b = body.strip_suffix('\n').unwrap_or(body);
        b.split('\n')
            .map(|l| l.strip_suffix('\r').unwrap_or(l).to_string())
            .collect()
    }

    /// Replace everything between the `tm:<name>` markers with `body`
    /// (lines; a trailing newline is optional), keeping the marker lines.
    /// `info` rewrites the text after `start` on the start marker (a
    /// timestamp); `None` keeps whatever is there. Missing markers are
    /// inserted after the front matter and, when it directly follows, the
    /// `![…](…)` image line; else at the top.
    ///
    /// An **unterminated** block gets its end marker put back directly under
    /// the start marker and the new body between them: whatever followed the
    /// lost `<!-- tm:<name> end -->` (a stale timeline, `# Pinned`, the
    /// append-only `## Log`, `## Notes`) is text outside the markers and is
    /// kept verbatim, below the closed block. Callers that emit a body
    /// should reject marker-shaped lines in it first (see
    /// [`Store::replace_generated_stamped`]), or the next replacement would
    /// close the block early.
    pub fn replace_generated(parsed: &ParsedFile, name: &str, info: Option<&str>, body: &str) -> String {
        let body = body_lines(body);
        let mut doc = Doc::new(parsed);
        match parsed.generated(name) {
            Some(g) => {
                let (start_line, end_line) = generated_span(g);
                let start = start_line - 1;
                let end = end_line - 1;
                for _ in start + 1..end {
                    doc.remove(start + 1);
                }
                if g.end_line.is_none() {
                    doc.insert(start + 1, &end_marker(name));
                }
                for (k, l) in body.iter().enumerate() {
                    doc.insert(start + 1 + k, l);
                }
                if let Some(info) = info {
                    doc.lines[start].0 = start_marker(name, Some(info));
                }
            }
            None => {
                let mut at = front_matter_len(parsed);
                if doc
                    .lines
                    .get(at)
                    .is_some_and(|(t, _)| t.trim_start().starts_with("![") && t.contains("]("))
                {
                    at += 1;
                }
                doc.insert(at, &start_marker(name, info));
                for (k, l) in body.iter().enumerate() {
                    doc.insert(at + 1 + k, l);
                }
                doc.insert(at + 1 + body.len(), &end_marker(name));
            }
        }
        doc.text()
    }

    /// Check that `new_text` may replace the item on line `idx`: one line,
    /// an item line, and the same address. For a line with an `^id` that is
    /// the same id (an id may be *added* to an id-less line, never changed
    /// or removed); for an id-less line (`routines.md`, `optional.md`,
    /// `inbox.md`, §4.3) it is the same title, since that is the key the
    /// line is addressed by (`Tree::key_of`) — a replacement that renamed it
    /// would destroy the store's own handle on it.
    pub fn validate_replacement(parsed: &ParsedFile, idx: usize, new_text: &str) -> Result<(), StoreError> {
        let path = parsed.path.as_str();
        let line = idx + 1;
        if new_text.contains(['\n', '\r']) {
            return Err(parse_err(path, line, "replacement contains a line break"));
        }
        let new_line = ItemLine::parse(new_text)
            .map_err(|_| parse_err(path, line, format!("replacement is not an item line: {new_text:?}")))?;
        let Some(old) = parsed.lines[idx].item() else {
            return Err(parse_err(path, line, "not an item line"));
        };
        if old.has_id() {
            match new_line.id() {
                Some(id) if id == old.id => {}
                Some(id) => {
                    return Err(parse_err(
                        path,
                        line,
                        format!("replacement changes the id from ^{} to ^{id}", old.id),
                    ))
                }
                None => return Err(parse_err(path, line, format!("replacement drops ^{}", old.id))),
            }
        } else if new_line.id().is_none() {
            let title = new_line.title();
            if title != old.title {
                return Err(parse_err(
                    path,
                    line,
                    format!(
                        "replacement renames the id-less line {:?} to {title:?}; \
                         it is addressed by its title, so give it an ^id first",
                        old.title
                    ),
                ));
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// The trait
// ---------------------------------------------------------------------------

/// The edit callback of [`Store::modify_line`]: given the parsed file and
/// the line index of the addressed item, produce the whole new file text
/// (`None` = nothing to write).
pub type LineEdit<'a> = dyn FnMut(&ParsedFile, usize) -> Result<Option<String>, StoreError> + 'a;

/// The edit callback of [`Store::modify_file`]: given the parsed file (the
/// parsed initial text of its horizon when the file does not exist yet),
/// produce the whole new file text (`None` = nothing to write).
pub type FileEdit<'a> = dyn FnMut(&ParsedFile) -> Result<Option<String>, StoreError> + 'a;

/// Access to the `plan/` tree. Object-safe; see the module docs for the
/// provided operations. Relative paths use `/` and are relative to the plan
/// root (`week/2026-W37.md`, `.tm/state.json`).
pub trait Store {
    // -- primitives ---------------------------------------------------------

    /// Every plan file (`*.md`, see [`is_plan_file`]) in tree order.
    fn list_files(&self) -> Result<Vec<String>, StoreError>;
    /// The raw text of a file.
    fn read_text(&self, rel: &str) -> Result<String, StoreError>;
    /// The raw **bytes** of a file.
    ///
    /// The default answers from [`Store::read_text`], so a store whose
    /// contents are already `String`s behaves exactly as before; [`FsStore`]
    /// overrides it with a byte read. That override is what lets
    /// `.tm/log.jsonl` be split into lines *before* any line is decoded
    /// ([`crate::log::Log::parse_bytes`]): one line of invalid UTF-8 is then a
    /// warning like any other malformed line (the owner's D18 (i), design
    /// §17's parity P13) instead of failing the whole command.
    fn read_bytes(&self, rel: &str) -> Result<Vec<u8>, StoreError> {
        self.read_text(rel).map(String::into_bytes)
    }
    /// Write a whole file (atomically on disk; parent directories created).
    fn write_file(&self, rel: &str, text: &str) -> Result<(), StoreError>;
    /// Delete a file.  A file that is not there is not an error.
    ///
    /// The primitive a WRITE THAT MUST BE UNDONE needs (W-31 repair,
    /// kernel/README.md gap 2263).  A verb that writes, reloads and finds the
    /// kernel refusing the tree has to put back exactly what it found — which
    /// for a file the verb itself created means removing it, and `write_file`
    /// of some plausible initial text is not the same thing.
    fn delete_file(&self, rel: &str) -> Result<(), StoreError>;
    /// True when the file exists.
    fn exists(&self, rel: &str) -> bool;
    /// The absolute path of a file, when the store is on disk.
    fn abs_path(&self, rel: &str) -> Option<PathBuf>;

    /// Append `text` to `rel`, creating the file when missing. For the
    /// append-only `.tm/log.jsonl` (§10.1) — no parsing, no markers, no
    /// guard: the file is only ever added to. [`FsStore`] opens it in append
    /// mode instead of rewriting it.
    ///
    /// **A torn last line is repaired first** (G9, parity P19): when the file
    /// is non-empty and does not end in `\n` (a write cut short, a hand edit
    /// saved without a final newline), a `\n` is written before `text`, so
    /// the append starts a line of its own instead of being glued onto the
    /// fragment and losing both.
    fn append_text(&self, rel: &str, text: &str) -> Result<(), StoreError> {
        let mut out = if self.exists(rel) {
            self.read_text(rel)?
        } else {
            String::new()
        };
        if !text.is_empty() && !out.is_empty() && !out.ends_with('\n') {
            out.push('\n');
        }
        out.push_str(text);
        self.write_file(rel, &out)
    }

    /// `config.toml`, or the defaults when missing.
    fn read_config(&self) -> Result<Config, StoreError> {
        if self.exists(CONFIG_PATH) {
            Ok(Config::parse(&self.read_text(CONFIG_PATH)?)?)
        } else {
            Ok(Config::default())
        }
    }

    /// The one primitive every id-addressed edit goes through: locate the
    /// line for `id` (in `rel` only when given, else across the tree), run
    /// `edit` on the parsed file, and write the result. `ours` is the line
    /// text reported in a [`StoreError::Conflict`]. The default does a
    /// plain read–edit–write; [`FsStore`] adds the §1.3 guard (mtime +
    /// content hash checked before the write, one retry, then `Conflict`).
    fn modify_line(&self, rel: Option<&str>, id: &Id, ours: &str, edit: &mut LineEdit<'_>) -> Result<(), StoreError> {
        // Only a store with concurrent writers (i.e. [`FsStore`]) can raise a
        // `Conflict`, so the default implementation has no use for `ours`.
        let _ = ours;
        let cfg = self.read_config()?;
        let (rel, parsed, idx) = locate(self, &cfg, id, rel)?;
        if let Some(new_text) = edit(&parsed, idx)? {
            self.write_file(&rel, &new_text)?;
        }
        Ok(())
    }

    /// The primitive every whole-file edit goes through: parse `rel` (its
    /// horizon's initial text when it does not exist yet), run `edit`, write
    /// the result. The default reads, edits and writes; [`FsStore`] verifies
    /// that the file did not change in between and, when it did, re-runs
    /// `edit` on the new text — an append or a generated-block replacement is
    /// then merged into the other writer's version instead of clobbering it
    /// (§1.3). After [`MAX_FILE_ATTEMPTS`] racing saves it gives up with
    /// [`StoreError::Conflict`] carrying both file texts.
    fn modify_file(&self, rel: &str, edit: &mut FileEdit<'_>) -> Result<(), StoreError> {
        let parsed = read_or_initial(self, rel)?;
        if let Some(text) = edit(&parsed)? {
            self.write_file(rel, &text)?;
        }
        Ok(())
    }

    // -- reading --------------------------------------------------------------

    /// Parse every plan file plus the config.
    ///
    /// One unreadable file does not make the tree unreadable: a `.md` that is
    /// not valid UTF-8 (a note dropped into `plan/` in some other encoding)
    /// becomes an empty [`ParsedFile`] carrying the problem, which `tm check`
    /// reports; a file that vanished between the listing and the read is
    /// skipped. Anything else (a permission error) still fails.
    fn read_tree(&self) -> Result<PlanFiles, StoreError> {
        let config = self.read_config()?;
        let mut files = Vec::new();
        for rel in self.list_files()? {
            match self.read_text(&rel) {
                Ok(text) => files.push(parse_file(&rel, &text, &config)),
                Err(e) => match unreadable(&e) {
                    Some(Unreadable::NotUtf8) => {
                        let mut f = parse_file(&rel, "", &config);
                        f.problems.push(Problem {
                            // **Name the line** (W-16 repair, gap 579). D18 /
                            // gap 145 did exactly this for `.tm/log.jsonl` —
                            // split the bytes on newlines *first*, so one bad
                            // line is a named problem instead of a whole
                            // command that says only "stream did not contain
                            // valid UTF-8" — and the plan files never got it.
                            line: first_bad_utf8_line(self, &rel),
                            message: NOT_UTF8.to_string(),
                        });
                        files.push(f);
                    }
                    Some(Unreadable::Gone) => {}
                    None => return Err(e),
                },
            }
        }
        Ok(PlanFiles { config, files })
    }

    /// Parse one file.
    fn read_file(&self, rel: &str) -> Result<ParsedFile, StoreError> {
        let cfg = self.read_config()?;
        let text = self.read_text(rel)?;
        Ok(parse_file(rel, &text, &cfg))
    }

    // -- line edits -----------------------------------------------------------

    /// Replace exactly the line carrying `id` with `new_text` (§1.3). The
    /// replacement must be one item line with the same `^id` (an id-less
    /// line may gain one). Writing the identical text is a no-op.
    fn write_line(&self, id: &Id, new_text: &str) -> Result<(), StoreError> {
        self.write_line_in(None, id, new_text)
    }

    /// Like [`Store::write_line`], searching only `rel` when given — the way
    /// to address the `# Demoted` copy of a duplicated id (§6.3).
    fn write_line_in(&self, rel: Option<&str>, id: &Id, new_text: &str) -> Result<(), StoreError> {
        self.modify_line(rel, id, new_text, &mut |parsed: &ParsedFile, idx: usize| {
            edit::validate_replacement(parsed, idx, new_text)?;
            if parsed.lines[idx].text() == new_text {
                return Ok(None);
            }
            Ok(Some(edit::replace_line(parsed, idx, new_text)))
        })
    }

    /// Remove the line carrying `id`; returns its text.
    fn remove_line(&self, id: &Id) -> Result<String, StoreError> {
        self.remove_line_in(None, id)
    }

    /// Like [`Store::remove_line`], searching only `rel` when given.
    fn remove_line_in(&self, rel: Option<&str>, id: &Id) -> Result<String, StoreError> {
        let mut removed = String::new();
        self.modify_line(rel, id, "", &mut |parsed: &ParsedFile, idx: usize| {
            let (text, line) = edit::remove_line(parsed, idx);
            removed = line;
            Ok(Some(text))
        })?;
        Ok(removed)
    }

    /// Move the line carrying `id` `delta` positions down (up when
    /// negative) among the items of its section (TUI `J`/`K`). Returns
    /// whether it moved (a clamped no-op writes nothing).
    fn reorder_line(&self, id: &Id, delta: i32) -> Result<bool, StoreError> {
        let mut moved = false;
        self.modify_line(None, id, "", &mut |parsed: &ParsedFile, idx: usize| {
            let out = edit::reorder_line(parsed, idx, delta);
            moved = out.is_some();
            Ok(out)
        })?;
        Ok(moved)
    }

    /// Move the line carrying `id` into `to_rel` (appended to `section`, or
    /// to the end of the file), preserving its exact text. A missing
    /// destination horizon file is created with its front matter *before*
    /// the line leaves the source, so the paths that can fail (a missing
    /// directory, an unwritable file) fail while the line is still safely in
    /// place; if the insert fails anyway the line is put back.
    fn move_line(&self, id: &Id, to_rel: &str, section: Option<&str>) -> Result<(), StoreError> {
        self.move_line_from(None, id, to_rel, section)
    }

    /// Like [`Store::move_line`], taking the line from `from` when given
    /// (`tm readopt` moves the `# Demoted` copy, §6.3).
    ///
    /// The source line is removed first and *its removed text* is what the
    /// destination gets. Reading the text up front and inserting that would
    /// drop a concurrent edit to the very line being moved: the guarded
    /// removal re-reads and carries the other writer's version along instead
    /// (§1.3).
    fn move_line_from(&self, from: Option<&str>, id: &Id, to_rel: &str, section: Option<&str>) -> Result<(), StoreError> {
        check_rel(to_rel)?;
        let cfg = self.read_config()?;
        let (from_rel, parsed, idx) = locate(self, &cfg, id, from)?;
        if from_rel == to_rel {
            let text = parsed.lines[idx].text();
            let cfg2 = cfg.clone();
            return self.modify_line(Some(to_rel), id, &text, &mut |parsed: &ParsedFile, idx: usize| {
                let (without, line) = edit::remove_line(parsed, idx);
                let again = parse_file(to_rel, &without, &cfg2);
                Ok(Some(match section {
                    Some(s) => edit::append_to_section(&again, s, &line),
                    None => edit::append_to_end(&again, &line),
                }))
            });
        }
        // The section the line sits in now, so a failed insert can put it back
        // roughly where it was rather than losing it.
        let back = parsed.lines[idx].item().and_then(|i| i.src.section.clone());
        if !self.exists(to_rel) {
            let initial = Horizon::from_path(to_rel).map(|h| initial_text(&h)).unwrap_or_default();
            self.ensure_file(to_rel, &initial)?;
        }
        let text = self.remove_line_in(Some(&from_rel), id)?;
        if let Err(e) = self.insert_line(to_rel, section, &text) {
            let _ = self.insert_line(&from_rel, back.as_deref(), &text);
            return Err(e);
        }
        Ok(())
    }

    // -- file edits -----------------------------------------------------------

    /// Append `line` to the section `heading` (`"## Log"` or `"Log"`),
    /// creating the section at the end of the file when missing. A missing
    /// horizon file is created first.
    fn append_to_section(&self, rel: &str, heading: &str, line: &str) -> Result<(), StoreError> {
        check_line(rel, line)?;
        self.modify_file(rel, &mut |parsed: &ParsedFile| {
            Ok(Some(edit::append_to_section(parsed, heading, line)))
        })
    }

    /// Append `text` at the end of `section` (created as `# Section` when
    /// missing) or, with `None`, at the end of the file. A missing horizon
    /// file is created first.
    fn insert_line(&self, rel: &str, section: Option<&str>, text: &str) -> Result<(), StoreError> {
        check_line(rel, text)?;
        self.modify_file(rel, &mut |parsed: &ParsedFile| {
            Ok(Some(match section {
                Some(s) => edit::append_to_section(parsed, s, text),
                None => edit::append_to_end(parsed, text),
            }))
        })
    }

    /// Replace the body of the generated block `name` (§1.3), keeping the
    /// marker lines as they are; inserts the markers when missing (see
    /// [`edit::replace_generated`]). A missing horizon file is created first.
    fn replace_generated(&self, rel: &str, name: &str, body: &str) -> Result<(), StoreError> {
        self.replace_generated_stamped(rel, name, None, body)
    }

    /// Like [`Store::replace_generated`], also rewriting the start marker as
    /// `<!-- tm:<name> start <info> -->` when `info` is given.
    ///
    /// The name, the marker info and every line of the body are checked
    /// against the marker syntax first: a body line that is itself a
    /// `<!-- tm:… -->` marker would close the block early and leave the rest
    /// of the body stranded outside it for good — one item titled
    /// `<!-- tm:plan end -->` would otherwise grow the file on every replan.
    fn replace_generated_stamped(&self, rel: &str, name: &str, info: Option<&str>, body: &str) -> Result<(), StoreError> {
        if name.is_empty() || name.contains(char::is_whitespace) {
            return Err(parse_err(rel, 0, format!("invalid generated section name {name:?}")));
        }
        if info.is_some_and(|i| i.contains(['\n', '\r']) || i.contains("-->")) {
            return Err(parse_err(rel, 0, "marker info contains a line break or `-->`"));
        }
        for (n, line) in body.split('\n').enumerate() {
            if edit::marker_of(line.strip_suffix('\r').unwrap_or(line)).is_some() {
                return Err(parse_err(
                    rel,
                    0,
                    format!("generated body line {} is a `tm:` marker: {line:?}", n + 1),
                ));
            }
        }
        self.modify_file(rel, &mut |parsed: &ParsedFile| {
            Ok(Some(edit::replace_generated(parsed, name, info, body)))
        })
    }

    /// Create `rel` with `initial` unless it exists. Returns whether it was
    /// created.
    fn ensure_file(&self, rel: &str, initial: &str) -> Result<bool, StoreError> {
        if self.exists(rel) {
            return Ok(false);
        }
        self.write_file(rel, initial)?;
        Ok(true)
    }

    /// [`Store::ensure_file`] for a horizon file with its front matter.
    fn ensure_horizon_file(&self, h: &Horizon) -> Result<bool, StoreError> {
        self.ensure_file(&horizon_path(h), &initial_text(h))
    }

    // -- runtime state --------------------------------------------------------

    /// `.tm/state.json`; the default when missing.
    fn load_state(&self) -> Result<RuntimeState, StoreError> {
        Ok(read_json(self, STATE_PATH)?.unwrap_or_default())
    }

    /// Write `.tm/state.json`.
    fn save_state(&self, state: &RuntimeState) -> Result<(), StoreError> {
        write_json(self, STATE_PATH, state)
    }
}

/// Generic JSON helpers on every [`Store`] (`dyn Store` included).
pub trait StoreExt: Store {
    /// Read and parse a JSON file; `None` when missing.
    fn read_json<T: DeserializeOwned>(&self, rel: &str) -> Result<Option<T>, StoreError> {
        read_json(self, rel)
    }
    /// Write a value as pretty JSON.
    fn write_json<T: Serialize>(&self, rel: &str, value: &T) -> Result<(), StoreError> {
        write_json(self, rel, value)
    }
}

impl<S: Store + ?Sized> StoreExt for S {}

/// Read and parse a JSON file from a store; `None` when missing.
pub fn read_json<T: DeserializeOwned, S: Store + ?Sized>(store: &S, rel: &str) -> Result<Option<T>, StoreError> {
    if !store.exists(rel) {
        return Ok(None);
    }
    let text = store.read_text(rel)?;
    serde_json::from_str(&text)
        .map(Some)
        .map_err(|source| StoreError::Json {
            path: rel.to_string(),
            source,
        })
}

/// Write a value as pretty JSON (with a final newline) to a store.
pub fn write_json<T: Serialize, S: Store + ?Sized>(store: &S, rel: &str, value: &T) -> Result<(), StoreError> {
    let mut text = serde_json::to_string_pretty(value).map_err(|source| StoreError::Json {
        path: rel.to_string(),
        source,
    })?;
    text.push('\n');
    store.write_file(rel, &text)
}

fn check_line(rel: &str, line: &str) -> Result<(), StoreError> {
    if line.contains(['\n', '\r']) {
        return Err(parse_err(rel, 0, "text contains a line break"));
    }
    Ok(())
}

/// The parsed file, or the parsed initial text of its horizon when missing.
fn read_or_initial<S: Store + ?Sized>(store: &S, rel: &str) -> Result<ParsedFile, StoreError> {
    let cfg = store.read_config()?;
    let text = if store.exists(rel) {
        store.read_text(rel)?
    } else {
        Horizon::from_path(rel).map(|h| initial_text(&h)).unwrap_or_default()
    };
    Ok(parse_file(rel, &text, &cfg))
}

/// Find `(rel, parsed, line index)` for `id`, in `only` when given, else
/// across the tree (preferring the copy outside `# Demoted`).
fn locate<S: Store + ?Sized>(store: &S, cfg: &Config, id: &Id, only: Option<&str>) -> Result<(String, ParsedFile, usize), StoreError> {
    if let Some(rel) = only {
        if !store.exists(rel) {
            return Err(StoreError::NotFound(id.clone()));
        }
        let parsed = parse_file(rel, &store.read_text(rel)?, cfg);
        return match edit::find_line(&parsed, id) {
            Some(i) => Ok((rel.to_string(), parsed, i)),
            None => Err(StoreError::NotFound(id.clone())),
        };
    }
    let mut files = Vec::new();
    for rel in store.list_files()? {
        // A file that is not valid UTF-8, or that vanished since the
        // listing, holds no addressable line: skip it rather than failing
        // every lookup in the tree (see `Store::read_tree`).
        let text = match store.read_text(&rel) {
            Ok(text) => text,
            Err(e) if unreadable(&e).is_some() => continue,
            Err(e) => return Err(e),
        };
        files.push(parse_file(&rel, &text, cfg));
    }
    match choose(files.iter().enumerate(), id) {
        Some((fi, li)) => {
            let parsed = files.swap_remove(fi);
            Ok((parsed.path.clone(), parsed, li))
        }
        None => Err(StoreError::NotFound(id.clone())),
    }
}

// ---------------------------------------------------------------------------
// FsStore
// ---------------------------------------------------------------------------

/// A hook run between the read and the verified write of an id-addressed
/// edit: `(absolute path of the file, attempt number starting at 0)`.
pub type BeforeWriteHook = Box<dyn Fn(&Path, usize) + Send + Sync>;

/// The on-disk store rooted at the `plan/` directory.
pub struct FsStore {
    root: PathBuf,
    before_write: Option<BeforeWriteHook>,
}

impl fmt::Debug for FsStore {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FsStore")
            .field("root", &self.root)
            .field("before_write", &self.before_write.is_some())
            .finish()
    }
}

/// What a file looked like when it was read.
struct Snapshot {
    text: String,
    mtime: Option<SystemTime>,
    hash: u64,
}

/// A witness of one file's state at read time, for a write that happens
/// later in the same command: the §1.3 guard (mtime + content hash), carried
/// across the gap between [`FsStore::read_guarded`] and
/// [`FsStore::write_guarded`]. Opaque on purpose — the only thing to do with
/// one is hand it back to the store that issued it.
#[derive(Clone, Debug)]
pub struct FileGuard {
    mtime: Option<SystemTime>,
    hash: u64,
    existed: bool,
}

impl FileGuard {
    /// The guard for a file that did not exist at read time: the matching
    /// [`FsStore::write_guarded`] succeeds only while the file is *still*
    /// absent, so two racing creators cannot silently clobber each other.
    pub fn absent() -> FileGuard {
        FileGuard {
            mtime: None,
            hash: 0,
            existed: false,
        }
    }
}

impl Snapshot {
    fn read(path: &Path, rel: &str) -> Result<Snapshot, StoreError> {
        let bytes = fs::read(path).map_err(|e| io_err(rel, e))?;
        let mtime = fs::metadata(path).ok().and_then(|m| m.modified().ok());
        let mut h = DefaultHasher::new();
        bytes.hash(&mut h);
        let hash = h.finish();
        // **Name the line** (W-17 repair, gap 676). The bytes are already in
        // hand, so the position costs one split — and without it this reader,
        // which every guarded write and every id lookup goes through, said
        // `optional.md: not valid UTF-8` with no position while `tm check` and
        // the write gate both said `optional.md:3`.
        let text = String::from_utf8(bytes)
            .map_err(|e| parse_err(rel, bad_utf8_line(e.as_bytes()), NOT_UTF8_VERDICT))?;
        Ok(Snapshot { text, mtime, hash })
    }

    fn unchanged_since(&self, earlier: &Snapshot) -> bool {
        self.mtime == earlier.mtime && self.hash == earlier.hash
    }
}

static TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Write `text` to `path` via a temp file in the same directory and a
/// rename, so readers see either the old or the new file.
fn write_atomic(path: &Path, rel: &str, text: &str) -> Result<(), StoreError> {
    let dir = path.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
    fs::create_dir_all(dir).map_err(|e| io_err(rel, e))?;
    let name = path.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
    let n = TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let tmp = dir.join(format!(".{name}.tm-tmp-{}-{n}", std::process::id()));
    let result = (|| {
        let mut f = File::create(&tmp)?;
        f.write_all(text.as_bytes())?;
        f.sync_all()?;
        fs::rename(&tmp, path)
    })();
    if let Err(e) = result {
        let _ = fs::remove_file(&tmp);
        return Err(io_err(rel, e));
    }
    Ok(())
}

fn rel_path(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join("/")
}

/// Every file under `dir` (recursively) for which `keep(name)` holds;
/// directories whose name starts with `.` are skipped unless `hidden`.
fn walk(root: &Path, dir: &Path, hidden: bool, keep: &dyn Fn(&str) -> bool, out: &mut Vec<String>) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        if path.is_dir() {
            if hidden || !name.starts_with('.') {
                walk(root, &path, hidden, keep, out)?;
            }
        } else if keep(&name) {
            out.push(rel_path(root, &path));
        }
    }
    Ok(())
}

impl FsStore {
    /// A store over the `plan/` directory `root`.
    pub fn new(root: impl Into<PathBuf>) -> FsStore {
        FsStore {
            root: root.into(),
            before_write: None,
        }
    }

    /// The plan directory.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// The absolute path of a relative plan path, refused when it would
    /// leave the plan root (`..`, an absolute path, a drive prefix — see
    /// [`is_safe_rel`]). Every read and write goes through this, so no verb
    /// that takes a path or a horizon-ish string can touch a file outside
    /// `plan/` (§2).
    pub fn abs(&self, rel: &str) -> Result<PathBuf, StoreError> {
        check_rel(rel)?;
        Ok(self.root.join(rel))
    }

    /// Install a hook run between the read and the verified write of every
    /// id-addressed edit (`write_line`, `remove_line`, `reorder_line`,
    /// `move_line`'s removal). Tests use it to simulate a concurrent editor.
    pub fn with_before_write_hook(mut self, hook: BeforeWriteHook) -> FsStore {
        self.before_write = Some(hook);
        self
    }

    /// Read `rel` together with its §1.3 guard: the file's text plus the
    /// mtime + content hash [`FsStore::write_guarded`] verifies before it
    /// writes. This is the read half of the whole-tree edit the kernel
    /// bridge performs (read every file → one kernel call → write the
    /// changed files back): the write happens well after the read, so the
    /// guard has to travel with the text instead of living inside one
    /// `modify_file` call.
    pub fn read_guarded(&self, rel: &str) -> Result<(String, FileGuard), StoreError> {
        let snap = Snapshot::read(&self.abs(rel)?, rel)?;
        let guard = FileGuard {
            mtime: snap.mtime,
            hash: snap.hash,
            existed: true,
        };
        Ok((snap.text, guard))
    }

    /// Write `text` to `rel` atomically, but only when the file still
    /// matches `guard` — byte-for-byte (content hash) and by mtime, the same
    /// two checks [`FsStore::modify_file`] runs. A file that changed since
    /// the guarded read — or that appeared where [`FileGuard::absent`] said
    /// none was — is §1.3's write race: [`StoreError::Conflict`] with both
    /// texts, and nothing is written. There is no retry, deliberately: the
    /// caller's edit was computed from the guarded text (by the kernel),
    /// so re-running it on the racing writer's text is the caller's call.
    pub fn write_guarded(&self, rel: &str, guard: &FileGuard, text: &str) -> Result<(), StoreError> {
        let path = self.abs(rel)?;
        let now: Option<Snapshot> = if path.is_file() {
            Some(Snapshot::read(&path, rel)?)
        } else {
            None
        };
        let settled = match &now {
            Some(n) => guard.existed && n.mtime == guard.mtime && n.hash == guard.hash,
            None => !guard.existed,
        };
        if settled {
            return write_atomic(&path, rel, text);
        }
        Err(StoreError::Conflict {
            id: Id::default(),
            file: rel.to_string(),
            ours: text.to_string(),
            theirs: now.map(|n| n.text).unwrap_or_default(),
        })
    }

    /// Locate `id` with the snapshot of the file it lives in. With a hint
    /// that file is tried first; with `only` no other file is searched.
    fn locate_snapshot(&self, cfg: &Config, id: &Id, hint: Option<&str>, only: bool) -> Result<(String, Snapshot, ParsedFile, usize), StoreError> {
        if let Some(rel) = hint {
            if self.exists(rel) {
                let snap = Snapshot::read(&self.abs(rel)?, rel)?;
                let parsed = parse_file(rel, &snap.text, cfg);
                if let Some(i) = edit::find_line(&parsed, id) {
                    return Ok((rel.to_string(), snap, parsed, i));
                }
            }
            if only {
                return Err(StoreError::NotFound(id.clone()));
            }
        }
        // The record copy, by the same rank `choose` (and `Tree::get`) use.
        let mut best: Option<(tree::RecordRank, (String, Snapshot, ParsedFile, usize))> = None;
        for rel in self.list_files()? {
            // A file that is not valid UTF-8, or that vanished since the
            // listing, holds no addressable line: skip it rather than failing
            // every lookup in the tree.
            let snap = match Snapshot::read(&self.abs(&rel)?, &rel) {
                Ok(snap) => snap,
                Err(e) if unreadable(&e).is_some() => continue,
                Err(e) => return Err(e),
            };
            let parsed = parse_file(&rel, &snap.text, cfg);
            let Some(i) = edit::find_line(&parsed, id) else {
                continue;
            };
            let Some(item) = parsed.lines[i].item() else {
                continue;
            };
            let rank = tree::record_rank(item);
            if best.as_ref().is_none_or(|(b, _)| rank < *b) {
                best = Some((rank, (rel, snap, parsed, i)));
            }
        }
        best.map(|(_, found)| found)
            .ok_or_else(|| StoreError::NotFound(id.clone()))
    }
}

impl Store for FsStore {
    fn list_files(&self) -> Result<Vec<String>, StoreError> {
        let mut out = Vec::new();
        walk(&self.root, &self.root, false, &|n| n.ends_with(".md") && n != "CLAUDE.md" && !n.starts_with('.'), &mut out)
            .map_err(|e| io_err(&self.root.display().to_string(), e))?;
        out.retain(|r| is_plan_file(r));
        sort_files(&mut out);
        Ok(out)
    }

    /// **Bytes then decode, so a file that is not text names its line**
    /// (W-17 repair, gap 676). `fs::read_to_string` answers
    /// `ErrorKind::InvalidData` with the sentence *"stream did not contain
    /// valid UTF-8"* and no position, which is a third spelling of a verdict
    /// [`NOT_UTF8`] already owns; this raises [`StoreError::Parse`] at
    /// [`bad_utf8_line`] with [`NOT_UTF8_VERDICT`] instead. `unreadable`
    /// classifies both shapes as `NotUtf8`, so `read_tree`'s tolerance and
    /// [`StoreError::is_not_utf8`] are unchanged.
    fn read_text(&self, rel: &str) -> Result<String, StoreError> {
        let bytes = self.read_bytes(rel)?;
        String::from_utf8(bytes)
            .map_err(|e| parse_err(rel, bad_utf8_line(e.as_bytes()), NOT_UTF8_VERDICT))
    }

    fn read_bytes(&self, rel: &str) -> Result<Vec<u8>, StoreError> {
        fs::read(self.abs(rel)?).map_err(|e| io_err(rel, e))
    }

    fn write_file(&self, rel: &str, text: &str) -> Result<(), StoreError> {
        write_atomic(&self.abs(rel)?, rel, text)
    }

    /// A real `O_APPEND` write, so `.tm/log.jsonl` never has to be read to be
    /// extended and concurrent appends do not lose lines. Only the last byte
    /// is read: when the file is non-empty and that byte is not `\n`, the
    /// write is `\n` + `text` in one `write_all` (G9's torn-line repair,
    /// parity P19). Two writers racing past the same torn line each add a
    /// `\n`, which leaves a blank line — skipped by every reader — never a
    /// glued one.
    fn append_text(&self, rel: &str, text: &str) -> Result<(), StoreError> {
        let path = self.abs(rel)?;
        if let Some(dir) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
            fs::create_dir_all(dir).map_err(|e| io_err(rel, e))?;
        }
        let write = || -> std::io::Result<()> {
            let mut f = fs::OpenOptions::new().create(true).read(true).append(true).open(&path)?;
            let torn = !text.is_empty() && f.metadata()?.len() > 0 && {
                let mut last = [0u8; 1];
                f.seek(SeekFrom::End(-1))?;
                f.read_exact(&mut last)?;
                last[0] != b'\n'
            };
            if torn {
                let mut buf = Vec::with_capacity(text.len() + 1);
                buf.push(b'\n');
                buf.extend_from_slice(text.as_bytes());
                f.write_all(&buf)
            } else {
                f.write_all(text.as_bytes())
            }
        };
        write().map_err(|e| io_err(rel, e))
    }

    fn delete_file(&self, rel: &str) -> Result<(), StoreError> {
        let path = self.abs(rel)?;
        match fs::remove_file(&path) {
            Ok(()) => Ok(()),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
            Err(e) => Err(io_err(rel, e)),
        }
    }

    fn exists(&self, rel: &str) -> bool {
        self.abs(rel).is_ok_and(|p| p.is_file())
    }

    fn abs_path(&self, rel: &str) -> Option<PathBuf> {
        self.abs(rel).ok()
    }

    fn read_config(&self) -> Result<Config, StoreError> {
        Ok(Config::load_or_default(self.abs(CONFIG_PATH)?)?)
    }

    /// The §1.3 guard for a whole-file edit: read (snapshot), edit, run the
    /// hook, verify the file is still exactly as it was read (or still
    /// absent), write atomically. A racing save sends the edit round again on
    /// the new text — appends and generated blocks merge into it — up to
    /// [`MAX_FILE_ATTEMPTS`] times, then [`StoreError::Conflict`] with both
    /// file texts and an empty id.
    ///
    /// A file that *existed* on an earlier attempt is never rebuilt from its
    /// horizon's initial text: a writer that saves by deleting and
    /// re-creating (some editors, a `git checkout`, a sync tool) would
    /// otherwise turn an append into "throw the file away and write one
    /// line". Once the file has been seen, only its own content — or a
    /// conflict — can come out of this.
    fn modify_file(&self, rel: &str, edit: &mut FileEdit<'_>) -> Result<(), StoreError> {
        let cfg = self.read_config()?;
        let path = self.abs(rel)?;
        let mut ours = String::new();
        let mut ever_existed = false;
        for attempt in 0..MAX_FILE_ATTEMPTS {
            let before: Option<Snapshot> = if path.is_file() {
                Some(Snapshot::read(&path, rel)?)
            } else {
                None
            };
            let text = match &before {
                Some(snap) => {
                    ever_existed = true;
                    snap.text.clone()
                }
                // Gone since we last looked: whoever removed it is mid-save.
                // Go round again rather than re-creating it from scratch.
                None if ever_existed => continue,
                None => Horizon::from_path(rel).map(|h| initial_text(&h)).unwrap_or_default(),
            };
            let parsed = parse_file(rel, &text, &cfg);
            let Some(new_text) = edit(&parsed)? else {
                return Ok(());
            };
            ours = new_text;
            if let Some(hook) = &self.before_write {
                hook(&path, attempt);
            }
            // Unchanged since the read, or still not there: write.
            let now: Option<Snapshot> = if path.is_file() {
                Snapshot::read(&path, rel).ok()
            } else {
                None
            };
            let settled = match (&before, &now) {
                (Some(b), Some(n)) => n.unchanged_since(b),
                (None, None) => true,
                _ => false,
            };
            if settled {
                return write_atomic(&path, rel, &ours);
            }
        }
        Err(StoreError::Conflict {
            id: Id::default(),
            file: rel.to_string(),
            ours,
            theirs: fs::read_to_string(&path).unwrap_or_default(),
        })
    }

    /// The §1.3 guard: read (snapshot), edit, run the hook, verify the
    /// file's mtime and content hash are unchanged, write atomically. On a
    /// mismatch re-read and retry once; then [`StoreError::Conflict`] with
    /// `ours` and the line as it is now (empty when the other writer removed
    /// it, or removed the whole file — a save-by-delete-then-create is a
    /// write race like any other, not an I/O failure).
    fn modify_line(&self, rel: Option<&str>, id: &Id, ours: &str, edit: &mut LineEdit<'_>) -> Result<(), StoreError> {
        let cfg = self.read_config()?;
        let only = rel.is_some();
        let mut hint: Option<String> = rel.map(str::to_string);
        // `Some((file, their line))` once a race has been seen.
        let mut raced: Option<(String, String)> = None;
        for attempt in 0..2 {
            let located = self.locate_snapshot(&cfg, id, hint.as_deref(), only);
            let (rel, snap, parsed, idx) = match (located, &raced) {
                (Ok(found), _) => found,
                // The other writer took the line away between the attempts:
                // that is the race, not a plain "no such id".
                (Err(e), Some((file, theirs))) if e.is_not_found() => {
                    return Err(StoreError::Conflict {
                        id: id.clone(),
                        file: file.clone(),
                        ours: ours.to_string(),
                        theirs: theirs.clone(),
                    })
                }
                (Err(e), _) => return Err(e),
            };
            let Some(new_text) = edit(&parsed, idx)? else {
                return Ok(());
            };
            let path = self.abs(&rel)?;
            if let Some(hook) = &self.before_write {
                hook(&path, attempt);
            }
            // A file that is gone (or no longer readable) is *changed*: the
            // race path, not an error path.
            let now = Snapshot::read(&path, &rel).ok();
            if now.as_ref().is_some_and(|now| now.unchanged_since(&snap)) {
                return write_atomic(&path, &rel, &new_text);
            }
            let theirs = now
                .as_ref()
                .and_then(|now| {
                    let current = parse_file(&rel, &now.text, &cfg);
                    edit::find_line(&current, id).map(|i| current.lines[i].text())
                })
                .unwrap_or_default();
            raced = Some((rel.clone(), theirs));
            hint = Some(rel);
        }
        let (file, theirs) = raced.unwrap_or_default();
        Err(StoreError::Conflict {
            id: id.clone(),
            file,
            ours: ours.to_string(),
            theirs,
        })
    }
}

// ---------------------------------------------------------------------------
// MemStore
// ---------------------------------------------------------------------------

/// An in-memory store (`relative path → text`) with the same behaviour as
/// [`FsStore`] minus the disk: for tests and for the planner's purity
/// tests. Interior mutability, so it is shared like the on-disk store.
#[derive(Default)]
pub struct MemStore {
    files: Mutex<BTreeMap<String, String>>,
}

impl fmt::Debug for MemStore {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MemStore").field("files", &self.paths()).finish()
    }
}

impl Clone for MemStore {
    fn clone(&self) -> MemStore {
        MemStore {
            files: Mutex::new(self.lock().clone()),
        }
    }
}

impl MemStore {
    /// An empty store.
    pub fn new() -> MemStore {
        MemStore::default()
    }

    /// Load every UTF-8 file under `dir` (recursively, `.tm/` included,
    /// `.git/` and `target/` skipped) — a fixture tree such as
    /// `tests/fixtures/plan-basic`.
    pub fn from_dir(dir: impl AsRef<Path>) -> Result<MemStore, StoreError> {
        let dir = dir.as_ref();
        let mut rels = Vec::new();
        walk(dir, dir, true, &|_| true, &mut rels).map_err(|e| io_err(&dir.display().to_string(), e))?;
        let store = MemStore::new();
        for rel in rels {
            if rel.split('/').any(|p| p == ".git" || p == "target") {
                continue;
            }
            let bytes = fs::read(dir.join(&rel)).map_err(|e| io_err(&rel, e))?;
            if let Ok(text) = String::from_utf8(bytes) {
                store.insert(&rel, &text);
            }
        }
        Ok(store)
    }

    fn lock(&self) -> MutexGuard<'_, BTreeMap<String, String>> {
        self.files.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Builder form of [`MemStore::insert`].
    pub fn with_file(self, rel: &str, text: &str) -> MemStore {
        self.insert(rel, text);
        self
    }

    /// Set a file's text.
    pub fn insert(&self, rel: &str, text: &str) {
        self.lock().insert(rel.replace('\\', "/"), text.to_string());
    }

    /// Delete a file; returns its text.
    pub fn remove(&self, rel: &str) -> Option<String> {
        self.lock().remove(rel)
    }

    /// A file's text.
    pub fn text(&self, rel: &str) -> Option<String> {
        self.lock().get(rel).cloned()
    }

    /// Every path in the store, sorted.
    pub fn paths(&self) -> Vec<String> {
        self.lock().keys().cloned().collect()
    }

    /// A copy of every file.
    pub fn snapshot(&self) -> BTreeMap<String, String> {
        self.lock().clone()
    }
}

impl Store for MemStore {
    fn list_files(&self) -> Result<Vec<String>, StoreError> {
        let mut out: Vec<String> = self.lock().keys().filter(|k| is_plan_file(k)).cloned().collect();
        sort_files(&mut out);
        Ok(out)
    }

    fn read_text(&self, rel: &str) -> Result<String, StoreError> {
        check_rel(rel)?;
        self.text(rel).ok_or_else(|| {
            io_err(
                rel,
                std::io::Error::new(std::io::ErrorKind::NotFound, "no such file in the memory store"),
            )
        })
    }

    fn write_file(&self, rel: &str, text: &str) -> Result<(), StoreError> {
        check_rel(rel)?;
        self.insert(rel, text);
        Ok(())
    }

    fn delete_file(&self, rel: &str) -> Result<(), StoreError> {
        check_rel(rel)?;
        self.remove(rel);
        Ok(())
    }

    fn exists(&self, rel: &str) -> bool {
        is_safe_rel(rel) && self.lock().contains_key(rel)
    }

    fn abs_path(&self, _rel: &str) -> Option<PathBuf> {
        None
    }
}

// ---------------------------------------------------------------------------
// Runtime state (§10.2)
// ---------------------------------------------------------------------------

/// `Option<NaiveTime>` as `"HH:MM"` / `null`.
pub mod opt_hhmm {
    use super::hhmm;
    use chrono::NaiveTime;
    use serde::{de, Deserialize, Deserializer, Serializer};

    /// Serialize as `"HH:MM"` or `null`.
    pub fn serialize<S: Serializer>(t: &Option<NaiveTime>, s: S) -> Result<S::Ok, S::Error> {
        match t {
            Some(t) => s.serialize_str(&hhmm::format(t)),
            None => s.serialize_none(),
        }
    }

    /// Deserialize from `"HH:MM"` or `null`.
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Option<NaiveTime>, D::Error> {
        let s: Option<String> = Option::deserialize(d)?;
        s.map(|s| hhmm::parse(&s).map_err(de::Error::custom)).transpose()
    }
}

/// `Option<(NaiveTime, NaiveTime)>` as `["HH:MM", "HH:MM"]` / `null`.
pub mod opt_window {
    use super::hhmm;
    use chrono::NaiveTime;
    use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

    /// Serialize as a two-element array or `null`.
    pub fn serialize<S: Serializer>(w: &Option<(NaiveTime, NaiveTime)>, s: S) -> Result<S::Ok, S::Error> {
        match w {
            Some((a, b)) => [hhmm::format(a), hhmm::format(b)].serialize(s),
            None => s.serialize_none(),
        }
    }

    /// Deserialize from a two-element array or `null`.
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Option<(NaiveTime, NaiveTime)>, D::Error> {
        let v: Option<[String; 2]> = Option::deserialize(d)?;
        v.map(|[a, b]| {
            Ok((
                hhmm::parse(&a).map_err(de::Error::custom)?,
                hhmm::parse(&b).map_err(de::Error::custom)?,
            ))
        })
        .transpose()
    }
}

/// `Option<T>` as `T`'s `Display` / `FromStr` string (`2026-W36`,
/// `2026-08`) or `null`.
pub mod opt_str {
    use std::fmt::Display;
    use std::str::FromStr;

    use serde::{de, Deserialize, Deserializer, Serializer};

    /// Serialize with `Display`, or `null`.
    pub fn serialize<S: Serializer, T: Display>(v: &Option<T>, s: S) -> Result<S::Ok, S::Error> {
        match v {
            Some(t) => s.serialize_str(&t.to_string()),
            None => s.serialize_none(),
        }
    }

    /// Deserialize with `FromStr`, or `null`.
    pub fn deserialize<'de, D: Deserializer<'de>, T: FromStr>(d: D) -> Result<Option<T>, D::Error>
    where
        T::Err: Display,
    {
        let s: Option<String> = Option::deserialize(d)?;
        s.map(|s| s.parse().map_err(de::Error::custom)).transpose()
    }
}

/// The block being worked on (`state.active`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ActiveBlock {
    /// The item.
    pub id: Id,
    /// When it started (`HH:MM`).
    #[serde(with = "hhmm")]
    pub started: NaiveTime,
    /// Planned minutes (`est × duration multiplier`).
    pub est_min: u32,
    /// Timer paused (`Space`).
    pub paused: bool,
}

/// A running break (`state.break`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(default)]
pub struct BreakState {
    /// When it started (`HH:MM`).
    #[serde(with = "opt_hhmm")]
    pub started: Option<NaiveTime>,
    /// Planned minutes.
    pub planned_min: u32,
    /// `walk` / `seat` / `bed` / `phone` — one of [`BreakPlace`]'s words.
    #[serde(rename = "where")]
    pub place: Option<String>,
}

impl BreakState {
    /// **When the running break began, as an instant** — the ONE reading of
    /// `started` (the campaign's **D81** call on README gap 3820, parity
    /// **P73**, W-41 track T): the latest instant at or before `now` whose
    /// local clock in `tz` is that `HH:MM`
    /// ([`crate::capacity::latest_at_or_before`]). The log holds no line for a
    /// running break — its `break` entry is appended when it ENDS — so the
    /// cache's clock is all there is, and D75's rule is the reading under which
    /// the break can still be running: a break begun at 23:50 is still the
    /// evening's at 00:10. Fork 4748911 put the clock on TODAY's date at every
    /// site, so after local midnight the break began in the future: `tm done`
    /// netted none of it out of the block's worked minutes and `tm break`
    /// logged it tonight with `actual_min: 0`.
    ///
    /// Every host reader of a running break's start calls this — `day.rs`'
    /// worked minutes, `end_break`, `since_break_min`, D61's walls request, the
    /// week cut's and `tm pause`'s (all through `Ctx::running_break`), and the
    /// TUI's timer and break-overrun prompt — so none keeps a clock of its own.
    /// `None` when the cache holds no `started`.
    pub fn started_at(&self, tz: Tz, now: DateTime<Tz>) -> Option<DateTime<Tz>> {
        self.started
            .map(|clock| crate::capacity::latest_at_or_before(tz, now, clock))
    }
}

/// **The places a break is taken** — the ONE host table of them (the
/// campaign's **D81** call on README gap 3903, parity **P75**, W-41 track T):
/// §13's `tm break --where <place>` reads its word here and refuses any other
/// by name (D20's shape), and the TUI's `b` then `w`/`s`/`b`/`p` (§12.6) reads
/// its key and its word here (`tui::app::BreakPlace` is this type). The
/// kernel's `PlanWire.placeOf?` reads the same four words off the planner
/// request and refuses any other (`badBreak place`), so a word the verb wrote
/// is a word the planner reads. Fork 4748911 kept the four in the TUI alone
/// and `tm break --where` stored any word it was given.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BreakPlace {
    /// `w` — a walk.
    Walk,
    /// `s` — stayed in the seat.
    Seat,
    /// `b` — lay down.
    Bed,
    /// `p` — the phone.
    Phone,
}

/// [`BreakPlace`]'s table: each place, its `--where` word and its TUI key, in
/// the order the TUI's prompt lists them.
const BREAK_PLACES: [(BreakPlace, &str, char); 4] = [
    (BreakPlace::Walk, "walk", 'w'),
    (BreakPlace::Seat, "seat", 's'),
    (BreakPlace::Bed, "bed", 'b'),
    (BreakPlace::Phone, "phone", 'p'),
];

impl BreakPlace {
    /// Every place, in the table's order.
    pub fn all() -> impl Iterator<Item = BreakPlace> {
        BREAK_PLACES.iter().map(|(p, _, _)| *p)
    }

    /// Its row of the table: the rows are in the variants' order
    /// (`each_place_is_its_own_row_of_the_table`).
    fn row(self) -> &'static (BreakPlace, &'static str, char) {
        &BREAK_PLACES[self as usize]
    }

    /// The `--where` word (§13 `tm break --where walk`), and the `where` the
    /// `break` log line and `.tm/state.json` carry.
    pub fn as_str(self) -> &'static str {
        self.row().1
    }

    /// The TUI key that picks it (§12.6).
    pub fn key(self) -> char {
        self.row().2
    }

    /// The place a TUI key picks.
    pub fn from_key(c: char) -> Option<BreakPlace> {
        BREAK_PLACES.iter().find(|(_, _, k)| *k == c).map(|(p, _, _)| *p)
    }

    /// The place a `--where` word names, exactly as the table spells it.
    pub fn parse(word: &str) -> Option<BreakPlace> {
        BREAK_PLACES.iter().find(|(_, w, _)| *w == word).map(|(p, _, _)| *p)
    }

    /// The table's words, `walk, seat, bed, phone`, for a message.
    pub fn words() -> String {
        BREAK_PLACES.iter().map(|(_, w, _)| *w).collect::<Vec<_>>().join(", ")
    }
}

/// A running interruption (`state.interrupt`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(default)]
pub struct InterruptState {
    /// When it started (`HH:MM`).
    #[serde(with = "opt_hhmm")]
    pub started: Option<NaiveTime>,
    /// The block that was interrupted.
    pub id: Option<Id>,
}

/// The last closed periods (`state.closed`, §6.3).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(default)]
pub struct Closed {
    /// Last day closed.
    pub day: Option<NaiveDate>,
    /// Last week closed (`2026-W36`).
    #[serde(with = "opt_str")]
    pub week: Option<IsoWeek>,
    /// Last month closed (`2026-08`).
    #[serde(with = "opt_str")]
    pub month: Option<YearMonth>,
    /// Whether the kernel's `autoClose` has run to success over this tree
    /// since the stamps above were last written by a binary that did not
    /// know this field. The stamps say which periods have *ended* at the
    /// last close; only a kernel sweep makes them also say that nothing live
    /// is left in those periods. The fork-point binary stamped periods closed
    /// that its sixteen-period catch-up never ran (kernel/README.md, stage 4
    /// step 6's table, row 2), so a tree it last touched carries current
    /// stamps over stranded lines; this field's absence is how the automatic
    /// close tells such a tree apart and sweeps it once. It is written only
    /// when set, so §10.2's documented shape is unchanged, and a binary that
    /// does not know it drops it on its next write — which is exactly the
    /// writer whose stamps cannot be trusted.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub swept: bool,
}

/// `.tm/state.json` (§10.2) — runtime, not committed:
///
/// ```json
/// {"date":"2026-09-07","wake":"06:05","arrival":"07:00","loc":"lounge","window":["07:00","16:00"],"budget":6,
///  "active":{"id":"t3","started":"09:32","est_min":192,"paused":false},
///  "break":null,"interrupt":null,
///  "last_plan_hash":"a91f…","priorities_yesterday":{"d1":1,"m2":3},
///  "closed":{"day":"2026-09-06","week":"2026-W36","month":"2026-08"}}
/// ```
///
/// Every field has a default, so a partial file loads; unknown fields are
/// ignored.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(default)]
pub struct RuntimeState {
    /// The day this state describes.
    pub date: Option<NaiveDate>,
    /// `tm wake`.
    #[serde(with = "opt_hhmm")]
    pub wake: Option<NaiveTime>,
    /// `tm arrive`.
    #[serde(with = "opt_hhmm")]
    pub arrival: Option<NaiveTime>,
    /// Current location (`lounge`, `home`, …).
    pub loc: Option<String>,
    /// Working window `[start, end]` computed at arrival (§8.1).
    #[serde(with = "opt_window")]
    pub window: Option<(NaiveTime, NaiveTime)>,
    /// Block budget computed at arrival.
    pub budget: Option<u32>,
    /// The running block.
    pub active: Option<ActiveBlock>,
    /// The running break (`"break"` in JSON).
    #[serde(rename = "break")]
    pub break_: Option<BreakState>,
    /// The running interruption.
    pub interrupt: Option<InterruptState>,
    /// Hash of the last emitted plan.
    pub last_plan_hash: Option<String>,
    /// Yesterday's `p` per item, for hysteresis (§7.4).
    pub priorities_yesterday: BTreeMap<Id, u8>,
    /// Last closed periods.
    pub closed: Closed,
}

impl RuntimeState {
    /// **Roll the day-scoped fields to `today`** — what the binary's housekeeping does
    /// at the first verb of a new local date (`tm/src/cli/ctx.rs`' `roll_day`, which
    /// calls this): `date` becomes `today`, and `window`, `budget`, `arrival` and
    /// `last_plan_hash` — the facts §10.2 says belong to `date` — are dropped. `wake`
    /// and `loc` are kept (not day-scoped), and so are `active`, `break` and
    /// `interrupt`: a block begun before midnight is still running, and `tm wake` ends
    /// the night (§10.1). Returns whether anything changed: a state naming no date, or
    /// naming `today`, is left as it is.
    ///
    /// In `tm-core` since W-41 (README gap 4041) so the one rule is also what a test
    /// reads as "the state `tm plan` would plan at that instant": the TUI, left open
    /// past midnight, never runs it (it writes nothing on a timer), and the kernel
    /// reads its stale state as this roll leaves it (the campaign's D81 call on README
    /// gap 3860, parity P77).
    pub fn roll_to(&mut self, today: NaiveDate) -> bool {
        if !matches!(self.date, Some(d) if d != today) {
            return false;
        }
        self.date = Some(today);
        self.arrival = None;
        self.window = None;
        self.budget = None;
        self.last_plan_hash = None;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg() -> Config {
        Config::default()
    }

    /// **The break-place table is one table, read both ways** (D81, gap 3903):
    /// each variant is its own row, every word and every key reads back to its
    /// place, and nothing else reads as one.
    #[test]
    fn each_place_is_its_own_row_of_the_table() {
        for (i, (p, word, key)) in BREAK_PLACES.iter().enumerate() {
            assert_eq!(*p as usize, i, "{p:?} is row {i}");
            assert_eq!(p.as_str(), *word);
            assert_eq!(p.key(), *key);
            assert_eq!(BreakPlace::parse(word), Some(*p));
            assert_eq!(BreakPlace::from_key(*key), Some(*p));
        }
        assert_eq!(BreakPlace::all().count(), 4);
        assert_eq!(BreakPlace::words(), "walk, seat, bed, phone");
        for unknown in ["hammock", "Walk", " walk", "", "w"] {
            assert_eq!(BreakPlace::parse(unknown), None, "{unknown:?}");
        }
        assert_eq!(BreakPlace::from_key('z'), None);
    }

    /// **A running break's start is the latest instant at or before `now` with
    /// its clock** (D81, gap 3820, P73): begun at 23:50 and read at 00:10, it is
    /// last night's, not tonight's; read the same evening it is that evening's.
    #[test]
    fn a_running_break_began_at_the_latest_instant_with_its_clock() {
        use chrono::TimeZone;
        let tz: Tz = "America/Chicago".parse().expect("zone");
        let br = BreakState {
            started: Some(NaiveTime::from_hms_opt(23, 50, 0).expect("t")),
            planned_min: 20,
            place: None,
        };
        let at = |d, h, m| tz.with_ymd_and_hms(2026, 9, d, h, m, 0).single().expect("t");
        assert_eq!(br.started_at(tz, at(9, 0, 10)), Some(at(8, 23, 50)), "after midnight");
        assert_eq!(br.started_at(tz, at(8, 23, 55)), Some(at(8, 23, 50)), "the same evening");
        assert_eq!(BreakState::default().started_at(tz, at(8, 23, 55)), None);
    }

    #[test]
    fn plan_file_filter_and_order() {
        assert!(is_plan_file("week/2026-W37.md"));
        assert!(is_plan_file("backlog.md"));
        assert!(!is_plan_file(".tm/state.json"));
        assert!(!is_plan_file(".claude/skills/x/SKILL.md"));
        assert!(!is_plan_file("CLAUDE.md"));
        assert!(!is_plan_file("day/2026-09-07.svg"));
        assert!(!is_plan_file("week/.hidden.md"));
        let mut files: Vec<String> = [
            "inbox.md",
            "day/2026-09-08.md",
            "day/2026-09-07.md",
            "week/2026-W37.md",
            "notes/x.md",
            "calendar/2026-W37.md",
            "optional.md",
            "month/2026-09.md",
            "routines.md",
            "backlog.md",
            "month/2026-08.md",
            "backlog.md",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        sort_files(&mut files);
        assert_eq!(
            files,
            [
                "month/2026-08.md",
                "month/2026-09.md",
                "week/2026-W37.md",
                "backlog.md",
                "routines.md",
                "optional.md",
                "calendar/2026-W37.md",
                "day/2026-09-07.md",
                "day/2026-09-08.md",
                "inbox.md",
                "notes/x.md",
            ]
        );
    }

    #[test]
    fn initial_texts() {
        let w = Horizon::Week(IsoWeek::new(2026, 37));
        assert_eq!(
            initial_text(&w),
            "---\nweek: 2026-W37\nwindow: 2026-09-07..2026-09-13\n---\n"
        );
        assert_eq!(horizon_path(&w), "week/2026-W37.md");
        assert_eq!(
            initial_text(&Horizon::Month(YearMonth::new(2026, 9))),
            "---\nmonth: 2026-09\n---\n"
        );
        let d = Horizon::Day(NaiveDate::from_ymd_opt(2026, 9, 7).unwrap());
        assert_eq!(
            initial_text(&d),
            "---\ndate: 2026-09-07\n---\n![day](2026-09-07.svg)\n"
        );
        assert_eq!(initial_text(&Horizon::Backlog), "");
        let f = parse_file("week/2026-W37.md", &initial_text(&w), &cfg());
        assert_eq!(f.front("window"), Some("2026-09-07..2026-09-13"));
        assert!(f.problems.is_empty());
    }

    #[test]
    fn sections_and_headings() {
        let text = "---\nweek: 2026-W37\n---\n# A\n- [ ] 3 x ^a\n\n<!-- tm:plan start -->\n# not a heading\n<!-- tm:plan end -->\n## series:s\n- [ ] 3 y ^b\n- [ ] 3 z ^c\n";
        let f = parse_file("week/2026-W37.md", text, &cfg());
        assert_eq!(edit::front_matter_len(&f), 3);
        let hs = edit::headings(&f);
        assert_eq!(hs.len(), 2);
        assert_eq!((hs[0].index, hs[0].level, hs[0].text.as_str()), (3, 1, "A"));
        assert_eq!((hs[1].index, hs[1].level, hs[1].text.as_str()), (9, 2, "series:s"));
        assert_eq!(edit::section_range(&f, 4), (4, 9));
        assert_eq!(edit::section_range(&f, 10), (10, 12));
        let g = parse_file("routines.md", "- a dur:1m\n- b dur:1m\n", &cfg());
        assert_eq!(edit::section_range(&g, 1), (0, 2));
    }

    #[test]
    fn append_and_insert_keep_bytes() {
        let text = "# A\n- [ ] 3 x ^a\n\n## Log\n07:00 start\n\n## Notes\n";
        let f = parse_file("day/2026-09-07.md", text, &cfg());
        assert_eq!(
            edit::append_to_section(&f, "## Log", "08:00 done"),
            "# A\n- [ ] 3 x ^a\n\n## Log\n07:00 start\n08:00 done\n\n## Notes\n"
        );
        assert_eq!(
            edit::append_to_section(&f, "Notes", "free text"),
            "# A\n- [ ] 3 x ^a\n\n## Log\n07:00 start\n\n## Notes\nfree text\n"
        );
        assert_eq!(
            edit::append_to_section(&f, "Pinned", "- [ ] 2 y ^b"),
            "# A\n- [ ] 3 x ^a\n\n## Log\n07:00 start\n\n## Notes\n\n# Pinned\n- [ ] 2 y ^b\n"
        );
        assert_eq!(edit::append_to_end(&f, "tail"), "# A\n- [ ] 3 x ^a\n\n## Log\n07:00 start\n\n## Notes\ntail\n");
        // No final newline: the convention is kept.
        let f = parse_file("inbox.md", "- a\n- b", &cfg());
        assert_eq!(edit::append_to_end(&f, "- c"), "- a\n- b\n- c");
        let f = parse_file("inbox.md", "", &cfg());
        assert_eq!(edit::append_to_end(&f, "- c"), "- c\n");
        assert_eq!(edit::append_to_section(&f, "## Log", "x"), "## Log\nx\n");
        // CRLF files keep CRLF.
        let f = parse_file("inbox.md", "- a\r\n- b\r\n", &cfg());
        assert_eq!(edit::append_to_end(&f, "- c"), "- a\r\n- b\r\n- c\r\n");
    }

    #[test]
    fn generated_blocks() {
        let text = "---\ndate: 2026-09-07\n---\n![day](2026-09-07.svg)\n<!-- tm:plan start 10:42 -->\nold 1\nold 2\n<!-- tm:plan end -->\n\n# Pinned\n- [ ] 2 y ^p1\n";
        let f = parse_file("day/2026-09-07.md", text, &cfg());
        assert_eq!(
            edit::replace_generated(&f, "plan", None, "new 1\nnew 2\nnew 3\n"),
            "---\ndate: 2026-09-07\n---\n![day](2026-09-07.svg)\n<!-- tm:plan start 10:42 -->\nnew 1\nnew 2\nnew 3\n<!-- tm:plan end -->\n\n# Pinned\n- [ ] 2 y ^p1\n"
        );
        assert_eq!(
            edit::replace_generated(&f, "plan", Some("11:00"), ""),
            "---\ndate: 2026-09-07\n---\n![day](2026-09-07.svg)\n<!-- tm:plan start 11:00 -->\n<!-- tm:plan end -->\n\n# Pinned\n- [ ] 2 y ^p1\n"
        );
        // Missing: after the image line.
        let f = parse_file("day/2026-09-07.md", "---\ndate: 2026-09-07\n---\n![day](2026-09-07.svg)\n\n# Pinned\n", &cfg());
        assert_eq!(
            edit::replace_generated(&f, "plan", Some("10:42"), "row"),
            "---\ndate: 2026-09-07\n---\n![day](2026-09-07.svg)\n<!-- tm:plan start 10:42 -->\nrow\n<!-- tm:plan end -->\n\n# Pinned\n"
        );
        // Missing: after the front matter; none: at the top.
        let f = parse_file("week/2026-W37.md", "---\nweek: 2026-W37\n---\n# M\n", &cfg());
        assert_eq!(
            edit::replace_generated(&f, "review", None, "a\nb"),
            "---\nweek: 2026-W37\n---\n<!-- tm:review start -->\na\nb\n<!-- tm:review end -->\n# M\n"
        );
        let f = parse_file("backlog.md", "# U\n- [ ] 3 x ^a\n", &cfg());
        assert_eq!(
            edit::replace_generated(&f, "x", None, "a"),
            "<!-- tm:x start -->\na\n<!-- tm:x end -->\n# U\n- [ ] 3 x ^a\n"
        );
        let f = parse_file("backlog.md", "", &cfg());
        assert_eq!(edit::replace_generated(&f, "x", None, ""), "<!-- tm:x start -->\n<!-- tm:x end -->\n");
        // Unterminated: the end marker goes back directly under the start
        // marker, so the text that followed the lost marker is kept.
        let f = parse_file("backlog.md", "# U\n<!-- tm:x start -->\nstale\nmore\n", &cfg());
        assert!(f.problems.iter().any(|p| p.message.contains("unterminated")));
        assert_eq!(
            edit::replace_generated(&f, "x", None, "fresh"),
            "# U\n<!-- tm:x start -->\nfresh\n<!-- tm:x end -->\nstale\nmore\n"
        );
        // …and the headings below it are visible again, so an append lands in
        // the real section instead of inside the block.
        let f = parse_file(
            "day/2026-09-07.md",
            "<!-- tm:plan start -->\nrow\n\n# Pinned\n- [ ] 2 C ^p1\n\n## Log\n06:05 wake\n",
            &cfg(),
        );
        assert_eq!(
            edit::headings(&f).iter().map(|h| h.text.as_str()).collect::<Vec<_>>(),
            ["Pinned", "Log"]
        );
        assert_eq!(
            edit::append_to_section(&f, "## Log", "07:00 start"),
            "<!-- tm:plan start -->\nrow\n\n# Pinned\n- [ ] 2 C ^p1\n\n## Log\n06:05 wake\n07:00 start\n"
        );
        assert_eq!(
            edit::replace_generated(&f, "plan", None, "new row"),
            "<!-- tm:plan start -->\nnew row\n<!-- tm:plan end -->\nrow\n\n# Pinned\n- [ ] 2 C ^p1\n\n## Log\n06:05 wake\n"
        );
        // Marker recognition mirrors the parser's.
        assert_eq!(edit::marker_of("  <!-- tm:plan end -->  "), Some(("plan".to_string(), false)));
        assert_eq!(edit::marker_of("<!-- tm:plan start 10:42 -->"), Some(("plan".to_string(), true)));
        assert_eq!(edit::marker_of("<!-- tm:plan -->"), None);
        assert_eq!(edit::marker_of("07:00 row"), None);
    }

    #[test]
    fn find_replace_remove_reorder() {
        let text = "# M\n- [ ] 3 a ^a\n- [ ] 3 b ^b\n\n# T\n- [ ] 3 c ^c\nprose\n- [ ] 3 d ^d\n- [ ] 3 e ^e\n";
        let f = parse_file("week/2026-W37.md", text, &cfg());
        assert_eq!(edit::find_line(&f, &Id::new("d")), Some(7));
        assert_eq!(edit::find_line(&f, &Id::new("zz")), None);
        assert_eq!(
            edit::replace_line(&f, 7, "- [x] 3 d ^d"),
            "# M\n- [ ] 3 a ^a\n- [ ] 3 b ^b\n\n# T\n- [ ] 3 c ^c\nprose\n- [x] 3 d ^d\n- [ ] 3 e ^e\n"
        );
        assert_eq!(
            edit::remove_line(&f, 7),
            (
                "# M\n- [ ] 3 a ^a\n- [ ] 3 b ^b\n\n# T\n- [ ] 3 c ^c\nprose\n- [ ] 3 e ^e\n".to_string(),
                "- [ ] 3 d ^d".to_string()
            )
        );
        // Up one: jumps over the prose line.
        assert_eq!(
            edit::reorder_line(&f, 7, -1).unwrap(),
            "# M\n- [ ] 3 a ^a\n- [ ] 3 b ^b\n\n# T\n- [ ] 3 d ^d\n- [ ] 3 c ^c\nprose\n- [ ] 3 e ^e\n"
        );
        // Down one.
        assert_eq!(
            edit::reorder_line(&f, 5, 1).unwrap(),
            "# M\n- [ ] 3 a ^a\n- [ ] 3 b ^b\n\n# T\nprose\n- [ ] 3 d ^d\n- [ ] 3 c ^c\n- [ ] 3 e ^e\n"
        );
        // Clamped to the section; a no-op writes nothing.
        assert_eq!(
            edit::reorder_line(&f, 5, -5),
            None,
            "first item of the section cannot move up"
        );
        assert_eq!(
            edit::reorder_line(&f, 5, 10).unwrap(),
            "# M\n- [ ] 3 a ^a\n- [ ] 3 b ^b\n\n# T\nprose\n- [ ] 3 d ^d\n- [ ] 3 e ^e\n- [ ] 3 c ^c\n"
        );
        assert_eq!(edit::reorder_line(&f, 2, 1), None, "last item of M stays in M");
        // Validation.
        assert!(edit::validate_replacement(&f, 7, "- [x] 3 d ^d").is_ok());
        assert!(edit::validate_replacement(&f, 7, "- [x] 3 d").is_err());
        assert!(edit::validate_replacement(&f, 7, "- [x] 3 d ^q").is_err());
        assert!(edit::validate_replacement(&f, 7, "- [x] 3 d ^d\n- more").is_err());
        assert!(edit::validate_replacement(&f, 7, "prose").is_err());
        let r = parse_file("routines.md", "- lunch win:11:30-13:30 dur:30m\n", &cfg());
        assert_eq!(edit::find_line(&r, &Id::new("lunch")), Some(0));
        assert!(edit::validate_replacement(&r, 0, "- lunch win:11:30-13:30 dur:30m ^lu").is_ok());
    }

    #[test]
    fn demoted_copy_is_not_preferred() {
        let month = parse_file(
            "month/2026-09.md",
            "# Outcomes\n- [ ] 5 !1 O ^O1\n\n# Demoted\n- [-] 4 3b R @O1 est:3b demoted:W37 ^m2\n",
            &cfg(),
        );
        let week = parse_file("week/2026-W37.md", "# M\n- [ ] 4 6b R @O1 ^m2\n", &cfg());
        assert_eq!(edit::find_line(&month, &Id::new("m2")), Some(4));
        assert!(edit::is_demoted(&month, 4));
        let files = [month, week];
        assert_eq!(choose(files.iter().enumerate(), &Id::new("m2")), Some((1, 1)));
        assert_eq!(choose(files.iter().enumerate(), &Id::new("O1")), Some((0, 1)));
        let only_month = &files[..1];
        assert_eq!(choose(only_month.iter().enumerate(), &Id::new("m2")), Some((0, 4)));
    }

    #[test]
    fn mem_store_round_trips() {
        let store = MemStore::new()
            .with_file("backlog.md", "# U\n- [ ] 3 x ^a\n")
            .with_file("week/2026-W37.md", "---\nweek: 2026-W37\n---\n# T\n- [ ] 3 y ^b\n")
            .with_file(".tm/state.json", "{}");
        assert_eq!(store.list_files().unwrap(), ["week/2026-W37.md", "backlog.md"]);
        let tree = store.read_tree().unwrap();
        assert_eq!(tree.files.len(), 2);
        assert_eq!(tree.locate(&Id::new("b")), Some(Location { file: 0, line: 4 }));
        assert_eq!(tree.file_of(&Id::new("a")), Some("backlog.md"));
        assert_eq!(tree.ids().len(), 2);
        store.write_line(&Id::new("a"), "- [x] 3 x ^a").unwrap();
        assert_eq!(store.text("backlog.md").unwrap(), "# U\n- [x] 3 x ^a\n");
        assert!(store.write_line(&Id::new("zz"), "- [x] 3 x ^zz").unwrap_err().is_not_found());
        store.move_line(&Id::new("a"), "week/2026-W37.md", Some("T")).unwrap();
        assert_eq!(store.text("backlog.md").unwrap(), "# U\n");
        assert_eq!(
            store.text("week/2026-W37.md").unwrap(),
            "---\nweek: 2026-W37\n---\n# T\n- [ ] 3 y ^b\n- [x] 3 x ^a\n"
        );
        assert!(store.reorder_line(&Id::new("a"), -1).unwrap());
        assert!(!store.reorder_line(&Id::new("a"), -1).unwrap());
        assert_eq!(store.remove_line(&Id::new("b")).unwrap(), "- [ ] 3 y ^b");
        assert_eq!(
            store.text("week/2026-W37.md").unwrap(),
            "---\nweek: 2026-W37\n---\n# T\n- [x] 3 x ^a\n"
        );
        // Same-file move into another section.
        store.move_line(&Id::new("a"), "week/2026-W37.md", Some("Done")).unwrap();
        assert_eq!(
            store.text("week/2026-W37.md").unwrap(),
            "---\nweek: 2026-W37\n---\n# T\n\n# Done\n- [x] 3 x ^a\n"
        );
        // A missing horizon file is created with its front matter.
        store.insert_line("week/2026-W38.md", Some("Tasks"), "- [ ] 3 z ^z").unwrap();
        assert_eq!(
            store.text("week/2026-W38.md").unwrap(),
            "---\nweek: 2026-W38\nwindow: 2026-09-14..2026-09-20\n---\n# Tasks\n- [ ] 3 z ^z\n"
        );
        assert!(!store.ensure_horizon_file(&Horizon::Week(IsoWeek::new(2026, 38))).unwrap());
        assert!(store.ensure_horizon_file(&Horizon::Month(YearMonth::new(2026, 10))).unwrap());
        assert_eq!(store.load_state().unwrap(), RuntimeState::default());
        let st = RuntimeState {
            budget: Some(6),
            ..RuntimeState::default()
        };
        store.save_state(&st).unwrap();
        assert_eq!(store.load_state().unwrap(), st);
        assert_eq!(store.read_json::<RuntimeState>("nope.json").unwrap(), None);
        store.insert(".tm/model.json", "{ not json");
        assert!(matches!(store.read_json::<RuntimeState>(".tm/model.json"), Err(StoreError::Json { .. })));
        let dyn_store: &dyn Store = &store;
        assert!(dyn_store.read_json::<RuntimeState>("nope.json").unwrap().is_none());
        let cloned = store.clone();
        assert_eq!(cloned.snapshot(), store.snapshot());
    }
}
