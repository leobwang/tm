//! The undo stack behind `tm undo` (tm-spec-v1.md §13, §10.1).
//!
//! # API overview
//!
//! Nothing in the log is ever edited: `tm undo` **appends** a compensating
//! `undo{of,id}` event for every event the undone command wrote (§10.1) and
//! reverts the file edit and the `state.json` change it made (§13). What each
//! command did is recorded here, in `.tm/undo.json`:
//!
//! * [`Recorder::start`] snapshots the plan files, `.tm/state.json` and the
//!   length of `.tm/log.jsonl` before the command runs;
//!   [`Recorder::finish`] diffs all three and pushes one [`UndoEntry`].
//! * [`undo`] pops the top entry, appends one `undo` event per event that
//!   entry wrote (most recent first), restores the bytes of every file it
//!   changed and puts `state.json` back — except `closed`, which stays as it
//!   is so the §6.3 auto-close does not run a second time.
//! * [`UndoStack`] keeps the last [`MAX_ENTRIES`] commands.
//!
//! `state.json` (§10.2) has no field for this stack, so it lives beside it in
//! [`UNDO_PATH`].

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use tm_core::log::{Event, Log};
use tm_core::store::{RuntimeState, Store, StoreExt, LOG_PATH};

use super::ctx::Ctx;
use super::out::CliError;

/// `.tm/undo.json`.
pub const UNDO_PATH: &str = ".tm/undo.json";
/// How many commands the stack remembers.
pub const MAX_ENTRIES: usize = 50;

/// One event a command appended, and the id it was about.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UndoneEvent {
    /// The `ev` tag (§10.1).
    pub ev: String,
    /// The event's primary id, when it has one.
    pub id: Option<String>,
}

/// One file as it stood before a command.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FileBefore {
    /// Path relative to the plan root.
    pub path: String,
    /// The text before; `None` when the command created the file.
    pub before: Option<String>,
}

/// One undoable command.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct UndoEntry {
    /// The verb (`done`, `start`, …).
    pub verb: String,
    /// When it ran (RFC 3339).
    pub t: String,
    /// One line of human summary.
    pub summary: String,
    /// The events it appended, in order.
    pub events: Vec<UndoneEvent>,
    /// The files it changed, with their previous bytes.
    pub files: Vec<FileBefore>,
    /// `.tm/state.json` as it stood before.
    pub state: RuntimeState,
}

/// The stack in `.tm/undo.json`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(default)]
pub struct UndoStack {
    /// Oldest first; the last entry is what `tm undo` undoes.
    pub entries: Vec<UndoEntry>,
}

impl UndoStack {
    /// Read the stack (a missing or unreadable file is an empty stack).
    pub fn load(ctx: &Ctx) -> UndoStack {
        ctx.store
            .read_json::<UndoStack>(UNDO_PATH)
            .ok()
            .flatten()
            .unwrap_or_default()
    }

    /// Write the stack.
    pub fn save(&self, ctx: &Ctx) -> Result<(), CliError> {
        ctx.store.write_json(UNDO_PATH, self)?;
        Ok(())
    }
}

/// Every plan file's text, keyed by path.
fn snapshot(ctx: &Ctx) -> Result<BTreeMap<String, String>, CliError> {
    let mut out = BTreeMap::new();
    for rel in ctx.store.list_files()? {
        if let Ok(text) = ctx.store.read_text(&rel) {
            out.insert(rel, text);
        }
    }
    Ok(out)
}

/// The number of lines currently in `.tm/log.jsonl`.
fn log_len(ctx: &Ctx) -> usize {
    if !ctx.store.exists(LOG_PATH) {
        return 0;
    }
    ctx.store
        .read_text(LOG_PATH)
        .map(|t| t.lines().filter(|l| !l.trim().is_empty()).count())
        .unwrap_or(0)
}

/// Records what one command changed.
pub struct Recorder {
    verb: String,
    files: BTreeMap<String, String>,
    state: RuntimeState,
    log_len: usize,
}

impl Recorder {
    /// Snapshot the tree, the state and the log before running `verb`.
    pub fn start(ctx: &Ctx, verb: &str) -> Result<Recorder, CliError> {
        Ok(Recorder {
            verb: verb.to_string(),
            files: snapshot(ctx)?,
            state: ctx.state.clone(),
            log_len: log_len(ctx),
        })
    }

    /// Diff everything and push one entry onto the stack. A command that
    /// changed nothing pushes nothing.
    pub fn finish(self, ctx: &Ctx, summary: impl Into<String>) -> Result<(), CliError> {
        let after = snapshot(ctx)?;
        let mut files: Vec<FileBefore> = Vec::new();
        for (path, text) in &after {
            match self.files.get(path) {
                Some(before) if before == text => {}
                Some(before) => files.push(FileBefore {
                    path: path.clone(),
                    before: Some(before.clone()),
                }),
                None => files.push(FileBefore {
                    path: path.clone(),
                    before: None,
                }),
            }
        }
        for (path, before) in &self.files {
            if !after.contains_key(path) {
                files.push(FileBefore {
                    path: path.clone(),
                    before: Some(before.clone()),
                });
            }
        }

        let events = new_events(ctx, self.log_len);
        let state_changed = ctx.state != self.state;
        if files.is_empty() && events.is_empty() && !state_changed {
            return Ok(());
        }
        let mut stack = UndoStack::load(ctx);
        stack.entries.push(UndoEntry {
            verb: self.verb,
            t: tm_core::log::fmt_timestamp(&ctx.now),
            summary: summary.into(),
            events,
            files,
            state: self.state,
        });
        let len = stack.entries.len();
        if len > MAX_ENTRIES {
            stack.entries.drain(0..len - MAX_ENTRIES);
        }
        stack.save(ctx)
    }
}

/// The events appended since the log had `from` lines.
fn new_events(ctx: &Ctx, from: usize) -> Vec<UndoneEvent> {
    if !ctx.store.exists(LOG_PATH) {
        return Vec::new();
    }
    let Ok(text) = ctx.store.read_text(LOG_PATH) else {
        return Vec::new();
    };
    Log::parse(&text)
        .entries
        .into_iter()
        .skip(from)
        .map(|e| UndoneEvent {
            ev: e.ev.name().to_string(),
            id: e.ev.primary_id().map(str::to_string),
        })
        .collect()
}

/// What one `tm undo` did.
#[derive(Clone, Debug, Serialize)]
pub struct Undone {
    /// The verb that was undone.
    pub verb: String,
    /// Its summary line.
    pub summary: String,
    /// The compensating `undo` events appended (§10.1).
    pub events: Vec<UndoneEvent>,
    /// The files put back.
    pub files: Vec<String>,
    /// How many entries are left on the stack.
    pub remaining: usize,
}

/// Undo the last recorded command (§13).
pub fn undo(ctx: &mut Ctx) -> Result<Undone, CliError> {
    let mut stack = UndoStack::load(ctx);
    let Some(entry) = stack.entries.pop() else {
        return Err(CliError::msg("nothing to undo"));
    };

    // 1. The log is append-only: cancel each event with an `undo` (§10.1).
    for e in entry.events.iter().rev() {
        ctx.append_event(Event::Undo {
            of: e.ev.clone(),
            id: e.id.clone(),
        })?;
    }

    // 2. Put the file bytes back.
    let mut restored = Vec::new();
    for f in &entry.files {
        match &f.before {
            Some(text) => ctx.store.write_file(&f.path, text)?,
            None => {
                if let Some(abs) = ctx.store.abs_path(&f.path) {
                    if abs.exists() {
                        std::fs::remove_file(&abs)
                            .map_err(|e| CliError::io(f.path.clone(), e))?;
                    }
                }
            }
        }
        restored.push(f.path.clone());
    }

    // 3. Put `state.json` back — but keep `closed`, so the §6.3 auto-close
    //    does not run a second time over periods it has already closed.
    let mut state = entry.state.clone();
    state.closed = ctx.state.closed.clone();
    ctx.state = state;
    ctx.save_state()?;
    stack.save(ctx)?;
    ctx.reload()?;

    Ok(Undone {
        verb: entry.verb,
        summary: entry.summary,
        events: entry.events,
        files: restored,
        remaining: stack.entries.len(),
    })
}
