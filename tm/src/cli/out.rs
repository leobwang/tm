//! Output and errors for the CLI (tm-spec-v1.md §13).
//!
//! # API overview
//!
//! * [`CliError`] — every failure a verb can produce, with
//!   [`CliError::exit_code`] implementing §13's table: `1` for an ordinary
//!   error, `3` for a [`StoreError::Conflict`] (a write race, whose two
//!   texts are printed by [`CliError::report`]). `2` is not an error at all —
//!   it is what `tm check` *returns* when the tree has problems.
//! * [`ErrorOut`] — the failure half of `--json` (§13: "every verb accepts
//!   `--json`"). Defined once here, so a verb that returns `Err` is
//!   machine-readable for free: [`CliError::report`] prints this object on
//!   stderr in JSON mode and the human lines otherwise.
//! * [`emit`] — the success half: with `--json` it prints
//!   `serde_json::to_string_pretty(value)`, otherwise the human string the
//!   closure builds (which is never computed in JSON mode).
//! * [`fmt_dur`] and [`fmt_time`] — the small formatting helpers the
//!   human output shares.

use std::cell::RefCell;
use std::io;

use serde::Serialize;
use serde_json::{Map, Value};
use thiserror::Error;
use tm_core::model::Id;
use tm_core::store::StoreError;

/// Exit code for an ordinary failure (§13).
pub const EXIT_ERROR: i32 = 1;
/// Exit code for a write conflict (§13).
pub const EXIT_CONFLICT: i32 = 3;

/// Anything a verb can fail with.
#[derive(Debug, Error)]
pub enum CliError {
    /// A plain message (bad argument, nothing running…).
    #[error("{0}")]
    Msg(String),
    /// No item in the tree carries this id (or, for an id-less routine or
    /// optional line, this title key). Its own variant so the `--json`
    /// document can name the id a script asked for.
    #[error("no such item: ^{0}")]
    NotFound(Id),
    /// The command line itself does not parse — clap's own message. Only
    /// [`crate::cli::main`] builds one, and only to give a usage error the
    /// same `--json` shape as every other failure.
    #[error("{0}")]
    Usage(String),
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
    /// The Lean kernel refused a kernel-backed verb, or the FFI faulted.
    /// Every kernel refusal is **named** (`occupied`, `noSuchId`,
    /// `notDemoted`, `alreadyDemoted`, `badHorizon`, `badItem`,
    /// `tabbedLine`, `keyAbsent`, `danglingDep`, `depCycle`, `siteOutOfRange`,
    /// `dupId`, `notADemotion`,
    /// `ambiguousDemotion`, `duplicatePath`, `badLine`, `unterminatedComment`,
    /// `itemCheck`) and the
    /// name reaches both the human line and the `--json` document verbatim —
    /// AGENTS §8.1: a refusal you can name is a finding, one swallowed into
    /// free text is not.
    #[error("{}", .0.message)]
    Kernel(KernelIssue),
    /// **A `tm undo` stopped by §1.3's guard, carrying who wrote the file
    /// afterwards** (README gap 887).
    ///
    /// The conflict itself is exactly the [`StoreError::Conflict`] the
    /// `Store` arm carries — [`CliError::conflict`] projects it, so the exit
    /// code (§13's `3`), the one-sentence [`CliError::message`] and the two
    /// whole texts in `--json` are byte-for-byte what they were. What is new
    /// is [`LaterWriter`], which only the undo path can build, because only
    /// the undo path knows *which* command is being reversed and therefore
    /// where in `.tm/log.jsonl` to read forward from.
    ///
    /// Gap 887 is explicit that attribution cannot be bolted onto
    /// `CliError::message`: that sentence is shared by every verb's write
    /// race and none of the others has an undone command to read forward
    /// from. So it is a variant, and nothing else changes.
    #[error("{conflict}")]
    UndoBlocked {
        /// The write race, unchanged.
        conflict: StoreError,
        /// What the log records after the command being undone.
        blame: LaterWriter,
    },
}

/// **Who wrote the plan after the command `tm undo` is reversing** (README
/// gap 887), read from `.tm/log.jsonl` through the one reader (D9).
///
/// §6.3's automatic close runs inside `Ctx::load_with`, *before* every verb's
/// `Recorder::start`, so it is in no undo entry (README gap 731) and the undo
/// stack cannot name it. The log can: the close appends
/// `{"ev":"close","period":…,"key":…}` like any other event, and the undo
/// entry records the physical line its own first event landed on, so the
/// entries that came after it are exactly the tail past that point.
///
/// Every field is a **measurement**, never an inference: this says what the
/// log holds after the undone command, and does not claim that any of it
/// wrote the file the guard tripped on. Saying which entry touched which file
/// would need the close to be in an undo entry, which is gap 731 and a
/// behaviour change on every verb at once (D19).
#[derive(Clone, Debug, Default, Serialize)]
pub struct LaterWriter {
    /// False when the undone command appended no log entry at all (`tm rank`
    /// on a tree it did not have to log, and every entry written before the
    /// `log_line` field existed). There is then no anchor to read forward
    /// from and this carries nothing.
    pub anchored: bool,
    /// How many entries `.tm/log.jsonl` holds after the undone command's own.
    pub entries_after: usize,
    /// The physical line of the **first `close`** among them, when there is
    /// one — the automatic close, or an explicit `tm close` that is itself
    /// further up the stack.
    pub close_line: Option<u64>,
    /// **When** that close ran, as the kernel renders the line's instant
    /// (`Ctx::entries_at`'s display, the same door `tm log` prints through),
    /// when it could be read back.
    ///
    /// The *display* and not the payload, deliberately: `tm log`'s body —
    /// `key=…  period=…` — is built by re-parsing the line's JSON in the
    /// host (`lifecycle.rs`'s `log_human`), and gap 887 rules out a second
    /// parse on the undo path (D9). A line number, a tag and an instant are
    /// what the two doors hand back, so they are what this says; `tm log`
    /// is where the payload is already spelled, and the message points
    /// there.
    pub close_at: Option<String>,
}

/// `.tm/log.jsonl`, spelled once for the sentences below.
const LOG: &str = ".tm/log.jsonl";

impl LaterWriter {
    /// The human lines, printed under the conflict's own summary.
    ///
    /// Four cases and no fifth, because each is a different thing to do next:
    /// a close is named and the user is told it is unreachable by design; a
    /// tail with no close says the log knows of no `tm` write that could have
    /// done it; an empty tail says the same more strongly; and an unanchored
    /// entry says plainly that this undo cannot tell, rather than guessing
    /// from the first close in the file — which would name a close that ran
    /// *before* the command being undone.
    fn report(&self) {
        if !self.anchored {
            eprintln!(
                "  the command being undone appended no log entry, so there is no point in \
                 {LOG} to read forward from and this undo cannot say who wrote next"
            );
            return;
        }
        match (self.close_line, self.entries_after) {
            (Some(line), _) => {
                match &self.close_at {
                    Some(at) => eprintln!(
                        "  the later writer is tm itself: {LOG}:{line} records a `close` at \
                         {at}, appended after the command being undone"
                    ),
                    None => eprintln!(
                        "  the later writer is tm itself: {LOG}:{line} records a `close`, \
                         appended after the command being undone"
                    ),
                }
                eprintln!(
                    "    §6.3's automatic close runs inside every verb's load, before that \
                     verb's undo entry is opened, so it is in no entry and `tm undo` cannot \
                     reverse it (README gap 731)"
                );
                eprintln!(
                    "    every entry older than that close is behind it; `tm log` prints the \
                     close and what it wrote"
                );
            }
            (None, 0) => eprintln!(
                "  {LOG} records no entry after the command being undone, so no `tm` verb \
                 wrote this file since — it was changed from outside tm"
            ),
            (None, n) => eprintln!(
                "  {LOG} records {n} entr{} after the command being undone and no `close` \
                 among them; `tm log` shows them",
                if n == 1 { "y" } else { "ies" }
            ),
        }
    }
}

/// One named kernel refusal (or FFI fault), as the kernel bridge mapped it
/// from the response's `err` shape (`kernel/TmKernel/TmKernel/Boundary.lean`).
#[derive(Debug)]
pub struct KernelIssue {
    /// The refusal's name, exactly as the wire carries it.
    pub name: String,
    /// The human sentence; always contains `name`.
    pub message: String,
    /// The structured payload (`refusal`, plus the id/path/line the shape
    /// carries), for the `--json` document's `detail`.
    pub detail: Map<String, Value>,
}

impl KernelIssue {
    /// True for an FFI-level **fault** (`kernelFault`) — the kernel returned
    /// nothing usable — as opposed to a named refusal, which is the kernel
    /// working as designed. A fault is loud and recoverable, never a wrong
    /// answer: the TUI exits for one (terminal restored, bug report printed,
    /// exit 1) where a refusal stays a status-line message.
    pub fn is_fault(&self) -> bool {
        self.name == "kernelFault"
    }
}

impl CliError {
    /// A message error from anything displayable.
    pub fn msg(m: impl Into<String>) -> CliError {
        CliError::Msg(m.into())
    }

    /// True when this is a kernel **fault** (see [`KernelIssue::is_fault`]).
    pub fn is_kernel_fault(&self) -> bool {
        matches!(self, CliError::Kernel(issue) if issue.is_fault())
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
            // README gap 887: the undo's conflict IS a conflict, so §13's
            // exit code 3, the shared sentence and the two whole texts all
            // come from here exactly as they did before the variant existed.
            CliError::UndoBlocked { conflict, .. } => conflict,
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

    /// The one sentence the human path prints after `tm: `, and the
    /// `message` of the `--json` document.
    ///
    /// Everything is its own `Display` except a conflict, whose `Display`
    /// inlines both whole texts — [`ErrorOut::detail`] carries those, so the
    /// message stays a sentence.
    pub fn message(&self) -> String {
        match self.conflict() {
            Some(StoreError::Conflict { id, file, .. }) if id.is_empty() => {
                format!("conflict in {file} — the file changed under us")
            }
            Some(StoreError::Conflict { id, file, .. }) => format!(
                "conflict in {file}: {} — the file changed under us",
                id.token()
            ),
            _ => self.to_string(),
        }
    }

    /// The `--json` failure document (§13): the same failure a script can
    /// read instead of the human line.
    pub fn document(&self) -> ErrorOut {
        let mut detail = Map::new();
        let kind = self.describe(&mut detail);
        ErrorOut {
            ok: false,
            kind,
            message: self.message(),
            exit_code: self.exit_code(),
            detail,
        }
    }

    /// The kind slug, filling `d` with whatever structured detail this error
    /// already carries. One place, so every verb gets both for free.
    fn describe(&self, d: &mut Map<String, Value>) -> &'static str {
        use tm_core::check::CheckError;
        use tm_core::grammar::EditError;
        use tm_core::horizon::HorizonError;
        use tm_core::ics::IcsError;
        use tm_core::model::ModelError;

        let put = |d: &mut Map<String, Value>, k: &str, v: &str| {
            d.insert(k.to_string(), Value::String(v.to_string()));
        };
        match self {
            CliError::Msg(_) => "error",
            CliError::Usage(_) => "usage",
            CliError::NotFound(id) => {
                put(d, "id", &id.token());
                "not-found"
            }
            CliError::Store(e) => store_kind(e, d),
            // README gap 887: the same `conflict` kind and the same detail as
            // any other write race, plus the one thing only `tm undo` knows.
            CliError::UndoBlocked { conflict, blame } => {
                let kind = store_kind(conflict, d);
                d.insert(
                    "laterWriter".to_string(),
                    serde_json::to_value(blame).unwrap_or(Value::Null),
                );
                kind
            }
            CliError::Horizon(HorizonError::Store(e)) => store_kind(e, d),
            CliError::Check(CheckError::Store(e)) => store_kind(e, d),
            CliError::Horizon(HorizonError::NotFound(id)) => {
                put(d, "id", &id.token());
                "not-found"
            }
            CliError::Horizon(HorizonError::MissingFile(path)) => {
                put(d, "path", path);
                "not-found"
            }
            CliError::Horizon(HorizonError::Edit { id, .. }) => {
                put(d, "id", &id.token());
                "edit"
            }
            CliError::Horizon(HorizonError::Horizon { id, horizon, .. }) => {
                put(d, "id", &id.token());
                put(d, "horizon", horizon);
                "horizon"
            }
            CliError::Horizon(HorizonError::Log(_)) => "json",
            // D16: the kernel refused to write the line. It is a log failure, not a JSON one —
            // nothing was encoded, because nothing was appended.
            CliError::Horizon(HorizonError::LogWrite(_)) => "log",
            CliError::Log(tm_core::log::LogError::Read { path, .. })
            | CliError::Log(tm_core::log::LogError::Write { path, .. }) => {
                put(d, "path", path);
                "log"
            }
            CliError::Log(tm_core::log::LogError::Json(_)) => "log",
            CliError::Ics(IcsError::Fetch { url, .. })
            | CliError::Ics(IcsError::Body { url, .. }) => {
                put(d, "url", url);
                "calendar"
            }
            CliError::Ics(_) => "calendar",
            CliError::Model(ModelError::Invalid { what, value }) => {
                put(d, "what", what);
                put(d, "value", value);
                "invalid"
            }
            CliError::Edit(EditError::Ambiguous { word }) => {
                put(d, "word", word);
                "edit"
            }
            CliError::Edit(EditError::FlagNeedsBoundary { flag }) => {
                put(d, "flag", flag);
                "edit"
            }
            CliError::Edit(_) => "edit",
            CliError::Energy(tm_core::energy::EnergyError::Io { path, .. })
            | CliError::Energy(tm_core::energy::EnergyError::Json { path, .. }) => {
                put(d, "path", path);
                "model"
            }
            CliError::Io { path, .. } => {
                put(d, "path", path);
                "io"
            }
            CliError::Json(_) => "json",
            CliError::Kernel(issue) => {
                for (k, v) in &issue.detail {
                    d.insert(k.clone(), v.clone());
                }
                // The refusal's name is the load-bearing datum: guaranteed
                // present even if a mapper forgot to put it in the detail.
                d.entry("refusal".to_string())
                    .or_insert_with(|| Value::String(issue.name.clone()));
                "kernel"
            }
        }
    }

    /// Print the error on stderr: one JSON object with `--json` (§13), else
    /// the human text — a conflict prints both versions of the line so the
    /// two writers can be reconciled (§1.3, §17.2).
    ///
    /// **A refusal §6.3's automatic close already printed is not printed twice**
    /// (W-12, README gap 239). `closing::auto_close` runs ahead of the verb and
    /// prints the kernel's refusal by name when the tree cannot be closed; a tree
    /// the kernel will not close is usually a tree it will not load either, so
    /// the verb then failed with the identical sentence and every command on a
    /// broken tree printed the same paragraph twice. The error line stays — a
    /// failing command must still say it failed — it just stops repeating what
    /// stands two lines above it. JSON output is untouched: a machine reader gets
    /// the whole object either way.
    pub fn report(&self, json: bool) {
        if json {
            self.document().report();
            return;
        }
        let message = self.message();
        if matches!(self, CliError::Kernel(i) if !i.is_fault()) && already_said_by_the_automatic_close(&message) {
            eprintln!(
                "tm: the automatic close's refusal above is this command's too, so nothing was \
                 written"
            );
            return;
        }
        eprintln!("tm: {message}");
        // **What the refusal means for the command that was just typed** (the
        // owner's D35, README gap 584). `kernel_bridge::gate` stamps
        // `refusedWrite` with the verb's own name; the kernel's sentence above
        // says what is wrong and names the file and the line, and this says
        // that the write did not happen and what to do about it. Only the
        // write gate sets it, so no existing message moves.
        if let CliError::Kernel(issue) = self {
            if let Some(Value::String(verb)) = issue.detail.get("refusedWrite") {
                eprintln!(
                    "  nothing was written: `tm {verb}` needs a tree the kernel can load whole, \
                     and every reading verb refuses this one too — fix the line named above, or \
                     run `tm undo`"
                );
            }
        }
        // A kernel fault is a bug report, not a plan problem: print whatever
        // layer 2 captured off the kernel's stderr (the backtrace the
        // terminal never saw), and say where to send it.
        if let CliError::Kernel(issue) = self {
            if issue.is_fault() {
                eprintln!("  please report this — nothing was written to the plan");
                if let Some(Value::String(s)) = issue.detail.get("stderr") {
                    if !s.trim().is_empty() {
                        eprintln!("  --- captured kernel stderr ---");
                        for l in s.lines() {
                            eprintln!("  {l}");
                        }
                        eprintln!("  ------------------------------");
                    }
                }
            }
        }
        if let Some(StoreError::Conflict {
            id,
            file,
            ours,
            theirs,
        }) = self.conflict()
        {
            // An id conflict is one line each; a whole-file conflict (an
            // empty id) would be two whole files, so that one is summarised —
            // the error itself still carries both texts for the TUI's diff.
            //
            // **The summary names the first line that differs** (W-14 repair,
            // README gap 395). It used to be two line counts and
            // "reconcile <file> in your editor, then try again", which on the
            // commonest whole-file conflict — `tm plan` regenerating the day
            // file's `<!-- tm:plan start HH:MM -->` block under a later minute
            // — printed `ours: 22 lines / theirs: 22 lines`: a message whose
            // only evidence says the two sides are the same, naming nothing to
            // reconcile. The advice could not be followed either, because what
            // `tm undo` requires is not a line count but the exact bytes the
            // undone command wrote. Both are fixed here; the two whole texts
            // stay where they were, in the `--json` document.
            if id.is_empty() {
                eprintln!(
                    "  ours:   {} lines — what the undone command wrote",
                    ours.lines().count()
                );
                eprintln!(
                    "  theirs: {} lines — what {file} holds now",
                    theirs.lines().count()
                );
                match first_difference(ours, theirs) {
                    Some(d) => {
                        eprintln!("  first difference, line {}:", d.line);
                        eprintln!("    ours:   {}", d.ours);
                        eprintln!("    theirs: {}", d.theirs);
                    }
                    // `lines()` drops line endings, so two texts that differ
                    // only in a trailing newline or in CRLF reach here. Through
                    // `undo` the strings provably differ, so saying *where* is
                    // still the whole job — and a silent branch would be this
                    // gap again.
                    None => eprintln!(
                        "  every line agrees — they differ only in a line ending or a trailing \
                         newline"
                    ),
                }
                // **Who wrote it afterwards** (README gap 887). Only the undo
                // path can say, and only the half the log can answer for: it
                // names the close, which is the writer the undo stack
                // structurally cannot hold (gap 731).
                if let CliError::UndoBlocked { blame, .. } = self {
                    blame.report();
                }
                eprintln!(
                    "  undo needs {file} to hold exactly what the undone command wrote, byte for \
                     byte"
                );
                eprintln!("  `tm --json undo` prints both texts whole, as detail.ours and detail.theirs");
            } else {
                eprintln!("  ours:   {}", ours.trim_end());
                eprintln!("  theirs: {}", theirs.trim_end());
            }
        }
    }
}

/// The first line at which two whole-file texts differ (W-14 repair, gap 395).
///
/// A conflict the user can act on has to name something; a line count does not,
/// and two equal line counts actively mislead. Lines are compared in order and
/// the end of the shorter text is reported as `(end of file)`, so a pure
/// truncation is named as precisely as a rewrite.
pub struct FirstDifference {
    /// 1-indexed line number.
    pub line: usize,
    /// The line the undone command wrote there, or `(end of file)`.
    pub ours: String,
    /// The line the file holds there now, or `(end of file)`.
    pub theirs: String,
}

/// `None` only when the two texts agree line by line — which `undo` cannot
/// produce, since it compares the strings themselves.
pub fn first_difference(ours: &str, theirs: &str) -> Option<FirstDifference> {
    const EOF: &str = "(end of file)";
    let mut o = ours.lines();
    let mut t = theirs.lines();
    let mut line = 0usize;
    loop {
        line += 1;
        match (o.next(), t.next()) {
            (None, None) => return None,
            (a, b) if a == b => continue,
            (a, b) => {
                return Some(FirstDifference {
                    line,
                    ours: a.unwrap_or(EOF).to_string(),
                    theirs: b.unwrap_or(EOF).to_string(),
                })
            }
        }
    }
}

thread_local! {
    /// The refusal `closing::auto_close` last printed on stderr in this process,
    /// if any (W-12, README gap 239).
    static AUTO_CLOSE_SAID: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Record the refusal §6.3's automatic close just printed, so [`CliError::report`]
/// does not print the same sentence again when the verb behind it fails the same way.
///
/// Called only from `closing::auto_close`, and only on the branch that actually
/// wrote to stderr — inside the TUI nothing is printed, so nothing is recorded and
/// nothing is suppressed.
pub fn the_automatic_close_said(message: &str) {
    AUTO_CLOSE_SAID.with(|c| *c.borrow_mut() = Some(message.to_string()));
}

/// Whether `message` is exactly the refusal the automatic close already printed.
///
/// What is recorded is the [`KernelIssue`]'s own `message`, not the line the close
/// printed around it, so the test is equality: a *different* refusal — the close
/// refused one way and the verb another — still prints in full.
fn already_said_by_the_automatic_close(message: &str) -> bool {
    AUTO_CLOSE_SAID.with(|c| c.borrow().as_deref() == Some(message))
}

/// The kind slug of a [`StoreError`], filling `d` with its detail. Shared by
/// the store errors the horizon and `check` wrap.
fn store_kind(e: &StoreError, d: &mut Map<String, Value>) -> &'static str {
    let mut put = |k: &str, v: String| {
        d.insert(k.to_string(), Value::String(v));
    };
    match e {
        StoreError::Io { path, .. } => {
            put("path", path.clone());
            "io"
        }
        StoreError::Parse { path, line, .. } => {
            put("path", path.clone());
            d.insert("line".to_string(), Value::from(*line));
            "parse"
        }
        StoreError::NotFound(id) => {
            put("id", id.token());
            "not-found"
        }
        StoreError::Conflict {
            id,
            file,
            ours,
            theirs,
        } => {
            if !id.is_empty() {
                put("id", id.token());
            }
            put("file", file.clone());
            put("ours", ours.clone());
            put("theirs", theirs.clone());
            "conflict"
        }
        StoreError::Json { path, .. } => {
            put("path", path.clone());
            "json"
        }
        StoreError::Toml(_) => "config",
    }
}

/// The `--json` failure document (§13: "every verb accepts `--json`") — one
/// object on stderr, printed instead of the human line when a verb fails.
///
/// The shape is fixed for every verb and every failure, so a script tests
/// `ok`, branches on `kind`, shows `message`, and reads whatever `detail`
/// the failure happens to carry.
#[derive(Debug, Serialize)]
pub struct ErrorOut {
    /// Always `false`: what tells a failure document from a verb's result.
    pub ok: bool,
    /// A stable slug for what went wrong: `not-found`, `conflict`,
    /// `invalid`, `usage`, `parse`, `edit`, `horizon`, `io`, `json`,
    /// `config`, `log`, `calendar`, `model`, `kernel` (a named Lean-kernel
    /// refusal; `detail.refusal` carries the name), or `error` for anything
    /// else.
    pub kind: &'static str,
    /// The same sentence the human path prints after `tm: `.
    pub message: String,
    /// The process exit code that follows (§13: `1`, or `3` for a conflict).
    pub exit_code: i32,
    /// Whatever the failure itself carries — the `id` of a missing item, a
    /// conflict's `file`/`ours`/`theirs`, an I/O failure's `path` — and `{}`
    /// when it carries nothing.
    pub detail: Map<String, Value>,
}

impl ErrorOut {
    /// Print the document on stderr, one JSON object.
    pub fn report(&self) {
        match serde_json::to_string_pretty(self) {
            Ok(text) => eprintln!("{text}"),
            // Unreachable in practice (the document is strings and numbers),
            // but a failure to report must still say something.
            Err(e) => eprintln!("tm: {e}"),
        }
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

/// `HH:MM` — **re-exported, not declared** (AGENTS §5.3, W-23).  This file held a
/// byte-for-byte copy of `tm_core::model::fmt_time`; eight functions in this
/// repository rendered `HH:MM` and this was one of them.
pub use tm_core::model::fmt_time;

#[cfg(test)]
mod tests {
    use super::*;

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

    /// W-14 repair, gap 395. The whole-file conflict's summary used to be two
    /// line counts, and the commonest one in practice — `tm plan` rewriting the
    /// day file's generated block under a later minute — has the SAME count on
    /// both sides, so the message said "the file changed under us" and then
    /// printed its only evidence that it had not. What it must do instead is
    /// name a line.
    #[test]
    fn a_whole_file_conflict_names_the_first_line_that_differs() {
        let ours = "---\ndate: 2026-09-17\n<!-- tm:plan start 14:38 -->\nrest 1h\n";
        let theirs = "---\ndate: 2026-09-17\n<!-- tm:plan start 08:25 -->\nrest 1h\n";
        assert_eq!(ours.lines().count(), theirs.lines().count(), "the counts agree, so a \
             summary made of counts proves nothing — which is the defect");
        let d = first_difference(ours, theirs).expect("the two texts differ");
        assert_eq!(d.line, 3);
        assert_eq!(d.ours, "<!-- tm:plan start 14:38 -->");
        assert_eq!(d.theirs, "<!-- tm:plan start 08:25 -->");
    }

    /// A pure truncation is named as precisely as a rewrite: the end of the
    /// shorter text is a side of the difference, not a reason to say nothing.
    #[test]
    fn a_truncation_is_named_at_the_end_of_the_shorter_text() {
        let d = first_difference("a\nb\nc\n", "a\nb\n").expect("the two texts differ");
        assert_eq!((d.line, d.ours.as_str(), d.theirs.as_str()), (3, "c", "(end of file)"));
        let d = first_difference("a\nb\n", "a\nb\nc\n").expect("the two texts differ");
        assert_eq!((d.line, d.ours.as_str(), d.theirs.as_str()), (3, "(end of file)", "c"));
    }

    /// The one case with no line to name — two texts `lines()` cannot tell
    /// apart, which is a trailing newline or a CRLF. Kept honest rather than
    /// silent: the printed branch says which it is.
    #[test]
    fn texts_that_agree_line_by_line_have_no_first_difference() {
        assert!(first_difference("a\nb\n", "a\nb\n").is_none());
        assert!(first_difference("a\nb\n", "a\nb").is_none(), "a trailing newline is invisible \
             to `lines()`, which is why that branch names the line ending instead of a line");
        assert!(first_difference("a\r\nb\n", "a\nb\n").is_none());
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

    /// §13's `--json` on the failure path: a conflict is the one error whose
    /// human line is a summary, so the document has to carry the two texts
    /// the summary drops — the same pair the TUI diffs (§1.3, §17.2).
    #[test]
    fn a_conflict_document_carries_both_texts() {
        let doc = CliError::from(conflict()).document();
        assert!(!doc.ok);
        assert_eq!(doc.kind, "conflict");
        assert_eq!(doc.exit_code, EXIT_CONFLICT);
        assert_eq!(
            doc.message,
            "conflict in week/2026-W37.md: ^t3 — the file changed under us"
        );
        assert_eq!(doc.detail["id"], "^t3");
        assert_eq!(doc.detail["file"], "week/2026-W37.md");
        assert_eq!(doc.detail["ours"], "- [x] 4 2b Exercises 5.3–5.5 @m1 ^t3");
        assert_eq!(
            doc.detail["theirs"],
            "- [>] 4 2b Exercises 5.3–5.5 @m1 est:1b ^t3"
        );
    }

    /// A wrapped conflict is the same document, not a different one: the
    /// mapping lives in one place, so `tm move` and `tm check` report a race
    /// exactly as `tm drop` does.
    #[test]
    fn a_wrapped_conflict_is_the_same_document() {
        let plain = CliError::from(conflict()).document();
        for wrapped in [
            CliError::from(tm_core::horizon::HorizonError::Store(conflict())),
            CliError::from(tm_core::check::CheckError::Store(conflict())),
        ] {
            let doc = wrapped.document();
            assert_eq!(doc.kind, plain.kind);
            assert_eq!(doc.message, plain.message);
            assert_eq!(doc.detail, plain.detail);
        }
    }

    #[test]
    fn a_missing_id_document_carries_the_id() {
        let doc = CliError::NotFound(Id::new("nope")).document();
        assert_eq!(doc.kind, "not-found");
        assert_eq!(doc.message, "no such item: ^nope");
        assert_eq!(doc.exit_code, EXIT_ERROR);
        assert_eq!(doc.detail["id"], "^nope");
    }

    /// An error that carries nothing structured still has the four fields
    /// every document has, with an empty `detail` — a caller never has to
    /// test whether the key is there.
    #[test]
    fn a_plain_message_is_still_a_document() {
        let doc = CliError::msg("nothing to undo").document();
        assert_eq!(doc.kind, "error");
        assert_eq!(doc.message, "nothing to undo");
        assert_eq!(doc.exit_code, EXIT_ERROR);
        assert!(doc.detail.is_empty());
        let text = serde_json::to_string(&doc).expect("serialize");
        assert!(text.contains(r#""ok":false"#), "{text}");
        assert!(text.contains(r#""detail":{}"#), "{text}");
    }

    #[test]
    fn durations_read_the_way_the_spec_writes_them() {
        assert_eq!(fmt_dur(20), "20m");
        assert_eq!(fmt_dur(60), "1h");
        assert_eq!(fmt_dur(90), "1h30m");
    }
}
