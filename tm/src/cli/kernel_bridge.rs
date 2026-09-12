//! The single choke point between the CLI and the Lean kernel (stage 3).
//!
//! Every kernel-backed verb — `move`, `drop`, `edit est=`, `demote`,
//! `readopt` — goes through [`apply`], and nothing else talks to
//! `tm-kernel-ffi`: one place builds the request, one place reads the
//! response, one place writes files, so the wire format cannot fork.
//!
//! The shape, end to end:
//!
//! 1. **Read the whole plan tree** through the store, each file with its
//!    §1.3 guard ([`FsStore::read_guarded`]): the kernel's `planWf` is a
//!    whole-plan check, and the duplicate-id refusal (`occupied`) is only as
//!    strong as the set of files the kernel can see.
//! 2. **Resolve horizon names to paths and generate each document's
//!    `grain`/`ix` here, in the host** — gap 10's recorded stance: the wire
//!    takes a document *index* plus a declared region, and the kernel
//!    believes the region it is given. [`region_of`] computes the real
//!    numbers from the kernel's own calendar (day 0 = 0001-01-01, a Monday;
//!    week ordinal = day/7; month ordinal = 12·(year−1)+month−1).
//! 3. **One kernel call** (`tm_kernel_ffi::call`), the request as
//!    `{"docs":[{path,grain,ix,lines}],"cmds":[…]}`.
//! 4. **Carry each document's `grain`/`ix` back.** The response repeats the
//!    region because a next request built from a response that dropped them
//!    would be unloadable (`ambiguousDemotion`) — the named stage-3 trap
//!    (AGENTS §8.1). [`apply`] verifies the echo and stores it on every
//!    [`BridgeDoc`]; dropping it is a hard error here, not a silent lapse.
//! 5. **Write only the changed documents back**, atomically, through the
//!    same store the old path used, with the read-time guard still enforced
//!    ([`FsStore::write_guarded`]): a racing writer between our read and our
//!    write is §1.3's conflict, exit code 3, nothing clobbered.
//!
//! Every kernel refusal reaches the caller **by name** ([`refusal`]):
//! `occupied`, `noSuchId`, `notDemoted`, `alreadyDemoted`, `badHorizon`,
//! `badItem`, `tabbedLine`, `keyAbsent`, `siteOutOfRange`, `dupId`,
//! `notADemotion`, `ambiguousDemotion`, `duplicatePath`, `badLine`,
//! `itemCheck`, plus `parseCmd`'s parse-tier names riding the free-text
//! `err` (`badValue <k>`, `keyNotWired <k>`, `unknownKey <k>`, and `add`'s
//! five `title…` refusals) — re-derived from `Boundary.lean`'s one `ok` and
//! eight `err` shapes, not guessed. A refusal writes nothing.

use std::sync::atomic::{AtomicBool, Ordering};

use serde_json::{json, Map, Value};

use tm_core::model::Horizon;
use tm_core::store::{self, FileGuard, Store};

use super::ctx::Ctx;
use super::out::{CliError, KernelIssue};

// ---------------------------------------------------------------------------
// Panic layer 2: Lean's stderr, captured (AGENTS 8.1 scope item 6)
// ---------------------------------------------------------------------------

/// Whether kernel calls run with fd 2 redirected to a pipe. The TUI turns
/// this on for its whole run: layer 1 is totality (CI-enforced) and layer 3
/// is `lean_set_exit_on_panic(false)` + `KernelFault` in the ffi crate, but
/// neither stops a runtime backtrace *printed to stderr* from shredding the
/// ratatui alternate screen — layer 2 does. Whatever is captured rides the
/// fault's detail instead of the terminal.
static CAPTURE_STDERR: AtomicBool = AtomicBool::new(false);

/// Turn layer-2 stderr capture on or off for every subsequent kernel call
/// in this process. The TUI owns this switch.
pub fn capture_kernel_stderr(on: bool) {
    CAPTURE_STDERR.store(on, Ordering::SeqCst);
}

/// One capture window: fd 2 `dup2`'d to a pipe, a thread draining the read
/// end (so a large backtrace cannot fill the pipe and block the writer),
/// the original fd restored on [`StderrCapture::finish`].
///
/// The libc calls are declared here rather than through the `libc` crate —
/// R7: no new external dependency, and the symbols are in the C library
/// every Unix binary already links.
#[cfg(unix)]
struct StderrCapture {
    saved: i32,
    reader: std::thread::JoinHandle<Vec<u8>>,
}

#[cfg(unix)]
extern "C" {
    fn pipe(fds: *mut i32) -> i32;
    fn dup(fd: i32) -> i32;
    fn dup2(oldfd: i32, newfd: i32) -> i32;
    fn close(fd: i32) -> i32;
}

#[cfg(unix)]
impl StderrCapture {
    /// Start capturing fd 2, when the TUI asked for it. `None` when capture
    /// is off or any step fails — a failed capture must never fail the
    /// verb, it only loses the cosmetic protection.
    fn start() -> Option<StderrCapture> {
        if !CAPTURE_STDERR.load(Ordering::SeqCst) {
            return None;
        }
        let (read_fd, saved) = unsafe {
            let mut fds = [0i32; 2];
            if pipe(fds.as_mut_ptr()) != 0 {
                return None;
            }
            let saved = dup(2);
            if saved < 0 || dup2(fds[1], 2) < 0 {
                if saved >= 0 {
                    close(saved);
                }
                close(fds[0]);
                close(fds[1]);
                return None;
            }
            close(fds[1]);
            (fds[0], saved)
        };
        let reader = std::thread::spawn(move || {
            use std::io::Read;
            use std::os::unix::io::FromRawFd;
            let mut f = unsafe { std::fs::File::from_raw_fd(read_fd) };
            let mut buf = Vec::new();
            let _ = f.read_to_end(&mut buf);
            buf
        });
        Some(StderrCapture { saved, reader })
    }

    /// Put fd 2 back and return whatever was written while it was ours.
    fn finish(self) -> String {
        unsafe {
            dup2(self.saved, 2);
            close(self.saved);
        }
        // fd 2 no longer points at the pipe and the write end is closed, so
        // the drain thread sees EOF.
        let bytes = self.reader.join().unwrap_or_default();
        String::from_utf8_lossy(&bytes).into_owned()
    }
}

#[cfg(not(unix))]
struct StderrCapture;

#[cfg(not(unix))]
impl StderrCapture {
    fn start() -> Option<StderrCapture> {
        None
    }
    fn finish(self) -> String {
        String::new()
    }
}

/// One kernel-backed command, already resolved by the verb: ids are bare
/// (no `^`), destinations are plan-relative file paths.
#[derive(Clone, Debug)]
pub enum Cmd {
    /// `{"op":"move","id":…,"doc":…}`.
    Move { id: String, to: String },
    /// `{"op":"drop","id":…}`.
    Drop { id: String },
    /// `{"op":"est","id":…,"min":…}` — the `tm edit est=` op.
    Est { id: String, min: u32 },
    /// `{"op":"demote","id":…,"doc":…,"period":…}` (week stamp).
    Demote { id: String, to: String, period: u32 },
    /// `{"op":"readopt","id":…,"doc":…}`.
    Readopt { id: String, to: String },
    /// `{"op":"rank","id":…,"rank":…}` — the raw kernel rank: a document's
    /// line index. The kernel refuses a taken rank (`badHorizon`), so the
    /// caller ([`crate::cli::items::rank`]) rotates lines through the one
    /// always-free rank past the end of the file.
    Rank { id: String, rank: u64 },
    /// `{"op":"add","seed":…,"doc":…,"title":…}` — the host supplies the
    /// seed (Lean has no randomness); `freshId` (L21) makes freshness a
    /// theorem, and the id comes back on the rendered line.
    Add { seed: u64, to: String, title: String },
    /// `{"op":"edit","id":…,"key":…,"value":…}` — the keyed edit for the
    /// nine wired keys. An **empty** `value` is the unset form
    /// (`tm edit ^id <key>=`). The value rides raw: the kernel parses it
    /// with the key's own field grammar and refuses `badValue <k>` by name.
    EditKey { id: String, key: String, value: String },
}

impl Cmd {
    /// The destination path the command relocates into (or adds into), if
    /// any.
    fn dest(&self) -> Option<&str> {
        match self {
            Cmd::Move { to, .. }
            | Cmd::Demote { to, .. }
            | Cmd::Readopt { to, .. }
            | Cmd::Add { to, .. } => Some(to),
            Cmd::Drop { .. } | Cmd::Est { .. } | Cmd::Rank { .. } | Cmd::EditKey { .. } => None,
        }
    }
}

/// One plan document as it went through the kernel.
#[derive(Debug)]
pub struct BridgeDoc {
    /// Plan-relative path.
    pub path: String,
    /// The text sent (for a file the tree did not hold yet: its horizon's
    /// initial text).
    pub sent: String,
    /// The text the kernel returned.
    pub returned: String,
    /// The document's region as the **response** carried it back — kept, not
    /// dropped (the stage-3 trap by name).
    pub region: Option<(u64, u64)>,
    /// Whether `returned` differs from `sent` (and was therefore written).
    pub changed: bool,
}

/// What one kernel call did to the tree.
#[derive(Debug)]
pub struct Applied {
    /// Every document, in request order.
    pub docs: Vec<BridgeDoc>,
}

impl Applied {
    /// The document at `path`.
    pub fn doc(&self, path: &str) -> Option<&BridgeDoc> {
        self.docs.iter().find(|d| d.path == path)
    }

    /// The line carrying `^id` in `path`'s returned text, verbatim.
    pub fn line_in(&self, path: &str, id: &str) -> Option<String> {
        let doc = self.doc(path)?;
        doc.returned
            .lines()
            .find(|l| has_id_token(l, id))
            .map(|l| l.to_string())
    }

    /// The line carrying `^id`, verbatim, searched in changed documents
    /// first.
    pub fn line_of(&self, id: &str) -> Option<(String, String)> {
        let scan = |changed: bool| {
            self.docs.iter().filter(move |d| d.changed == changed).find_map(|d| {
                d.returned
                    .lines()
                    .find(|l| has_id_token(l, id))
                    .map(|l| (d.path.clone(), l.to_string()))
            })
        };
        scan(true).or_else(|| scan(false))
    }

    /// The changed document (other than `skip`) whose text no longer carries
    /// `^id` — for `move`/`readopt`, the file the item left.
    pub fn lost_id(&self, id: &str, skip: &str) -> Option<String> {
        self.docs
            .iter()
            .filter(|d| d.changed && d.path != skip)
            .find(|d| {
                d.sent.lines().any(|l| has_id_token(l, id))
                    && !d.returned.lines().any(|l| has_id_token(l, id))
            })
            .map(|d| d.path.clone())
    }
}

/// True when `line` carries the token `^id` as a whole word.
pub fn has_id_token(line: &str, id: &str) -> bool {
    line.split_whitespace().any(|w| w.strip_prefix('^') == Some(id))
}

/// Days since 0001-01-01 — the kernel's `Day` (`Cal.toDay`; day 0 is a
/// Monday). `chrono`'s `num_days_from_ce` counts from the same origin, one
/// off (0001-01-01 = 1 there).
fn kernel_day(d: chrono::NaiveDate) -> u64 {
    use chrono::Datelike;
    (d.num_days_from_ce() as i64 - 1).max(0) as u64
}

/// The region a plan path declares, in the kernel's own numbers — the host's
/// half of gap 10: `week/2026-W37.md` really is `(grain 1, ix 105695)` here,
/// not a placeholder. Files without a horizon grain (backlog, inbox,
/// routines, optional, calendar) declare none; `none` is the backlog
/// horizon, after every bounded region.
pub fn region_of(path: &str) -> Option<(u64, u64)> {
    match Horizon::from_path(path)? {
        Horizon::Day(d) => Some((0, kernel_day(d))),
        Horizon::Week(w) => Some((1, kernel_day(w.monday()) / 7)),
        Horizon::Month(m) => {
            let (y, mo) = (m.year as u64, m.month as u64);
            Some((2, 12 * (y - 1) + (mo - 1)))
        }
        _ => None,
    }
}

/// Apply `cmds` to the plan tree through the kernel: read every plan file,
/// call the kernel once, write the changed files back. See the module
/// docs for the contract; on any kernel refusal ([`CliError::Kernel`],
/// named) nothing has been written.
pub fn apply(ctx: &Ctx, cmds: &[Cmd]) -> Result<Applied, CliError> {
    // 1. The whole tree, guarded.
    let mut paths = ctx.store.list_files()?;
    let mut texts: Vec<String> = Vec::new();
    let mut guards: Vec<FileGuard> = Vec::new();
    for rel in &paths {
        let (text, guard) = ctx.store.read_guarded(rel)?;
        texts.push(text);
        guards.push(guard);
    }
    // A destination the tree does not hold yet enters the request as its
    // horizon's initial text, and is created on write only if the kernel
    // put something there (its guard demands the file still be absent).
    for cmd in cmds {
        if let Some(dest) = cmd.dest() {
            if !paths.iter().any(|p| p == dest) {
                let initial = Horizon::from_path(dest)
                    .map(|h| store::initial_text(&h))
                    .unwrap_or_default();
                paths.push(dest.to_string());
                texts.push(initial);
                guards.push(FileGuard::absent());
            }
        }
    }

    // 2. The request: regions are generated here (gap 10), lines split the
    // way the kernel joins them (`Tm.splitOn '\n'` — the recorded host
    // agreement).
    let mut docs_json = Vec::new();
    for (rel, text) in paths.iter().zip(&texts) {
        let lines: Vec<&str> = text.split('\n').collect();
        let mut doc = json!({ "path": rel, "lines": lines });
        if let Some((g, ix)) = region_of(rel) {
            doc["grain"] = json!(g);
            doc["ix"] = json!(ix);
        }
        docs_json.push(doc);
    }
    let doc_ix = |dest: &str| -> u64 {
        paths.iter().position(|p| p == dest).expect("dest was added above") as u64
    };
    let cmds_json: Vec<Value> = cmds
        .iter()
        .map(|c| match c {
            Cmd::Move { id, to } => json!({"op":"move","id":id,"doc":doc_ix(to)}),
            Cmd::Drop { id } => json!({"op":"drop","id":id}),
            Cmd::Est { id, min } => json!({"op":"est","id":id,"min":min}),
            Cmd::Demote { id, to, period } => {
                json!({"op":"demote","id":id,"doc":doc_ix(to),"period":period})
            }
            Cmd::Readopt { id, to } => json!({"op":"readopt","id":id,"doc":doc_ix(to)}),
            Cmd::Rank { id, rank } => json!({"op":"rank","id":id,"rank":rank}),
            Cmd::Add { seed, to, title } => {
                json!({"op":"add","seed":seed,"doc":doc_ix(to),"title":title})
            }
            Cmd::EditKey { id, key, value } => {
                json!({"op":"edit","id":id,"key":key,"value":value})
            }
        })
        .collect();
    let request = json!({ "docs": docs_json, "cmds": cmds_json }).to_string();

    // 3. One call — with Lean's stderr captured while it runs when the TUI
    // asked for it (panic layer 2), so a backtrace lands in the fault's
    // detail, never on the alternate screen.
    let capture = StderrCapture::start();
    let called = tm_kernel_ffi::call(&request);
    let stderr = capture.map(StderrCapture::finish).unwrap_or_default();
    // The constructed panic probe (AGENTS 8.1's named trap: the kernel is
    // total by CI, so a reachable panic does not exist — the probe injects
    // the fault at the host's own seam, the response bytes, and the tests
    // assert the HOST's reaction: named fault, non-zero exit, nothing
    // written, terminal restored). The real call still runs first.
    let called = if std::env::var_os("TM_KERNEL_FAULT_PROBE").is_some() {
        called.map(|_| "*** panic probe: a deliberately non-JSON response (TM_KERNEL_FAULT_PROBE) ***".to_string())
    } else {
        called
    };
    let raw = called.map_err(|f| {
        CliError::Kernel(fault_issue(&format!("{f:?}"), &stderr))
    })?;
    let resp: Value = serde_json::from_str(&raw).map_err(|e| {
        CliError::Kernel(fault_issue(&format!("unparseable response ({e})"), &stderr))
    })?;
    if let Some(err) = resp.get("err") {
        return Err(CliError::Kernel(refusal(err)));
    }
    let out_docs = resp["ok"]["docs"]
        .as_array()
        .ok_or_else(|| CliError::Kernel(fault_issue("response carries neither ok nor err", &stderr)))?;
    if out_docs.len() != paths.len() {
        return Err(CliError::Kernel(fault_issue(
            &format!(
                "response has {} documents for a {}-document request",
                out_docs.len(),
                paths.len()
            ),
            &stderr,
        )));
    }

    // 4. Read the documents back; the response's grain/ix are carried, and
    // an echo that dropped or moved a region is refused loudly (the trap).
    let mut docs: Vec<BridgeDoc> = Vec::new();
    for (i, od) in out_docs.iter().enumerate() {
        let path = od["path"].as_str().unwrap_or_default().to_string();
        if path != paths[i] {
            return Err(CliError::Kernel(fault_issue(
                &format!("response document {i} is {path:?}, request sent {:?}", paths[i]),
                &stderr,
            )));
        }
        let lines = od["lines"]
            .as_array()
            .ok_or_else(|| {
                CliError::Kernel(fault_issue(&format!("{path}: no lines array"), &stderr))
            })?;
        let mut returned = String::new();
        for (j, l) in lines.iter().enumerate() {
            if j > 0 {
                returned.push('\n');
            }
            returned.push_str(l.as_str().ok_or_else(|| {
                CliError::Kernel(fault_issue(&format!("{path}: line {j} is not a string"), &stderr))
            })?);
        }
        let region = match (od.get("grain").and_then(Value::as_u64), od.get("ix").and_then(Value::as_u64)) {
            (Some(g), Some(ix)) => Some((g, ix)),
            _ => None,
        };
        let changed = returned != texts[i];
        docs.push(BridgeDoc {
            path,
            sent: texts[i].clone(),
            returned,
            region,
            changed,
        });
    }
    // The carried region is checked from the struct itself, so a refactor
    // that stopped carrying it would fail here before it failed a demotion.
    for doc in &docs {
        if doc.region != region_of(&doc.path) {
            return Err(CliError::Kernel(fault_issue(
                &format!(
                    "{}: the response dropped or moved the document's grain/ix \
                     (declared {:?}, returned {:?}) — refusing to write from it",
                    doc.path,
                    region_of(&doc.path),
                    doc.region
                ),
                &stderr,
            )));
        }
    }

    // 5. Write the changed documents through the guarded atomic store.
    for (doc, guard) in docs.iter().zip(&guards) {
        if doc.changed {
            ctx.store.write_guarded(&doc.path, guard, &doc.returned)?;
        }
    }
    Ok(Applied { docs })
}

/// An FFI-level fault (no usable response). Loud and recoverable, never a
/// wrong answer — and nothing has been written when it is raised. `stderr`
/// is whatever layer 2 captured off fd 2 during the call (empty outside the
/// TUI); it rides the detail so the bug report carries the backtrace the
/// terminal never saw.
fn fault_issue(what: &str, stderr: &str) -> KernelIssue {
    let mut detail = Map::new();
    detail.insert("refusal".into(), Value::String("kernelFault".into()));
    detail.insert("what".into(), Value::String(what.to_string()));
    if !stderr.is_empty() {
        detail.insert("stderr".into(), Value::String(stderr.to_string()));
    }
    KernelIssue {
        name: "kernelFault".into(),
        message: format!(
            "kernel fault: {what} — nothing was written; this is a bug in tm, not a plan problem"
        ),
        detail,
    }
}

/// Map the response's `err` payload to a named [`KernelIssue`]. The shapes
/// are `Boundary.lean`'s: a free-text string, `{"kernel":name}`, and the six
/// structured loader diagnostics.
fn refusal(err: &Value) -> KernelIssue {
    let mut detail = Map::new();
    let mut put = |k: &str, v: String| {
        detail.insert(k.to_string(), Value::String(v));
    };
    let (name, message): (String, String) = if let Some(s) = err.as_str() {
        // The free-text `err`. `parseCmd`'s named parse-tier refusals ride
        // it (Boundary.lean: `unknownKey`/`keyNotWired`/`badValue` for the
        // keyed edit, the five `title…` refusals for `add`), and since the
        // keyed edit forwards the user's raw value, these reach real users —
        // so they are mapped to their names, not swallowed as "request".
        if let Some(k) = s.strip_prefix("badValue ") {
            put("key", k.to_string());
            ("badValue".into(), format!(
                "kernel refusal: badValue — {k:?} refuses this value (the key's own field grammar, one reader end to end)"
            ))
        } else if let Some(k) = s.strip_prefix("keyNotWired ") {
            put("key", k.to_string());
            ("keyNotWired".into(), format!(
                "kernel refusal: keyNotWired — {k:?} is not on the kernel's edit path yet (kernel/README.md gap 40 names the deferred keys)"
            ))
        } else if let Some(k) = s.strip_prefix("unknownKey ") {
            put("key", k.to_string());
            ("unknownKey".into(), format!(
                "kernel refusal: unknownKey — {k:?} is not a §4.1 key"
            ))
        } else if s.starts_with("title") && !s.contains(' ') {
            let why = match s {
                "titleNewline" => "the title carries a newline, which would split the line",
                "titleTab" => "the title carries a tab, which this kernel cannot read as a separator (gap 32)",
                "titleId" => "the title carries a `^`, which would read back as a second id",
                "titleBlank" => "the title is empty or only spaces",
                "titleEdge" => "the title starts or ends with a space, which would not re-tokenize as written",
                _ => "an unlisted title refusal — see Boundary.lean's parseCmd",
            };
            (s.to_string(), format!("kernel refusal: {s} — {why}"))
        } else {
            // jsonErr: bad JSON, bad doc, unknown op — a host-side bug by
            // the time it appears here, since this module builds every
            // request.
            put("error", s.to_string());
            ("request".into(), format!("the kernel refused the request: {s}"))
        }
    } else if let Some(name) = err.get("kernel").and_then(Value::as_str) {
        let why = match name {
            "occupied" => "the destination file already holds a line with this id, so the move would write the id twice (the duplicate-id class, refused by name)",
            "noSuchId" => "no item in the plan carries this id",
            "notDemoted" => "the item is not demoted, so there is nothing to readopt (use `tm move`)",
            "alreadyDemoted" => "the item already has a standing archive record; demoting it again would overwrite that record",
            "badHorizon" => "the rewritten plan fails the kernel's whole-plan check — a destination that is not in the plan, a line landing in a section it may not occupy, or a rank collision",
            "badItem" => "the rewritten item fails the kernel's item check",
            "tabbedLine" => "the line carries a tab, which this kernel does not read as a separator; the edit is refused rather than written against the wrong token (gap 32)",
            "keyAbsent" => "the line does not carry that key",
            "siteOutOfRange" => "a placement points at a document the plan does not hold",
            _ => "an unlisted kernel refusal — see kernel/TmKernel/TmKernel/Boundary.lean",
        };
        (name.to_string(), format!("kernel refusal: {name} — {why}"))
    } else if let Some(id) = err.get("dupId").and_then(Value::as_str) {
        put("id", format!("^{id}"));
        ("dupId".into(), format!(
            "kernel refusal: dupId — two lines in the tree carry ^{id}; the kernel refuses a tree it cannot load whole (run `tm check`)"
        ))
    } else if let Some(id) = err.get("notADemotion").and_then(Value::as_str) {
        put("id", format!("^{id}"));
        ("notADemotion".into(), format!(
            "kernel refusal: notADemotion — the two lines of ^{id} are not a demotion pair the kernel can read"
        ))
    } else if let Some(id) = err.get("ambiguousDemotion").and_then(Value::as_str) {
        put("id", format!("^{id}"));
        ("ambiguousDemotion".into(), format!(
            "kernel refusal: ambiguousDemotion — the documents do not order the two lines of ^{id}, so which one is the record is ambiguous"
        ))
    } else if let Some(p) = err.get("duplicatePath").and_then(Value::as_str) {
        put("path", p.to_string());
        ("duplicatePath".into(), format!(
            "kernel refusal: duplicatePath — two request documents share the path {p}"
        ))
    } else if let Some(b) = err.get("badLine") {
        let path = b["path"].as_str().unwrap_or_default().to_string();
        let line = b["line"].as_u64().unwrap_or_default();
        let why = b["why"].as_str().unwrap_or_default().to_string();
        put("path", path.clone());
        put("why", why.clone());
        detail.insert("line".into(), Value::from(line));
        ("badLine".into(), format!(
            "kernel refusal: badLine — {path}:{line} looks like an item but does not parse ({why}); the kernel refuses a tree it cannot load whole"
        ))
    } else if let Some(f) = err.get("itemCheck").and_then(Value::as_str) {
        put("fault", f.to_string());
        ("itemCheck".into(), format!(
            "kernel refusal: itemCheck — the tree fails the kernel's item invariant ({f}); the kernel refuses a tree it cannot load whole"
        ))
    } else {
        put("error", err.to_string());
        ("unknown".into(), format!("kernel refusal (unrecognised shape): {err}"))
    };
    detail.insert("refusal".into(), Value::String(name.clone()));
    KernelIssue { name, message, detail }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Gap 10's numbers are the kernel's own, cross-checked against the
    /// values AGENTS §8.1 records: 2026-W37 is week ordinal 105695, and the
    /// week/month/day grains are 1/2/0.
    #[test]
    fn regions_are_the_kernels_numbers() {
        assert_eq!(region_of("week/2026-W37.md"), Some((1, 105695)));
        assert_eq!(region_of("month/2026-09.md"), Some((2, 12 * 2025 + 8)));
        assert_eq!(region_of("day/2026-09-07.md"), Some((0, 739865)));
        // Day 0 is 0001-01-01, and it is a Monday: the week ordinal of a
        // Monday is exact division.
        assert_eq!(739865 % 7, 0);
        assert_eq!(region_of("backlog.md"), None);
        assert_eq!(region_of("calendar/2026-W37.md"), None);
        assert_eq!(region_of("inbox.md"), None);
    }

    /// Panic layer 2's machinery, tested at the host level: while a capture
    /// window is open, bytes written to fd 2 land in the capture (not the
    /// terminal), and after `finish` the original stderr is back. Raw
    /// `Stderr::write_all` bypasses libtest's thread-local capture, so this
    /// really exercises the `dup2`.
    #[test]
    #[cfg(unix)]
    fn stderr_capture_takes_fd2_and_gives_it_back() {
        use std::io::Write;
        // Off by default: no window opens.
        assert!(StderrCapture::start().is_none());
        capture_kernel_stderr(true);
        let cap = StderrCapture::start().expect("capture window");
        std::io::stderr()
            .write_all(b"a lean backtrace would land here\n")
            .expect("write");
        let seen = cap.finish();
        capture_kernel_stderr(false);
        assert!(
            seen.contains("a lean backtrace would land here"),
            "{seen:?}"
        );
        // And the captured text rides the fault's detail for the bug report.
        let issue = fault_issue("probe", &seen);
        assert_eq!(issue.name, "kernelFault");
        assert!(issue.detail["stderr"]
            .as_str()
            .is_some_and(|s| s.contains("backtrace")));
        // fd 2 is restored: this write must not panic (and lands on the
        // real stderr, which libtest owns again).
        std::io::stderr().write_all(b"").expect("stderr is back");
    }

    #[test]
    fn a_fault_without_captured_stderr_has_no_stderr_key() {
        let issue = fault_issue("no response", "");
        assert_eq!(issue.name, "kernelFault");
        assert!(issue.is_fault());
        assert!(!issue.detail.contains_key("stderr"));
        assert!(issue.message.contains("nothing was written"), "{}", issue.message);
    }

    #[test]
    fn every_named_refusal_reaches_the_message_by_name() {
        for (payload, name) in [
            (serde_json::json!({"kernel":"occupied"}), "occupied"),
            (serde_json::json!({"kernel":"noSuchId"}), "noSuchId"),
            (serde_json::json!({"kernel":"notDemoted"}), "notDemoted"),
            (serde_json::json!({"kernel":"alreadyDemoted"}), "alreadyDemoted"),
            (serde_json::json!({"kernel":"badHorizon"}), "badHorizon"),
            (serde_json::json!({"kernel":"badItem"}), "badItem"),
            (serde_json::json!({"kernel":"tabbedLine"}), "tabbedLine"),
            (serde_json::json!({"kernel":"keyAbsent"}), "keyAbsent"),
            (serde_json::json!({"kernel":"siteOutOfRange"}), "siteOutOfRange"),
            (serde_json::json!({"dupId":"m1"}), "dupId"),
            (serde_json::json!({"notADemotion":"m1"}), "notADemotion"),
            (serde_json::json!({"ambiguousDemotion":"m1"}), "ambiguousDemotion"),
            (serde_json::json!({"duplicatePath":"a.md"}), "duplicatePath"),
            (
                serde_json::json!({"badLine":{"path":"a.md","line":3,"why":"noId"}}),
                "badLine",
            ),
            (serde_json::json!({"itemCheck":"depCycle"}), "itemCheck"),
            // The parse-tier free-text refusals the keyed edit and `add`
            // forward from real user input (Boundary.lean's parseCmd).
            (serde_json::json!("badValue ci"), "badValue"),
            (serde_json::json!("keyNotWired due"), "keyNotWired"),
            (serde_json::json!("unknownKey size"), "unknownKey"),
            (serde_json::json!("titleNewline"), "titleNewline"),
            (serde_json::json!("titleTab"), "titleTab"),
            (serde_json::json!("titleId"), "titleId"),
            (serde_json::json!("titleBlank"), "titleBlank"),
            (serde_json::json!("titleEdge"), "titleEdge"),
        ] {
            let issue = refusal(&payload);
            assert_eq!(issue.name, name);
            assert!(issue.message.contains(name), "{}", issue.message);
            assert_eq!(issue.detail["refusal"], name);
        }
    }
}
