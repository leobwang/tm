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
//! `itemCheck` — re-derived from `Boundary.lean`'s one `ok` and eight `err`
//! shapes, not guessed. A refusal writes nothing.

use serde_json::{json, Map, Value};

use tm_core::model::Horizon;
use tm_core::store::{self, FileGuard, Store};

use super::ctx::Ctx;
use super::out::{CliError, KernelIssue};

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
}

impl Cmd {
    /// The destination path the command relocates into, if any.
    fn dest(&self) -> Option<&str> {
        match self {
            Cmd::Move { to, .. } | Cmd::Demote { to, .. } | Cmd::Readopt { to, .. } => Some(to),
            Cmd::Drop { .. } | Cmd::Est { .. } => None,
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
        })
        .collect();
    let request = json!({ "docs": docs_json, "cmds": cmds_json }).to_string();

    // 3. One call.
    let raw = tm_kernel_ffi::call(&request).map_err(|f| {
        CliError::Kernel(fault_issue(&format!("{f:?}")))
    })?;
    let resp: Value = serde_json::from_str(&raw)
        .map_err(|e| CliError::Kernel(fault_issue(&format!("unparseable response ({e})"))))?;
    if let Some(err) = resp.get("err") {
        return Err(CliError::Kernel(refusal(err)));
    }
    let out_docs = resp["ok"]["docs"]
        .as_array()
        .ok_or_else(|| CliError::Kernel(fault_issue("response carries neither ok nor err")))?;
    if out_docs.len() != paths.len() {
        return Err(CliError::Kernel(fault_issue(&format!(
            "response has {} documents for a {}-document request",
            out_docs.len(),
            paths.len()
        ))));
    }

    // 4. Read the documents back; the response's grain/ix are carried, and
    // an echo that dropped or moved a region is refused loudly (the trap).
    let mut docs: Vec<BridgeDoc> = Vec::new();
    for (i, od) in out_docs.iter().enumerate() {
        let path = od["path"].as_str().unwrap_or_default().to_string();
        if path != paths[i] {
            return Err(CliError::Kernel(fault_issue(&format!(
                "response document {i} is {path:?}, request sent {:?}",
                paths[i]
            ))));
        }
        let lines = od["lines"]
            .as_array()
            .ok_or_else(|| CliError::Kernel(fault_issue(&format!("{path}: no lines array"))))?;
        let mut returned = String::new();
        for (j, l) in lines.iter().enumerate() {
            if j > 0 {
                returned.push('\n');
            }
            returned.push_str(l.as_str().ok_or_else(|| {
                CliError::Kernel(fault_issue(&format!("{path}: line {j} is not a string")))
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
            return Err(CliError::Kernel(fault_issue(&format!(
                "{}: the response dropped or moved the document's grain/ix \
                 (declared {:?}, returned {:?}) — refusing to write from it",
                doc.path,
                region_of(&doc.path),
                doc.region
            ))));
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
/// wrong answer — and nothing has been written when it is raised.
fn fault_issue(what: &str) -> KernelIssue {
    let mut detail = Map::new();
    detail.insert("refusal".into(), Value::String("kernelFault".into()));
    detail.insert("what".into(), Value::String(what.to_string()));
    KernelIssue {
        name: "kernelFault".into(),
        message: format!("kernel fault: {what} — nothing was written"),
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
        // jsonErr: bad JSON, bad doc, unknown op — a host-side bug by the
        // time it appears here, since this module builds every request.
        put("error", s.to_string());
        ("request".into(), format!("the kernel refused the request: {s}"))
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
        ] {
            let issue = refusal(&payload);
            assert_eq!(issue.name, name);
            assert!(issue.message.contains(name), "{}", issue.message);
            assert_eq!(issue.detail["refusal"], name);
        }
    }
}
