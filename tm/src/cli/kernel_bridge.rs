//! The single choke point between the CLI and the Lean kernel (stage 3).
//!
//! Every kernel-backed verb — `move`, `drop`, `demote`, `readopt`, `rank`,
//! `add`, the keyed `edit`/unset (`est=` included), and since stage 4 step 6
//! `close` and the automatic close — goes through
//! [`apply`], and nothing else talks to `tm-kernel-ffi`: one place builds
//! the request, one place reads the response, one place writes files, so
//! the wire format cannot fork.
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
//! ## The newline convention (the file edge, gap 6's host half)
//!
//! The kernel works over a list of lines and never sees the final newline.
//! A newline-terminated file split naively on `'\n'` grows a trailing empty
//! segment, which the kernel would read as a ranked prose line — and its
//! append (`freshRank`) would land *after* it, writing `…^p1\n\n- [ ] … ^a1`
//! with no final newline (the 2026-09-12 drive-verification defect). So the
//! bridge normalizes at the edge, both ways:
//!
//! * **request build**: split on `'\n'`, then strip exactly one trailing
//!   empty segment iff the file ends with `'\n'` — the lines the kernel
//!   sees are the file's real lines, none phantom;
//! * **write-back**: a *rewritten* file is `lines.join("\n") + "\n"` —
//!   newline-terminated, exactly one `'\n'` between any two lines.
//!
//! The recorded convention for a source file that does **not** end in a
//! newline: it is read as-is (no strip — there is no trailing empty
//! segment), an *untouched* one is never written (stays byte-identical),
//! and a *rewritten* one comes back newline-terminated — the bridge
//! normalizes rewritten files to the POSIX text-file shape rather than
//! propagating a missing EOF newline. `changed` is therefore judged on the
//! kernel's line lists, not on reconstructed bytes, so the normalization
//! itself never counts as a change.
//!
//! (The corpus harness — `kernel/tm-kernel-ffi/tests/harness/mod.rs`,
//! check 6 — keeps the naive identity `split('\n')`/`join('\n')` including
//! the trailing empty segment. That is byte-faithful for its read-only,
//! no-commands round trip, but wrong for a host that lets the kernel
//! append; the two conventions agree on every file the kernel does not
//! change.)
//!
//! Every kernel refusal reaches the caller **by name** ([`refusal`]):
//! `occupied`, `noSuchId`, `notDemoted`, `alreadyDemoted`, `badHorizon`,
//! `badItem`, `keyAbsent`, `danglingDep`, `depCycle`,
//! `siteOutOfRange`, `noTarget`, `noSection`, `dupId`,
//! `notADemotion`, `ambiguousDemotion`, `duplicatePath`, `badLine`,
//! `unterminatedComment`, `itemCheck`, plus `parseCmd`'s parse-tier names riding the free-text
//! `err` (`badValue <k>`, `keyNotWired <k>`, `unknownKey <k>`, and `add`'s
//! five `title…` refusals) and the request clock's four (`nowAbsent`,
//! `badNow`, `blockMinAbsent`, `badBlockMin`) — re-derived from
//! `Boundary.lean`'s one `ok` and nine `err` shapes, not guessed. A refusal
//! writes nothing.
//!
//! Every `ok` carries `report` beside `docs` (stage 4 step 5, the owner's
//! D3): [`decode_report`] reads it through smart constructors on every call.
//! Only a request carrying a close ([`Cmd::Close`], [`Cmd::AutoClose`]) may
//! get a report that names lines — it comes back as [`Applied::closes`], the
//! one account of what the close did, which `tm close`, the automatic close
//! and the log all read (stage 4 step 6, [`super::closing`]); anywhere else a
//! non-empty report is a fault. A close request also carries the clock
//! (`now`, `blockMin`) and the three destinations a close needs — the week and
//! the month containing now, the month with §4.3's `# Outcomes`/`# Demoted`,
//! and `backlog.md` with `# Overdue` (the owner's D7) — because the kernel
//! cannot create a file or a section (gap 56).

use std::sync::atomic::{AtomicBool, Ordering};

use serde_json::{json, Map, Value};

use tm_core::model::{Horizon, IsoWeek, YearMonth};
use tm_core::grammar::IdGen;
use tm_core::store::{self, FileGuard, MemStore, Store};

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

/// Whether the TUI's capture is on — i.e. whether stderr belongs to a
/// ratatui screen, so a host-side warning must not be printed to it.
pub fn capturing_kernel_stderr() -> bool {
    CAPTURE_STDERR.load(Ordering::SeqCst)
}

/// The notices a verb's housekeeping said while the TUI owned stderr, oldest
/// first — see [`notice`].
static NOTICES: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());

/// **Say one line to the user** — `tm: <line>` on stderr, or, while the TUI
/// owns the screen ([`capturing_kernel_stderr`]), kept for its status line
/// ([`take_notices`]). Until the W-37 repair a line D65 promises to SAY (the
/// meeting pause a verb's housekeeping logs) was dropped on the floor in the
/// TUI: the status line read `now: ok` and nothing else (README gap 3339).
pub fn notice(line: String) {
    if capturing_kernel_stderr() {
        NOTICES.lock().unwrap_or_else(|p| p.into_inner()).push(line);
    } else {
        eprintln!("tm: {line}");
    }
}

/// The notices kept since the last call, oldest first, and the queue emptied.
pub fn take_notices() -> Vec<String> {
    std::mem::take(&mut *NOTICES.lock().unwrap_or_else(|p| p.into_inner()))
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
    /// `{"op":"est","id":…,"value":…,"blockMin":…}` — the `tm edit est=` op,
    /// carrying the value AS WRITTEN (`20b`) and what its `b` means. Since W-35
    /// (the owner's D56, README gap 2572) the kernel reads the value with its
    /// own duration grammar and writes the slot the view reads: a leading
    /// estimate that is the slot is rewritten in place, as written; an `est:`
    /// token (present, or inserted when the line has no estimate at all) gets
    /// the canonical minutes the `min` form always wrote (`est:1200m`).
    Est {
        id: String,
        value: String,
        block_min: u32,
    },
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
    /// `{"op":"close","grain":g}` — §6.3's close of one grain at the
    /// request's `now`: every region of that grain that has ended, whatever
    /// its age (stage 4, `Close.lean`). The request gains `now` and
    /// `blockMin`, and the destinations the close needs (gap 56).
    Close { grain: Grain },
    /// `{"op":"autoClose"}` — each grain's close once, day then week then
    /// month (`autoClose`, L19a/b): the §6.3 catch-up in one call.
    AutoClose,
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
            Cmd::Drop { .. }
            | Cmd::Est { .. }
            | Cmd::Rank { .. }
            | Cmd::EditKey { .. }
            | Cmd::Close { .. }
            | Cmd::AutoClose => None,
        }
    }

    /// Whether the command is a close — the only commands that read the
    /// request's clock and the only ones whose report may name lines.
    fn closes(&self) -> bool {
        matches!(self, Cmd::Close { .. } | Cmd::AutoClose)
    }
}

/// One plan document as it went through the kernel.
#[derive(Debug)]
pub struct BridgeDoc {
    /// Plan-relative path.
    pub path: String,
    /// The text read from disk (for a file the tree did not hold yet: its
    /// horizon's initial text) — original bytes, before the request-build
    /// newline normalization.
    pub sent: String,
    /// The text as written back: for a changed document the kernel's lines
    /// joined and newline-terminated (the module-level newline convention);
    /// for an untouched one, `sent` verbatim.
    pub returned: String,
    /// The document's region as the **response** carried it back — kept, not
    /// dropped (the stage-3 trap by name).
    pub region: Option<(u64, u64)>,
    /// Whether the kernel's returned line list differs from the one sent
    /// (and the file was therefore written).
    pub changed: bool,
}

/// A grain on the wire: `0` day, `1` week, `2` month — `Fin 3` in the
/// kernel, and nothing else decodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Grain {
    Day,
    Week,
    Month,
}

impl Grain {
    /// The decoder's smart constructor: exactly `0..=2`.
    pub fn from_wire(n: u64) -> Option<Grain> {
        match n {
            0 => Some(Grain::Day),
            1 => Some(Grain::Week),
            2 => Some(Grain::Month),
            _ => None,
        }
    }

    /// The wire number, the inverse of [`Grain::from_wire`].
    pub fn to_wire(self) -> u64 {
        match self {
            Grain::Day => 0,
            Grain::Week => 1,
            Grain::Month => 2,
        }
    }

    /// The grain of a §13 period argument.
    pub fn of_period(p: tm_core::model::Period) -> Grain {
        match p {
            tm_core::model::Period::Day => Grain::Day,
            tm_core::model::Period::Week => Grain::Week,
            tm_core::model::Period::Month => Grain::Month,
        }
    }

    /// `day`, `week`, `month` — §13's period names.
    pub fn name(self) -> &'static str {
        match self {
            Grain::Day => "day",
            Grain::Week => "week",
            Grain::Month => "month",
        }
    }
}

/// What a close did to one line — `Report.lean`'s `CloseDid`, by its
/// constructor's name. An unknown name is refused, never read as a default:
/// a variant the kernel adds later must fail loudly here, not fall through.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CloseDid {
    /// moved unchanged (§6.3's month row)
    Move,
    /// moved, `[>]` reopened, stamped (§6.3's day row)
    MoveReopening,
    /// `[-]` left behind, the stamped record filed forward (§6.3's week row)
    Copy,
    /// `[-]` left behind, and the item's standing `# Demoted` record rewritten
    /// in its place — stamps merged, estimate floored per L15 (§6.3's week row
    /// over §4.3's pre-close pair; kernel/README.md gap 53)
    CopyMerging,
    /// a wall still ahead, moved undemoted into the live week
    Carry,
    /// past due with `persist`: moved, box and bytes kept, unstamped, leaving
    /// no `[-]`, to the end of `backlog.md`'s `# Overdue` (§6.3's week row;
    /// the owner's D7, kernel/README.md gap 55)
    MoveOverdue,
    /// an unfinished child of a line the week close files from the same file:
    /// `[~]` in place, unstamped, its own remaining folded into that line's
    /// record (§6.3's week row, "Unfinished children are dropped …"; goal B3's
    /// repair, kernel/README.md "Stage 4 final, step 4")
    DropIntoParent,
    /// `Copy`, the record's estimate floored at the remaining of the children
    /// dropped with it by §6.4's `max`
    CopyFolding,
    /// `CopyMerging`, the merged record's estimate floored the same way
    CopyMergingFolding,
}

impl CloseDid {
    pub fn from_wire(s: &str) -> Option<CloseDid> {
        match s {
            "move" => Some(CloseDid::Move),
            "moveReopening" => Some(CloseDid::MoveReopening),
            "copy" => Some(CloseDid::Copy),
            "copyMerging" => Some(CloseDid::CopyMerging),
            "carry" => Some(CloseDid::Carry),
            "moveOverdue" => Some(CloseDid::MoveOverdue),
            "dropIntoParent" => Some(CloseDid::DropIntoParent),
            "copyFolding" => Some(CloseDid::CopyFolding),
            "copyMergingFolding" => Some(CloseDid::CopyMergingFolding),
            _ => None,
        }
    }

    /// The constructor's name, as the wire spells it — the inverse of
    /// [`CloseDid::from_wire`].
    pub fn name(self) -> &'static str {
        match self {
            CloseDid::Move => "move",
            CloseDid::MoveReopening => "moveReopening",
            CloseDid::Copy => "copy",
            CloseDid::CopyMerging => "copyMerging",
            CloseDid::Carry => "carry",
            CloseDid::MoveOverdue => "moveOverdue",
            CloseDid::DropIntoParent => "dropIntoParent",
            CloseDid::CopyFolding => "copyFolding",
            CloseDid::CopyMergingFolding => "copyMergingFolding",
        }
    }
}

/// A stamp the close appended: `D<dd>` or `W<ww>`, the bytes `demoted:`
/// carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stamp {
    Day(u32),
    Week(u32),
}

impl Stamp {
    /// `Field.parseStamp`'s grammar: a `D` or `W` and at least two digits.
    pub fn from_wire(s: &str) -> Option<Stamp> {
        let (tag, digits) = s.split_at_checked(1)?;
        if digits.len() < 2 || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        let n: u32 = digits.parse().ok()?;
        match tag {
            "D" => Some(Stamp::Day(n)),
            "W" => Some(Stamp::Week(n)),
            _ => None,
        }
    }
}

impl std::fmt::Display for Stamp {
    /// The bytes `demoted:` carries: `D07`, `W37` (two digits at least, as
    /// the kernel renders them).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stamp::Day(n) => write!(f, "D{n:02}"),
            Stamp::Week(n) => write!(f, "W{n:02}"),
        }
    }
}

/// Minutes as the kernel emits them: an integer numerator and a positive
/// denominator (`Arith.Pos`). The kernel never divides; the screen does.
/// Width: both fit `u64` or the report is refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Minutes {
    num: u64,
    den: std::num::NonZeroU64,
}

impl Minutes {
    /// The smart constructor: a zero denominator is refused, not repaired.
    pub fn new(num: u64, den: u64) -> Option<Minutes> {
        Some(Minutes { num, den: std::num::NonZeroU64::new(den)? })
    }
    pub fn num(self) -> u64 {
        self.num
    }
    pub fn den(self) -> u64 {
        self.den.get()
    }
    /// Whole minutes, rounded down — the one place the host divides
    /// (§10.1's `est_min` is an integer; every stage-4 denominator is `1`).
    pub fn whole(self) -> u32 {
        u32::try_from(self.num / self.den.get()).unwrap_or(u32::MAX)
    }
}

/// One line a close touched (the owner's D3): its id, what happened, from
/// which document to which (indices into the response's `docs`), the stamp
/// it gained, and its minutes afterwards (`None`: the line has no estimate).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CloseEntry {
    pub id: String,
    pub grain: Grain,
    pub did: CloseDid,
    pub from: usize,
    pub to: usize,
    pub stamp: Option<Stamp>,
    pub minutes: Option<Minutes>,
}

/// Decode `ok.report` with the smart constructors above. Every refusal names
/// the field; a family this reader does not know (stage 6's) is ignored by
/// design — families are looked up by name — but a malformed `closes` entry
/// is never skipped.
pub fn decode_report(report: &Value, ndocs: usize) -> Result<Vec<CloseEntry>, String> {
    let closes = report
        .get("closes")
        .and_then(Value::as_array)
        .ok_or("report: no closes array")?;
    closes
        .iter()
        .enumerate()
        .map(|(k, e)| {
            let field = |name: &str| e.get(name).ok_or(format!("report.closes[{k}]: no {name}"));
            let id = field("id")?.as_str().ok_or(format!("report.closes[{k}]: id is not a string"))?;
            let grain = field("grain")?
                .as_u64()
                .and_then(Grain::from_wire)
                .ok_or(format!("report.closes[{k}]: grain out of range"))?;
            let did = field("did")?
                .as_str()
                .and_then(CloseDid::from_wire)
                .ok_or(format!("report.closes[{k}]: unknown did"))?;
            let doc = |name: &str| -> Result<usize, String> {
                field(name)?
                    .as_u64()
                    .and_then(|n| usize::try_from(n).ok())
                    .filter(|&n| n < ndocs)
                    .ok_or(format!("report.closes[{k}]: {name} is not a document of this response"))
            };
            let (from, to) = (doc("from")?, doc("to")?);
            let stamp = match field("stamp")? {
                Value::Null => None,
                v => Some(
                    v.as_str()
                        .and_then(Stamp::from_wire)
                        .ok_or(format!("report.closes[{k}]: bad stamp"))?,
                ),
            };
            let minutes = match field("min")? {
                Value::Null => None,
                v => Some(
                    match (v.get("num").and_then(Value::as_u64), v.get("den").and_then(Value::as_u64)) {
                        (Some(n), Some(d)) => Minutes::new(n, d),
                        _ => None,
                    }
                    .ok_or(format!("report.closes[{k}]: min is not an integer pair with a positive denominator"))?,
                ),
            };
            Ok(CloseEntry { id: id.to_string(), grain, did, from, to, stamp, minutes })
        })
        .collect()
}

/// What one kernel call did to the tree.
#[derive(Debug)]
pub struct Applied {
    /// Every document, in request order.
    pub docs: Vec<BridgeDoc>,
    /// The report's `closes` (D3), in the kernel's fold order: one entry per
    /// line a close acted on. Always empty for a request without a close —
    /// a non-empty report there is refused as a fault before anything is
    /// written. `from`/`to` index [`Applied::docs`].
    pub closes: Vec<CloseEntry>,
}

impl Applied {
    /// The document at `path`.
    pub fn doc(&self, path: &str) -> Option<&BridgeDoc> {
        self.docs.iter().find(|d| d.path == path)
    }

    /// The path of the response's document `k` — how a report entry's
    /// `from`/`to` are read (the decoder already bounded `k`).
    pub fn path_of(&self, k: usize) -> &str {
        self.docs.get(k).map(|d| d.path.as_str()).unwrap_or_default()
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

/// **D35's "nothing was written" line, for the kernel-backed half** (README
/// gap 1080).
///
/// [`gate`] stamps `refusedWrite` on the host-only write paths, and in `drop`,
/// `move`, `readopt` and `demote` that call sits inside the **id-less** branch
/// — D33's "the gate goes ahead of both, because this branch never reaches the
/// kernel" — so an item that HAS an id went straight to [`apply`] and was
/// refused with no stamp. Driven on one refused tree at one refusal
/// (`badLine`, `Tm.PErr.noId`): `rank`, `edit`, `skip`, `start`, `add`
/// (inbox), `event`, `routine done`, `wake` and `break` printed the second
/// line; `drop`, `demote`, `readopt`, `move`, `add --to`, `close day` and the
/// two readers printed only the kernel's sentence. Half the verbs reassured
/// the user and half did not, on identical bytes.
///
/// **The rule is one rule and it is not a list of refusal names.** The line
/// says the tree cannot be loaded whole and every reading verb refuses it too,
/// so it fires exactly when that is true — and "does the kernel load this
/// tree?" already has one definition in this module ([`tree_refusal`], AGENTS
/// §5.3). So the failing `apply` asks it. A name list would have to grow every
/// time `Boundary.lean` gains an `LErr` constructor, silently, which is the
/// class this repository keeps finding; this cannot go stale.
///
/// **It costs nothing on a green tree.** The ask happens only after the
/// kernel has already refused, so no successful verb gains a whole-tree load
/// and `kernel_call_counts.rs`'s `apply` column does not move.
///
/// What it cannot see: the two calls are two instants, so a writer that
/// repairs the tree between them makes this answer `None` and the line is
/// missed. That is a missing reassurance, never a false one — and nothing is
/// written either way.
fn stamp_refused_write(ctx: &Ctx, verb: &str, e: CliError) -> CliError {
    let CliError::Kernel(mut issue) = e else { return e };
    // A fault is not a tree problem: it already prints its own "nothing was
    // written to the plan" line and a bug-report address.
    if issue.is_fault() {
        return CliError::Kernel(issue);
    }
    if matches!(tree_refusal(ctx), Ok(Some(_))) {
        issue.detail.insert("refusedWrite".to_string(), json!(verb));
    }
    CliError::Kernel(issue)
}

/// Apply `cmds` to the plan tree through the kernel: read every plan file,
/// call the kernel once, write the changed files back. See the module
/// docs for the contract; on any kernel refusal ([`CliError::Kernel`],
/// named) nothing has been written.
///
/// `verb` is the user's own word for what they typed, and it is here for the
/// same reason [`gate`] takes one: a refusal that names a file and a line, and
/// does not say whether the command went through, is half an answer
/// ([`stamp_refused_write`], README gap 1080).
pub fn apply(ctx: &Ctx, verb: &str, cmds: &[Cmd]) -> Result<Applied, CliError> {
    // 1. The whole tree, guarded.
    let mut docs: Vec<(String, String)> = Vec::new();
    let mut guards: Vec<FileGuard> = Vec::new();
    for rel in ctx.store.list_files()? {
        let (text, guard) = ctx.store.read_guarded(&rel)?;
        docs.push((rel, text));
        guards.push(guard);
    }
    // 2-4. The request, the one call, and the documents read back ([`answer`]).
    let applied = answer(ctx, verb, cmds, docs)?;

    // 5. Write the changed documents through the guarded atomic store. The
    // documents [`answer`] returns are the ones read above, in their order,
    // then the destinations it added: each of those enters with a guard that
    // demands the file still be absent.
    for (i, doc) in applied.docs.iter().enumerate() {
        if doc.changed {
            match guards.get(i) {
                Some(guard) => ctx.store.write_guarded(&doc.path, guard, &doc.returned)?,
                None => ctx.store.write_guarded(&doc.path, &FileGuard::absent(), &doc.returned)?,
            }
        }
    }
    Ok(applied)
}

/// **The kernel's answer to `cmds` over the documents `docs`, writing nothing**
/// — [`apply`]'s steps 2-4: the destinations and sections a command needs
/// added, the one request, the one call, and every document read back with its
/// region checked. [`apply`] writes what it answers; the TUI's automatic close
/// past midnight HOLDS it (the owner's D91, README gap 4342,
/// `closing::close_in_memory`) — one builder of the request, never a second
/// copy of it. `docs` is every plan file in tree order with its text.
pub fn answer(ctx: &Ctx, verb: &str, cmds: &[Cmd], docs: Vec<(String, String)>) -> Result<Applied, CliError> {
    let (mut paths, mut texts): (Vec<String>, Vec<String>) = docs.into_iter().unzip();
    // A destination the tree does not hold yet enters the request as its
    // horizon's initial text, and is created on write only if the kernel
    // put something there (its guard demands the file still be absent).
    // A close names no destination of its own: it files into the week and
    // the month containing *now* (D1, `closeTo`), so those two are its
    // destinations — the host hands them over because the kernel cannot
    // create a file (gap 56).
    let closing = cmds.iter().any(Cmd::closes);
    let month_now = Horizon::Month(YearMonth::from_date(ctx.today)).path();
    // The months whose §4.3 sections the host hands over (below): the month
    // containing now for a close, and a `demote`'s destination, whose record
    // the kernel files at the end of `# Demoted` exactly as the week close
    // does (`demoteSpot`, kernel/README.md gap 20's remainder, stage 4 step 9).
    let mut sectioned: Vec<String> = cmds
        .iter()
        .filter_map(|c| match c {
            Cmd::Demote { to, .. } => Some(to.clone()),
            _ => None,
        })
        .collect();
    if closing {
        sectioned.push(month_now.clone());
    }
    let mut dests: Vec<String> = cmds.iter().filter_map(|c| c.dest().map(str::to_string)).collect();
    if closing {
        dests.push(Horizon::Week(IsoWeek::from_date(ctx.today)).path());
        dests.push(month_now.clone());
        // The owner's D7: the week close moves a past-due `persist` line to
        // `backlog.md # Overdue`, so the backlog is a close's third
        // destination (kernel/README.md gap 55, `overdueTarget`).
        dests.push(Horizon::Backlog.path());
    }
    for dest in &dests {
        if !paths.iter().any(|p| p == dest) {
            let initial = Horizon::from_path(dest)
                .map(|h| store::initial_text(&h))
                .unwrap_or_default();
            paths.push(dest.to_string());
            texts.push(initial);
        }
    }

    // 2. The request: regions are generated here (gap 10), lines split on
    // '\n' with exactly one trailing empty segment stripped iff the file
    // ends with '\n' (the module-level newline convention) — otherwise the
    // final newline's phantom line becomes a ranked prose line and the
    // kernel's append lands after it.
    let mut docs_json = Vec::new();
    let mut sent_joined: Vec<String> = Vec::new();
    for (rel, text) in paths.iter().zip(&texts) {
        let mut lines = doc_lines(text);
        // The other half of gap 56: a close lands a week's record at the end
        // of the month's `# Demoted`, and a month's leftover under the
        // heading it stood under, and the kernel refuses `noSection` rather
        // than choose where a heading goes (AGENTS §5.6). So the host hands
        // over the month containing now with §4.3's two month sections,
        // appended at its end when missing — and a `demote`'s month too, so
        // the verb's record lands under `# Demoted` rather than at the end
        // of a month that lacks one (the kernel's fallback, gap 60). Prose
        // only; written only if a line lands in the file (an untouched
        // document is never written).
        if sectioned.iter().any(|m| m == rel) {
            for (name, heading) in MONTH_SECTIONS {
                if !lines.iter().any(|l| heading_body(l) == Some(name)) {
                    lines.push(heading);
                }
            }
        }
        // The same rule for D7's section (kernel/README.md gap 56's overdue
        // half, closed at stage 4 final step 2): a close request carries
        // `backlog.md` with `# Overdue` as its **last line** when the file has
        // no heading of that name — one fixed place, so the kernel never
        // chooses where a heading goes (AGENTS §5.6), and written only if a
        // line lands under it.
        if closing && *rel == Horizon::Backlog.path() {
            let (name, heading) = OVERDUE_SECTION;
            if !lines.iter().any(|l| heading_body(l) == Some(name)) {
                lines.push(heading);
            }
        }
        sent_joined.push(lines.join("\n"));
        docs_json.push(doc_json(rel, &lines));
    }
    let doc_ix = |dest: &str| -> u64 {
        paths.iter().position(|p| p == dest).expect("dest was added above") as u64
    };
    let cmds_json: Vec<Value> = cmds
        .iter()
        .map(|c| match c {
            Cmd::Move { id, to } => json!({"op":"move","id":id,"doc":doc_ix(to)}),
            Cmd::Drop { id } => json!({"op":"drop","id":id}),
            Cmd::Est {
                id,
                value,
                block_min,
            } => json!({"op":"est","id":id,"value":value,"blockMin":block_min}),
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
            Cmd::Close { grain } => json!({"op":"close","grain":grain.to_wire()}),
            Cmd::AutoClose => json!({"op":"autoClose"}),
        })
        .collect();
    // **The block length rides every request** (the campaign's D69 call on
    // README gap 3345): the loader reads a leading `Nb` at it when it refuses a
    // duration past the host's width (`pastWidth`), as `tm-core`'s parser does.
    let mut request = json!({ "docs": docs_json, "cmds": cmds_json, "blockMin": ctx.block_min() });
    if closing {
        // The request's clock (stage 4 step 5): `now` is the CLI's own
        // instant as a local date — `--now` in tests, the real clock
        // otherwise — and the kernel never invents one. Sent only with a
        // close, the one op that reads it.
        request["now"] = json!(ctx.today.format("%Y-%m-%d").to_string());
    }
    // 3. One call ([`call`]: stderr captured, the fault probe, the refusal by
    // name) — and, on a refusal, D35's own sentence for the verb that was
    // typed (README gap 1080).
    let (resp, stderr) = call(&request).map_err(|e| stamp_refused_write(ctx, verb, e))?;
    let out_docs = resp["ok"]["docs"]
        .as_array()
        .ok_or_else(|| CliError::Kernel(fault_issue("response carries neither ok nor err", &stderr)))?;
    // The report (D3) rides every `ok`. A request without a close must get
    // a report that names nothing; either failure is a named fault, and
    // nothing has been written.
    let report = decode_report(&resp["ok"]["report"], out_docs.len())
        .map_err(|e| CliError::Kernel(fault_issue(&e, &stderr)))?;
    if !closing && !report.is_empty() {
        return Err(CliError::Kernel(fault_issue(
            &format!("the response reports {} closed lines for a request that closed nothing", report.len()),
            &stderr,
        )));
    }
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
        let mut joined = String::new();
        for (j, l) in lines.iter().enumerate() {
            if j > 0 {
                joined.push('\n');
            }
            joined.push_str(l.as_str().ok_or_else(|| {
                CliError::Kernel(fault_issue(&format!("{path}: line {j} is not a string"), &stderr))
            })?);
        }
        let region = match (od.get("grain").and_then(Value::as_u64), od.get("ix").and_then(Value::as_u64)) {
            (Some(g), Some(ix)) => Some((g, ix)),
            _ => None,
        };
        // `changed` is a statement about the kernel's line lists, so the
        // write-back normalization below never counts as a change: an
        // untouched file — final newline or not — stays byte-identical on
        // disk because it is never written at all.
        let changed = joined != sent_joined[i];
        // A rewritten file is newline-terminated with exactly one '\n'
        // between lines (the module-level newline convention); an untouched
        // one keeps its original bytes.
        let returned = if changed { joined + "\n" } else { texts[i].clone() };
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

    Ok(Applied { docs, closes: report })
}

/// **Does the kernel still load this tree?** — asked in one place, by both
/// the verb that reports it and the verbs that must not write over it.
///
/// `Ok(None)` means the kernel loaded the whole tree; `Ok(Some(issue))` is a
/// named refusal (`dupId`, `danglingParent`, `badLine`, `itemCheck`, …) with
/// D32's widened `path`/`line` detail on it; `Err` is a **fault**, which is
/// not a tree problem and is nobody's to swallow.
///
/// **It writes nothing, by construction** (D32 item 2, `e31e0c5`): it goes to
/// [`call`] directly, which has no write step at all, rather than to [`apply`]
/// with an empty command list — so `tm check`, which runs in the pre-commit
/// hook of every generated plan, is unable to write rather than merely
/// unlikely to. `check_never_writes_a_byte` pins that, and it is now the
/// property of one function instead of one command.
///
/// **A file whose bytes are not text is skipped, not fatal** (W-16 repair, gap
/// 579): the kernel cannot be shown bytes that are not text, so it is asked
/// about the rest of the tree and `StoreError::is_not_utf8` is the one place
/// that verdict is taken. `Store::read_tree` reports the decode
/// problem separately, naming the line, and `tm check` prints it beside
/// whatever the kernel says.
pub fn tree_refusal(ctx: &Ctx) -> Result<Option<KernelIssue>, CliError> {
    refusal_in(&ctx.store, ctx.block_min())
}

/// **The same question, of any store** — the body [`tree_refusal`] is now a
/// projection of.
///
/// Widened (and not copied) so that the one write path whose tree is not yet on
/// disk can ask it too: `tm check --fix-ids` builds the tree it *would* write in
/// a [`MemStore`] and asks about that ([`fix_ids_refusal`]). One definition of
/// "does the kernel load this tree", over one trait (AGENTS §5.3).
///
/// **It carries the block length** (the campaign's D69 call on README gap 3345):
/// the kernel's loader refuses a duration past the host's `u32` minutes BY
/// NAME (`pastWidth`), and a leading `Nb` is only minutes at a block length —
/// so the tree is asked about at this configuration's, the one `tm-core`'s own
/// parser reads it at, and the two bounds are one.
pub fn refusal_in(store: &dyn Store, block_min: u32) -> Result<Option<KernelIssue>, CliError> {
    let docs = text_docs(store)?;
    match call(&json!({ "docs": docs, "cmds": [], "blockMin": block_min })) {
        Ok(_) => Ok(None),
        Err(CliError::Kernel(issue)) if !issue.is_fault() => Ok(Some(issue)),
        Err(e) => Err(e),
    }
}

/// **The tree as a read-only request's `docs`**: every plan file whose bytes are
/// text, as [`refusal_in`] sends it (a file that is not UTF-8 is skipped, not
/// fatal — `Store::read_tree` reports it). Shared by the questions that only
/// read the tree — whether it loads, and what its walls write (README gap 3139).
pub fn text_docs(store: &dyn Store) -> Result<Vec<Value>, CliError> {
    let mut docs = Vec::new();
    for rel in store.list_files()? {
        let text = match store.read_text(&rel) {
            Ok(text) => text,
            Err(e) if e.is_not_utf8() => continue,
            Err(e) => return Err(e.into()),
        };
        docs.push(doc_json(&rel, &doc_lines(&text)));
    }
    Ok(docs)
}

/// **D35 for the one write path [`gate`] cannot gate** (README gap 675):
/// does the tree `tm check --fix-ids` *would write* load?
///
/// `--fix-ids` writes — `tm-core`'s `check::fix_ids` appends an `^id` to every
/// line that needs one, through [`Store::modify_file`] — and it did so with no
/// gate, no [`super::undo::Recorder`] entry and exit **0** on the write. Driven
/// before this landed, on a tree made refused by an unrelated duplicate routine:
/// `tm check --fix-ids` wrote `backlog.md`, printed the kernel's `dupId` beside
/// it, exited 2 on the errors, and `tm undo` then said *"nothing to undo"*.
///
/// **It cannot be [`gate`], and that is the whole difficulty.** A tree refused
/// *for a missing `^id`* is exactly the tree `--fix-ids` exists to repair —
/// driven: two id-less `- [ ] Twin thing` lines in `backlog.md` make the kernel
/// refuse with `badLine (Tm.PErr.noId)`, `--fix-ids` assigns both ids, and
/// `tm check` is clean afterwards. Gating on the tree *before* the write would
/// trap that user inside a refusal, which is the same reason `tm undo` is not
/// gated.
///
/// So the question asked is the one D35 is actually about — **does the tree this
/// write produces load?** — and it is asked of a [`MemStore`] mirror, so the
/// answer comes from running the *same* `fix_ids` the real write runs rather
/// than from a second implementation of the assignment (AGENTS §5.3). The ids
/// the mirror picks are not the ids the real write picks (the generator is
/// seeded per call and `taken` keeps both collision-free), and the kernel's
/// verdict does not depend on which fresh ids were chosen — it depends on
/// *whether every line that needs one now has one*.
///
/// `Ok(None)` means write; `Ok(Some(issue))` means the fix would not be enough
/// and nothing is written.
pub fn fix_ids_refusal(ctx: &Ctx, gen: &mut IdGen) -> Result<Option<KernelIssue>, CliError> {
    let mirror = MemStore::new();
    // `config.toml` first: `fix_ids` reads the horizon rules through
    // `Store::read_config`, and a mirror without it would answer `Config`'s
    // defaults and could decide differently about which lines need an id.
    if ctx.store.exists(store::CONFIG_PATH) {
        mirror.insert(store::CONFIG_PATH, &ctx.store.read_text(store::CONFIG_PATH)?);
    }
    for rel in ctx.store.list_files()? {
        match ctx.store.read_text(&rel) {
            Ok(text) => mirror.insert(&rel, &text),
            // The undecodable file is `gate`'s own case and is refused before
            // this is reached; skipping it here keeps the mirror a mirror of
            // what the kernel would be shown.
            Err(e) if e.is_not_utf8() => continue,
            Err(e) => return Err(e.into()),
        }
    }
    let mut files = mirror.read_tree()?.files;
    if tm_core::check::fix_ids(&mirror, &mut files, gen)?.is_empty() {
        // **Nothing to write, so nothing to gate.** The proposed tree IS the
        // tree on disk, and `tm check` is about to ask the kernel about that
        // one anyway (`lifecycle::kernel_problems`) — so the common
        // `tm check --fix-ids`, on a tree where every line already has its id,
        // costs the mirror and no second kernel call at all.
        return Ok(None);
    }
    refusal_in(&mirror, ctx.block_min())
}

/// **The one write gate** (the owner's D35, README gap 584): a host-only write
/// path asks the kernel whether the tree still loads, and refuses if it does
/// not.
///
/// Every *kernel-backed* write is gated already — [`apply`] refuses the whole
/// request and writes nothing. The host-only paths are the ones gap 41, gap 5
/// and §4.1's line surgery left behind, and before this a user could keep
/// editing a tree that `tm plan`, `tm now` and `tm review` all refused:
/// `tm edit ^d1 'title=…'` rewrote its file and exited **0** while `tm check`
/// exited 2 on the same bytes.
///
/// **It refuses with the same error the kernel-backed paths refuse with** —
/// the kernel's own named sentence, carrying D32's two positions — so a broken
/// tree reads the same whichever path the verb took (AGENTS §5.3: one spelling
/// of the refusal). `verb` rides the detail as `refusedWrite`, which is the
/// only thing added, and it is what [`super::out::CliError::report`] turns into
/// the "nothing was written" line: the kernel says *what* is wrong and *where*,
/// this says what it means for the command the user just typed.
///
/// **Deliberately not called from `tm undo`, `tm init` or `tm check`, and the
/// reason is different for each — two of the three were stated wrongly until the
/// W-17 repair** (README gaps 675 and 680).
///
/// * `tm undo` is the way *out* of a tree the kernel refuses and gating it would
///   trap the user inside one.
/// * `tm init` — **not** "no tree yet", which is false under `--force`: driven on
///   a tree the kernel refuses, `tm init --force` exits 0 and creates
///   `week/2026-W38.md`. What makes it safe is that it is **preserving and
///   additive**: every file whose content is the user's is `Mode::Preserve` and
///   is listed in the run's own `skipped`, so a `--force` over a refused tree
///   changed **not one existing byte** (md5 of every file before and after, and
///   the refusal identical on both sides). `init_force_preserves_a_refused_tree`
///   is the test that keeps it true; the day `init` rewrites a plan file it owes
///   the gate.
/// * `tm check` is D18/gap 145's one tolerant verb, whose whole job is to name
///   the line — but **`tm check --fix-ids` writes**, and that write has its own
///   gate now ([`fix_ids_refusal`]), because it can neither go ungated nor take
///   this one.
pub fn gate(ctx: &Ctx, verb: &str) -> Result<(), CliError> {
    // **A file whose bytes are not text is a tree that does not load either**,
    // and the kernel cannot be asked about it: `tree_refusal` skips it (gap
    // 579) so that `tm check` survives it, which means the kernel would answer
    // "fine" about the rest and the write would go through. Driven on a tree
    // with one stray byte appended to `inbox.md`: `tm check` exits 2 naming
    // `inbox.md:5`, `tm plan` exits 1, and before this line `tm edit ^d1
    // 'title=…'` rewrote `week/2026-W37.md` and exited **0** — gap 584's own
    // shape, one input class over.
    //
    // `read_tree` already decided it and already found the line (§17.2's one
    // reader); this asks `PlanFiles` rather than decoding anything a second
    // time. `tm check` still reports it as a problem and still exits 2, which
    // is where a reader is sent.
    if let Some((path, line)) = ctx.files.undecodable() {
        return Err(CliError::msg(format!(
            "{path}:{line}: {} — nothing was written: `tm {verb}` needs a tree that can be read \
             whole, and every reading verb refuses this one too (run `tm check`: it names every \
             such line)",
            store::NOT_UTF8
        )));
    }
    match tree_refusal(ctx)? {
        None => Ok(()),
        Some(mut issue) => {
            issue.detail.insert("refusedWrite".to_string(), json!(verb));
            Err(CliError::Kernel(issue))
        }
    }
}

/// **The lines the kernel sees for a file's text** (the module-level newline
/// convention): split on `'\n'`, with exactly one trailing empty segment
/// stripped iff the text ends with `'\n'`. Every request document is built
/// through it ([`apply`]'s, and the capacity request's,
/// [`super::kernel_capacity`]).
pub fn doc_lines(text: &str) -> Vec<&str> {
    let mut lines: Vec<&str> = text.split('\n').collect();
    if text.ends_with('\n') {
        lines.pop();
    }
    lines
}

/// **One request document**: `{path, lines}`, with the region the path
/// declares ([`region_of`], gap 10's host half) when it declares one.
pub fn doc_json(rel: &str, lines: &[&str]) -> Value {
    let mut doc = json!({ "path": rel, "lines": lines });
    if let Some((g, ix)) = region_of(rel) {
        doc["grain"] = json!(g);
        doc["ix"] = json!(ix);
    }
    doc
}

/// **One kernel call**, the only one in the binary: the request's bytes to
/// `tm_kernel_ffi::call`, with Lean's stderr captured while it runs when the
/// TUI asked for it (panic layer 2), so a backtrace lands in the fault's
/// detail, never on the alternate screen. Returns the parsed response (whose
/// `ok` the caller reads) and the captured stderr; an `err` is the named
/// refusal ([`refusal`]), and no usable response is a named fault.
pub fn call(request: &Value) -> Result<(Value, String), CliError> {
    call_text(&request.to_string())
}

/// **The same call, from the request's own bytes** (stage 6 step L9).  The
/// capacity request carries a `log` section since L9, and a checkpoint inside it
/// is read **in build order** (`Seal.readCkptFields`): `serde_json::Value` is a
/// `BTreeMap`, so round-tripping the section through it alphabetises the
/// checkpoint's keys and the kernel refuses `badCkpt v` — gap 144's lesson, at a
/// second seam.  The section is therefore spliced in as text and never parsed.
pub fn call_text(request: &str) -> Result<(Value, String), CliError> {
    let capture = StderrCapture::start();
    let called = tm_kernel_ffi::call(request);
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
    Ok((resp, stderr))
}

/// §4.3's month-file sections, the two a close lands lines under: each
/// heading's name, and the line the host appends when a month lacks it.
const MONTH_SECTIONS: [(&str, &str); 2] = [("Outcomes", "# Outcomes"), ("Demoted", "# Demoted")];

/// The backlog section a week close moves a past-due `persist` line into
/// (§6.3's week row, fork-point `OVERDUE_SECTION`; the owner's D7), with the
/// heading the host appends when `backlog.md` has none.
const OVERDUE_SECTION: (&str, &str) = ("Overdue", "# Overdue");

/// The name of a heading line — `Plan.lean`'s `isHeading`/`headingBody`: a
/// line whose first character is `#`, with its `#`s and the spaces after
/// them stripped, so `# Demoted` and `## Demoted` are one name.
fn heading_body(line: &str) -> Option<&str> {
    line.starts_with('#')
        .then(|| line.trim_start_matches('#').trim_start_matches(' '))
}

/// An FFI-level fault (no usable response). Loud and recoverable, never a
/// wrong answer — and nothing has been written when it is raised. `stderr`
/// is whatever layer 2 captured off fd 2 during the call (empty outside the
/// TUI); it rides the detail so the bug report carries the backtrace the
/// terminal never saw.
pub fn fault_issue(what: &str, stderr: &str) -> KernelIssue {
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

/// A refusal of the request's `log` or `tz` section (`{"err":{"log":…}}`,
/// stage 5 D9 B4; design §10.3). Every one the kernel names at B4 —
/// `tzAbsent`, `badTz <why>`, `tooManyLines`, `badLogReq <field>`,
/// `renderNotInTail {line}` — is a **host defect**: tm builds every log request,
/// and a line of the log never refuses one (a bad line is a warning). So each is
/// a loud fault ([`fault_issue`]) whose detail names the refusal (`logRefusal`)
/// and the field it is about (`why`, `field` or `line`). W3 adds the checkpoint
/// refusals (`undoReach`, `cutMismatch`, …), whose reaction is a rebuild, not a
/// fault. Nothing in the binary sends a `log` section before W3.
fn log_refusal(l: &Value) -> KernelIssue {
    let (name, arg) = match l {
        Value::String(s) => (s.clone(), None),
        Value::Object(m) if m.len() == 1 => match m.iter().next() {
            Some((k, v)) => (k.clone(), Some(v)),
            None => ("unrecognised".to_string(), None),
        },
        _ => ("unrecognised".to_string(), None),
    };
    let text = |v: Option<&Value>| v.and_then(Value::as_str).unwrap_or_default().to_string();
    let (what, key, val): (String, &str, Value) = match name.as_str() {
        "tzAbsent" => ("a log section was sent without its tz table".into(), "", Value::Null),
        "tooManyLines" => ("more than 8,192 log lines were sent in one call (the memory gate, gap 102)".into(), "", Value::Null),
        // W3 (design §10.3): the resume's refusals. `kernel_log` reacts to these (genesis, then the request once more,
        // or genesis at that `now` unpersisted); one that reaches the bridge is a host defect.
        "undoReach" | "wakeBehindCut" | "sealedDay" | "sealedWindow" | "nowBelowLedger" => {
            let line = arg.and_then(|v| v.get("line").or_else(|| v.get("now"))).and_then(Value::as_u64).unwrap_or_default();
            (format!("the replay cache's guard `{name}` refused line {line} and no rebuild answered"), "line", Value::from(line))
        }
        "badCkpt" | "counterOverflow" => {
            let field = text(arg);
            (format!("the checkpoint's `{field}` is out of its bounds"), "field", Value::String(field))
        }
        "cutMismatch" => ("the log tail did not start at the checkpoint's cut".into(), "", Value::Null),
        "zone" => ("the checkpoint was attributed under another zone table".into(), "", Value::Null),
        "badTz" => {
            let why = text(arg);
            (format!("the tz table's `{why}` is malformed (tm/src/cli/tz_table.rs writes it)"), "why", Value::String(why))
        }
        "badLogReq" => {
            let field = text(arg);
            (format!("the log section's `{field}` is malformed or not yet supported"), "field", Value::String(field))
        }
        "renderNotInTail" => {
            let line = arg.and_then(|v| v.get("line")).and_then(Value::as_u64).unwrap_or_default();
            (format!("render asked for line {line}, outside the lines sent"), "line", Value::from(line))
        }
        _ => (format!("an unlisted log refusal {l}"), "", Value::Null),
    };
    let mut issue = fault_issue(&format!("log refusal {name} — {what}"), "");
    issue.detail.insert("logRefusal".into(), Value::String(name));
    if !key.is_empty() {
        issue.detail.insert(key.into(), val);
    }
    issue
}

/// What a store key is, appended to the three key-collision refusals.
///
/// Since D31 (`Line.lean`'s `keyOf`) the key is the line's `^id` when it spells
/// one and `Field.titleKey` — the title words joined by single spaces — when it
/// does not. The title key is **synthesised**; it is deliberately never written
/// into a file (`serialize_parseLine`), so there is no `^`-token to grep for.
const KEY_NOTE: &str = " (a line with no `^id` is keyed by its title, and that key is never \
                        written into a file, so the two positions above are where it is)";

/// One widened key collision (**D32, gap 475**): the store key, and each of the
/// two colliding lines as `(path, line)` with the line already converted to the
/// 1-based convention every other position this binary prints uses (gap 479).
///
/// The kernel decides *which* two lines and *in which order* — path, then line,
/// by `Boundary.lean`'s `spotPair`, which is a total order on the position and
/// deliberately not the order the host listed its documents in (AGENTS §5.6).
/// The bridge does not go back to the tree to find them: the host's
/// `Tree::key_of` is a **second** answer to "what is this line's key", and
/// asking it here is how the two readings would start to disagree inside a
/// diagnostic (AGENTS §5.3).
fn collision(c: &Value) -> (String, (String, u64), (String, u64)) {
    let key = c.get("key").and_then(Value::as_str).unwrap_or_default().to_string();
    let spot = |k: &str| {
        let s = c.get(k);
        (
            s.and_then(|s| s.get("path")).and_then(Value::as_str).unwrap_or_default().to_string(),
            one_based(s.and_then(|s| s.get("line")).and_then(Value::as_u64).unwrap_or_default()),
        )
    };
    (key, spot("a"), spot("b"))
}

/// The kernel counts a document's lines from **0** (`Boundary.lean`'s `badLine`
/// doc comment: "0-based, as `badLine`"), and `tm check` — every other
/// `file:line` this binary prints — counts from **1**. The bridge is the one
/// place the two meet, so it converts here rather than printing two conventions
/// out of one binary (W-15 repair, gap 479).
fn one_based(kernel_line: u64) -> u64 {
    kernel_line + 1
}

/// **The one sentence that points a reader at `tm check`**, and the one place
/// it is spelled.
///
/// `itemCheck` is a property of the whole tree, so the refusal carries a fault
/// name and no position; `tm check` answers exactly that question against the
/// same tree, so every *other* verb's refusal says so (W-12, gap 239). Inside
/// `tm check`'s own output it is nonsense — the advice is to run the command
/// that is printing it, immediately above the two lines that do name the file
/// and the line — so `lifecycle::load_problems` takes it back off, and
/// `the_check_hint_is_not_printed_by_check_itself` pins both halves (W-16
/// repair, gap 580).
pub const CHECK_HINT: &str = " (run `tm check`: it names the file and the line)";

/// Map the response's `err` payload to a named [`KernelIssue`]. The shapes
/// are `Boundary.lean`'s: a free-text string, `{"kernel":name}`, the six
/// structured loader diagnostics, and (stage 5 D9 B4) `{"log":…}`, which
/// [`log_refusal`] maps.
fn refusal(err: &Value) -> KernelIssue {
    if let Some(l) = err.get("log") {
        return log_refusal(l);
    }
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
                "kernel refusal: keyNotWired — {k:?} is not on the kernel's edit path (kernel/README.md gap 40: `demoted` is lifecycle state that demote/readopt own)"
            ))
        } else if let Some(k) = s.strip_prefix("unknownKey ") {
            put("key", k.to_string());
            ("unknownKey".into(), format!(
                "kernel refusal: unknownKey — {k:?} is not a §4.1 key"
            ))
        } else if s.starts_with("title") && !s.contains(' ') {
            let why = match s {
                "titleNewline" => "the title carries a newline, which would split the line",
                "titleTab" => "the title carries a tab; `add` refuses one by name rather than write it (README gap 4164)",
                "titleId" => "the title carries a `^`, which would read back as a second id",
                "titleBlank" => "the title is empty or only spaces",
                "titleEdge" => "the title starts or ends with a space, which would not re-tokenize as written",
                _ => "an unlisted title refusal — see Boundary.lean's parseCmd",
            };
            (s.to_string(), format!("kernel refusal: {s} — {why}"))
        } else if matches!(s, "nowAbsent" | "badNow" | "blockMinAbsent" | "badBlockMin") {
            // The request's clock (stage 4 step 5): the kernel never invents
            // `now`, so a close without one is refused by name.
            let why = match s {
                "nowAbsent" => "a close was sent without `now`; the kernel never invents the instant it closes at",
                "badNow" => "`now` is not a YYYY-MM-DD date",
                "blockMinAbsent" => "a close was sent without `blockMin`, which its report's minutes need",
                _ => "`blockMin` is not a positive number of minutes",
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
            "alreadyDemoted" => "the line is itself a `[-]` archive record, or the item's other line is a `[-]` outside a month's `# Demoted`; demoting again would overwrite that tombstone and delete its line (a record is carried by the month close)",
            "badHorizon" => "the rewritten plan fails the kernel's whole-plan check — a destination that is not in the plan, a line landing in a section it may not occupy, or a rank collision",
            "badItem" => "the rewritten item fails the kernel's item check",
            "keyAbsent" => "the line does not carry that key",
            "danglingDep" => "the edited `after:` names an id no item in the plan carries",
            "depCycle" => "the edited `after:` makes the dependencies cycle (§5.5)",
            "siteOutOfRange" => "a placement points at a document the plan does not hold",
            "noTarget" => "a close has no file to put a line in — the host must hand over the destination week, month or backlog file (kernel/README.md gap 56)",
            "noSection" => "a close's destination file has no section to land the line in (`# Demoted`, the backlog's `# Overdue`, or the heading it stood under; gap 56)",
            _ => "an unlisted kernel refusal — see kernel/TmKernel/TmKernel/Boundary.lean",
        };
        (name.to_string(), format!("kernel refusal: {name} — {why}"))
    } else if let Some(text) = err.get("capacity").and_then(Value::as_str) {
        // Stage 5 D10 step L6 (design §13.6, Boundary.lean's `CapWire.Refusal`):
        // `<name> <key>`. No verb sends `capacity` until L8's host half wires the
        // encoder, so today these reach the host only from a hand-built request.
        let (name, key) = match text.split_once(' ') {
            Some((n, k)) => (n, Some(k)),
            None => (text, None),
        };
        if let Some(k) = key {
            put("key", k.to_string());
        }
        let why = match name {
            "nowAbsent" => "a capacity request was sent without `now`, which is the lookahead's first day",
            "blockMinAbsent" => "a capacity request was sent without `blockMin`, which is `[day] block_min`",
            "tzAbsent" => "a capacity request was sent without the zone table `tz`",
            "badTz" => "the zone table is malformed, out of order, or longer than 4,096 transitions",
            "badCapacity" => "a required key of the capacity section is absent, repeated, or of the wrong type",
            "badWeight" => "a `p_lounge` value is not a decimal pair with a positive denominator",
            "weightAboveOne" => "a `p_lounge` value is above 1",
            "weightPrecision" => "a `p_lounge` value has more than 18 decimal places",
            "badClock" => "a clock is not `HH:MM` below 24:00",
            "badWake" => "today's logged wake is not a time of day chrono can hold",
            "badCurve" => "a learned energy curve is not 12 levels below 256",
            "badPrior" => "the energy prior has more than 16 curves, a key over 64 characters, or a key twice",
            "badStep" => "an energy prior range has a key outside [0, 48] hours with at most 6 decimal places, an empty range, or is out of order",
            "badLevel" => "an energy prior level is above 5",
            "badCap" => "`home_max_ci` is above 5",
            "badDay" => "a `[day]` value is outside its bound",
            "lookaheadTooLong" => "the lookahead runs past 3,660 days or past year 9999",
            // stage 6 step L9: day 0's own inputs (gap 93; `badDay0` is gone with the argument
            // it refused — the kernel derives day 0 rather than being handed it)
            "badAt" => "the `at` stamp is not a timestamp the kernel can read",
            "nowDisagrees" => "the `at` stamp's local date is not the request's `now`, so day 0 would be cut from an instant outside the day being planned",
            "badState" => "a `state.json` value the capacity request carries is of the wrong type or outside its bound",
            "badPosterior" => "an `[energy]` posterior decimal is not an exact pair with a denominator of at most 10^6",
            "badSleep" => "an `[energy.sleep_debt]` decimal (or the model's `sleep_debt_shift`) is not an exact pair with a denominator of at most 10^6",
            "day0WithoutLog" => "a capacity request carried no `log` section, so the kernel has no replay to derive today's capacity from",
            "badBins" => "`priority.bins` is not a descending ladder of at most 16 edges in (0, 1]",
            "badSafety" => "`priority.safety` is not in (0, 1000]",
            "badDefaultPriority" => "`priority.default_priority` is not 1 to 4",
            // stage 5 D10 L8: the candidates, and gap 109's rule
            "tooManyCandidates" => "a capacity request carried more than 1,024 candidates",
            "badCandidate" => "a candidate record's key is absent, of the wrong type, or outside its bound (the key names the record's position and the key)",
            "capacityWithCommands" => "a capacity request also carried commands; the lookahead reads the documents as sent, so capacity is asked for without commands",
            _ => "an unlisted capacity refusal — see Boundary.lean's `CapWire.Refusal`",
        };
        (name.to_string(), format!("kernel refusal: {text} — {why}"))
    // ---------------------------------------------------------------------
    // The three **store-key** collisions (W-15 repair, gaps 475 and 479).
    //
    // The kernel's key is not always an `^id`.  Since D31's widened grammar
    // (`Line.lean`'s `keyOf`) a line with **no** `^id` is keyed by
    // `Field.titleKey` — the title words joined by single spaces — and that key
    // is never written into a file.  So `^{key}` is a **lie** for exactly the
    // lines D31 made loadable: printing `^Factorio` or
    // `^read the Lean 4 metaprogramming book` sends the reader grepping for a
    // token that exists nowhere in the tree.  These three messages name the key
    // as a key, and say where a key with no `^` came from.
    //
    // `dupId` does not point at `tm check`, and since D32 the reason has
    // changed rather than gone away.  Gap 239 added that pointer on the
    // premise that "`tm check` on the same tree answers instantly and
    // precisely"; for this class the premise was false, because `tm check`'s
    // duplicate detection is the host's `Tree::key_of`, which per AGENTS §5.6
    // keys the later of two colliding lines `file:line` and reported *no
    // problem at all*.  D32 closed that (gap 476): `tm check` now asks the
    // kernel and prints this refusal at both lines, as `kernel-load`.  The
    // pointer stays off because the message **already names the two lines**,
    // so sending the reader to another verb to be told the same thing is a
    // detour, not help.
    } else if let Some(c) = err.get("dupId") {
        let (key, (pa, la), (pb, lb)) = collision(c);
        put("key", key.clone());
        detail.insert("a".into(), serde_json::json!({ "path": pa, "line": la }));
        detail.insert("b".into(), serde_json::json!({ "path": pb, "line": lb }));
        ("dupId".into(), format!(
            "kernel refusal: dupId — {pa}:{la} and {pb}:{lb} are two lines in one file that \
             resolve to the store key `{key}`{KEY_NOTE}; the kernel refuses a tree it cannot \
             load whole"
        ))
    } else if let Some(c) = err.get("notADemotion") {
        let (key, (pa, la), (pb, lb)) = collision(c);
        put("key", key.clone());
        detail.insert("a".into(), serde_json::json!({ "path": pa, "line": la }));
        detail.insert("b".into(), serde_json::json!({ "path": pb, "line": lb }));
        ("notADemotion".into(), format!(
            "kernel refusal: notADemotion — {pa}:{la} and {pb}:{lb} are two lines in different \
             files that resolve to the store key `{key}` and are not a demotion pair the kernel \
             can read{KEY_NOTE}"
        ))
    } else if let Some(c) = err.get("ambiguousDemotion") {
        let (key, (pa, la), (pb, lb)) = collision(c);
        put("key", key.clone());
        detail.insert("a".into(), serde_json::json!({ "path": pa, "line": la }));
        detail.insert("b".into(), serde_json::json!({ "path": pb, "line": lb }));
        ("ambiguousDemotion".into(), format!(
            "kernel refusal: ambiguousDemotion — the documents do not order {pa}:{la} and \
             {pb}:{lb}, which resolve to the store key `{key}`, so which one is the record is \
             ambiguous{KEY_NOTE}"
        ))
    } else if let Some(p) = err.get("duplicatePath").and_then(Value::as_str) {
        put("path", p.to_string());
        ("duplicatePath".into(), format!(
            "kernel refusal: duplicatePath — two request documents share the path {p}"
        ))
    } else if let Some(b) = err.get("badLine") {
        let path = b["path"].as_str().unwrap_or_default().to_string();
        let line = one_based(b["line"].as_u64().unwrap_or_default());
        let why = b["why"].as_str().unwrap_or_default().to_string();
        put("path", path.clone());
        put("why", why.clone());
        detail.insert("line".into(), Value::from(line));
        ("badLine".into(), format!(
            "kernel refusal: badLine — {path}:{line} looks like an item but does not parse ({why}); the kernel refuses a tree it cannot load whole"
        ))
    } else if let Some(b) = err.get("pastWidth") {
        // The campaign's D69 call on README gap 3345 (`Width.lean`): a duration
        // the line carries is past the `u32` minutes the host holds it in, at
        // the request's block length — one bound, the host's, read by both.
        let path = b["path"].as_str().unwrap_or_default().to_string();
        let line = one_based(b["line"].as_u64().unwrap_or_default());
        let slot = b["slot"].as_str().unwrap_or_default().to_string();
        let what = match slot.as_str() {
            "lead" => "its leading estimate".to_string(),
            other => format!("its `{other}:`"),
        };
        put("path", path.clone());
        put("slot", slot.clone());
        detail.insert("line".into(), Value::from(line));
        ("pastWidth".into(), format!(
            "kernel refusal: pastWidth — {path}:{line}: {what} is more than {} minutes, which \
             tm cannot hold; the kernel refuses a tree it cannot load whole",
            u32::MAX
        ))
    } else if let Some(b) = err.get("unterminatedComment") {
        let path = b["path"].as_str().unwrap_or_default().to_string();
        let line = one_based(b["line"].as_u64().unwrap_or_default());
        put("path", path.clone());
        detail.insert("line".into(), Value::from(line));
        ("unterminatedComment".into(), format!(
            "kernel refusal: unterminatedComment — the HTML comment opened at {path}:{line} is never closed with `-->`; everything after it would be prose, so the kernel refuses a tree it cannot load whole"
        ))
    } else if let Some(f) = err.get("itemCheck").and_then(Value::as_str) {
        put("fault", f.to_string());
        // The owner's D6 (kernel/README.md gap 22, closed at stage 4 final
        // step 3): a parent is read off its line, and a dangling or cyclic
        // link refuses the whole tree — so these two say what to fix.
        let hint = match f {
            "danglingParent" => " — an `@parent` names an id no line of the tree carries (a typo, or a parent whose line is gone); fix or remove the link",
            "parentCycle" => " — the `@parent` links form a cycle, so no item on it has a root; break the cycle",
            _ => "",
        };
        // W-12, README gap 239: the kernel's item invariant is a property of the whole tree, so
        // the refusal carries a fault name and no position — which left a user staring at
        // `fileKindShape` with no file and no line. `tm check` answers exactly that question
        // against the same tree, so the refusal now says so instead of leaving it to be guessed.
        ("itemCheck".into(), format!(
            "kernel refusal: itemCheck — the tree fails the kernel's item invariant ({f}){hint}; the kernel refuses a tree it cannot load whole{CHECK_HINT}"
        ))
    } else if let Some(text) = err.get("planner").and_then(Value::as_str) {
        // The `planner` section's refusal (`PlanWire.PlannerRefusal`, `<name> <key…>`).
        // No shipped verb sends the section until R3's swap; `tm check` asks it
        // since the W-41 repair (`kernel_capacity::planner_request`, README gap 4142),
        // and a `ciDisagrees` names the item, so the problem can name its line.
        let (name, rest) = match text.split_once(' ') {
            Some((n, k)) => (n, Some(k)),
            None => (text, None),
        };
        if let Some(k) = rest {
            put("key", k.to_string());
        }
        if name == "ciDisagrees" {
            if let Some(id) = rest.and_then(|k| k.split(' ').next()) {
                put("id", id.to_string());
            }
        }
        let why = match name {
            "ciDisagrees" => "a candidate's `ci` as tm reads its line is not the `ci` the kernel reads on \
                 the same line, so the kernel refuses to plan the day rather than plan it on one \
                 reader's number (the owner's D80, parity P72) — the two read a line's separators \
                 alike since the owner's D83 (README gaps 32 and 4130, closed), so a refusal here \
                 is a disagreement in what they derive from the line, and a finding",
            "eveningPastTheCalendar" => "the day's evening runs past the calendar's last second (the \
                 owner's D80, parity P71)",
            _ => "a value of the planner request is refused — see PlanWire.lean's `PlannerRefusal`",
        };
        (name.to_string(), format!("kernel refusal: {text} — {why}"))
    } else if let Some(w) = err.get("emit").and_then(|e| e.get("walls")).and_then(Value::as_str) {
        // W-37 (README gap 3139): the `emit` section's walls form, `WallTimer.Refusal`.
        let why = match w {
            "logAbsent" => "the request carried no replay (a `log` section asking for facts)",
            "tzAbsent" => "the request carried no zone table",
            "withCommands" => "the walls form was sent beside commands",
            "badAt" | "badBreak" => "an instant is not a stamp the log's reader accepts",
            // W-39 (README gaps 3432 and 3528): the week grid's `week`, `GridCut.Refusal`.
            "badWeek" => "the week asked for is not a `YYYY-MM-DD` date",
            _ => "see WallTimer.lean's and GridCut.lean's `Refusal`",
        };
        (w.to_string(), format!("kernel refusal: {w} — the day's walls could not be read: {why}"))
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
            (serde_json::json!({"kernel":"keyAbsent"}), "keyAbsent"),
            (serde_json::json!({"kernel":"danglingDep"}), "danglingDep"),
            (serde_json::json!({"kernel":"depCycle"}), "depCycle"),
            (serde_json::json!({"kernel":"siteOutOfRange"}), "siteOutOfRange"),
            // D32, gap 475: the widened shape, which is the only shape the
            // kernel emits — a bare string here would pass against a payload
            // nothing sends.
            (key_collision("dupId", "m1"), "dupId"),
            (key_collision("notADemotion", "m1"), "notADemotion"),
            (key_collision("ambiguousDemotion", "m1"), "ambiguousDemotion"),
            (serde_json::json!({"duplicatePath":"a.md"}), "duplicatePath"),
            (
                serde_json::json!({"badLine":{"path":"a.md","line":3,"why":"noId"}}),
                "badLine",
            ),
            (
                serde_json::json!({"unterminatedComment":{"path":"a.md","line":1}}),
                "unterminatedComment",
            ),
            (serde_json::json!({"itemCheck":"depCycle"}), "itemCheck"),
            // The parse-tier free-text refusals the keyed edit and `add`
            // forward from real user input (Boundary.lean's parseCmd).
            (serde_json::json!("badValue ci"), "badValue"),
            (serde_json::json!("keyNotWired demoted"), "keyNotWired"),
            (serde_json::json!("unknownKey size"), "unknownKey"),
            (serde_json::json!("titleNewline"), "titleNewline"),
            (serde_json::json!("titleTab"), "titleTab"),
            (serde_json::json!("titleId"), "titleId"),
            (serde_json::json!("titleBlank"), "titleBlank"),
            (serde_json::json!("titleEdge"), "titleEdge"),
            // stage 4 step 5: the close refusals and the request's clock
            (serde_json::json!({"kernel":"noTarget"}), "noTarget"),
            (serde_json::json!({"kernel":"noSection"}), "noSection"),
            (serde_json::json!("nowAbsent"), "nowAbsent"),
            (serde_json::json!("badNow"), "badNow"),
            (serde_json::json!("blockMinAbsent"), "blockMinAbsent"),
            (serde_json::json!("badBlockMin"), "badBlockMin"),
            // stage 5 D10 L6: the capacity section's names (design §13.6)
            (serde_json::json!({"capacity":"nowAbsent"}), "nowAbsent"),
            (serde_json::json!({"capacity":"tzAbsent"}), "tzAbsent"),
            (serde_json::json!({"capacity":"badTz unsorted"}), "badTz"),
            (serde_json::json!({"capacity":"badCapacity pLounge.config"}), "badCapacity"),
            (serde_json::json!({"capacity":"badWeight pLounge.config.Fri"}), "badWeight"),
            (serde_json::json!({"capacity":"weightAboveOne pLounge.model.Sat"}), "weightAboveOne"),
            (serde_json::json!({"capacity":"weightPrecision pLounge.model.Wed"}), "weightPrecision"),
            (serde_json::json!({"capacity":"badClock arrival.config.Thu"}), "badClock"),
            (serde_json::json!({"capacity":"badWake"}), "badWake"),
            (serde_json::json!({"capacity":"badCurve energy.home"}), "badCurve"),
            (serde_json::json!({"capacity":"badPrior prior.home"}), "badPrior"),
            (serde_json::json!({"capacity":"badStep prior.lounge"}), "badStep"),
            (serde_json::json!({"capacity":"badLevel prior.home"}), "badLevel"),
            (serde_json::json!({"capacity":"badCap homeMaxCi"}), "badCap"),
            (serde_json::json!({"capacity":"badDay breakMin"}), "badDay"),
            (serde_json::json!({"capacity":"lookaheadTooLong"}), "lookaheadTooLong"),
            // stage 6 step L9
            (serde_json::json!({"capacity":"badAt at"}), "badAt"),
            (serde_json::json!({"capacity":"nowDisagrees at"}), "nowDisagrees"),
            (serde_json::json!({"capacity":"badState state.loc"}), "badState"),
            (serde_json::json!({"capacity":"badPosterior posterior.fullHours"}), "badPosterior"),
            (serde_json::json!({"capacity":"badSleep sleep.shiftConfig"}), "badSleep"),
            (serde_json::json!({"capacity":"day0WithoutLog"}), "day0WithoutLog"),
            (serde_json::json!({"capacity":"badBins"}), "badBins"),
            (serde_json::json!({"capacity":"badSafety"}), "badSafety"),
            (serde_json::json!({"capacity":"badDefaultPriority"}), "badDefaultPriority"),
            // stage 5 D10 L8
            (serde_json::json!({"capacity":"tooManyCandidates"}), "tooManyCandidates"),
            (serde_json::json!({"capacity":"badCandidate 3 ci"}), "badCandidate"),
            (serde_json::json!({"capacity":"capacityWithCommands"}), "capacityWithCommands"),
        ] {
            let issue = refusal(&payload);
            assert_eq!(issue.name, name);
            assert!(issue.message.contains(name), "{}", issue.message);
            assert_eq!(issue.detail["refusal"], name);
        }
    }

    /// **A store key is not an `^id`** (W-15 repair, audit defect 3; gap 475).
    ///
    /// D31's widened grammar keys a line with no `^id` by `Field.titleKey`, and
    /// that key is **never written into a file**. The three key-collision
    /// refusals used to print `^{key}`, so a real tree answered *"two lines in
    /// the tree carry ^read the Lean 4 metaprogramming book"* — a token that
    /// appears nowhere the user could grep. None of the three may spell a `^`
    /// in front of the key again.
    ///
    /// `dupId` also may not send the reader to `tm check`. Gap 239 added that
    /// pointer on the premise that `tm check` answers precisely; for this class
    /// it answered *"no problems"*. D32 (gap 476) fixed `tm check` — it now
    /// prints this very refusal at both lines — and the pointer still stays
    /// off, because the message already names them.
    ///
    /// **Widened at W-16 for D32**: the payload is the kernel's widened one,
    /// so this test now also pins that the message and the `--json` detail
    /// carry *both* colliding lines.
    fn key_collision(kind: &str, key: &str) -> Value {
        serde_json::json!({ kind: {
            "key": key,
            "a": { "path": "inbox.md", "line": 3 },
            "b": { "path": "week/2026-W38.md", "line": 11 },
        }})
    }

    #[test]
    fn a_key_collision_names_a_key_and_never_invents_an_id_token() {
        let title = "read the Lean 4 metaprogramming book";
        for kind in ["dupId", "notADemotion", "ambiguousDemotion"] {
            let issue = refusal(&key_collision(kind, title));
            assert_eq!(issue.name, kind);
            assert!(issue.message.contains(title), "{kind}: {}", issue.message);
            assert!(
                !issue.message.contains(&format!("^{title}")),
                "{kind} still spells the synthesised key as an id token: {}",
                issue.message
            );
            // The key reaches `--json` as the key, not as an id token.
            assert_eq!(issue.detail["key"], title);
            assert!(!issue.detail.contains_key("id"), "{kind}: {:?}", issue.detail);
        }
        let dup = refusal(&key_collision("dupId", title));
        assert!(
            !dup.message.contains(CHECK_HINT),
            "dupId still points at a verb that reports nothing: {}",
            dup.message
        );
        // A line that really does spell its id reads the same way, minus the lie.
        let real = refusal(&key_collision("dupId", "a1"));
        assert!(real.message.contains("`a1`"), "{}", real.message);
    }

    /// **A collision names both lines, 1-based, in the message and in
    /// `--json`** — D32 item 1, gap 475.
    ///
    /// Before it the three refusals carried the key and nothing else, so the
    /// one class D31 made reachable was also the one class with no token in
    /// any file to grep for: the reader was told a collision existed and not
    /// where. The kernel's 0-based wire lines come out 1-based here, through
    /// the same `one_based` gap 479 installed, in the English **and** in the
    /// detail, so one refusal never carries two conventions.
    #[test]
    fn a_key_collision_names_both_lines() {
        for kind in ["dupId", "notADemotion", "ambiguousDemotion"] {
            let issue = refusal(&key_collision(kind, "lunch"));
            assert!(
                issue.message.contains("inbox.md:4") && issue.message.contains("week/2026-W38.md:12"),
                "{kind} does not name both lines: {}",
                issue.message
            );
            assert_eq!(issue.detail["a"]["path"], "inbox.md");
            assert_eq!(issue.detail["a"]["line"], 4);
            assert_eq!(issue.detail["b"]["path"], "week/2026-W38.md");
            assert_eq!(issue.detail["b"]["line"], 12);
        }
    }

    /// **One `file:line` convention out of one binary** (W-15 repair, gap 479).
    ///
    /// `Boundary.lean` counts a document's lines from 0 ("0-based, as
    /// `badLine`"); `tm check` and every other `file:line` this binary prints
    /// counts from 1. A tree whose thirteenth line is `- [ ] no id on this
    /// line` used to answer `backlog.md:12`, pointing at the line above.
    #[test]
    fn a_loader_position_is_printed_the_way_tm_check_prints_one() {
        let bad = refusal(&serde_json::json!(
            {"badLine": {"path": "backlog.md", "line": 12, "why": "Tm.PErr.noId"}}
        ));
        assert!(bad.message.contains("backlog.md:13"), "{}", bad.message);
        assert_eq!(bad.detail["line"], 13);

        let cmt = refusal(&serde_json::json!({"unterminatedComment": {"path": "a.md", "line": 0}}));
        assert!(cmt.message.contains("a.md:1"), "{}", cmt.message);
        assert_eq!(cmt.detail["line"], 1);
    }

    /// Stage 5 D9 B4 (design §10.3): the `log` section's refusals are host
    /// defects, so each is a loud fault that names the refusal and its field.
    #[test]
    fn every_log_refusal_is_a_loud_fault_naming_its_field() {
        for (payload, name, key, val) in [
            (serde_json::json!({"log":"tzAbsent"}), "tzAbsent", None, Value::Null),
            (serde_json::json!({"log":"tooManyLines"}), "tooManyLines", None, Value::Null),
            (serde_json::json!({"log":{"badTz":"unsorted"}}), "badTz", Some("why"), Value::from("unsorted")),
            (serde_json::json!({"log":{"badLogReq":"from"}}), "badLogReq", Some("field"), Value::from("from")),
            (serde_json::json!({"log":{"renderNotInTail":{"line":45101}}}), "renderNotInTail", Some("line"), Value::from(45101)),
            (serde_json::json!({"log":{"undoReach":{"line":45171,"below":45100}}}), "undoReach", Some("line"), Value::from(45171)),
            (serde_json::json!({"log":{"nowBelowLedger":{"now":739860,"ledgerDay":739870}}}), "nowBelowLedger", Some("line"), Value::from(739860)),
            (serde_json::json!({"log":{"badCkpt":"items"}}), "badCkpt", Some("field"), Value::from("items")),
            (serde_json::json!({"log":{"counterOverflow":"facts.items"}}), "counterOverflow", Some("field"), Value::from("facts.items")),
            (serde_json::json!({"log":"cutMismatch"}), "cutMismatch", None, Value::Null),
            (serde_json::json!({"log":"zone"}), "zone", None, Value::Null),
        ] {
            let issue = refusal(&payload);
            assert!(issue.is_fault(), "{name}: {}", issue.message);
            assert_eq!(issue.detail["logRefusal"], name);
            assert!(issue.message.contains(name), "{}", issue.message);
            if let Some(k) = key {
                assert_eq!(issue.detail[k], val, "{name}");
            }
        }
    }

    /// The same names, from the real kernel: each request below is refused by
    /// `Boundary.lean`'s `readLogSection` with the name the host maps.
    #[test]
    fn the_kernel_names_its_log_refusals() {
        let utc = r#"{"key":"UTC","base":"+00:00:00","then":[]}"#;
        let many = vec!["null"; 8_193].join(",");
        for (req, name) in [
            (r#"{"docs":[],"log":{"from":1,"lines":[],"terminated":true}}"#.to_string(), "tzAbsent"),
            (
                r#"{"docs":[],"tz":{"key":"UTC","base":"+00:00:00","then":[["2026-03-08T08:00:00Z","+00:00:00"],["2026-03-08T07:00:00Z","+01:00:00"]]}}"#.to_string(),
                "badTz",
            ),
            (format!(r#"{{"docs":[],"tz":{utc},"log":{{"from":1,"lines":[{many}],"terminated":true}}}}"#), "tooManyLines"),
            (format!(r#"{{"docs":[],"tz":{utc},"log":{{"from":0,"lines":[],"terminated":true}}}}"#), "badLogReq"),
            (
                format!(r#"{{"docs":[],"tz":{utc},"log":{{"from":5,"lines":["x"],"terminated":true,"want":{{"render":[4]}}}}}}"#),
                "renderNotInTail",
            ),
            // W3: G0 at the op, a guard, and the checkpoint's own decoder.
            (format!(r#"{{"docs":[],"now":"2026-09-15","tz":{utc},"log":{{"from":2,"lines":[],"terminated":true,"want":{{"facts":true}}}}}}"#), "cutMismatch"),
            (format!(r#"{{"docs":[],"now":"2026-09-15","tz":{utc},"log":{{"ckpt":{{}},"from":1,"lines":[],"terminated":true}}}}"#), "badCkpt"),
        ] {
            let raw = tm_kernel_ffi::call(&req).expect("kernel call");
            let resp: Value = serde_json::from_str(&raw).expect("json");
            let issue = refusal(&resp["err"]);
            assert_eq!(issue.detail["logRefusal"], name, "{raw}");
        }
    }

    /// Stage 5 D10 L6: a capacity refusal carries the key it names.
    #[test]
    fn a_capacity_refusal_carries_its_key() {
        let issue = refusal(&serde_json::json!({"capacity":"weightPrecision pLounge.model.Wed"}));
        assert_eq!(issue.name, "weightPrecision");
        assert_eq!(issue.detail["key"], "pLounge.model.Wed");
        assert!(issue.message.contains("more than 18 decimal places"), "{}", issue.message);
        let bare = refusal(&serde_json::json!({"capacity":"badWake"}));
        assert!(!bare.detail.contains_key("key"));
    }

    /// The owner's D6: a dangling or cyclic `@parent` refuses the whole tree as
    /// `itemCheck`, and the message carries the fault's name and what to fix.
    #[test]
    fn the_parent_faults_are_named_with_what_to_fix() {
        for (fault, says) in [("danglingParent", "names an id no line"), ("parentCycle", "form a cycle")] {
            let issue = refusal(&serde_json::json!({ "itemCheck": fault }));
            assert_eq!(issue.name, "itemCheck");
            assert_eq!(issue.detail["fault"], fault);
            assert!(issue.message.contains(fault), "{}", issue.message);
            assert!(issue.message.contains(says), "{}", issue.message);
        }
    }
    /// Stage 5 A2 (design §5.1; kernel/README.md gaps 42 and 43, closed): the
    /// kernel's JSON reader takes a request exactly when serde_json takes the
    /// same bytes, on the numerals and surrogate escapes the design names.  A
    /// numeral is read at a key no field reads, so only the parser answers; a
    /// line read through a pair comes back as the character serde decodes.
    /// `kernel/tm-kernel-ffi/tests/kernel.rs` pins the kernel's texts.
    #[test]
    fn the_kernel_reads_numerals_and_surrogates_as_serde_reads_them() {
        for n in [
            "-0.5", "1e5", "1E+05", "2.50e-3", "0", "0.5", "-0", "007", "-01", "01.5", "1.",
            "1e", "1e+", "-", "+1", ".5",
        ] {
            let req = format!(r#"{{"docs":[],"x":{n}}}"#);
            let serde_ok = serde_json::from_str::<Value>(&req).is_ok();
            let raw = tm_kernel_ffi::call(&req).expect("kernel call");
            assert_eq!(!raw.contains("bad json"), serde_ok, "{n}: the kernel answered {raw}");
        }
        for esc in [
            r"\ud83d\ude00", r"\uD83D\uDE00", r"\ud800\udc00", r"\ud83d", r"\ude00",
            r"\ud83d\u0041", r"\ud83dx", r"\ud83d\ud83d",
        ] {
            let req = format!(r#"{{"docs":[{{"path":"w.md","lines":["{esc}"]}}],"cmds":[]}}"#);
            let raw = tm_kernel_ffi::call(&req).expect("kernel call");
            match serde_json::from_str::<Value>(&req) {
                Ok(v) => {
                    let resp: Value = serde_json::from_str(&raw).expect("json");
                    assert_eq!(resp["ok"]["docs"][0]["lines"][0], v["docs"][0]["lines"][0], "{esc}: {raw}");
                }
                Err(_) => assert!(raw.contains("bad json: badEscape surrogateEscape"), "{esc}: {raw}"),
            }
        }
        // A request `-3` is a number to serde; the kernel refuses it by the
        // field's reader, never as `bad json`.
        let req = r#"{"docs":[],"cmds":[{"op":"est","id":"m1","min":-3}]}"#;
        assert!(serde_json::from_str::<Value>(req).is_ok());
        assert_eq!(tm_kernel_ffi::call(req).expect("kernel call"), r#"{"err":"Natural number expected"}"#);
    }

    /// The report decoder, end to end against the real kernel: a week close
    /// sent through `tm_kernel_ffi::call` comes back with the per-item list
    /// `Boundary.lean`'s `the_week_close_reports_each_line` decides, and every
    /// field decodes through its smart constructor.
    #[test]
    fn a_real_close_report_decodes_through_the_smart_constructors() {
        let request = r##"{"now":"2026-09-07","blockMin":50,"docs":[{"path":"week/2026-W36.md","grain":1,"ix":105694,"lines":["# Tasks","- [ ] 4 6b Rollback path passes tests ^m2","- [x] 2 1b Send the draft ^t1","- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1"]},{"path":"week/2026-W37.md","grain":1,"ix":105695,"lines":["# Tasks"]},{"path":"month/2026-09.md","grain":2,"ix":24308,"lines":["# Outcomes","# Demoted"]}],"cmds":[{"op":"close","grain":1}]}"##;
        let raw = tm_kernel_ffi::call(request).expect("kernel call");
        let resp: Value = serde_json::from_str(&raw).expect("json");
        let n = resp["ok"]["docs"].as_array().expect("docs").len();
        let report = decode_report(&resp["ok"]["report"], n).expect("report decodes");
        // Source order (kernel/README.md gap 59): `^m2` at rank 1 before `^x1`
        // at rank 3.
        assert_eq!(
            report,
            vec![
                CloseEntry {
                    id: "m2".into(),
                    grain: Grain::Week,
                    did: CloseDid::Copy,
                    from: 0,
                    to: 2,
                    stamp: Some(Stamp::Week(36)),
                    minutes: Minutes::new(300, 1),
                },
                CloseEntry {
                    id: "x1".into(),
                    grain: Grain::Week,
                    did: CloseDid::Carry,
                    from: 0,
                    to: 1,
                    stamp: None,
                    minutes: Minutes::new(120, 1),
                },
            ],
            "{raw}"
        );
    }

    /// The decoder bites, by field, and does not over-bite: an empty report
    /// and an unknown family beside `closes` decode.
    #[test]
    fn the_report_decoder_refuses_each_malformed_field_by_name() {
        let ok = serde_json::json!({"id":"m2","grain":1,"did":"copy","from":0,"to":2,"stamp":"W36","min":{"num":300,"den":1}});
        let with = |k: &str, v: Value| {
            let mut e = ok.clone();
            e[k] = v;
            serde_json::json!({ "closes": [e] })
        };
        assert_eq!(decode_report(&serde_json::json!({"closes":[]}), 3), Ok(vec![]));
        assert!(decode_report(&serde_json::json!({"closes":[],"diagnostics":[]}), 3).is_ok());
        assert!(decode_report(&serde_json::json!({ "closes": [ok.clone()] }), 3).is_ok());
        for (report, why) in [
            (serde_json::json!({}), "no closes"),
            (with("did", serde_json::json!("moved")), "unknown did"),
            (with("did", serde_json::json!("copymerging")), "unknown did"),
            (with("grain", serde_json::json!(3)), "grain out of range"),
            (with("to", serde_json::json!(3)), "to is not a document"),
            (with("stamp", serde_json::json!("M09")), "bad stamp"),
            (with("stamp", serde_json::json!("W3")), "bad stamp"),
            (with("min", serde_json::json!({"num":300,"den":0})), "positive denominator"),
            (with("min", serde_json::json!(6.0)), "positive denominator"),
        ] {
            let err = decode_report(&report, 3).expect_err(why);
            assert!(err.contains(why), "{err} / {why}");
        }
    }
}
