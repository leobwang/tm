//! **The replay cache and the kernel's `log` op, host side** (stage 5 D9 W3; design
//! `kernel/design/stage5/stage5-D9-D10-design.md` §9.6 host policy, §9.7 genesis, §9.8
//! persistence and integrity, §10 the wire, §11.1's merge).
//!
//! **This is the binary's only reader of the log, and since S2 its only writer too.**
//! `Ctx::replay_with` calls [`replay_scoped`] (the switch S, `2b26be3`, which deleted
//! Rust's own reader: `tm-core/src/log.rs` fell 3,609 lines to 1,806), and every appending
//! verb sends its typed event through [`render_events`], which asks the kernel for the exact
//! bytes to append (D16's S2, `47a0443`). The log's grammar therefore has one definition, the
//! kernel's, on both sides. *(This paragraph said "Nothing in the binary calls this yet"
//! for two commits after it stopped being true — W-12's audit, README gap 238.)*
//!
//! What lives here:
//! * **The byte split** ([`split`]): lines on `\n`, `None` for a line that is not UTF-8, and
//!   whether the last line had its `\n` (`terminated`, CRIT 8), with each line's end offset
//!   for the prefix digest.
//! * **The wire** ([`request`], [`log_call`]): one `log` request, its answer, and the
//!   refusals of §10.3 by name ([`Refusal`]). The checkpoint crosses as **raw JSON text**,
//!   byte for byte: the kernel's reader wants its keys in build order (W1's disagreement 12),
//!   so it is never parsed into a map on this side.
//! * **Genesis** ([`genesis`], §9.7): chunks of at most [`CHUNK_LINES`] lines and
//!   [`CHUNK_BYTES`] bytes, every call resealing, a stack of checkpoints, and on a guard's
//!   refusal a pop to exactly the entry the refusal cannot name, the lines from its cut through
//!   the refusing chunk resent in one call. A call past the **resend cap**
//!   ([`RESEND_LINES`], [`RESEND_BYTES`], gap 102's memory gate) is not sent: genesis fails
//!   with the named fault [`GenesisError::ReachTooFar`] (OWNER Q9 (iii), D18).
//! * **The files** under `.tm/cache/replay/` (D13): `ckpt.json` (format 4 since the owner's D93:
//!   the kernel id, the zone key, the prefix's line count, byte count and FNV-1a-64, the
//!   generation and the previous one, the manifest of month files and the DIGEST of each —
//!   `digests`, FNV-1a-64 of the file's bytes — `meta`, and the checkpoint), immutable
//!   `sealed/YYYY-MM.g<gen>.json` month files, and `tz.json` (`tz_table`'s). Every write is a
//!   temporary file and a rename; a reseal writes new month files, then `ckpt.json`, then
//!   collects month files named by neither manifest and older than ten minutes.
//! * **The snapshot rule** (CRIT 7): a process reads `ckpt.json` once, loads month files only
//!   by that manifest, and uses day records only below its `ledgerDay` and window records only
//!   below its `horizon`. A missing month file re-reads `ckpt.json` once, then rebuilds in memory.
//! * **Integrity** (G9, §9.8): the prefix digest is checked on every call; a differing length,
//!   a prefix not ending in `\n`, a differing FNV, zone key, format or kernel id goes straight
//!   to genesis. **A sealed month file is checked against its digest every time it is read**
//!   (the owner's D93, README gap 4246): one that does not match — corrupted or hand-edited — is
//!   never served and never merged into a later generation; the cache is rebuilt from the log,
//!   as for a month file that is missing (README gap 3711), and a `ckpt.json` written before
//!   D93 (format 3, no digests) is rebuilt once.
//! * **Host policy** (§9.6): reseal when more than [`FOLDABLE_TRIGGER`] foldable lines were
//!   appended since the snapshot was written (`logLines`, W4's gap 124: a tail a reseal could not
//!   fold does not reseal again on every call), or when `now` is more than two days past the ledger
//!   day and the checkpoint was not sealed today (the back-off, CRIT 19).
//! * **An unwritable cache** (CRIT 26) is not fatal: one named notice per process, and the
//!   checkpoint is kept in memory for that process.

// **The module-wide `#![allow(dead_code)]` is gone** (W-12, README gap 238). It was noise
// control for the period when nothing under `tm/src` called this file: measured with the
// attribute removed, `cargo check -p tm --all-targets` reported **92** unreachable items, and
// the comment here promised the attribute would be deleted at S, "when `replay_scoped` becomes
// the binary's one reader". S and S2 landed and it was not. Measured again now, the same
// command reports **4**, with or without `--all-targets`; each of the four carries its own
// `#[allow(dead_code)]` and says why it is kept. The cost the old comment named is paid off
// with it: `cargo test --workspace`'s "0 warnings" now does say that a function added to this
// file is reachable or tested.
//
// The other instrument stays, and is the sharper one:
// `tests/kernel_log_door.rs::every_door_function_the_switch_calls_is_exercised_here` requires
// every `pub fn` below the DOOR banner to be called by name in that file. It found
// [`max_line_of`] shipped and called by nothing at all — not the binary, not a test.

use chrono::{DateTime, FixedOffset, NaiveDate};
use chrono_tz::Tz;
use serde_json::value::RawValue;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, SystemTime};

/// The format `ckpt.json` carries; any other goes to genesis. **4 since the owner's D93** (W-43 track H,
/// README gap 4246): the manifest's month files each carry a digest, so a cache written before it — format 3,
/// with none — is rebuilt once rather than trusted. **5 since the campaign's D98** (W-44 track H, README gap
/// 4394): the checkpoint carries a digest of its own text ([`Snapshot::to_text`]), so a checkpoint written before
/// it — format 4, with none — is rebuilt once, as D93's format 3 was.
pub const FORMAT: u64 = 5;
/// The cache directory, relative to the plan root (D13; `tm init` excludes `.tm/cache/` from sync).
pub const CACHE_DIR: &str = ".tm/cache/replay";
/// The checkpoint's file inside the cache directory.
pub const CKPT_FILE: &str = "ckpt.json";
/// The month files' directory inside the cache directory.
pub const SEALED_DIR: &str = "sealed";
/// Genesis' chunk bounds (§9.7, lowered at W3 with the resend cap): at most this many lines …
pub const CHUNK_LINES: usize = 4_096;
/// … and at most this many bytes of lines, each counted with its newline. Half the resend cap each way, so a pop
/// resends the refusing chunk and the one before it in one call within the cap.
pub const CHUNK_BYTES: usize = 786_432;
/// **The resend cap's line bound** (gap 102, W3): the kernel's per-call bound (`Boundary.maxLogLines`), the largest power
/// of two whose measured peak RSS for one resend-shaped call (a reseal and facts) is at most 200 MiB: 111.5 MiB at 8,192
/// generated lines by `logbench` (f)'s committed table; 16,384 lines measured 218.9 MiB (README "Stage 5 D9 W3").
pub const RESEND_LINES: usize = 8_192;
/// **The resend cap's byte bound** (gap 102, W3): 1,536 KiB, whose worst shape (8,192 lines of long note text, the
/// kernel's per-character cost) measured 174.1 MiB in `logbench` (f)'s committed table; 1,792 KiB measured 211.9 MiB.
pub const RESEND_BYTES: usize = 1_572_864;
/// Days a reseal leaves unfolded (§9.6).
pub const KEEP_DAYS: u64 = 2;
/// A tail of more foldable lines than this reseals (§9.6).
pub const FOLDABLE_TRIGGER: usize = 512;
/// G2's fence, in seconds (W2's disagreement 2: three days, not two).
pub const FENCE_SEC: u64 = 259_200;
/// Month files named by neither manifest are collected once older than this (§9.8).
pub const COLLECT_AFTER: Duration = Duration::from_secs(600);
/// The most sealed records one request carries (§10.4).
// Dead since S: the `Dates` route that would cap on it is [`sealed_between`], also dead.
// Kept because §10.4's bound is the kernel's and the number belongs next to the other caps.
#[allow(dead_code)]
pub const MAX_SEALED_IN: usize = 62;

/// The kernel this binary links (`tm-kernel-ffi/build.rs`: FNV-1a-64 of its archive). A checkpoint written by another
/// kernel goes to genesis (§9.8).
pub fn kernel_id() -> &'static str {
    tm_kernel_ffi::KERNEL_ID
}

/// FNV-1a-64 (§9.8's prefix digest, and since the owner's D93 each sealed month file's — [`month_digest`]).
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

// ---------------------------------------------------------------------------
// The byte split.

/// **A log as the host sends it** (§10.1): each line's text or `None` when it is not UTF-8, each line's end offset (past
/// its `\n` when it has one), and whether the last line had its `\n`.
#[derive(Clone, Debug, PartialEq)]
pub struct Split {
    pub lines: Vec<Option<String>>,
    pub ends: Vec<usize>,
    pub terminated: bool,
}

impl Split {
    /// The byte length of lines `1..=n` (0 for none).
    pub fn prefix_bytes(&self, n: usize) -> usize {
        if n == 0 { 0 } else { self.ends[n - 1] }
    }
    /// The byte length of lines `a+1..=b`.
    pub fn bytes_between(&self, a: usize, b: usize) -> usize {
        self.prefix_bytes(b) - self.prefix_bytes(a)
    }
}

/// **Split a log's bytes into lines** (CRIT 8): the empty segment after a final `\n` is not a line.
pub fn split(bytes: &[u8]) -> Split {
    let mut lines = Vec::new();
    let mut ends = Vec::new();
    let mut start = 0;
    for (i, &b) in bytes.iter().enumerate() {
        if b == b'\n' {
            lines.push(std::str::from_utf8(&bytes[start..i]).ok().map(str::to_owned));
            ends.push(i + 1);
            start = i + 1;
        }
    }
    let terminated = start == bytes.len();
    if !terminated {
        lines.push(std::str::from_utf8(&bytes[start..]).ok().map(str::to_owned));
        ends.push(bytes.len());
    }
    Split { lines, ends, terminated }
}

// ---------------------------------------------------------------------------
// The wire.

/// **The reseal policy** (§9.6): days left unfolded, and the undo stack's pin.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Policy {
    pub keep_days: u64,
    pub max_line: Option<u64>,
}

/// **What a call asks for** (§10.1's `want`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Want {
    pub facts: bool,
    pub headers_from: Option<u64>,
    pub render: Vec<u64>,
}

/// **`meta`** (§9.2): the checkpoint's cut, horizons, reseal day and G2 instants (`[sec, ns]`).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Meta {
    pub cut: u64,
    pub ledger_day: u64,
    pub horizon: u64,
    pub reseal_day: u64,
    pub max_t: Option<(u64, u64)>,
    pub future_floor: Option<(u64, u64)>,
}

fn instant_of(v: &Value) -> Result<Option<(u64, u64)>, String> {
    match v {
        Value::Null => Ok(None),
        Value::Array(a) if a.len() == 2 => match (a[0].as_u64(), a[1].as_u64()) {
            (Some(s), Some(n)) => Ok(Some((s, n))),
            _ => Err(format!("an instant {v}")),
        },
        _ => Err(format!("an instant {v}")),
    }
}

fn instant_json(i: Option<(u64, u64)>) -> Value {
    match i {
        None => Value::Null,
        Some((s, n)) => serde_json::json!([s, n]),
    }
}

impl Meta {
    /// Read the kernel's `meta` object.
    pub fn from_json(v: &Value) -> Result<Meta, String> {
        let n = |k: &str| v.get(k).and_then(Value::as_u64).ok_or_else(|| format!("meta.{k}: {v}"));
        Ok(Meta {
            cut: n("cut")?,
            ledger_day: n("ledgerDay")?,
            horizon: n("horizon")?,
            reseal_day: n("resealDay")?,
            max_t: instant_of(v.get("maxT").unwrap_or(&Value::Null))?,
            future_floor: instant_of(v.get("futureFloor").unwrap_or(&Value::Null))?,
        })
    }
    pub fn to_json(&self) -> Value {
        serde_json::json!({"cut": self.cut, "ledgerDay": self.ledger_day, "horizon": self.horizon,
            "resealDay": self.reseal_day, "maxT": instant_json(self.max_t), "futureFloor": instant_json(self.future_floor)})
    }
}

/// **A refusal of the `log` op** (§10.3), by name. The first five are the guards; each names its bound (§9.7's pops).
#[derive(Clone, Debug, PartialEq)]
pub enum Refusal {
    UndoReach { line: u64, below: u64 },
    WakeBehindCut { line: u64, t: (u64, u64) },
    SealedDay { line: u64, day: u64 },
    SealedWindow { line: u64, day: u64 },
    NowBelowLedger { now: u64, ledger_day: u64 },
    BadCkpt(String),
    CutMismatch,
    Zone,
    /// A host defect or an impossible log (`tzAbsent`, `badLogReq`, `tooManyLines`, `counterOverflow`, …): a loud fault.
    Fault(Value),
}

impl Refusal {
    /// Read `{"log": …}` from an `err` payload.
    pub fn from_err(err: &Value) -> Refusal {
        let Some(l) = err.get("log") else { return Refusal::Fault(err.clone()) };
        let num = |v: &Value, k: &str| v.get(k).and_then(Value::as_u64);
        match l {
            Value::String(s) if s == "cutMismatch" => Refusal::CutMismatch,
            Value::String(s) if s == "zone" => Refusal::Zone,
            Value::Object(m) if m.len() == 1 => {
                let (k, v) = m.iter().next().expect("one key");
                let r = match k.as_str() {
                    "undoReach" => num(v, "line").zip(num(v, "below")).map(|(line, below)| Refusal::UndoReach { line, below }),
                    "wakeBehindCut" => num(v, "line")
                        .zip(v.get("t").and_then(|t| instant_of(t).ok().flatten()))
                        .map(|(line, t)| Refusal::WakeBehindCut { line, t }),
                    "sealedDay" => num(v, "line").zip(num(v, "day")).map(|(line, day)| Refusal::SealedDay { line, day }),
                    "sealedWindow" => num(v, "line").zip(num(v, "day")).map(|(line, day)| Refusal::SealedWindow { line, day }),
                    "nowBelowLedger" => {
                        num(v, "now").zip(num(v, "ledgerDay")).map(|(now, ledger_day)| Refusal::NowBelowLedger { now, ledger_day })
                    }
                    "badCkpt" => v.as_str().map(|f| Refusal::BadCkpt(f.to_string())),
                    _ => None,
                };
                r.unwrap_or_else(|| Refusal::Fault(err.clone()))
            }
            _ => Refusal::Fault(err.clone()),
        }
    }

    /// The guards (G1–G4): a checkpoint built from a prefix could otherwise be wrong.
    pub fn is_guard(&self) -> bool {
        matches!(
            self,
            Refusal::UndoReach { .. }
                | Refusal::WakeBehindCut { .. }
                | Refusal::SealedDay { .. }
                | Refusal::SealedWindow { .. }
                | Refusal::NowBelowLedger { .. }
        )
    }

    /// The line and kind a refusal names (for [`GenesisError::ReachTooFar`]).
    pub fn line_and_kind(&self) -> (u64, &'static str) {
        match self {
            Refusal::UndoReach { line, .. } => (*line, "undoReach"),
            Refusal::WakeBehindCut { line, .. } => (*line, "wakeBehindCut"),
            Refusal::SealedDay { line, .. } => (*line, "sealedDay"),
            Refusal::SealedWindow { line, .. } => (*line, "sealedWindow"),
            Refusal::NowBelowLedger { .. } => (0, "nowBelowLedger"),
            Refusal::BadCkpt(_) => (0, "badCkpt"),
            Refusal::CutMismatch => (0, "cutMismatch"),
            Refusal::Zone => (0, "zone"),
            Refusal::Fault(_) => (0, "fault"),
        }
    }

    /// **May a stack entry be the start a refusal pops to?** (§9.7's table; the fence is G2's three days.)
    pub fn pop_ok(&self, m: &Meta) -> bool {
        match self {
            Refusal::UndoReach { below, .. } => m.cut < *below,
            Refusal::WakeBehindCut { t, .. } => {
                m.max_t.is_none_or(|x| x < *t) && m.future_floor.is_none_or(|f| t.0 + FENCE_SEC < f.0)
            }
            Refusal::SealedDay { day, .. } => m.ledger_day <= *day,
            Refusal::SealedWindow { day, .. } => m.horizon <= *day,
            _ => false,
        }
    }
}

/// **What a reseal emits** (§9.4): the checkpoint as the kernel wrote it, its `meta`, and the records it sealed, each
/// as raw JSON with its day.
#[derive(Clone, Debug, PartialEq)]
pub struct Resealed {
    pub ckpt: String,
    pub meta: Meta,
    pub days: Vec<(u64, String)>,
    pub window: Vec<(u64, String)>,
}

/// **The `log` answer** (§10.2).
#[derive(Clone, Debug, PartialEq)]
pub struct LogAnswer {
    pub lines: u64,
    pub warnings: Value,
    pub facts: Option<Value>,
    pub headers: Value,
    pub render: Value,
    pub reseal: Option<Resealed>,
}

/// **One `log` section** (§10.1), built as text so the checkpoint and the records go in byte for byte.
///
/// Split out of [`request`] at stage 6 step L9, because a **capacity** request now carries one
/// too: day 0 of the lookahead is the kernel's own, derived from this call's replay through D24's
/// seam ([`capacity_log_section`]).
#[allow(clippy::too_many_arguments)]
pub fn log_section(
    ckpt: Option<&str>,
    from: u64,
    lines: &[Option<String>],
    terminated: bool,
    reseal: Option<Policy>,
    want: &Want,
    sealed: Option<(&[String], &[String])>,
) -> String {
    let mut r = String::with_capacity(lines.iter().map(|l| l.as_ref().map_or(4, |s| s.len() + 8)).sum::<usize>() + 4096);
    r.push_str(r#"{"ckpt":"#);
    r.push_str(ckpt.unwrap_or("null"));
    r.push_str(&format!(r#","from":{from},"lines":"#));
    r.push_str(&serde_json::to_string(lines).expect("lines serialise"));
    r.push_str(&format!(r#","terminated":{terminated},"reseal":"#));
    match reseal {
        None => r.push_str("null"),
        Some(p) => r.push_str(&serde_json::json!({"keepDays": p.keep_days, "maxLine": p.max_line}).to_string()),
    }
    r.push_str(&format!(
        r#","want":{{"facts":{},"headersFrom":{},"render":{}}}"#,
        want.facts,
        want.headers_from.map_or("null".to_string(), |h| h.to_string()),
        serde_json::to_string(&want.render).expect("render serialises")
    ));
    r.push_str(r#","sealed":"#);
    match sealed {
        None => r.push_str("null"),
        Some((days, window)) => {
            r.push_str(r#"{"days":["#);
            r.push_str(&days.join(","));
            r.push_str(r#"],"window":["#);
            r.push_str(&window.join(","));
            r.push_str("]}");
        }
    }
    r.push('}');
    r
}

/// **One `log` request** (§10.1): the section, with the empty documents, the clock and the zone
/// the op needs around it.
#[allow(clippy::too_many_arguments)]
pub fn request(
    now: &str,
    tz: &Value,
    ckpt: Option<&str>,
    from: u64,
    lines: &[Option<String>],
    terminated: bool,
    reseal: Option<Policy>,
    want: &Want,
    sealed: Option<(&[String], &[String])>,
) -> String {
    wrap_log(now, tz, &log_section(ckpt, from, lines, terminated, reseal, want, sealed))
}

/// A `log` section wrapped as [`request`] wraps it: the empty documents, the clock and the zone around it.
fn wrap_log(now: &str, tz: &Value, section: &str) -> String {
    let mut r = String::with_capacity(section.len() + 4096);
    r.push_str(r#"{"docs":[],"now":"#);
    r.push_str(&Value::String(now.to_string()).to_string());
    r.push_str(r#","tz":"#);
    r.push_str(&tz.to_string());
    r.push_str(r#","log":"#);
    r.push_str(section);
    r.push('}');
    r
}

type RawMap<'a> = BTreeMap<String, &'a RawValue>;

fn raw_map(text: &str) -> Result<RawMap<'_>, String> {
    serde_json::from_str(text).map_err(|e| format!("not an object: {e}"))
}

fn record_day(raw: &str) -> Result<u64, String> {
    let v: Value = serde_json::from_str(raw).map_err(|e| format!("a record: {e}"))?;
    v.get(0).and_then(Value::as_u64).ok_or_else(|| format!("a record without its day: {}", &raw[..raw.len().min(80)]))
}

/// **Read a response's `log`**: the answer, a refusal by name, or a fault (a response that is not the kernel's shape).
pub fn read_response(resp: &str) -> Result<Result<LogAnswer, Refusal>, String> {
    let top = raw_map(resp)?;
    if let Some(err) = top.get("err") {
        let e: Value = serde_json::from_str(err.get()).map_err(|e| e.to_string())?;
        return Ok(Err(Refusal::from_err(&e)));
    }
    let ok = raw_map(top.get("ok").ok_or("no ok")?.get())?;
    let log = raw_map(ok.get("log").ok_or("no log")?.get())?;
    let val = |k: &str| -> Result<Value, String> {
        serde_json::from_str(log.get(k).ok_or_else(|| format!("no log.{k}"))?.get()).map_err(|e| e.to_string())
    };
    let facts = val("facts")?;
    let reseal_raw = log.get("reseal").ok_or("no log.reseal")?.get();
    let reseal = if reseal_raw == "null" {
        None
    } else {
        let m = raw_map(reseal_raw)?;
        let get = |k: &str| m.get(k).copied().ok_or_else(|| format!("no reseal.{k}"));
        let meta: Value = serde_json::from_str(get("meta")?.get()).map_err(|e| e.to_string())?;
        let days: Vec<&RawValue> = serde_json::from_str(get("days")?.get()).map_err(|e| e.to_string())?;
        let window: Vec<&RawValue> = serde_json::from_str(get("window")?.get()).map_err(|e| e.to_string())?;
        Some(Resealed {
            ckpt: get("ckpt")?.get().to_string(),
            meta: Meta::from_json(&meta)?,
            days: days.iter().map(|r| Ok((record_day(r.get())?, r.get().to_string()))).collect::<Result<_, String>>()?,
            window: window.iter().map(|r| Ok((record_day(r.get())?, r.get().to_string()))).collect::<Result<_, String>>()?,
        })
    };
    Ok(Ok(LogAnswer {
        lines: val("lines")?.as_u64().ok_or("log.lines")?,
        warnings: val("warnings")?,
        facts: if facts.is_null() { None } else { Some(facts) },
        headers: val("headers")?,
        render: val("render")?,
        reseal,
    }))
}

/// **One `log` call through the FFI.**
pub fn log_call(req: &str) -> Result<Result<LogAnswer, Refusal>, String> {
    let resp = tm_kernel_ffi::call(req).map_err(|e| format!("kernel fault: {e:?}"))?;
    read_response(&resp)
}

// ---------------------------------------------------------------------------
// Genesis (§9.7).

/// **One entry of genesis' stack**: a checkpoint (`None` for the empty one), its `meta`, the records sealed below its
/// horizons, and how many lines its call had read.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Entry {
    pub ckpt: Option<String>,
    pub meta: Meta,
    pub days: BTreeMap<u64, String>,
    pub window: BTreeMap<u64, String>,
    pub known: usize,
}

/// Why genesis did not answer.
#[derive(Clone, Debug, PartialEq)]
pub enum GenesisError {
    /// **The named fault** (OWNER Q9 (iii), P31, D18): the call a refusal needs would carry more than the resend cap,
    /// so it is not sent; `reach` is its line count (or its bytes past the byte bound, in `bytes`).
    ReachTooFar { line: u64, kind: String, reach: u64, bytes: u64 },
    /// A refusal no pop can answer (not a guard, or the stack holds only the empty checkpoint).
    Refused(Refusal),
    /// The kernel faulted or answered out of shape.
    Fault(String),
}

/// **What genesis built**: the last call's answer, the top of the stack, and the calls and pops it took.
#[derive(Clone, Debug, PartialEq)]
pub struct Genesis {
    pub answer: LogAnswer,
    pub top: Entry,
    pub calls: usize,
    pub pops: usize,
    pub largest_call: usize,
}

/// The chunks' ends, as line counts: at most [`CHUNK_LINES`] lines and [`CHUNK_BYTES`] bytes each, and one empty chunk
/// for an empty log.
pub fn chunk_ends(s: &Split) -> Vec<usize> {
    let mut ends = Vec::new();
    let (mut start, n) = (0usize, s.lines.len());
    while start < n {
        let mut end = start + 1;
        while end < n && end - start < CHUNK_LINES && s.bytes_between(start, end + 1) <= CHUNK_BYTES {
            end += 1;
        }
        ends.push(end);
        start = end;
    }
    if ends.is_empty() {
        ends.push(0);
    }
    ends
}

/// **Genesis** (§9.7): the log's chunks resumed from the empty checkpoint with `policy`, pops exactly to what a refusal
/// names, one call through the refusing chunk's end, and the resend cap. The last call asks `last`.
pub fn genesis(now: &str, tz: &Value, s: &Split, policy: Policy, last: &Want) -> Result<Genesis, GenesisError> {
    let total = s.lines.len();
    let mut ends: VecDeque<usize> = chunk_ends(s).into();
    let mut stack = vec![Entry::default()];
    let (mut calls, mut pops, mut largest) = (0, 0, 0);
    let mut answer: Option<LogAnswer> = None;
    let mut refused: Option<Refusal> = None;
    let mut fuel = 2 * ends.len() + 2;
    while let Some(&e) = ends.front() {
        if fuel == 0 {
            return Err(GenesisError::Fault("genesis ran out of fuel".into()));
        }
        fuel -= 1;
        let top = stack.last().expect("the stack holds the empty checkpoint");
        let cut = top.meta.cut as usize;
        let (n, bytes) = (e - cut, s.bytes_between(cut, e));
        if n > RESEND_LINES || bytes > RESEND_BYTES {
            let (line, kind) = refused.as_ref().map_or((cut as u64 + 1, "unfolded"), Refusal::line_and_kind);
            return Err(GenesisError::ReachTooFar { line, kind: kind.to_string(), reach: n as u64, bytes: bytes as u64 });
        }
        largest = largest.max(n);
        let want = if e == total { last.clone() } else { Want::default() };
        let terminated = e < total || s.terminated;
        let req = request(now, tz, top.ckpt.as_deref(), cut as u64 + 1, &s.lines[cut..e], terminated, Some(policy), &want, None);
        calls += 1;
        match log_call(&req).map_err(GenesisError::Fault)? {
            Ok(a) => {
                if let Some(rs) = a.reseal.clone() {
                    let mut next = Entry { ckpt: Some(rs.ckpt), meta: rs.meta, days: top.days.clone(), window: top.window.clone(), known: e };
                    next.days.extend(rs.days);
                    next.window.extend(rs.window);
                    stack.push(next);
                }
                ends.pop_front();
                answer = Some(a);
                refused = None;
            }
            Err(r) if r.is_guard() && stack.len() > 1 => {
                stack.pop();
                while stack.len() > 1 && !r.pop_ok(&stack.last().expect("non-empty").meta) {
                    stack.pop();
                }
                pops += 1;
                refused = Some(r);
            }
            Err(r) => return Err(GenesisError::Refused(r)),
        }
    }
    let top = stack.pop().expect("the stack is never empty");
    Ok(Genesis { answer: answer.ok_or_else(|| GenesisError::Fault("genesis made no call".into()))?, top, calls, pops, largest_call: largest })
}

// ---------------------------------------------------------------------------
// The files (§9.8).

/// `YYYY-MM` of a kernel day (days since 0001-01-01).
pub fn month_of(day: u64) -> String {
    let d = chrono::NaiveDate::from_num_days_from_ce_opt(i32::try_from(day + 1).unwrap_or(i32::MAX))
        .unwrap_or(chrono::NaiveDate::MAX);
    d.format("%Y-%m").to_string()
}

/// `YYYY-MM-DD` of a kernel day.
pub fn date_of(day: u64) -> String {
    let d = chrono::NaiveDate::from_num_days_from_ce_opt(i32::try_from(day + 1).unwrap_or(i32::MAX))
        .unwrap_or(chrono::NaiveDate::MAX);
    d.format("%Y-%m-%d").to_string()
}

/// A kernel day of a calendar date.
pub fn day_of(d: chrono::NaiveDate) -> u64 {
    use chrono::Datelike;
    u64::try_from(d.num_days_from_ce() - 1).unwrap_or(0)
}

/// **`ckpt.json`** (§9.8, format 2).
#[derive(Clone, Debug, PartialEq)]
pub struct Snapshot {
    pub kernel: String,
    pub tz_key: String,
    pub prefix_lines: u64,
    /// The log's line count when this snapshot was written (W4, gap 124): the reseal trigger counts only lines after it.
    pub log_lines: u64,
    pub prefix_bytes: u64,
    pub prefix_fnv: String,
    pub gen: String,
    pub prev_gen: String,
    pub manifest: BTreeMap<String, String>,
    /// **The digest of each month file the manifest names** (the owner's D93, README gap 4246): month key to
    /// [`month_digest`] of the file's bytes as written. The same keys as `manifest`, always ([`Snapshot::from_text`]
    /// refuses any other); a file read whose bytes do not match is never served ([`ReplayCache::load_months`]).
    pub digests: BTreeMap<String, String>,
    pub meta: Meta,
    pub ckpt: String,
}

impl Snapshot {
    /// The text of `ckpt.json`, the checkpoint spliced in verbatim — **opening with the digest of the rest of
    /// itself** (the campaign's D98, README gap 4394): `{"digest":"<16 hex>",` and then the text a format-4 file
    /// held after its `{`, through its last newline, which is exactly the bytes the digest is taken over
    /// ([`month_digest`], D93's rule for a month file, applied to the checkpoint that names them). A byte of it
    /// changed by a disk or a hand is then caught as surely as a month file's is: [`Snapshot::from_text`] refuses
    /// it ([`CKPT_CORRUPT`]), and the cache is rebuilt from the log rather than resumed from it.
    pub fn to_text(&self) -> String {
        let head = serde_json::json!({
            "format": FORMAT, "kernel": self.kernel, "tzKey": self.tz_key, "prefixLines": self.prefix_lines, "logLines": self.log_lines,
            "prefixBytes": self.prefix_bytes, "prefixFnv": self.prefix_fnv, "gen": self.gen, "prevGen": self.prev_gen,
            "manifest": self.manifest, "digests": self.digests, "meta": self.meta.to_json(),
        })
        .to_string();
        let body = format!("{},\"ckpt\":{}}}\n", &head[1..head.len() - 1], self.ckpt);
        format!("{CKPT_DIGEST_HEAD}{}\",{body}", month_digest(&body))
    }

    /// Read `ckpt.json`; `Err` names what is wrong (corrupt, another format). **The digest first** (D98): a text
    /// whose digest does not match the rest of it is [`CKPT_CORRUPT`] and is never read further; a checkpoint of
    /// another format — every one written before D98 carries no digest — is "another format", rebuilt once and
    /// not named, as D93's format bump was.
    pub fn from_text(text: &str) -> Result<Snapshot, String> {
        let digested = text.strip_prefix(CKPT_DIGEST_HEAD).and_then(|rest| {
            let (hex, body) = (rest.get(..16)?, rest.get(16..)?.strip_prefix("\",")?);
            (month_digest(body) == hex).then_some(())
        });
        if digested.is_none() {
            let format = raw_map(text).ok().and_then(|m| m.get("format").and_then(|f| f.get().parse::<u64>().ok()));
            return Err(if format.is_some_and(|f| f != FORMAT) { "another format" } else { CKPT_CORRUPT }.into());
        }
        let m = raw_map(text)?;
        let val = |k: &str| -> Result<Value, String> {
            serde_json::from_str(m.get(k).ok_or_else(|| format!("no {k}"))?.get()).map_err(|e| e.to_string())
        };
        if val("format")?.as_u64() != Some(FORMAT) {
            return Err("another format".into());
        }
        let s = |k: &str| val(k).and_then(|v| v.as_str().map(str::to_owned).ok_or_else(|| format!("{k} is not a string")));
        let n = |k: &str| val(k).and_then(|v| v.as_u64().ok_or_else(|| format!("{k} is not a number")));
        let manifest: BTreeMap<String, String> = serde_json::from_value(val("manifest")?).map_err(|e| e.to_string())?;
        let digests: BTreeMap<String, String> = serde_json::from_value(val("digests")?).map_err(|e| e.to_string())?;
        // Every month file the manifest names has its digest, and nothing else does (D93): a snapshot that cannot say
        // what its months should read is not one to resume from.
        if !digests.keys().eq(manifest.keys()) {
            return Err("the digests do not name the manifest's months".into());
        }
        Ok(Snapshot {
            kernel: s("kernel")?,
            tz_key: s("tzKey")?,
            prefix_lines: n("prefixLines")?,
            log_lines: n("logLines")?,
            prefix_bytes: n("prefixBytes")?,
            prefix_fnv: s("prefixFnv")?,
            gen: s("gen")?,
            prev_gen: s("prevGen")?,
            manifest,
            digests,
            meta: Meta::from_json(&val("meta")?)?,
            ckpt: m.get("ckpt").ok_or("no ckpt")?.get().to_string(),
        })
    }

    /// **Integrity** (G9, §9.8): the snapshot is this kernel's, this zone's, and a prefix of these bytes.
    pub fn valid_for(&self, bytes: &[u8], tz_key: &str) -> Result<(), &'static str> {
        let pb = self.prefix_bytes as usize;
        if self.kernel != kernel_id() {
            return Err("another kernel");
        }
        if self.tz_key != tz_key {
            return Err("another zone");
        }
        if pb > bytes.len() {
            return Err("the log is shorter than the prefix");
        }
        if pb > 0 && bytes[pb - 1] != b'\n' {
            return Err("the prefix does not end a line");
        }
        if format!("{:016x}", fnv1a64(&bytes[..pb])) != self.prefix_fnv {
            return Err("the prefix's digest differs");
        }
        if self.meta.cut != self.prefix_lines {
            return Err("the prefix is not the checkpoint's cut");
        }
        Ok(())
    }
}

/// A month file's text: `{"v":1,"days":{"<Day>": record, …},"window":{"<Day>": record, …}}`, the records verbatim.
fn month_text(days: &BTreeMap<u64, String>, window: &BTreeMap<u64, String>) -> String {
    let obj = |m: &BTreeMap<u64, String>| {
        let parts: Vec<String> = m.iter().map(|(d, r)| format!("\"{d}\":{r}")).collect();
        format!("{{{}}}", parts.join(","))
    };
    format!("{{\"v\":1,\"days\":{},\"window\":{}}}\n", obj(days), obj(window))
}

/// Read a month file's records.
fn read_month(text: &str) -> Result<(BTreeMap<u64, String>, BTreeMap<u64, String>), String> {
    let m = raw_map(text)?;
    let rec = |k: &str| -> Result<BTreeMap<u64, String>, String> {
        let inner: BTreeMap<String, &RawValue> = serde_json::from_str(m.get(k).ok_or_else(|| format!("no {k}"))?.get())
            .map_err(|e| e.to_string())?;
        inner.iter().map(|(d, r)| Ok((d.parse::<u64>().map_err(|e| e.to_string())?, r.get().to_string()))).collect()
    };
    Ok((rec("days")?, rec("window")?))
}

/// A fresh generation tag: 16 hex digits from the process's hasher keys, the clock and the process id.
pub fn fresh_gen() -> String {
    use std::hash::{BuildHasher, Hasher};
    let mut h = std::collections::hash_map::RandomState::new().build_hasher();
    h.write_u128(SystemTime::now().duration_since(SystemTime::UNIX_EPOCH).map_or(0, |d| d.as_nanos()));
    h.write_u32(std::process::id());
    format!("{:016x}", h.finish())
}

/// Write a file through a temporary file and a rename (§9.8).
fn write_atomic(path: &Path, text: &str) -> std::io::Result<()> {
    let dir = path.parent().expect("a file in a directory");
    std::fs::create_dir_all(dir)?;
    let tmp = dir.join(format!(".{}.{}.tmp", path.file_name().and_then(|f| f.to_str()).unwrap_or("f"), fresh_gen()));
    {
        let mut f = std::fs::File::create(&tmp)?;
        f.write_all(text.as_bytes())?;
        f.sync_all()?;
    }
    std::fs::rename(&tmp, path)
}

static UNWRITABLE_NOTICE: AtomicBool = AtomicBool::new(false);

/// Why a reseal's write stopped before publishing: a month file it must merge is missing or does not match its digest
/// (D93, README gaps 4246 and 4395), and the cache is rebuilt from the log instead.
const MONTH_CORRUPT: &str = "a month file the manifest names is missing or does not match its digest";

/// Why `ckpt.json` was not read: its text does not match the digest it carries (the campaign's D98, README gap 4394).
/// The cache is rebuilt from the log and the rebuild says so once ([`corrupt_ckpt_notice`]).
const CKPT_CORRUPT: &str = "the checkpoint does not match its digest";

/// What `ckpt.json` opens with since D98: the digest of the rest of its text, then the rest.
const CKPT_DIGEST_HEAD: &str = "{\"digest\":\"";

/// **A sealed month file's digest** (the owner's D93, README gap 4246): FNV-1a-64 of its bytes, the hash §9.8's
/// prefix digest already is ([`fnv1a64`]) — no second hash and no new dependency. **Since the campaign's D98**
/// (README gap 4394) it is the checkpoint's own digest too ([`Snapshot::to_text`]): one rule for every file of the
/// cache, and one function for it.
///
/// **Why it is enough here.** The threat is accidental corruption and a hand edit, never an adversary (whoever can
/// edit `.tm/cache/` can edit `.tm/log.jsonl` itself). Every step of FNV-1a — XOR a byte, multiply by an odd prime
/// modulo 2^64 — is a bijection of the running state, so two inputs of one length that differ in ONE byte always
/// digest differently (`a_digest_moves_with_every_single_byte_edit`): a flipped bit, a typed digit, a stray
/// character is detected with certainty, not with probability. A truncation or a multi-byte change escapes it only
/// by a 64-bit collision, about one in 1.8 × 10^19 for an edit that is not aimed at it. It is not cryptographic, and
/// a forger who wanted to could aim one; that is not this file's threat.
pub fn month_digest(text: &str) -> String {
    format!("{:016x}", fnv1a64(text.as_bytes()))
}

/// **The one notice an unwritable cache prints per process** (CRIT 26), or `None` when it was already given.
pub fn unwritable_notice(err: &std::io::Error) -> Option<String> {
    if UNWRITABLE_NOTICE.swap(true, Ordering::SeqCst) {
        None
    } else {
        Some(format!("replay cache {CACHE_DIR} is not writable ({err}); each command rebuilds in memory"))
    }
}

/// How a call was answered.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// From the stored checkpoint, no reseal.
    Hot,
    /// From the stored checkpoint, resealed and written.
    Resealed,
    /// Genesis, written.
    Genesis,
    /// Genesis at a `now` below the ledger day, not written (§9.7).
    GenesisUnpersisted,
}

/// **What one replay gives a verb**: the answer, how it was answered, the snapshot it answered from, the records this call
/// sealed (a reseal's or a genesis', which an unpersisted genesis holds only here), and any notices.  A hot call loads no
/// month file (§11.1's `Hot` scope); a verb that needs older records asks [`ReplayCache::records_of`].
#[derive(Clone, Debug)]
pub struct Replayed {
    pub answer: LogAnswer,
    pub outcome: Outcome,
    pub snapshot: Snapshot,
    pub days: BTreeMap<u64, String>,
    pub window: BTreeMap<u64, String>,
    pub notices: Vec<String>,
    /// Why the stored checkpoint was not used, when it was not.
    // Written on every genesis path and read by nothing the binary compiles: the notice a verb
    // prints comes from `notices`, and the readers are `kernel_replay_parity.rs`'s assertion
    // messages, which are a separate target. Kept as the one place a rebuild's *cause* survives.
    #[allow(dead_code)]
    pub rebuilt_because: Option<String>,
}

/// **The replay cache of one process** (§9.8): the directory when it is writable, else the checkpoint in memory.
#[derive(Clone, Debug, Default)]
pub struct ReplayCache {
    pub dir: Option<PathBuf>,
    /// The process's own checkpoint and records, used when the directory is not writable (CRIT 26).
    pub memory: Option<(Snapshot, BTreeMap<u64, String>, BTreeMap<u64, String>)>,
    pub writable: bool,
    /// **The snapshot this process's last replay ended on** (stage 6 step L9), persisted or not.
    /// A `now` below the ledger day answers from an *unpersisted* genesis (§9.7), and the stored
    /// `ckpt.json` is then the wrong one to resume from — but the capacity request that follows,
    /// in the same process and for the same bytes, needs a checkpoint to derive day 0 from.
    /// This is it ([`capacity_log_section`]).
    pub last: Option<Snapshot>,
}

impl ReplayCache {
    /// A cache in `dir` (`<root>/.tm/cache/replay`), or in memory only.
    pub fn new(dir: Option<PathBuf>) -> ReplayCache {
        ReplayCache { writable: dir.is_some(), dir, memory: None, last: None }
    }

    fn ckpt_path(&self) -> Option<PathBuf> {
        self.dir.as_ref().map(|d| d.join(CKPT_FILE))
    }

    /// **Read the snapshot once** (CRIT 7): `ckpt.json`, or the in-memory checkpoint; `None` when there is none or it is
    /// unreadable — a checkpoint that does not match its own digest among them (the campaign's D98, README gap 4394).
    pub fn read_snapshot(&self) -> Option<Snapshot> {
        self.read_ckpt().ok().flatten()
    }

    /// [`ReplayCache::read_snapshot`], saying why a `ckpt.json` that is there was not read: `Err` with
    /// [`Snapshot::from_text`]'s reason ([`CKPT_CORRUPT`] for a digest that does not match), `Ok(None)` when there is
    /// neither a file nor a checkpoint in memory.
    fn read_ckpt(&self) -> Result<Option<Snapshot>, String> {
        if let Some(p) = self.ckpt_path() {
            if let Ok(text) = std::fs::read_to_string(p) {
                return Snapshot::from_text(&text).map(Some);
            }
        }
        Ok(self.memory.as_ref().map(|m| m.0.clone()))
    }

    /// **The records of a snapshot's months** (by its manifest only), `None` when a named file is missing — **or
    /// does not match the digest the manifest records for it** (the owner's D93, README gap 4246): a corrupted or
    /// hand-edited month file is never served. Every caller answers `None` with a rebuild from the log
    /// ([`ReplayCache::rebuild_missing`], README gap 3711), so the answer is the one a cache-less run gives.
    pub fn load_months(&self, snap: &Snapshot, months: &[String]) -> Option<(BTreeMap<u64, String>, BTreeMap<u64, String>)> {
        if let Some((ms, d, w)) = &self.memory {
            if ms.gen == snap.gen {
                return Some((d.clone(), w.clone()));
            }
        }
        let dir = self.dir.as_ref()?;
        let (mut days, mut window) = (BTreeMap::new(), BTreeMap::new());
        for m in months {
            let Some(rel) = snap.manifest.get(m) else { continue };
            let text = std::fs::read_to_string(dir.join(rel)).ok()?;
            if snap.digests.get(m) != Some(&month_digest(&text)) {
                return None;
            }
            let (d, w) = read_month(&text).ok()?;
            days.extend(d.into_iter().filter(|(k, _)| *k < snap.meta.ledger_day));
            window.extend(w.into_iter().filter(|(k, _)| *k < snap.meta.horizon));
        }
        Some((days, window))
    }

    /// **Every record of a snapshot** (the `All` scope), re-reading `ckpt.json` once when a month file is missing
    /// (§9.8's snapshot rule). `None` after the retry: the caller rebuilds ([`ReplayCache::rebuild_missing`]).
    pub fn all_records(&self, snap: &Snapshot) -> Option<(Snapshot, BTreeMap<u64, String>, BTreeMap<u64, String>)> {
        let months: Vec<String> = snap.manifest.keys().cloned().collect();
        if let Some((d, w)) = self.load_months(snap, &months) {
            return Some((snap.clone(), d, w));
        }
        let again = self.read_snapshot()?;
        let months: Vec<String> = again.manifest.keys().cloned().collect();
        self.load_months(&again, &months).map(|(d, w)| (again, d, w))
    }

    /// **Write a new generation** (§9.8): each month touched by `days`/`window` read from the current manifest, the
    /// touched keys replaced, written as a new immutable file with its digest recorded beside its name (D93); then
    /// `ckpt.json`; then collection. On an I/O error the checkpoint and records are kept in memory and the notice
    /// returned.
    ///
    /// **`Err(month)` when a month file the read-modify-write must read is missing or does not match its digest** (the
    /// owner's D93, README gaps 4246 and 4395): nothing is published, and the caller rebuilds the cache from the log.
    /// Merging a corrupted file would carry its records into a new file under a FRESH digest — the corruption laundered
    /// into a file the next read trusts; and a missing one used to leave this process holding the reseal's new records
    /// ALONE in memory, which every older-date read in the same verb then answered from (`records_of`'s generation is
    /// the memory's): driven, a reseal over a deleted September file answered `Scope::All` with 8 days of a 50-day log.
    /// With `all_records` nothing is read back, so a rebuild's write never answers `Err`.
    pub fn write_generation(
        &mut self,
        prev: Option<&Snapshot>,
        mut snap: Snapshot,
        days: &BTreeMap<u64, String>,
        window: &BTreeMap<u64, String>,
        all_records: bool,
    ) -> Result<(Snapshot, Option<String>), String> {
        let gen = fresh_gen();
        snap.prev_gen = prev.map_or_else(String::new, |p| p.gen.clone());
        snap.gen = gen.clone();
        snap.manifest = if all_records { BTreeMap::new() } else { prev.map(|p| p.manifest.clone()).unwrap_or_default() };
        snap.digests = if all_records { BTreeMap::new() } else { prev.map(|p| p.digests.clone()).unwrap_or_default() };
        let mut corrupt: Option<String> = None;
        let mut touched: BTreeMap<String, (BTreeMap<u64, String>, BTreeMap<u64, String>)> = BTreeMap::new();
        for (d, r) in days {
            touched.entry(month_of(*d)).or_default().0.insert(*d, r.clone());
        }
        for (d, r) in window {
            touched.entry(month_of(*d)).or_default().1.insert(*d, r.clone());
        }
        let result: std::io::Result<()> = (|| {
            let dir = self.dir.clone().ok_or_else(|| std::io::Error::other("no cache directory"))?;
            for (month, (d, w)) in &touched {
                let (mut md, mut mw) = (BTreeMap::new(), BTreeMap::new());
                if !all_records {
                    if let Some((p, rel)) = prev.and_then(|p| p.manifest.get(month).map(|rel| (p, rel))) {
                        // The input of a read-modify-write must be the file that was written: there (a month file the
                        // manifest names but another process collected would otherwise publish a month without its
                        // older records, CRIT 7) and matching its digest (D93). Neither is merged; both rebuild.
                        let text = std::fs::read_to_string(dir.join(rel)).ok().filter(|t| p.digests.get(month) == Some(&month_digest(t)));
                        let Some((od, ow)) = text.and_then(|t| read_month(&t).ok()) else {
                            corrupt = Some(month.clone());
                            return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, MONTH_CORRUPT));
                        };
                        md = od;
                        mw = ow;
                    }
                }
                md.extend(d.clone());
                mw.extend(w.clone());
                let rel = format!("{SEALED_DIR}/{month}.g{gen}.json");
                let text = month_text(&md, &mw);
                write_atomic(&dir.join(&rel), &text)?;
                snap.manifest.insert(month.clone(), rel);
                snap.digests.insert(month.clone(), month_digest(&text));
            }
            write_atomic(&dir.join(CKPT_FILE), &snap.to_text())?;
            collect(&dir, &snap, prev);
            Ok(())
        })();
        if let Some(month) = corrupt {
            return Err(month);
        }
        Ok(match result {
            Ok(()) => {
                self.memory = None;
                (snap, None)
            }
            Err(e) => {
                self.writable = false;
                let (mut md, mut mw) = self.memory.take().map(|m| (m.1, m.2)).unwrap_or_default();
                if all_records {
                    md.clear();
                    mw.clear();
                }
                md.extend(days.clone());
                mw.extend(window.clone());
                self.memory = Some((snap.clone(), md, mw));
                (snap, unwritable_notice(&e))
            }
        })
    }

    /// **One replay for a verb** (§9.8, §9.7, §9.6): check the stored checkpoint against the log, resume its tail (with a
    /// reseal when the policy says so), and fall back to genesis on a refusal, a failed digest or no checkpoint.
    ///
    /// The snapshot it ends on is kept in [`ReplayCache::last`] for the capacity request that may
    /// follow it in the same process (stage 6 step L9).
    #[allow(clippy::too_many_arguments)]
    pub fn replay(
        &mut self,
        bytes: &[u8],
        now_day: u64,
        tz: &Value,
        max_line: Option<u64>,
        want: &Want,
    ) -> Result<Replayed, GenesisError> {
        let r = self.replay_once(bytes, now_day, tz, max_line, want)?;
        self.last = Some(r.snapshot.clone());
        Ok(r)
    }

    #[allow(clippy::too_many_arguments)]
    fn replay_once(
        &mut self,
        bytes: &[u8],
        now_day: u64,
        tz: &Value,
        max_line: Option<u64>,
        want: &Want,
    ) -> Result<Replayed, GenesisError> {
        let now = date_of(now_day);
        let tz_key = tz.get("key").and_then(Value::as_str).unwrap_or_default().to_string();
        let s = split(bytes);
        // A checkpoint that does not match its own digest (D98) is not resumed from: the cache is rebuilt from the
        // log below, and the rebuild says so once.
        let (snap, corrupt) = match self.read_ckpt() {
            Ok(snap) => (snap, false),
            Err(why) => (None, why == CKPT_CORRUPT),
        };
        let why = match &snap {
            None if corrupt => Some(CKPT_CORRUPT.to_string()),
            None => Some("no checkpoint".to_string()),
            Some(sn) => sn.valid_for(bytes, &tz_key).err().map(str::to_string),
        };
        if let (Some(sn), None) = (&snap, &why) {
            let cut = sn.meta.cut as usize;
            let tail = &s.lines[cut..];
            let too_big = tail.len() > RESEND_LINES || s.bytes_between(cut, s.lines.len()) > RESEND_BYTES;
            if !too_big {
                // Gap 124 (W4): only lines appended since this snapshot was written count, so a tail the last reseal could
                // not fold (an unfolded undo's target, `SealResume.cutOk`'s condition (vi)) does not reseal on every call.
                let written = (sn.log_lines as usize).clamp(cut, s.lines.len());
                let foldable = tail
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| cut + i >= written && max_line.is_none_or(|m| (cut + i + 1) as u64 <= m))
                    .count();
                let reseal = (foldable > FOLDABLE_TRIGGER
                    || (now_day > sn.meta.ledger_day + KEEP_DAYS && sn.meta.reseal_day < now_day))
                    .then_some(Policy { keep_days: KEEP_DAYS, max_line });
                let req = request(&now, tz, Some(&sn.ckpt), cut as u64 + 1, tail, s.terminated, reseal, want, None);
                match log_call(&req).map_err(GenesisError::Fault)? {
                    Ok(a) => {
                        let Some(rs) = a.reseal.clone() else {
                            return Ok(Replayed {
                                answer: a,
                                outcome: Outcome::Hot,
                                snapshot: sn.clone(),
                                days: BTreeMap::new(),
                                window: BTreeMap::new(),
                                notices: vec![],
                                rebuilt_because: None,
                            });
                        };
                        let next = snapshot_of(&rs, &tz_key, &s, bytes);
                        let days: BTreeMap<u64, String> = rs.days.iter().cloned().collect();
                        let window: BTreeMap<u64, String> = rs.window.iter().cloned().collect();
                        let (next, notice) = match self.write_generation(Some(sn), next, &days, &window, false) {
                            Ok(written) => written,
                            // A month the reseal must merge does not match its digest (D93): nothing was written,
                            // and the cache is rebuilt from the log rather than built on it.
                            Err(month) => {
                                let mut r = self.rebuild(&now, tz, &s, max_line, want, bytes, Some(format!("{MONTH_CORRUPT} ({month})")), false)?;
                                r.notices.push(corrupt_month_notice(&month));
                                return Ok(r);
                            }
                        };
                        return Ok(Replayed {
                            answer: a,
                            outcome: Outcome::Resealed,
                            snapshot: next,
                            days,
                            window,
                            notices: notice.into_iter().collect(),
                            rebuilt_because: None,
                        });
                    }
                    Err(Refusal::NowBelowLedger { .. }) => {
                        return self.rebuild(&now, tz, &s, max_line, want, bytes, Some("nowBelowLedger".into()), true);
                    }
                    Err(r @ Refusal::Fault(_)) => return Err(GenesisError::Refused(r)),
                    Err(r) => {
                        let (line, kind) = r.line_and_kind();
                        return self.rebuild(&now, tz, &s, max_line, want, bytes, Some(format!("{kind} at line {line}")), false);
                    }
                }
            }
            return self.rebuild(&now, tz, &s, max_line, want, bytes, Some("a tail past the resend cap".into()), false);
        }
        let mut r = self.rebuild(&now, tz, &s, max_line, want, bytes, why, false)?;
        if corrupt {
            r.notices.push(corrupt_ckpt_notice());
        }
        Ok(r)
    }

    #[allow(clippy::too_many_arguments)]
    fn rebuild(
        &mut self,
        now: &str,
        tz: &Value,
        s: &Split,
        max_line: Option<u64>,
        want: &Want,
        bytes: &[u8],
        why: Option<String>,
        unpersisted: bool,
    ) -> Result<Replayed, GenesisError> {
        let tz_key = tz.get("key").and_then(Value::as_str).unwrap_or_default().to_string();
        let g = genesis(now, tz, s, Policy { keep_days: KEEP_DAYS, max_line }, want)?;
        let rs = Resealed {
            ckpt: g.top.ckpt.clone().unwrap_or_default(),
            meta: g.top.meta.clone(),
            days: g.top.days.iter().map(|(d, r)| (*d, r.clone())).collect(),
            window: g.top.window.iter().map(|(d, r)| (*d, r.clone())).collect(),
        };
        if g.top.ckpt.is_none() {
            // Nothing was sealed (a log of recent lines only): nothing to store; the answer stands.
            let snap = Snapshot {
                kernel: kernel_id().into(),
                tz_key,
                prefix_lines: 0,
                log_lines: s.lines.len() as u64,
                prefix_bytes: 0,
                prefix_fnv: format!("{:016x}", fnv1a64(&[])),
                gen: String::new(),
                prev_gen: String::new(),
                manifest: BTreeMap::new(),
                digests: BTreeMap::new(),
                meta: Meta::default(),
                ckpt: String::new(),
            };
            return Ok(Replayed { answer: g.answer, outcome: if unpersisted { Outcome::GenesisUnpersisted } else { Outcome::Genesis }, snapshot: snap, days: BTreeMap::new(), window: BTreeMap::new(), notices: vec![], rebuilt_because: why });
        }
        let snap = snapshot_of(&rs, &tz_key, s, bytes);
        if unpersisted {
            return Ok(Replayed { answer: g.answer, outcome: Outcome::GenesisUnpersisted, snapshot: snap, days: g.top.days, window: g.top.window, notices: vec![], rebuilt_because: why });
        }
        let prev = self.read_snapshot();
        // `all_records`: nothing is read back, so no digest can refuse this write (D93); were one to, the generation is
        // this call's alone, kept in memory as an unwritable cache keeps it, and named.
        let (snap, notice) = match self.write_generation(prev.as_ref(), snap.clone(), &g.top.days, &g.top.window, true) {
            Ok(written) => written,
            Err(month) => {
                self.memory = Some((snap.clone(), g.top.days.clone(), g.top.window.clone()));
                (snap, Some(corrupt_month_notice(&month)))
            }
        };
        Ok(Replayed { answer: g.answer, outcome: Outcome::Genesis, snapshot: snap, days: g.top.days, window: g.top.window, notices: notice.into_iter().collect(), rebuilt_because: why })
    }

    /// **A sealed month file the snapshot names is missing — or does not match its digest (D93, README gap 4246):
    /// rebuild the cache from the log** (README gap **3711**, the W-39 repair; D13 — the cache is derived and
    /// rebuildable). Genesis over the
    /// whole log, written as a fresh generation that reads no old month (`write_generation`'s
    /// `all_records`), or kept in memory when the cache cannot be written; the snapshot it ends on
    /// becomes [`ReplayCache::last`], so a request section asked in the same process reads it.
    pub fn rebuild_missing(
        &mut self,
        bytes: &[u8],
        now_day: u64,
        tz: &Value,
        max_line: Option<u64>,
        want: &Want,
    ) -> Result<Replayed, GenesisError> {
        let s = split(bytes);
        let r = self.rebuild(&date_of(now_day), tz, &s, max_line, want, bytes, Some("a sealed month file is missing or does not match its digest".into()), false)?;
        self.last = Some(r.snapshot.clone());
        Ok(r)
    }

    /// **Every record a replay's answer stands on** (§11.1's `All` scope): an unpersisted genesis' own records, else the
    /// snapshot's months by its manifest (re-reading `ckpt.json` once when a file is missing). `None` when the files moved
    /// underneath twice: the caller rebuilds the cache from the log ([`ReplayCache::rebuild_missing`], gap 3711).
    pub fn records_of(&self, r: &Replayed) -> Option<(BTreeMap<u64, String>, BTreeMap<u64, String>)> {
        if r.outcome == Outcome::GenesisUnpersisted || r.snapshot.gen.is_empty() {
            return Some((r.days.clone(), r.window.clone()));
        }
        self.all_records(&r.snapshot).map(|(_, d, w)| (d, w))
    }

    /// **An old-date read** (§11.1's `Dates` scope, D13): the snapshot's day records of `[from − 1, to + 1]` below its
    /// ledger day and window records of `[from, to]` below its horizon, sent as `sealed` (at most 62 per call) with the
    /// same tail, so the kernel's facts carry them merged.
    #[allow(dead_code)] // §11.1's `Dates` scope reaches the same records through `records_of`; kept as D13's documented route.
    pub fn sealed_between(snap: &Snapshot, days: &BTreeMap<u64, String>, window: &BTreeMap<u64, String>, from: u64, to: u64) -> (Vec<String>, Vec<String>) {
        let d: Vec<String> = days
            .range(from.saturating_sub(1)..=to + 1)
            .filter(|(k, _)| **k < snap.meta.ledger_day)
            .map(|(_, r)| r.clone())
            .collect();
        let w: Vec<String> = window.range(from..=to).filter(|(k, _)| **k < snap.meta.horizon).map(|(_, r)| r.clone()).collect();
        (d, w)
    }
}

/// The snapshot of a reseal over these bytes.
fn snapshot_of(rs: &Resealed, tz_key: &str, s: &Split, bytes: &[u8]) -> Snapshot {
    let pb = s.prefix_bytes(rs.meta.cut as usize);
    Snapshot {
        kernel: kernel_id().into(),
        tz_key: tz_key.into(),
        prefix_lines: rs.meta.cut,
        log_lines: s.lines.len() as u64,
        prefix_bytes: pb as u64,
        prefix_fnv: format!("{:016x}", fnv1a64(&bytes[..pb])),
        gen: String::new(),
        prev_gen: String::new(),
        manifest: BTreeMap::new(),
        digests: BTreeMap::new(),
        meta: rs.meta.clone(),
        ckpt: rs.ckpt.clone(),
    }
}

/// **Collection** (§9.8): delete month files named by neither the new nor the previous manifest and older than ten
/// minutes by mtime, so an in-flight writer keeps its own.
fn collect(dir: &Path, snap: &Snapshot, prev: Option<&Snapshot>) {
    let keep: std::collections::BTreeSet<&String> =
        snap.manifest.values().chain(prev.into_iter().flat_map(|p| p.manifest.values())).collect();
    let Ok(rd) = std::fs::read_dir(dir.join(SEALED_DIR)) else { return };
    for entry in rd.flatten() {
        let rel = format!("{SEALED_DIR}/{}", entry.file_name().to_string_lossy());
        if keep.contains(&rel) {
            continue;
        }
        let old = entry
            .metadata()
            .and_then(|m| m.modified())
            .ok()
            .and_then(|t| SystemTime::now().duration_since(t).ok())
            .is_some_and(|age| age > COLLECT_AFTER);
        if old {
            let _ = std::fs::remove_file(entry.path());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_split_keeps_a_torn_last_line_and_its_offsets() {
        let s = split(b"a\nb\n\xff\nc");
        assert_eq!(s.lines, vec![Some("a".into()), Some("b".into()), None, Some("c".into())]);
        assert_eq!(s.ends, vec![2, 4, 6, 7]);
        assert!(!s.terminated);
        assert_eq!(s.bytes_between(1, 3), 4);
        assert!(split(b"a\n").terminated);
        assert_eq!(split(b"").lines.len(), 0);
    }

    #[test]
    fn a_refusal_is_read_by_name_and_pops_exactly() {
        let r = Refusal::from_err(&serde_json::json!({"log":{"undoReach":{"line":45171,"below":45100}}}));
        assert_eq!(r, Refusal::UndoReach { line: 45171, below: 45100 });
        assert!(r.is_guard() && r.pop_ok(&Meta { cut: 45099, ..Meta::default() }) && !r.pop_ok(&Meta { cut: 45100, ..Meta::default() }));
        assert_eq!(Refusal::from_err(&serde_json::json!({"log":"cutMismatch"})), Refusal::CutMismatch);
        let w = Refusal::from_err(&serde_json::json!({"log":{"wakeBehindCut":{"line":9,"t":[100,0]}}}));
        assert!(w.pop_ok(&Meta { max_t: Some((99, 0)), ..Meta::default() }));
        assert!(!w.pop_ok(&Meta { max_t: Some((100, 0)), ..Meta::default() }));
        assert!(!w.pop_ok(&Meta { future_floor: Some((100 + FENCE_SEC, 0)), ..Meta::default() }));
        assert!(matches!(Refusal::from_err(&serde_json::json!({"log":"tzAbsent"})), Refusal::Fault(_)));
    }

    #[test]
    fn a_snapshot_round_trips_its_text_with_the_checkpoint_verbatim() {
        let s = Snapshot {
            kernel: kernel_id().into(),
            tz_key: "UTC".into(),
            prefix_lines: 2,
            log_lines: 3,
            prefix_bytes: 4,
            prefix_fnv: format!("{:016x}", fnv1a64(b"a\nb\n")),
            gen: "0123456789abcdef".into(),
            prev_gen: String::new(),
            manifest: BTreeMap::from([("2026-09".to_string(), "sealed/2026-09.g0123456789abcdef.json".to_string())]),
            digests: BTreeMap::from([("2026-09".to_string(), month_digest("{\"v\":1,\"days\":{},\"window\":{}}\n"))]),
            meta: Meta { cut: 2, ledger_day: 739870, horizon: 739855, reseal_day: 739872, max_t: Some((1, 0)), future_floor: None },
            ckpt: r#"{"v":1,"tzKey":"UTC","cut":2}"#.into(),
        };
        let back = Snapshot::from_text(&s.to_text()).expect("reads back");
        assert_eq!(back, s);
        // D93: a manifest month without its digest, or a digest for no month, is not a snapshot to resume from.
        for digests in [BTreeMap::new(), BTreeMap::from([("2026-08".to_string(), "0".repeat(16))])] {
            let other = Snapshot { digests, ..s.clone() };
            assert!(Snapshot::from_text(&other.to_text()).is_err(), "{:?}", other.digests);
        }
        assert!(s.valid_for(b"a\nb\nc\n", "UTC").is_ok());
        assert_eq!(s.valid_for(b"a\nB\nc\n", "UTC"), Err("the prefix's digest differs"));
        assert_eq!(s.valid_for(b"a\nb", "UTC"), Err("the log is shorter than the prefix"));
        assert_eq!(s.valid_for(b"a\nb\nc\n", "America/Chicago"), Err("another zone"));
    }

    #[test]
    fn chunks_hold_at_most_their_lines_and_bytes() {
        let text: String = (0..20_000).map(|i| format!("line {i}\n")).collect();
        let s = split(text.as_bytes());
        let ends = chunk_ends(&s);
        let mut start = 0;
        for &e in &ends {
            assert!(e - start <= CHUNK_LINES && s.bytes_between(start, e) <= CHUNK_BYTES);
            start = e;
        }
        assert_eq!(start, 20_000);
        assert_eq!(chunk_ends(&split(b"")), vec![0]);
        assert_eq!(month_of(739865), "2026-09");
        assert_eq!(day_of(chrono::NaiveDate::from_ymd_opt(2026, 9, 7).unwrap()), 739865);
    }

    /// **A sealed month file the snapshot names and the disk lacks is REBUILT, not a fault** (README gap
    /// 3711, the W-39 repair; D13).  A month of logged wakes is replayed and sealed; every month file is
    /// deleted; the week's `log` section is asked for a SEALED week straight off the stale snapshot — the
    /// path a verb whose own replay did not read the months takes, or one the files moved underneath
    /// between two reads.  It rebuilds, and the section carries the week's seven sealed day records.
    #[test]
    fn a_missing_month_file_is_rebuilt_for_the_weeks_section() {
        let dir = tempfile::tempdir().expect("a scratch directory");
        let root = dir.path();
        let tz: Tz = "America/Chicago".parse().expect("a zone");
        let tz_wire = super::super::tz_table::wire_for(Some(&root.join(CACHE_DIR)), tz);
        let mut text = String::new();
        let first = chrono::NaiveDate::from_ymd_opt(2026, 8, 1).expect("a date");
        for i in 0..45 {
            let d = first + chrono::Duration::days(i);
            text.push_str(&format!("{{\"t\":\"{d}T06:05:00-05:00\",\"ev\":\"wake\",\"slept_min\":480}}\n"));
        }
        let today = first + chrono::Duration::days(45);
        replay_scoped(root, text.as_bytes(), tz, &tz_wire, today, Scope::All, None).expect("the replay");
        let sealed: Vec<_> = std::fs::read_dir(root.join(CACHE_DIR).join(SEALED_DIR))
            .expect("the sealed months")
            .map(|e| e.expect("an entry").path())
            .collect();
        assert!(!sealed.is_empty(), "the replay sealed a month");
        for p in &sealed {
            std::fs::remove_file(p).expect("a month file");
        }
        let (from, to) = (day_of(first + chrono::Duration::days(7)), day_of(first + chrono::Duration::days(13)));
        let section = week_log_section(root, text.as_bytes(), &tz_wire, day_of(today), from, to)
            .expect("rebuilt, not a fault");
        let v: Value = serde_json::from_str(&section).expect("a section");
        assert_eq!(v["sealed"]["days"].as_array().map(Vec::len), Some(7), "the week's sealed records: {}", v["sealed"]);
    }

    /// **A digest moves with every single-byte edit** (the owner's D93, README gap 4246) — the property
    /// [`month_digest`]'s doc argues from: every step of FNV-1a is a bijection of its state, so two texts of one
    /// length that differ in one byte never share a digest. Exhaustive over a sealed month file's shape (every
    /// position, every other byte value), and over random texts by the same rule.
    #[test]
    fn a_digest_moves_with_every_single_byte_edit() {
        let month = r#"{"v":1,"days":{"739865":[739865,[null,[],260,4,948]]},"window":{}}"#;
        let base = fnv1a64(month.as_bytes());
        let mut edits = 0u32;
        for at in 0..month.len() {
            for b in 0u8..=255 {
                if b == month.as_bytes()[at] {
                    continue;
                }
                let mut v = month.as_bytes().to_vec();
                v[at] = b;
                assert_ne!(fnv1a64(&v), base, "a one-byte edit at {at} to {b:#04x} kept the digest");
                edits += 1;
            }
        }
        assert_eq!(edits, month.len() as u32 * 255);
        let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..2_000 {
            let len = (next() % 64 + 1) as usize;
            let text: Vec<u8> = (0..len).map(|_| next() as u8).collect();
            let at = (next() as usize) % len;
            let mut edited = text.clone();
            edited[at] ^= ((next() % 255) + 1) as u8;
            assert_ne!(fnv1a64(&edited), fnv1a64(&text), "{text:?} at {at}");
        }
    }

    /// Forty-five days of logged wakes from 2026-08-01, and `n` more after them.
    fn wakes(days: i64) -> String {
        let first = chrono::NaiveDate::from_ymd_opt(2026, 8, 1).expect("a date");
        (0..days)
            .map(|i| format!("{{\"t\":\"{}T06:05:00-05:00\",\"ev\":\"wake\",\"slept_min\":480}}\n", first + chrono::Duration::days(i)))
            .collect()
    }

    /// **A month file read whose bytes do not match its digest is never served** (the owner's D93, README gap
    /// 4246): one byte of a sealed record changed, the JSON still valid — so the file still READS — and the replay
    /// that needs it rebuilds from the log, answering exactly what a cache-less replay answers; the rebuilt files
    /// match their digests and the edited one is named by no manifest.
    #[test]
    fn a_month_file_that_does_not_match_its_digest_is_never_served() {
        let dir = tempfile::tempdir().expect("a scratch directory");
        let root = dir.path();
        let tz: Tz = "America/Chicago".parse().expect("a zone");
        let tz_wire = super::super::tz_table::wire_for(Some(&root.join(CACHE_DIR)), tz);
        let text = wakes(45);
        let today = chrono::NaiveDate::from_ymd_opt(2026, 9, 15).expect("a date");
        replay_scoped(root, text.as_bytes(), tz, &tz_wire, today, Scope::All, None).expect("the replay");
        let snap = ReplayCache::new(Some(root.join(CACHE_DIR))).read_snapshot().expect("a snapshot");
        assert_eq!(snap.digests.keys().collect::<Vec<_>>(), snap.manifest.keys().collect::<Vec<_>>());
        let august = root.join(CACHE_DIR).join(&snap.manifest["2026-08"]);
        let before = std::fs::read_to_string(&august).expect("the August file");
        assert_eq!(snap.digests["2026-08"], month_digest(&before), "the manifest records the file's own digest");
        let at = before.find("480").expect("a night's 480 minutes") + 2;
        let mut edited = before.clone();
        edited.replace_range(at..at + 1, "1");
        assert!(read_month(&edited).is_ok(), "the edit keeps the file readable");
        std::fs::write(&august, &edited).expect("edit the August file");

        // The bite: the stored snapshot's months are refused by their digests.
        let cache = ReplayCache::new(Some(root.join(CACHE_DIR)));
        assert!(cache.load_months(&snap, &["2026-08".to_string()]).is_none(), "an edited month file was served");
        assert!(cache.load_months(&snap, &["2026-09".to_string()]).is_some(), "an untouched month file is served");

        // A fresh process (the process caches are per root, so this one is new) asks for every record.
        caches().lock().unwrap_or_else(|p| p.into_inner()).remove(root);
        let read = replay_scoped(root, text.as_bytes(), tz, &tz_wire, today, Scope::All, None).expect("rebuilt, not a fault");
        assert!(read.notices.iter().any(|n| n.contains("does not match its digest") && n.contains("rebuilt from the log")), "{:?}", read.notices);
        let fresh = tempfile::tempdir().expect("a second scratch directory");
        let cacheless = replay_scoped(fresh.path(), text.as_bytes(), tz, &tz_wire, today, Scope::All, None).expect("a cache-less replay");
        assert_eq!(read.replay, cacheless.replay, "the answer is a cache-less replay's");

        let again = ReplayCache::new(Some(root.join(CACHE_DIR))).read_snapshot().expect("the rebuilt snapshot");
        assert_ne!(again.gen, snap.gen, "a new generation");
        for (m, rel) in &again.manifest {
            let t = std::fs::read_to_string(root.join(CACHE_DIR).join(rel)).expect("a named month file");
            assert_eq!(again.digests[m], month_digest(&t), "{m}: the rebuilt file matches its digest");
            assert_ne!(t, edited, "{m}: the edited file is served again");
        }
    }

    /// **A reseal never merges a month file that does not match its digest** (the owner's D93, README gap 4246):
    /// its read-modify-write would carry the edit into a new file under a FRESH digest, and every later read would
    /// trust it. Genesis at 2026-09-15 seals August and early September; five more days, and a replay at 2026-09-20
    /// reseals September — whose file has had one byte changed. The cache is rebuilt from the log instead: the
    /// replay's records are a cache-less genesis's, and no file the new manifest names holds the edit.
    #[test]
    fn a_reseal_never_merges_a_month_file_that_does_not_match_its_digest() {
        let dir = tempfile::tempdir().expect("a scratch directory");
        let cdir = dir.path().join(CACHE_DIR);
        let tz: Tz = "America/Chicago".parse().expect("a zone");
        let tz_wire = super::super::tz_table::wire_for(Some(&cdir), tz);
        let want = Want { facts: true, headers_from: None, render: vec![] };
        let mut cache = ReplayCache::new(Some(cdir.clone()));
        let day = |d: u32| day_of(chrono::NaiveDate::from_ymd_opt(2026, 9, d).expect("a date"));
        let first = cache.replay(wakes(45).as_bytes(), day(15), &tz_wire, None, &want).expect("genesis");
        assert_eq!(first.outcome, Outcome::Genesis);
        let september = cdir.join(&first.snapshot.manifest["2026-09"]);
        let mut text = std::fs::read_to_string(&september).expect("the September file");
        let at = text.find("480").expect("a night's 480 minutes") + 2;
        text.replace_range(at..at + 1, "1");
        std::fs::write(&september, &text).expect("edit the September file");

        let log = wakes(50);
        let r = cache.replay(log.as_bytes(), day(20), &tz_wire, None, &want).expect("rebuilt, not a fault");
        assert_eq!(r.outcome, Outcome::Genesis, "the reseal merged the edited file: {:?}", r.rebuilt_because);
        assert!(r.rebuilt_because.as_deref().is_some_and(|w| w.starts_with(MONTH_CORRUPT) && w.contains("2026-09")), "{:?}", r.rebuilt_because);
        assert!(r.notices.iter().any(|n| n.contains("2026-09 is missing or does not match its digest")), "{:?}", r.notices);

        let fresh = tempfile::tempdir().expect("a second scratch directory");
        let mut cacheless = ReplayCache::new(Some(fresh.path().join(CACHE_DIR)));
        let c = cacheless.replay(log.as_bytes(), day(20), &tz_wire, None, &want).expect("a cache-less genesis");
        assert_eq!((&r.days, &r.window), (&c.days, &c.window), "the rebuilt records are a cache-less genesis's");
        let snap = cache.read_snapshot().expect("the rebuilt snapshot");
        let (_, d, w) = cache.all_records(&snap).expect("every month file matches its digest");
        assert_eq!((&d, &w), (&c.days, &c.window));
        for rel in snap.manifest.values() {
            assert_ne!(std::fs::read_to_string(cdir.join(rel)).expect("a named file"), text, "the edited file is named");
        }
    }

    /// **A reseal over a MISSING month file rebuilds too** (README gap 4395, closed with D93's rule): it used to keep the
    /// reseal's new records alone in memory and answer every older-date read in the same verb from them — driven before
    /// this change, `Scope::All` answered 8 days of a 50-day log under the notice "kept in memory". Now the answer is a
    /// cache-less replay's, and the rebuilt manifest names files that are there and match their digests.
    #[test]
    fn a_reseal_over_a_missing_month_file_rebuilds_and_answers_as_a_cache_less_replay() {
        let tz: Tz = "America/Chicago".parse().expect("a zone");
        let dir = tempfile::tempdir().expect("a scratch directory");
        let root = dir.path();
        let tz_wire = super::super::tz_table::wire_for(Some(&root.join(CACHE_DIR)), tz);
        let (d15, d20) = (
            chrono::NaiveDate::from_ymd_opt(2026, 9, 15).expect("a date"),
            chrono::NaiveDate::from_ymd_opt(2026, 9, 20).expect("a date"),
        );
        replay_scoped(root, wakes(45).as_bytes(), tz, &tz_wire, d15, Scope::All, None).expect("genesis");
        let snap = ReplayCache::new(Some(root.join(CACHE_DIR))).read_snapshot().expect("a snapshot");
        std::fs::remove_file(root.join(CACHE_DIR).join(&snap.manifest["2026-09"])).expect("delete September");
        let read = replay_scoped(root, wakes(50).as_bytes(), tz, &tz_wire, d20, Scope::All, None).expect("rebuilt, not a fault");
        let fresh = tempfile::tempdir().expect("a second scratch directory");
        let cacheless = replay_scoped(fresh.path(), wakes(50).as_bytes(), tz, &tz_wire, d20, Scope::All, None).expect("a cache-less replay");
        assert_eq!(read.replay.days.len(), 50, "every day of the log");
        assert_eq!(read.replay, cacheless.replay, "the answer is a cache-less replay's");
        assert_eq!(read.outcome, Outcome::Genesis, "rebuilt from the log");
        assert!(read.notices.iter().any(|n| n.contains("2026-09 is missing or does not match its digest")), "{:?}", read.notices);
        let again = ReplayCache::new(Some(root.join(CACHE_DIR))).read_snapshot().expect("the rebuilt snapshot");
        for (m, rel) in &again.manifest {
            let t = std::fs::read_to_string(root.join(CACHE_DIR).join(rel)).expect("a named file is there");
            assert_eq!(again.digests[m], month_digest(&t), "{m}");
        }
    }

    /// **A cache written before D93 is rebuilt once** (README gap 4246): a format-3 `ckpt.json`, no digests, is not
    /// read; the next replay is a genesis that writes format 4, and the one after resumes it.
    #[test]
    fn a_checkpoint_written_before_d93_is_rebuilt_once() {
        let dir = tempfile::tempdir().expect("a scratch directory");
        let cdir = dir.path().join(CACHE_DIR);
        let tz: Tz = "America/Chicago".parse().expect("a zone");
        let tz_wire = super::super::tz_table::wire_for(Some(&cdir), tz);
        let want = Want { facts: true, headers_from: None, render: vec![] };
        let today = day_of(chrono::NaiveDate::from_ymd_opt(2026, 9, 15).expect("a date"));
        let log = wakes(45);
        let mut cache = ReplayCache::new(Some(cdir.clone()));
        let first = cache.replay(log.as_bytes(), today, &tz_wire, None, &want).expect("genesis");
        let ckpt = cdir.join(CKPT_FILE);
        let text = std::fs::read_to_string(&ckpt).expect("ckpt.json");
        let digests = format!("\"digests\":{},", serde_json::to_string(&first.snapshot.digests).expect("a map"));
        assert_eq!(text.matches(&digests).count(), 1, "{text}");
        // A format-3 file as the binary before D93 wrote it: no digests, and (before D98) no digest of its own.
        let body = text.strip_prefix(CKPT_DIGEST_HEAD).and_then(|r| r.get(16..)).and_then(|r| r.strip_prefix("\",")).expect("a digested checkpoint");
        let old = format!("{{{body}").replace(&digests, "").replace(&format!("\"format\":{FORMAT}"), "\"format\":3");
        std::fs::write(&ckpt, &old).expect("a format-3 checkpoint");
        assert!(Snapshot::from_text(&old).is_err(), "a format-3 checkpoint is read");
        let mut process = ReplayCache::new(Some(cdir.clone()));
        let r = process.replay(log.as_bytes(), today, &tz_wire, None, &want).expect("rebuilt");
        assert_eq!((r.outcome, r.rebuilt_because.as_deref()), (Outcome::Genesis, Some("no checkpoint")));
        let snap = Snapshot::from_text(&std::fs::read_to_string(&ckpt).expect("ckpt.json")).expect("this format again");
        assert!(!snap.digests.is_empty() && snap.digests.keys().eq(snap.manifest.keys()));
        let again = process.replay(log.as_bytes(), today, &tz_wire, None, &want).expect("a resume");
        assert_eq!((again.outcome, again.snapshot.gen.as_str()), (Outcome::Hot, snap.gen.as_str()), "rebuilt once, not twice");
    }

    /// **The checkpoint carries a digest of its own text, and no one-byte edit of it is ever read** (the campaign's
    /// D98, README gap 4394): over every byte of a checkpoint's text, the byte replaced by another printable one — a
    /// digit of the digest, a byte of its head, of the manifest, of the checkpoint itself — and `from_text` refuses
    /// the result. The digest's own argument is D93's (`a_digest_moves_with_every_single_byte_edit`): FNV-1a moves
    /// with every single-byte edit of a text of one length, and an edit of the digest is an edit of what the rest
    /// must match.
    #[test]
    fn a_checkpoint_one_byte_edited_is_never_read() {
        let s = Snapshot {
            kernel: kernel_id().into(),
            tz_key: "UTC".into(),
            prefix_lines: 2,
            log_lines: 3,
            prefix_bytes: 4,
            prefix_fnv: format!("{:016x}", fnv1a64(b"a\nb\n")),
            gen: "0123456789abcdef".into(),
            prev_gen: String::new(),
            manifest: BTreeMap::from([("2026-09".to_string(), "sealed/2026-09.g0123456789abcdef.json".to_string())]),
            digests: BTreeMap::from([("2026-09".to_string(), month_digest("{\"v\":1,\"days\":{},\"window\":{}}\n"))]),
            meta: Meta { cut: 2, ledger_day: 739870, horizon: 739855, reseal_day: 739872, max_t: Some((1, 0)), future_floor: None },
            ckpt: r#"{"v":1,"tzKey":"UTC","cut":2}"#.into(),
        };
        let text = s.to_text();
        assert!(text.starts_with(CKPT_DIGEST_HEAD), "{text}");
        assert_eq!(Snapshot::from_text(&text), Ok(s.clone()));
        let mut edits = 0;
        for i in 0..text.len() {
            let was = text.as_bytes()[i];
            let to = if was == b'7' { b'8' } else { b'7' };
            let mut bytes = text.clone().into_bytes();
            bytes[i] = to;
            let edited = String::from_utf8(bytes).expect("ASCII");
            assert!(Snapshot::from_text(&edited).is_err(), "byte {i} ({:?} -> {:?}) read back: {edited}", was as char, to as char);
            edits += 1;
        }
        assert_eq!(edits, text.len());
        // A checkpoint written before D98 — format 4, no digest of its own — is "another format": rebuilt, not named.
        let body = text.strip_prefix(CKPT_DIGEST_HEAD).and_then(|r| r.get(16..)).and_then(|r| r.strip_prefix("\",")).expect("a body");
        let before = format!("{{{body}").replace(&format!("\"format\":{FORMAT}"), "\"format\":4");
        assert_eq!(Snapshot::from_text(&before), Err("another format".to_string()));
        // The same text with a digest that does not match is named.
        let wrong = format!("{CKPT_DIGEST_HEAD}{}\",{body}", "0".repeat(16));
        assert_eq!(Snapshot::from_text(&wrong), Err(CKPT_CORRUPT.to_string()));
    }

    /// **A corrupted checkpoint is rebuilt, said once, and answers as a cache-less run** (D98, README gap 4394): the
    /// one-byte edit is not resumed from — genesis runs, says so once, and writes a checkpoint that matches; the
    /// replay after it resumes that and says nothing; and the facts are those of a run with no cache at all.
    #[test]
    fn a_corrupted_checkpoint_is_rebuilt_and_said_once() {
        let dir = tempfile::tempdir().expect("a scratch directory");
        let cdir = dir.path().join(CACHE_DIR);
        let tz: Tz = "America/Chicago".parse().expect("a zone");
        let tz_wire = super::super::tz_table::wire_for(Some(&cdir), tz);
        let want = Want { facts: true, headers_from: None, render: vec![] };
        let today = day_of(chrono::NaiveDate::from_ymd_opt(2026, 9, 15).expect("a date"));
        let log = wakes(45);
        let first = ReplayCache::new(Some(cdir.clone())).replay(log.as_bytes(), today, &tz_wire, None, &want).expect("genesis");
        assert!(!first.snapshot.manifest.is_empty(), "the log seals a month");
        let ckpt = cdir.join(CKPT_FILE);
        let text = std::fs::read_to_string(&ckpt).expect("ckpt.json");
        // One digit of `ledgerDay` moved by one: the checkpoint still parses, and is the wrong one to resume from.
        let at = text.find("\"ledgerDay\":").expect("a ledger day") + "\"ledgerDay\":".len();
        let mut bytes = text.clone().into_bytes();
        bytes[at + 3] = if bytes[at + 3] == b'9' { b'8' } else { bytes[at + 3] + 1 };
        let edited = String::from_utf8(bytes).expect("ASCII");
        assert_eq!(text.bytes().zip(edited.bytes()).filter(|(a, b)| a != b).count(), 1, "one byte");
        std::fs::write(&ckpt, &edited).expect("the edited checkpoint");

        let mut process = ReplayCache::new(Some(cdir.clone()));
        let r = process.replay(log.as_bytes(), today, &tz_wire, None, &want).expect("rebuilt");
        assert_eq!((r.outcome, r.rebuilt_because.as_deref()), (Outcome::Genesis, Some(CKPT_CORRUPT)));
        assert_eq!(r.notices, vec![corrupt_ckpt_notice()]);
        assert_eq!(r.answer.facts, first.answer.facts, "the facts are a cache-less run's");
        let healed = Snapshot::from_text(&std::fs::read_to_string(&ckpt).expect("ckpt.json")).expect("a checkpoint that matches");
        assert_eq!(healed.meta, first.snapshot.meta);
        let again = process.replay(log.as_bytes(), today, &tz_wire, None, &want).expect("a resume");
        assert_eq!((again.outcome, again.notices.len()), (Outcome::Hot, 0), "said once, rebuilt once");
    }

    /// **D18's named fault, raised before any call** (OWNER Q9 (iii), §17 P31, gap 120): a hand-edited first line longer
    /// than the resend cap's byte bound is a chunk of its own, so the first call genesis would make is already past the
    /// cap. It is not sent: genesis names the line, its kind and its size. The zone table here is `null`, which every
    /// real call faults on (`tzAbsent`), so a fault named `ReachTooFar` is proof that **no call was made** — if the cap
    /// check went away, this would come back a `Fault`, not the named fault.
    #[test]
    fn a_line_past_the_resend_cap_is_the_named_fault_before_any_call() {
        let mut text = format!(r#"{{"t":"2026-01-01T06:00:00Z","ev":"note","text":"{}"}}"#, "x".repeat(RESEND_BYTES));
        text.push('\n');
        text.push_str("{\"t\":\"2026-01-02T06:00:00Z\",\"ev\":\"wake\",\"slept_min\":420}\n");
        let s = split(text.as_bytes());
        assert_eq!(chunk_ends(&s), vec![1, 2], "the over-long line is a chunk of its own");
        assert!(s.bytes_between(0, 1) > RESEND_BYTES, "{} bytes", s.bytes_between(0, 1));
        let policy = Policy { keep_days: KEEP_DAYS, max_line: None };
        let e = genesis("2026-01-03", &Value::Null, &s, policy, &Want::default()).expect_err("no window reaches this line");
        assert_eq!(
            e,
            GenesisError::ReachTooFar { line: 1, kind: "unfolded".into(), reach: 1, bytes: s.bytes_between(0, 1) as u64 },
            "the named fault, not a kernel call"
        );
    }
}

// ---------------------------------------------------------------------------
// §11.1: the kernel's facts, decoded into Rust's `Replay`.

use tm_core::log::{
    fmt_timestamp, BreakRecord, CloseRecord, DayReplay, DaySeam, Demotion, DurationObs, EnergyObs, IdleMark, IdleRecord, InstanceRecord, Interruption,
    ItemReplay, LeakRecord, LogSegment, LogWarning, NamedLatest, NamedRecord, OpenBlock, Replay, SegmentKind, StartRecord, ViewRow,
};
use tm_core::model::InstanceStatus;

/// Seconds from `0001-01-01T00:00:00Z` to the Unix epoch — one number, stated
/// once, in the host's kernel codec since stage 6 W-35.
use tm_core::planwire::EPOCH_FROM_CE;

/// What a malformed answer says. Every decoder below names the field it could
/// not read, as `read_response` and [`Refusal`] do; nothing here panics, so a
/// kernel that changes a shape is a named error and not a crash.
type D<T> = Result<T, String>;

fn d_arr<'a>(v: &'a Value, what: &str) -> D<&'a Vec<Value>> {
    v.as_array().ok_or_else(|| format!("{what}: not an array"))
}
fn d_at<'a>(a: &'a [Value], i: usize, what: &str) -> D<&'a Value> {
    a.get(i).ok_or_else(|| format!("{what}: no field {i} of {}", a.len()))
}
fn d_tuple<'a>(v: &'a Value, n: usize, what: &str) -> D<&'a Vec<Value>> {
    let a = d_arr(v, what)?;
    if a.len() != n {
        return Err(format!("{what}: {} fields, not {n}", a.len()));
    }
    Ok(a)
}
fn d_u64(v: &Value, what: &str) -> D<u64> {
    v.as_u64().ok_or_else(|| format!("{what}: not a number"))
}
fn d_i64(v: &Value, what: &str) -> D<i64> {
    v.as_i64().ok_or_else(|| format!("{what}: not a signed number"))
}
fn d_str(v: &Value, what: &str) -> D<String> {
    Ok(v.as_str().ok_or_else(|| format!("{what}: not a string"))?.to_string())
}
fn d_bool(v: &Value, what: &str) -> D<bool> {
    v.as_bool().ok_or_else(|| format!("{what}: not a boolean"))
}
fn d_strs(v: &Value, what: &str) -> D<Vec<String>> {
    d_arr(v, what)?.iter().map(|s| d_str(s, what)).collect()
}
fn d_opt<T>(v: &Value, f: impl FnOnce(&Value) -> D<T>) -> D<Option<T>> {
    if v.is_null() {
        Ok(None)
    } else {
        f(v).map(Some)
    }
}
/// A minute or count the fork holds in a `u32`. **Parity P17**: the kernel
/// counts in `Nat`, and a sum past `u32::MAX` is refused here by name rather
/// than saturated.
fn d_u32(v: &Value, what: &str) -> D<u32> {
    u32::try_from(d_u64(v, what)?).map_err(|_| format!("minutesOverflow at {what}"))
}
fn d_u8(v: &Value, what: &str) -> D<u8> {
    u8::try_from(d_u64(v, what)?).map_err(|_| format!("{what}: not a U8"))
}
/// An instant as the kernel writes one: `[sec, ns, west, offsetSec]`, seconds
/// from `0001-01-01T00:00:00Z`, with the offset **as written** kept.
fn d_when(v: &Value, what: &str) -> D<DateTime<FixedOffset>> {
    let a = d_tuple(v, 4, what)?;
    let (sec, ns) = (d_i64(d_at(a, 0, what)?, what)?, d_u32(d_at(a, 1, what)?, what)?);
    let west = d_bool(d_at(a, 2, what)?, what)?;
    let off = i32::try_from(d_u64(d_at(a, 3, what)?, what)?).map_err(|_| format!("{what}: an offset"))?;
    let off = FixedOffset::east_opt(if west { -off } else { off }).ok_or_else(|| format!("{what}: an offset"))?;
    let t = DateTime::from_timestamp(sec - EPOCH_FROM_CE, ns).ok_or_else(|| format!("{what}: an instant"))?;
    Ok(t.with_timezone(&off))
}
/// A day, counted from `0001-01-01` as `Cal.Day` is.
fn d_date(v: &Value, what: &str) -> D<NaiveDate> {
    let d = d_i64(v, what)?;
    let n = i32::try_from(d + 1).map_err(|_| format!("{what}: a day"))?;
    NaiveDate::from_num_days_from_ce_opt(n).ok_or_else(|| format!("{what}: a day"))
}

/// A list the fork keeps in file order, restored by the line each record carries.
fn in_line_order<T>(mut xs: Vec<(u64, T)>) -> Vec<T> {
    xs.sort_by_key(|x| x.0);
    xs.into_iter().map(|x| x.1).collect()
}

/// A segment kind in the codec's numeral tags (`[0, id]` block, `[1, id]` pause,
/// `[2, id?]` interrupt, `[3, where?]` break, `[4, item, inst]` routine,
/// `[5, attributed]` idle).
fn d_seg_kind(v: &Value) -> D<SegmentKind> {
    let a = d_arr(v, "a segment kind")?;
    let arg = |i: usize| -> D<Option<String>> {
        match a.get(i) {
            None | Some(Value::Null) => Ok(None),
            Some(x) => d_str(x, "a segment argument").map(Some),
        }
    };
    let need = |i: usize, what: &str| -> D<String> { arg(i)?.ok_or_else(|| format!("a segment kind: no {what}")) };
    match d_u64(d_at(a, 0, "a segment kind's tag")?, "a segment kind's tag")? {
        0 => Ok(SegmentKind::Block { id: need(1, "id")? }),
        1 => Ok(SegmentKind::Pause { id: need(1, "id")? }),
        2 => Ok(SegmentKind::Interrupt { id: arg(1)? }),
        3 => Ok(SegmentKind::Break { r#where: arg(1)? }),
        4 => Ok(SegmentKind::Routine { item: need(1, "item")?, inst: need(2, "inst")? }),
        5 => Ok(SegmentKind::Idle { attributed: need(1, "attribution")? }),
        t => Err(format!("a segment kind tag {t}")),
    }
}

/// An idle mark in the codec's numeral tags (`[0, t]` pause, `[1, t]` interrupt,
/// `[2, t]` unpause, `[3, t]` resume, `[4, t, actual]` break).
fn d_idle_mark(v: &Value) -> D<IdleMark> {
    let a = d_arr(v, "an idle mark")?;
    let t = d_when(d_at(a, 1, "an idle mark's t")?, "an idle mark's t")?;
    match d_u64(d_at(a, 0, "an idle mark's tag")?, "an idle mark's tag")? {
        0 => Ok(IdleMark::Pause(t)),
        1 => Ok(IdleMark::Interrupt(t)),
        2 => Ok(IdleMark::Unpause(t)),
        3 => Ok(IdleMark::Resume(t)),
        4 => Ok(IdleMark::Break { t, actual_min: d_opt(d_at(a, 2, "a break mark's minutes")?, |x| d_u32(x, "a break mark's minutes"))? }),
        t => Err(format!("an idle mark tag {t}")),
    }
}

/// A demotion's stamp in the codec's shape, `[0, week]` or `[1, day]`, as
/// `demoted:` writes it (`W37`, `D07`).
fn d_demotion_stamp(v: &Value) -> D<tm_core::model::Stamp> {
    let a = d_arr(v, "a demotion stamp")?;
    let n = d_u64(d_at(a, 1, "a demotion stamp's number")?, "a demotion stamp's number")?;
    let text = match d_u64(d_at(a, 0, "a demotion stamp's tag")?, "a demotion stamp's tag")? {
        0 => format!("W{n:02}"),
        1 => format!("D{n:02}"),
        t => return Err(format!("a demotion stamp tag {t}")),
    };
    tm_core::model::Stamp::parse(&text).map_err(|_| format!("a demotion stamp {text}"))
}

/// An interruption, `[line, start, stop, day, id, lost, dropped]`: the line of
/// the `resume` that pushed it (0 for the still-open one), and the fork's record.
fn d_interruption(v: &Value) -> D<(u64, Interruption)> {
    let a = d_tuple(v, 7, "an interruption")?;
    Ok((
        d_u64(d_at(a, 0, "an interruption's line")?, "an interruption's line")?,
        Interruption {
            start: d_opt(d_at(a, 1, "an interruption's start")?, |x| d_when(x, "an interruption's start"))?,
            end: d_opt(d_at(a, 2, "an interruption's end")?, |x| d_when(x, "an interruption's end"))?,
            day: d_date(d_at(a, 3, "an interruption's day")?, "an interruption's day")?,
            id: d_opt(d_at(a, 4, "an interruption's id")?, |x| d_str(x, "an interruption's id"))?,
            lost_min: d_u32(d_at(a, 5, "an interruption's lost minutes")?, "an interruption's lost minutes")?,
            dropped: d_strs(d_at(a, 6, "an interruption's dropped ids")?, "an interruption's dropped ids")?,
        },
    ))
}

/// A routine instance, `[[item, inst], [t, status, raw, actualMin]]`, its status
/// a numeral (done 0, pending 1, missed 2, expired 3, skipped 4).
fn d_instance(v: &Value) -> D<((String, String), InstanceRecord)> {
    let a = d_tuple(v, 2, "an instance")?;
    let key = d_tuple(d_at(a, 0, "an instance key")?, 2, "an instance key")?;
    let rec = d_arr(d_at(a, 1, "an instance record")?, "an instance record")?;
    let status = match d_u64(d_at(rec, 1, "an instance status")?, "an instance status")? {
        0 => InstanceStatus::Done,
        1 => InstanceStatus::Pending,
        2 => InstanceStatus::Missed,
        3 => InstanceStatus::Expired,
        4 => InstanceStatus::Skipped,
        s => return Err(format!("an instance status {s}")),
    };
    Ok((
        (d_str(d_at(key, 0, "an instance's item")?, "an instance's item")?, d_str(d_at(key, 1, "an instance's inst")?, "an instance's inst")?),
        InstanceRecord {
            t: d_when(d_at(rec, 0, "an instance's t")?, "an instance's t")?,
            status,
            raw_status: d_str(d_at(rec, 2, "an instance's raw status")?, "an instance's raw status")?,
            actual_min: d_opt(d_at(rec, 3, "an instance's minutes")?, |x| d_u32(x, "an instance's minutes"))?,
        },
    ))
}

/// **The kernel's facts as a `tm_core::log::Replay`** (design §11.1).
///
/// `answer` is one `log` answer — the object under `ok.log` — whose `facts` the
/// kernel has already merged with every sealed record the request sent
/// (`LogReq.merged`, §10.1's `sealed`), so the scope a verb asked for is already
/// in front of this decoder and it merges nothing itself. Every field of
/// `Replay` is built from that answer and from its `headers` and `lines`:
/// nothing here reads `.tm/log.jsonl`, and nothing here borrows from the Rust
/// reader the switch deletes. That is gap 128, and this function is its closure.
///
/// **What comes from where.** The facts give the days, items, window, instances,
/// named events, open machine and counts. The answer's `headers`
/// (`want.headersFrom`) give each row's display; each day record's own headers
/// give its rows' tag, id, mask bit and instant. `answer.lines` is the physical
/// line count. `Replay::range` is `None`: a kernel answer is never a ranged
/// replay.
///
/// **One narrowing, named** (gap 133): a replay warning's text embeds the warned
/// line's timestamp, which this decoder takes from that line's header. In the
/// `Hot` scope a folded line has no header, and such a warning is dropped. It
/// has no reader in the binary — `Replay::warnings` is read by no verb — and T5
/// compares it in full at every scope that carries the headers.
pub fn decode_facts(answer: &Value, tz: Tz) -> D<Replay> {
    let v = answer.get("facts").ok_or("no facts in the answer")?;
    if !v.is_object() {
        return Err("facts: not an object".to_string());
    }

    // The display of every line the answer carries a header for.
    let mut displays: BTreeMap<u64, String> = BTreeMap::new();
    for h in d_arr(answer.get("headers").unwrap_or(&Value::Null), "headers")? {
        let a = d_tuple(h, 6, "a header")?;
        displays.insert(
            d_u64(d_at(a, 0, "a header's line")?, "a header's line")?,
            d_str(d_at(a, 5, "a header's display")?, "a header's display")?,
        );
    }

    let mut days: BTreeMap<NaiveDate, DayReplay> = BTreeMap::new();
    let mut seams: BTreeMap<NaiveDate, DaySeam> = BTreeMap::new();
    let mut energy: Vec<(u64, EnergyObs)> = Vec::new();
    let mut durations: Vec<(u64, DurationObs)> = Vec::new();
    let mut interrupts: Vec<(u64, Interruption)> = Vec::new();
    let mut demotions: Vec<(u64, Demotion)> = Vec::new();
    let mut closes: Vec<(u64, CloseRecord)> = Vec::new();
    let mut rows: Vec<(u64, ViewRow)> = Vec::new();

    for p in d_arr(v.get("days").unwrap_or(&Value::Null), "facts.days")? {
        let p = d_tuple(p, 9, "a day")?;
        let dn = d_at(p, 0, "a day's number")?;
        let date = d_date(dn, "a day's number")?;
        let rec = d_at(p, 1, "a day record")?;
        if !rec.is_null() {
            let a = d_tuple(rec, 28, "a day record")?;
            let g = |i: usize, what: &'static str| -> D<&Value> { d_at(a, i, what) };
            let mut ci_unknown = BTreeMap::new();
            for c in d_arr(g(6, "ciUnknown")?, "ciUnknown")? {
                let c = d_tuple(c, 2, "a ciUnknown pair")?;
                ci_unknown.insert(
                    d_str(d_at(c, 0, "a ciUnknown id")?, "a ciUnknown id")?,
                    d_u32(d_at(c, 1, "a ciUnknown minute")?, "a ciUnknown minute")?,
                );
            }
            let by_ci = d_tuple(g(5, "byCi")?, 6, "byCi")?;
            let mut minutes_by_ci = [0u32; 6];
            for (i, slot) in minutes_by_ci.iter_mut().enumerate() {
                *slot = d_u32(d_at(by_ci, i, "a byCi minute")?, "a byCi minute")?;
            }
            let day = DayReplay {
                date,
                wake: d_opt(g(11, "wake")?, |x| d_when(x, "wake"))?,
                slept_min: d_opt(g(12, "sleptMin")?, |x| d_u32(x, "sleptMin"))?,
                onset_min: d_opt(g(13, "onsetMin")?, |x| d_u32(x, "onsetMin"))?,
                arrival: d_opt(g(14, "arrival")?, |x| d_when(x, "arrival"))?,
                loc: d_opt(g(15, "loc")?, |x| d_str(x, "loc"))?,
                window: d_opt(g(16, "window")?, |x| {
                    let w = d_tuple(x, 2, "a window")?;
                    Ok([d_str(d_at(w, 0, "a window")?, "a window")?, d_str(d_at(w, 1, "a window")?, "a window")?])
                })?,
                budget: d_opt(g(17, "budget")?, |x| d_u32(x, "budget"))?,
                loc_changes: d_arr(g(18, "locChanges")?, "locChanges")?
                    .iter()
                    .map(|c| {
                        let c = d_tuple(c, 2, "a location change")?;
                        Ok((d_when(d_at(c, 0, "a location change")?, "a location change")?, d_str(d_at(c, 1, "a location")?, "a location")?))
                    })
                    .collect::<D<Vec<_>>>()?,
                first_start: d_opt(g(0, "firstStart")?, |x| d_when(x, "firstStart"))?,
                starts: d_arr(g(1, "starts")?, "starts")?
                    .iter()
                    .map(|r| {
                        let r = d_tuple(r, 4, "a start")?;
                        Ok(StartRecord {
                            t: d_when(d_at(r, 0, "a start's t")?, "a start's t")?,
                            id: d_str(d_at(r, 1, "a start's id")?, "a start's id")?,
                            pred: d_u8(d_at(r, 2, "a start's pred")?, "a start's pred")?,
                            rep: d_opt(d_at(r, 3, "a start's rep")?, |x| d_u8(x, "a start's rep"))?,
                        })
                    })
                    .collect::<D<Vec<_>>>()?,
                block_min: d_u32(g(2, "blockMin")?, "blockMin")?,
                blocks_done: d_u32(g(3, "blocksDone")?, "blocksDone")?,
                load_fifths: d_u64(g(4, "loadFifths")?, "loadFifths")?,
                minutes_by_ci,
                ci_unknown,
                done: d_strs(g(7, "done")?, "done")?,
                lost_min: d_u32(g(8, "lostMin")?, "lostMin")?,
                dropped: d_strs(g(9, "dropped")?, "dropped")?,
                leak_min: d_u32(g(19, "leakMin")?, "leakMin")?,
                longest_leak: d_u32(g(20, "longestLeak")?, "longestLeak")?,
                idle: d_arr(g(21, "idle")?, "idle")?
                    .iter()
                    .map(|r| {
                        let r = d_tuple(r, 4, "an idle record")?;
                        Ok(IdleRecord {
                            t: d_when(d_at(r, 0, "an idle record's t")?, "an idle record's t")?,
                            day: d_date(d_at(r, 1, "an idle record's day")?, "an idle record's day")?,
                            attributed: d_str(d_at(r, 2, "an idle attribution")?, "an idle attribution")?,
                            min: d_u32(d_at(r, 3, "an idle record's minutes")?, "an idle record's minutes")?,
                        })
                    })
                    .collect::<D<Vec<_>>>()?,
                breaks: d_arr(g(22, "breaks")?, "breaks")?
                    .iter()
                    .map(|r| {
                        let r = d_tuple(r, 5, "a break")?;
                        Ok(BreakRecord {
                            t: d_when(d_at(r, 0, "a break's t")?, "a break's t")?,
                            day: d_date(d_at(r, 1, "a break's day")?, "a break's day")?,
                            planned_min: d_u32(d_at(r, 2, "a break's planned minutes")?, "a break's planned minutes")?,
                            actual_min: d_opt(d_at(r, 3, "a break's actual minutes")?, |x| d_u32(x, "a break's actual minutes"))?,
                            r#where: d_opt(d_at(r, 4, "a break's where")?, |x| d_str(x, "a break's where"))?,
                        })
                    })
                    .collect::<D<Vec<_>>>()?,
                routine_min: d_u32(g(23, "routineMin")?, "routineMin")?,
                plans: d_u32(g(24, "plans")?, "plans")?,
                replans_today: d_u32(g(25, "replansToday")?, "replansToday")?,
                drift_min: d_u32(g(26, "driftMin")?, "driftMin")?,
                last_plan_hash: d_opt(g(27, "lastPlanHash")?, |x| d_str(x, "lastPlanHash"))?,
                segments: d_arr(g(10, "segments")?, "segments")?
                    .iter()
                    .map(|s| {
                        let s = d_tuple(s, 3, "a segment")?;
                        Ok(LogSegment {
                            start: d_when(d_at(s, 0, "a segment's start")?, "a segment's start")?,
                            end: d_when(d_at(s, 1, "a segment's end")?, "a segment's end")?,
                            kind: d_seg_kind(d_at(s, 2, "a segment's kind")?)?,
                        })
                    })
                    .collect::<D<Vec<_>>>()?,
            };
            if days.insert(date, day).is_some() {
                return Err(format!("a repeated day {date}"));
            }
        }
        let seam = d_at(p, 2, "a seam")?;
        if !seam.is_null() {
            let a = d_tuple(seam, 3, "a seam")?;
            seams.insert(
                date,
                DaySeam {
                    since_break: d_opt(d_at(a, 0, "sinceBreak")?, |x| d_when(x, "sinceBreak"))?,
                    idle_marks: d_arr(d_at(a, 1, "idleMarks")?, "idleMarks")?.iter().map(d_idle_mark).collect::<D<Vec<_>>>()?,
                    last_t: d_opt(d_at(a, 2, "lastT")?, |x| d_when(x, "lastT"))?,
                },
            );
        }
        for o in d_arr(d_at(p, 3, "a day's energy")?, "energy")? {
            let o = d_tuple(o, 11, "an energy observation")?;
            let line = d_u64(d_at(o, 0, "an observation's line")?, "an observation's line")?;
            energy.push((
                line,
                EnergyObs {
                    line,
                    t: d_when(d_at(o, 1, "an observation's t")?, "an observation's t")?,
                    day: d_date(d_at(o, 2, "an observation's day")?, "an observation's day")?,
                    pred: d_u8(d_at(o, 3, "pred")?, "pred")?,
                    rep: d_u8(d_at(o, 4, "rep")?, "rep")?,
                    hsw: d_at(o, 5, "hsw")?.as_f64().ok_or("hsw: not a number")?,
                    loc: d_str(d_at(o, 6, "loc")?, "loc")?,
                    slept_min: d_opt(d_at(o, 7, "sleptMin")?, |x| d_u32(x, "sleptMin"))?,
                    went: d_opt(d_at(o, 8, "went")?, |x| d_u8(x, "went"))?,
                    id: d_opt(d_at(o, 9, "an observation's id")?, |x| d_str(x, "an observation's id"))?,
                    from_start: d_bool(d_at(o, 10, "fromStart")?, "fromStart")?,
                },
            ));
        }
        for o in d_arr(d_at(p, 4, "a day's durations")?, "durations")? {
            let o = d_tuple(o, 10, "a duration observation")?;
            let line = d_u64(d_at(o, 0, "a duration's line")?, "a duration's line")?;
            durations.push((
                line,
                DurationObs {
                    line,
                    t: d_when(d_at(o, 1, "a duration's t")?, "a duration's t")?,
                    day: d_date(d_at(o, 2, "a duration's day")?, "a duration's day")?,
                    id: d_str(d_at(o, 3, "a duration's id")?, "a duration's id")?,
                    ci: d_u8(d_at(o, 4, "ci")?, "ci")?,
                    tags: d_strs(d_at(o, 5, "tags")?, "tags")?,
                    est_min: d_u32(d_at(o, 6, "estMin")?, "estMin")?,
                    actual_min: d_u32(d_at(o, 7, "actualMin")?, "actualMin")?,
                    went: d_opt(d_at(o, 8, "went")?, |x| d_u8(x, "went"))?,
                    partial: d_bool(d_at(o, 9, "partial")?, "partial")?,
                },
            ));
        }
        for o in d_arr(d_at(p, 5, "a day's interrupts")?, "interrupts")? {
            interrupts.push(d_interruption(o)?);
        }
        for o in d_arr(d_at(p, 6, "a day's demotions")?, "demotions")? {
            let o = d_tuple(o, 7, "a demotion")?;
            let id = d_str(d_at(o, 2, "a demotion's id")?, "a demotion's id")?;
            demotions.push((
                d_u64(d_at(o, 0, "a demotion's line")?, "a demotion's line")?,
                Demotion {
                    t: d_when(d_at(o, 1, "a demotion's t")?, "a demotion's t")?,
                    id,
                    from: d_str(d_at(o, 3, "a demotion's from")?, "a demotion's from")?,
                    to: d_str(d_at(o, 4, "a demotion's to")?, "a demotion's to")?,
                    est_min: d_u32(d_at(o, 5, "a demotion's estimate")?, "a demotion's estimate")?,
                    stamp: d_opt(d_at(o, 6, "a demotion's stamp")?, d_demotion_stamp)?,
                },
            ));
        }
        for o in d_arr(d_at(p, 7, "a day's closes")?, "closes")? {
            let o = d_tuple(o, 4, "a close")?;
            closes.push((
                d_u64(d_at(o, 0, "a close's line")?, "a close's line")?,
                CloseRecord {
                    t: d_when(d_at(o, 1, "a close's t")?, "a close's t")?,
                    period: d_str(d_at(o, 2, "a close's period")?, "a close's period")?,
                    key: d_str(d_at(o, 3, "a close's key")?, "a close's key")?,
                },
            ));
        }
        for h in d_arr(d_at(p, 8, "a day's headers")?, "headers")? {
            let h = d_tuple(h, 6, "a day's header")?;
            let line = d_u64(d_at(h, 0, "a header's line")?, "a header's line")?;
            let (sec, off) = (d_tuple(d_at(h, 4, "a header's t")?, 2, "a header's t")?, d_tuple(d_at(h, 5, "a header's offset")?, 2, "a header's offset")?);
            let when = serde_json::json!([sec[0], sec[1], off[0], off[1]]);
            rows.push((
                line,
                ViewRow {
                    line,
                    tag: d_str(d_at(h, 1, "a header's tag")?, "a header's tag")?,
                    id: d_opt(d_at(h, 2, "a header's id")?, |x| d_str(x, "a header's id"))?,
                    t: d_when(&when, "a header's t")?,
                    day: date,
                    cancelled: d_bool(d_at(h, 3, "a header's mask bit")?, "a header's mask bit")?,
                },
            ));
        }
    }

    // Items: the record, the latest completion, the dropped bit.
    let mut items: BTreeMap<String, ItemReplay> = BTreeMap::new();
    let mut last_done: BTreeMap<String, DateTime<FixedOffset>> = BTreeMap::new();
    let mut dropped_items: BTreeSet<String> = BTreeSet::new();
    let mut done_date_totals: BTreeMap<String, (Option<NaiveDate>, u32)> = BTreeMap::new();
    for p in d_arr(v.get("items").unwrap_or(&Value::Null), "facts.items")? {
        let p = d_tuple(p, 6, "an item")?;
        let id = d_str(d_at(p, 0, "an item's id")?, "an item's id")?;
        let rec = d_at(p, 1, "an item record")?;
        if !rec.is_null() {
            let o = d_tuple(rec, 6, "an item record")?;
            let item = ItemReplay {
                id: id.clone(),
                minutes: d_u32(d_at(o, 0, "an item's minutes")?, "an item's minutes")?,
                blocks: d_u32(d_at(o, 1, "an item's blocks")?, "an item's blocks")?,
                minutes_by_day: BTreeMap::new(),
                done_at: d_arr(d_at(o, 2, "doneAt")?, "doneAt")?.iter().map(|x| d_when(x, "doneAt")).collect::<D<Vec<_>>>()?,
                partial_done_at: d_arr(d_at(o, 3, "partialDoneAt")?, "partialDoneAt")?.iter().map(|x| d_when(x, "partialDoneAt")).collect::<D<Vec<_>>>()?,
                stops: d_u32(d_at(o, 4, "stops")?, "stops")?,
                extended_min: d_u32(d_at(o, 5, "extendedMin")?, "extendedMin")?,
            };
            if items.insert(id.clone(), item).is_some() {
                return Err(format!("a repeated item {id}"));
            }
        }
        if let Some(t) = d_opt(d_at(p, 2, "an item's lastDone")?, |x| d_when(x, "lastDone"))? {
            last_done.insert(id.clone(), t);
        }
        // **The all-time done-date facts** (§8.4's `done_dates` row, column A):
        // the first done date and the count of distinct ones, over *every*
        // date, a date below the horizon included (`Seal.ItemAgg`). They are
        // read here rather than derived from the window's dates because the
        // window is exactly what a narrowed scope drops: `done_dates` carries
        // the dates at or above the horizon, and `.first()`/`.len()` over it
        // would answer for that suffix. `tm plan`'s `every:Nd` phase anchor and
        // the ordinal recurrences' pending number are those two questions.
        let first = d_opt(d_at(p, 4, "an item's first done date")?, |x| d_date(x, "an item's first done date"))?;
        let count = d_u32(d_at(p, 5, "an item's done-date count")?, "an item's done-date count")?;
        if first.is_some() || count > 0 {
            done_date_totals.insert(id.clone(), (first, count));
        }
        if d_bool(d_at(p, 3, "an item's dropped bit")?, "an item's dropped bit")? {
            dropped_items.insert(id);
        }
    }

    // The window: item-day minutes, done dates, date-keyed instances.
    let mut done_dates: BTreeMap<String, BTreeSet<NaiveDate>> = BTreeMap::new();
    let mut instances: BTreeMap<String, BTreeMap<String, InstanceRecord>> = BTreeMap::new();
    for w in d_arr(v.get("window").unwrap_or(&Value::Null), "facts.window")? {
        let w = d_tuple(w, 4, "a window date")?;
        let date = d_date(d_at(w, 0, "a window date")?, "a window date")?;
        for m in d_arr(d_at(w, 1, "itemMin")?, "itemMin")? {
            let m = d_tuple(m, 2, "an item's minutes")?;
            let id = d_str(d_at(m, 0, "an item's id")?, "an item's id")?;
            let min = d_u32(d_at(m, 1, "an item's minutes")?, "an item's minutes")?;
            items
                .get_mut(&id)
                .ok_or_else(|| format!("minutes on {date} of {id}, which has no item record"))?
                .minutes_by_day
                .insert(date, min);
        }
        for id in d_strs(d_at(w, 2, "a window date's done ids")?, "a window date's done ids")? {
            done_dates.entry(id).or_default().insert(date);
        }
        for r in d_arr(d_at(w, 3, "a window date's instances")?, "inst")? {
            let ((item, inst), rec) = d_instance(r)?;
            instances.entry(item).or_default().insert(inst, rec);
        }
    }
    for r in d_arr(v.get("instOther").unwrap_or(&Value::Null), "facts.instOther")? {
        let ((item, inst), rec) = d_instance(r)?;
        instances.entry(item).or_default().insert(inst, rec);
    }

    // `tm event`, narrowed to the latest per `(name, id?)` (§8.4).
    let mut named: BTreeMap<String, NamedRecord> = BTreeMap::new();
    for r in d_arr(v.get("named").unwrap_or(&Value::Null), "facts.named")? {
        let r = d_tuple(r, 2, "a named record")?;
        let key = d_tuple(d_at(r, 0, "a named key")?, 2, "a named key")?;
        let rec = d_tuple(d_at(r, 1, "a named record's value")?, 2, "a named record's value")?;
        let latest = d_tuple(d_at(rec, 0, "the latest occurrence")?, 2, "the latest occurrence")?;
        let dated = d_tuple(d_at(rec, 1, "the dated occurrence")?, 2, "the dated occurrence")?;
        let dated = d_tuple(d_at(dated, 1, "the dated occurrence's line and t")?, 2, "the dated occurrence's line and t")?;
        let rec = NamedLatest {
            latest: d_when(d_at(latest, 1, "the latest occurrence's t")?, "the latest occurrence's t")?,
            latest_line: d_u64(d_at(latest, 0, "the latest occurrence's line")?, "the latest occurrence's line")?,
            latest_dated: d_when(d_at(dated, 1, "the dated occurrence's t")?, "the dated occurrence's t")?,
            dated_line: d_u64(d_at(dated, 0, "the dated occurrence's line")?, "the dated occurrence's line")?,
        };
        let name = d_str(d_at(key, 0, "a named key's name")?, "a named key's name")?;
        let who = d_opt(d_at(key, 1, "a named key's id")?, |x| d_str(x, "a named key's id"))?;
        let slot = named.entry(name).or_default();
        match who {
            None => slot.unaddressed = Some(rec),
            Some(i) => {
                slot.by_id.insert(i, rec);
            }
        }
    }

    let rows: Vec<ViewRow> = in_line_order(rows);
    // The replay warnings, in the fork's words: one a surviving routine whose
    // status the fork does not read, stamped with the warned line's own `t`.
    let mut warnings: Vec<String> = Vec::new();
    for x in d_arr(v.get("replayWarnings").unwrap_or(&Value::Null), "facts.replayWarnings")? {
        let x = d_tuple(x, 2, "a replay warning")?;
        let line = d_u64(d_at(x, 0, "a replay warning's line")?, "a replay warning's line")?;
        let raw = d_str(d_at(x, 1, "a replay warning's status")?, "a replay warning's status")?;
        // Gap 133: no header for the line, no timestamp to print with it.
        if let Ok(i) = rows.binary_search_by_key(&line, |r| r.line) {
            warnings.push(format!("{}: unknown routine status {raw:?}", fmt_timestamp(&rows[i].t)));
        }
    }

    let open = v.get("open").unwrap_or(&Value::Null);
    let open_block = d_opt(open.get("block").unwrap_or(&Value::Null), |o| {
        let o = d_tuple(o, 5, "the open block")?;
        Ok(OpenBlock {
            id: d_str(d_at(o, 0, "the open block's id")?, "the open block's id")?,
            started: d_when(d_at(o, 1, "the open block's start")?, "the open block's start")?,
            worked_min: d_u32(d_at(o, 2, "the open block's minutes")?, "the open block's minutes")?,
            since: d_opt(d_at(o, 3, "the open block's since")?, |x| d_when(x, "the open block's since"))?,
            paused: d_bool(d_at(o, 4, "the open block's paused bit")?, "the open block's paused bit")?,
        })
    })?;
    let open_interrupt = d_opt(open.get("interrupt").unwrap_or(&Value::Null), |o| d_interruption(o).map(|p| p.1))?;
    let longest_leak = d_opt(v.get("longestLeak").unwrap_or(&Value::Null), |x| {
        let x = d_tuple(x, 3, "the longest leak")?;
        Ok(LeakRecord {
            t: d_when(d_at(x, 0, "the longest leak's t")?, "the longest leak's t")?,
            day: d_date(d_at(x, 1, "the longest leak's day")?, "the longest leak's day")?,
            min: d_u32(d_at(x, 2, "the longest leak's minutes")?, "the longest leak's minutes")?,
        })
    })?;

    Ok(Replay {
        tz,
        range: None,
        days,
        items,
        instances,
        energy: in_line_order(energy),
        durations: in_line_order(durations),
        interrupts: in_line_order(interrupts),
        named,
        demotions: {
            let mut by_id: BTreeMap<String, Vec<Demotion>> = BTreeMap::new();
            for d in in_line_order(demotions) {
                by_id.entry(d.id.clone()).or_default().push(d);
            }
            by_id
        },
        closes: in_line_order(closes),
        dropped_items,
        done_items: last_done.keys().cloned().collect(),
        last_done,
        done_dates,
        longest_leak,
        open_block,
        open_interrupt,
        unknown: d_u32(v.get("unknown").unwrap_or(&Value::Null), "facts.unknown")?,
        warnings,
        seams,
        last_effective_t: d_opt(v.get("lastEffective").unwrap_or(&Value::Null), |x| d_when(x, "lastEffective"))?,
        rows,
        line_count: d_u64(answer.get("lines").unwrap_or(&Value::Null), "the answer's line count")?,
        // §11.4 step 5: `tm log`'s `total` is the log's all-time entry count,
        // which the checkpoint carries, not the row count of this scope.
        entry_count: usize::try_from(d_u64(v.get("entryCount").unwrap_or(&Value::Null), "facts.entryCount")?)
            .map_err(|_| "facts.entryCount: too many entries".to_string())?,
        done_date_totals,
    })
}

// ---------------------------------------------------------------------------
// The switch (S, design §14.6): the one door `Ctx::replay_with` calls.

/// **The replay a verb family asks for** (§11.1), host side.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scope {
    /// The answer only (A, W, O).
    Hot,
    /// The answer, plus day records for `[from − 1, to + 1]` and window records for `[from, to]`.
    Dates { from: NaiveDate, to: NaiveDate },
    /// The answer, plus every month's records.
    All,
}

/// **What one scoped replay gives a verb**: the decoded `Replay`, how it was answered, and the
/// notices the cache raised (an unwritable directory, a generation that moved underneath).
#[derive(Clone, Debug)]
pub struct Read {
    pub replay: Replay,
    // `Replayed::outcome` is read; this copy of it, on the *scoped* read, is not — no verb
    // branches on how its replay was answered. Kept so the scoped path does not silently lose
    // the genesis/reseal/hot distinction the unscoped one carries.
    #[allow(dead_code)]
    pub outcome: Outcome,
    pub notices: Vec<String>,
    /// **The checkpoint's ledger day `L` after this call** (§9.1), or `None`
    /// when nothing is sealed.
    ///
    /// Every day below `L` is final; days at or above it stay in the
    /// checkpoint as open days, so how far `L` trails `now` is what a stall
    /// costs (§9.4, §18.7). `tm check` reads it to name one (README gap 119).
    ///
    /// **`0` is the "nothing sealed" sentinel, not year 1.** A genesis that
    /// sealed nothing — a log of recent lines only — carries `Meta::default()`,
    /// and `Ckpt.empty` has `ledgerDay 0` too, so a lag computed against it
    /// would read as seven hundred thousand days. It is `None` here instead.
    pub ledger_day: Option<u64>,
}

/// **The process's replay caches**, one per plan root (§9.8, CRIT 26, K14).
///
/// A cache is per process, not per call: an unwritable directory keeps its checkpoint in memory
/// for the life of the process, so a TUI session pays genesis once rather than once per reload.
fn caches() -> &'static std::sync::Mutex<BTreeMap<PathBuf, ReplayCache>> {
    static CACHES: std::sync::OnceLock<std::sync::Mutex<BTreeMap<PathBuf, ReplayCache>>> =
        std::sync::OnceLock::new();
    CACHES.get_or_init(|| std::sync::Mutex::new(BTreeMap::new()))
}

// ===========================================================================
// THE DOOR THE SWITCH OPENS (design §14.6 item 1, §11.1, §11.4).
//
// Every `pub fn` below this banner is one `Ctx` calls at S, and
// `tests/kernel_log_door.rs` must call each of them by name — see
// `every_door_function_the_switch_calls_is_exercised_here`, which reads this
// banner and that file. Adding a function here without a test fails it.
// ===========================================================================

/// **The replay of `bytes` that WRITES NOTHING** — the owner's **D96** (W-44 track H, README gaps 4393 and
/// 4392): how a TUI past midnight reads its log while it holds in memory every housekeeping write `tm plan` makes,
/// the file's bytes with the held lines after them (`Ctx::log_now`), so its replay is the one `tm plan` reads after
/// writing them. The section is [`capacity_log_section`]'s — this process's checkpoint and the tail since its cut,
/// or genesis in one call — and it **never reseals** (`reseal: null`); the scope's sealed records are READ from the
/// snapshot's month files ([`records_for`]) and merged ([`merge_records`]) and the facts decoded ([`decode_facts`]),
/// as [`replay_scoped`] does. `Ok(None)` when the scope needs a sealed month file that is missing or does not match its
/// digest: answering it would mean rebuilding the cache ([`ReplayCache::rebuild_missing`]), which is a write, so the
/// caller holds nothing rather than write on a timer.
pub fn replay_unsealed(
    root: &Path,
    bytes: &[u8],
    tz: Tz,
    tz_wire: &Value,
    today: NaiveDate,
    scope: Scope,
) -> Result<Option<Read>, GenesisError> {
    let now_day = day_of(today);
    let (section, snapshot) = resume_section_from(root, bytes, tz_wire, now_day, None)?;
    let answer = match log_call(&wrap_log(&date_of(now_day), tz_wire, &section)).map_err(GenesisError::Fault)? {
        Ok(a) => a,
        Err(r) => return Err(GenesisError::Refused(r)),
    };
    let (days, window, ledger_day) = match snapshot {
        // Genesis in one call sealed nothing: every day of the log is in its answer.
        None => (BTreeMap::new(), BTreeMap::new(), None),
        Some(sn) => {
            let ledger_day = (sn.meta.ledger_day > 0).then_some(sn.meta.ledger_day);
            let dir = root.join(CACHE_DIR);
            let mut all = caches().lock().unwrap_or_else(|p| p.into_inner());
            let cache = all.entry(root.to_path_buf()).or_insert_with(|| ReplayCache::new(Some(dir)));
            let r = Replayed {
                answer: answer.clone(),
                outcome: Outcome::Hot,
                snapshot: sn,
                days: BTreeMap::new(),
                window: BTreeMap::new(),
                notices: vec![],
                rebuilt_because: None,
            };
            let Some((d, w)) = records_for(cache, &r, scope) else {
                return Ok(None);
            };
            (d, w, ledger_day)
        }
    };
    let facts = answer.facts.clone().ok_or_else(|| GenesisError::Fault("the answer carries no facts".into()))?;
    let merged = merge_records(&facts, &days, &window).map_err(GenesisError::Fault)?;
    let answer = serde_json::json!({"lines": answer.lines, "facts": merged, "headers": answer.headers});
    let replay = decode_facts(&answer, tz).map_err(GenesisError::Fault)?;
    Ok(Some(Read { replay, outcome: Outcome::Hot, notices: vec![], ledger_day }))
}

/// **The undo stack's pin** (§9.6): the smallest `UndoEntry.log_line` among entries younger than
/// 14 days, or `None`. Read from `.tm/undo.json` directly — the seal policy needs a number, not a
/// stack, and `UndoStack::load` wants a whole `Ctx` this is called to build.
///
/// An entry written before R6 has no `log_line` and is ignored (CRIT 27); so is one older than 14
/// days, so a light user's stale stack does not pin the tail.
pub fn max_line_of(undo_json: &str, now: DateTime<FixedOffset>) -> Option<u64> {
    let v: Value = serde_json::from_str(undo_json).ok()?;
    let cutoff = now - chrono::Duration::days(14);
    v.get("entries")?
        .as_array()?
        .iter()
        .filter(|e| {
            e.get("t")
                .and_then(Value::as_str)
                .and_then(|t| DateTime::parse_from_rfc3339(t).ok())
                .is_some_and(|t| t >= cutoff)
        })
        .filter_map(|e| e.get("log_line").and_then(Value::as_u64))
        .min()
}

/// **The `All` and `Dates` merge** (§11.1), host side.
///
/// Design §11.1 has the kernel merge the records a request sends (`LogReq.merged`). That is the
/// `Dates` scope's route and D13's, and it is capped: [`MAX_SEALED_IN`] records per call. The
/// `All` scope reaches every month — about 1,100 day records at three years — so its merge cannot
/// be a request's, and is done here instead: the sealed `days` and `window` arrays are merged in
/// front of the answer's own, which win where both hold a key.
///
/// Only those two arrays are windowed away by a reseal. The items, instances, named records, open
/// machine and counts are carried by the checkpoint itself, so the answer already holds them
/// whole. T5's windowed arm compares the result with the fork's whole replay, which is what says
/// this merge is complete.
pub fn merge_records(facts: &Value, days: &BTreeMap<u64, String>, window: &BTreeMap<u64, String>) -> Result<Value, String> {
    if days.is_empty() && window.is_empty() {
        return Ok(facts.clone());
    }
    let mut facts = facts.clone();
    let parse = |t: &String| serde_json::from_str::<Value>(t).map_err(|e| format!("a sealed record: {e}"));
    let merge = |key: &str, sealed: &BTreeMap<u64, String>, facts: &mut Value| -> Result<(), String> {
        let mut all: BTreeMap<u64, Value> = BTreeMap::new();
        for (d, t) in sealed {
            all.insert(*d, parse(t)?);
        }
        for r in facts[key].as_array().ok_or_else(|| format!("facts.{key} is not an array"))? {
            let d = r[0].as_u64().ok_or_else(|| format!("a facts.{key} entry has no day"))?;
            all.insert(d, r.clone());
        }
        facts[key] = Value::Array(all.into_values().collect());
        Ok(())
    };
    merge("days", days, &mut facts)?;
    merge("window", window, &mut facts)?;
    Ok(facts)
}

/// A line warning's sentence, from the kernel's **named** verdict (§17's P15: named
/// constructors where the fork had serde's free text).
fn warning_text(w: &Value) -> String {
    let name = w.get("w").and_then(Value::as_str).unwrap_or("unreadable");
    let why = w.get("why").and_then(Value::as_str).unwrap_or_default();
    match name {
        // The fork's sentence began `invalid UTF-8: …`; the phrase is kept, the cause is named.
        "invalidUtf8" => "invalid UTF-8".to_string(),
        "lineTooLong" => "the line is longer than 65,536 characters".to_string(),
        "lineTooDeep" => "the line nests deeper than 64 brackets".to_string(),
        "notJson" => format!("not JSON: {why}"),
        "numberOutOfRange" => "a number out of range".to_string(),
        "notAnObject" => "not a JSON object".to_string(),
        "noT" => "missing field `t`".to_string(),
        "tNotString" => "`t` is not a string".to_string(),
        "badT" => format!("invalid timestamp: {why}"),
        "duplicateT" => "duplicate field `t`".to_string(),
        other => format!("the kernel refused this line: {other}"),
    }
}

/// The chunks a read-only sweep sends: at most [`CHUNK_LINES`] lines and [`CHUNK_BYTES`] bytes.
fn sweep_chunks(s: &Split) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    let (mut start, n) = (0usize, s.lines.len());
    while start < n {
        let mut end = start + 1;
        while end < n && end - start < CHUNK_LINES && s.bytes_between(start, end + 1) <= CHUNK_BYTES {
            end += 1;
        }
        out.push((start, end));
        start = end;
    }
    out
}

/// **Every line of the log the reader refuses** (D18 (i)), for `tm check`.
///
/// A call that asks for no facts, no headers, no reseal and no records **does not resume**
/// (`Boundary.LogReq.resumes`): the kernel reads its lines with `Log.readLine` and answers their
/// warnings, with no replay and no checkpoint. So this is a read-only sweep of the whole file, in
/// chunks, and it is exact whatever scope the verb's own replay asked for.
///
/// It exists because **the answer's `warnings` array is per call** (`Boundary.logBody`): a hot
/// call carries only its tail's, and genesis returns only its last chunk's. `tm check` must name
/// every unreadable line in the file, so it asks for them directly rather than taking whatever the
/// last call happened to see.
pub fn line_warnings(bytes: &[u8], now: &str, tz: &Value) -> Result<Vec<LogWarning>, String> {
    let s = split(bytes);
    let mut out: Vec<LogWarning> = Vec::new();
    let want = Want::default();
    for (a, b) in sweep_chunks(&s) {
        let req = request(now, tz, None, a as u64 + 1, &s.lines[a..b], b < s.lines.len() || s.terminated, None, &want, None);
        let answer = log_call(&req)?.map_err(|r| format!("a read-only sweep was refused: {r:?}"))?;
        for w in answer.warnings.as_array().ok_or("warnings is not an array")? {
            let line = w.get("line").and_then(Value::as_u64).ok_or("a warning without its line")?;
            let text = s
                .lines
                .get(line as usize - 1)
                .and_then(|l| l.clone())
                .unwrap_or_else(|| {
                    // A line that is not UTF-8 has no text on this side either; show it lossily,
                    // as the fork's reader did, so `tm check` can quote the bytes.
                    let (from, to) = (if line == 1 { 0 } else { s.ends[line as usize - 2] }, s.ends[line as usize - 1]);
                    String::from_utf8_lossy(&bytes[from..to]).trim_end_matches('\n').trim_end_matches('\r').to_string()
                });
            out.push(LogWarning { line: line as usize, text, error: warning_text(w) });
        }
    }
    Ok(out)
}

/// **The `render` op** (§11.4 steps 3-4): each wanted line's canonical rendering and its display.
///
/// The lines a verb selected are scattered through the file, and one call may carry at most
/// [`RESEND_LINES`] lines, so the file is swept in chunks and a chunk holding none of the wanted
/// lines is never sent. A line the kernel cannot render (a malformed one) comes back absent, which
/// is what `tm log` prints a header without a payload for.
///
/// **It hands back the rendering's own bytes** ([`RawValue`]), not a parsed [`Value`]. Design §11.4
/// step 5 says `tm log --json` "emits each rendering parsed as a generic `serde_json::Value`" and
/// in the same sentence that it "is byte-identical to today" — and those two cannot both hold.
/// This workspace's `serde_json` has no `preserve_order`, so `Value`'s map is a `BTreeMap` and
/// parsing re-orders every object's keys **alphabetically**, where the fork's `LogEntry` writes
/// them in declaration order (`t` first). Measured: `tm log --json` moved on 7 of 69 corpus
/// invocations, every difference a key order and no value. The bytes are kept instead.
pub fn render_lines(bytes: &[u8], now: &str, tz: &Value, wanted: &[u64]) -> Result<BTreeMap<u64, (Box<RawValue>, String)>, String> {
    let mut out = BTreeMap::new();
    if wanted.is_empty() {
        return Ok(out);
    }
    let s = split(bytes);
    let want_set: BTreeSet<u64> = wanted.iter().copied().collect();
    for (a, b) in sweep_chunks(&s) {
        let here: Vec<u64> = want_set.range(a as u64 + 1..=b as u64).copied().collect();
        if here.is_empty() {
            continue;
        }
        let want = Want { facts: false, headers_from: None, render: here };
        let req = request(now, tz, None, a as u64 + 1, &s.lines[a..b], b < s.lines.len() || s.terminated, None, &want, None);
        let answer = log_call(&req)?.map_err(|r| format!("a render call was refused: {r:?}"))?;
        for r in answer.render.as_array().ok_or("render is not an array")? {
            let line = r[0].as_u64().ok_or("a render row without its line")?;
            let (Some(text), Some(display)) = (r[1].as_str(), r[2].as_str()) else { continue };
            let value = RawValue::from_string(text.to_string())
                .map_err(|e| format!("the kernel's rendering of line {line}: {e}"))?;
            out.insert(line, (value, display.to_string()));
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// S2 (owner decision D16): the kernel writes the lines the binary appends.

/// **An instant as the kernel encodes one** — `[sec, ns, west, offSec]`, the exact inverse of
/// [`d_when`]: seconds from `0001-01-01T00:00:00Z`, the subsecond nanoseconds (at or above 1e9 on
/// a leap second, as chrono holds one), and the offset **as written**, its sign in `west`.
///
/// An instant chrono can hold but `Cal.Instant` cannot — a year before 1 — sends a negative
/// `sec`, which is not a `JVal.num`, so the kernel refuses it by name (`badAt`) rather than
/// writing a line its own reader could not read back.
pub fn instant_wire(t: DateTime<FixedOffset>) -> Value {
    let off = t.offset().local_minus_utc();
    serde_json::json!([
        t.timestamp() + EPOCH_FROM_CE,
        t.timestamp_subsec_nanos(),
        off < 0,
        off.unsigned_abs()
    ])
}

/// **The bytes to append, from the kernel** (owner decision **D16**; design §22.1's step S2),
/// for events given as a tag and a bag of field **values**.
///
/// This is the whole of the writer swap: an appending verb sends its events' values and appends
/// exactly what comes back, so `.tm/log.jsonl`'s format has one definition — the kernel's
/// grammar, reached through the same `Log.renderLine` the reader reads through
/// (`the_log_emits_what_it_reads`).
///
/// The values may be in any order and may spell an optional field explicitly as `null`: the
/// kernel decides the key order, which fields are left out and how each numeral is written
/// (`the_kernel_decides_what_is_left_out`). There is deliberately no way to hand the kernel a
/// *line*, so the writer and the reader cannot drift apart.
///
/// A refusal is an error and never a written line: an event whose values the reader would refuse
/// is named (`emit.refused`) rather than appended, which is the defect this step removes.
pub fn render_values(evs: &[(DateTime<FixedOffset>, String, Value)]) -> Result<Vec<String>, String> {
    if evs.is_empty() {
        return Ok(Vec::new());
    }
    let items: Vec<Value> = evs
        .iter()
        .map(|(t, tag, f)| serde_json::json!({"at": instant_wire(*t), "ev": tag, "f": f}))
        .collect();
    let req = serde_json::json!({"docs": [], "emit": items});
    let resp = tm_kernel_ffi::call(&req.to_string()).map_err(|e| format!("kernel fault: {e:?}"))?;
    let v: Value =
        serde_json::from_str(&resp).map_err(|e| format!("the response is not JSON: {e}"))?;
    if let Some(err) = v.get("err") {
        return Err(format!("the kernel refused a line to append: {err}"));
    }
    let arr = v
        .get("ok")
        .and_then(|o| o.get("emit"))
        .and_then(Value::as_array)
        .ok_or_else(|| format!("no emit answer: {}", &resp[..resp.len().min(200)]))?;
    if arr.len() != evs.len() {
        return Err(format!("the kernel wrote {} lines for {} events", arr.len(), evs.len()));
    }
    arr.iter()
        .map(|x| {
            x.as_str()
                .map(str::to_string)
                .ok_or_else(|| "a rendering is not a string".to_string())
        })
        .collect()
}

/// [`render_values`] for typed events — what every appending verb calls (D16).
///
/// The field values are serde's (`to_value`); the **bytes** never are. serde's own
/// `skip_serializing_if` is redundant here rather than authoritative: the kernel's `renderF`
/// re-omits what serde omitted, and would omit an explicit `null` just the same
/// (`the_kernel_decides_what_is_left_out`). `ev` is dropped from the payload because the tag
/// travels in its own key — the kernel picks the kind from the tag, never from the payload.
pub fn render_events(
    evs: &[(DateTime<FixedOffset>, &tm_core::log::Event)],
) -> Result<Vec<String>, String> {
    let mut items = Vec::with_capacity(evs.len());
    for (t, ev) in evs {
        let mut v =
            serde_json::to_value(ev).map_err(|e| format!("an event does not serialise: {e}"))?;
        let obj = v.as_object_mut().ok_or("an event is not a JSON object")?;
        obj.remove("ev");
        items.push((*t, ev.name().to_string(), Value::Object(std::mem::take(obj))));
    }
    render_values(&items)
}

/// [`render_events`] for one entry — the function pointer `tm_core::horizon::Ctx` writes through
/// (D16), so the id-less fallback paths (gap 5) append the kernel's bytes too.
pub fn render_one(entry: &tm_core::log::LogEntry) -> Result<String, String> {
    render_events(&[(entry.t, &entry.ev)])?
        .into_iter()
        .next()
        .ok_or_else(|| "the kernel returned no line".to_string())
}

/// **The headers a command appended** (§11.4, design §14.3 row R6): the tail after `after`
/// physical lines, replayed on its own from the empty checkpoint, each header's line shifted back
/// into the whole file's numbering.
///
/// This is what `tm undo`'s recorder reads, and replaying the tail alone is exactly what it did
/// before the switch: a tail that starts after the day's `wake` attributes its lines from the
/// wakes it can see, which is why the day is not among the fields handed back.
pub fn headers_after(bytes: &[u8], now: &str, tz: &Value, after: u64) -> Result<Vec<(u64, String, Option<String>)>, String> {
    let s = split(bytes);
    let at = after as usize;
    if at >= s.lines.len() {
        return Ok(Vec::new());
    }
    let tail = &s.lines[at..];
    if tail.len() > RESEND_LINES || s.bytes_between(at, s.lines.len()) > RESEND_BYTES {
        return Err(format!("a tail of {} lines is past the resend cap", tail.len()));
    }
    let want = Want { facts: false, headers_from: Some(1), render: vec![] };
    let req = request(now, tz, None, 1, tail, s.terminated, None, &want, None);
    let answer = log_call(&req)?.map_err(|r| format!("a tail read was refused: {r:?}"))?;
    let mut out = Vec::new();
    for h in answer.headers.as_array().ok_or("headers is not an array")? {
        let line = h[0].as_u64().ok_or("a header without its line")?;
        let tag = h[1].as_str().ok_or("a header without its tag")?.to_string();
        let id = h[2].as_str().map(str::to_string);
        out.push((line + after, tag, id));
    }
    out.sort_by_key(|h| h.0);
    Ok(out)
}

/// The months a date range spans, as `YYYY-MM` keys, with §11.1's one-day margin already applied.
fn months_between(from: u64, to: u64) -> Vec<String> {
    let mut out: BTreeSet<String> = BTreeSet::new();
    let mut d = from;
    while d <= to {
        out.insert(month_of(d));
        d += 28;
    }
    out.insert(month_of(to));
    out.into_iter().collect()
}

/// The notice a replay raises when a sealed month file its snapshot names was missing — or, since the
/// owner's D93, did not match its digest — and the cache was rebuilt from the log (README gaps **3711**
/// and **4246**).
fn missing_month_notice() -> String {
    format!("replay cache {CACHE_DIR} changed underneath (a sealed month file is missing or does not match its digest); rebuilt from the log")
}

/// The notice a reseal raises when a month file it had to merge was missing or did not match its digest, and the
/// cache was rebuilt from the log instead (the owner's D93, README gaps 4246 and 4395).
fn corrupt_month_notice(month: &str) -> String {
    format!("replay cache {CACHE_DIR}: the sealed month file of {month} is missing or does not match its digest; rebuilt from the log")
}

/// The notice a replay raises when `ckpt.json` did not match its own digest and the cache was rebuilt from the log
/// (the campaign's D98, README gap 4394) — once: the rebuild writes a checkpoint that matches.
fn corrupt_ckpt_notice() -> String {
    format!("replay cache {CACHE_DIR}: {CKPT_FILE} does not match its digest; rebuilt from the log")
}

/// The sealed records a scope merges (§11.1, §9.8) — `None` when a month file the snapshot names is
/// missing after §9.8's one re-read of `ckpt.json`.
///
/// **`None` is answered by a REBUILD, never by the replay's own records** (README gap **3711**, the
/// W-39 repair). Until then this fell back to `r.days`, which a hot resume leaves EMPTY, under the
/// notice "rebuilt in memory" — and nothing was rebuilt. DRIVEN on the W-39 binary: with one month
/// file deleted, `tm review day --date 2026-09-08` said `0/6 blocks · load 0.0 · done -`, twice, where
/// the log holds `1/6 · done t4` — a silent wrong answer under a notice that said the opposite, while
/// W-39's week path faulted on the same condition. D13: the cache is derived and rebuildable.
fn records_for(cache: &ReplayCache, r: &Replayed, scope: Scope) -> Option<(BTreeMap<u64, String>, BTreeMap<u64, String>)> {
    match scope {
        Scope::Hot => Some((BTreeMap::new(), BTreeMap::new())),
        Scope::All => cache.records_of(r),
        Scope::Dates { from, to } => {
            let (lo, hi) = (day_of(from).saturating_sub(1), day_of(to) + 1);
            let (d, w) = if r.outcome == Outcome::GenesisUnpersisted || r.snapshot.gen.is_empty() {
                (r.days.clone(), r.window.clone())
            } else {
                cache.load_months(&r.snapshot, &months_between(lo, hi))?
            };
            Some((
                d.into_iter().filter(|(k, _)| *k >= lo && *k <= hi).collect(),
                w.into_iter().filter(|(k, _)| *k >= day_of(from) && *k <= day_of(to)).collect(),
            ))
        }
    }
}

/// **The `log` section a capacity request carries** (stage 6 step L9, gap 93; D24's seam).
///
/// Day 0 of the lookahead is the kernel's own since L9: it is cut from `now` and energised
/// through today's posterior and sleep debt, all of which the kernel derives from **its own**
/// replay. So a capacity request carries a `log` section beside its `capacity` section, and
/// `Boundary.runCapZ` hands the one section's replay to the other (`the_capacity_section_reads_
/// the_log_sections_own_replay`). Without it the kernel refuses by name, `day0WithoutLog`.
///
/// It is the section [`ReplayCache::replay`] sends on its hot path — the process checkpoint and
/// the tail since its cut — when that checkpoint is still valid for these bytes, and genesis in
/// one call (`ckpt: null`, every line) when it is not. **It never reseals** (`reseal: null`): the
/// verb's own replay owns the cache, and a second reseal in the same process would write a second
/// generation for one verb.
///
/// The one case it cannot serve is a log with no valid checkpoint that is also past the resend
/// cap — a log of more than [`RESEND_LINES`] lines, none of them older than [`KEEP_DAYS`], so
/// that genesis sealed nothing to resume from. It is named, not guessed at (D18: the cap is never
/// raised).
pub fn capacity_log_section(root: &Path, bytes: &[u8], tz: &Value, now_day: u64) -> Result<String, GenesisError> {
    resume_log_section(root, bytes, tz, now_day, None)
}

/// **The `log` section the week grid's cut asks with** (README gaps 3432 and 3528, W-39
/// track T): [`capacity_log_section`]'s — the process checkpoint and the tail since its cut,
/// or genesis in one call — and, in its `sealed` field, the snapshot's sealed records of the
/// days `from..=to` below its ledger day, so the kernel's answer holds every day of the week
/// the log has (`Seal.mergeSealed`; the owner's D13: the kernel may read a sealed record back
/// for an explicitly old date). A snapshot whose month file is missing is rebuilt from the log and
/// asked again (README gap 3711), never a week with its older days quietly absent; only a rebuild
/// that still leaves one missing is a named fault.
pub fn week_log_section(
    root: &Path,
    bytes: &[u8],
    tz: &Value,
    now_day: u64,
    from: u64,
    to: u64,
) -> Result<String, GenesisError> {
    resume_log_section(root, bytes, tz, now_day, Some((from, to)))
}

/// The two above: a resume (or genesis) section, with the sealed day records of `sealed`'s days.
fn resume_log_section(
    root: &Path,
    bytes: &[u8],
    tz: &Value,
    now_day: u64,
    sealed: Option<(u64, u64)>,
) -> Result<String, GenesisError> {
    resume_section_from(root, bytes, tz, now_day, sealed).map(|(section, _)| section)
}

/// [`resume_log_section`], and the snapshot it resumed from (`None` for genesis in one call).
fn resume_section_from(
    root: &Path,
    bytes: &[u8],
    tz: &Value,
    now_day: u64,
    sealed: Option<(u64, u64)>,
) -> Result<(String, Option<Snapshot>), GenesisError> {
    let want = Want { facts: true, headers_from: None, render: vec![] };
    let s = split(bytes);
    let tz_key = tz.get("key").and_then(Value::as_str).unwrap_or_default().to_string();
    let dir = root.join(CACHE_DIR);
    let mut all = caches().lock().unwrap_or_else(|p| p.into_inner());
    let cache = all.entry(root.to_path_buf()).or_insert_with(|| ReplayCache::new(Some(dir)));
    // A month file the snapshot names and the disk lacks is REBUILT, once, and the section asked
    // again (README gap 3711, the W-39 repair): D13's cache is derived and rebuildable, and a
    // missing month is not a bug in tm. Only a rebuild that still leaves one missing is a fault.
    let mut rebuilt = false;
    while let Some(sn) = cache.last.clone().or_else(|| cache.read_snapshot()) {
        let cut = sn.meta.cut as usize;
        if !sn.ckpt.is_empty()
            && sn.valid_for(bytes, &tz_key).is_ok()
            // G4 refuses a resume whose `now` is below the checkpoint's ledger day (§9.3), which is
            // the very case §9.7 answers from an unpersisted genesis: do not resume into a refusal.
            && now_day >= sn.meta.ledger_day
            && cut <= s.lines.len()
            && s.lines.len() - cut <= RESEND_LINES
            && s.bytes_between(cut, s.lines.len()) <= RESEND_BYTES
        {
            let days: Vec<String> = match sealed {
                Some((from, to)) if from < sn.meta.ledger_day => match cache.load_months(&sn, &months_between(from, to)) {
                    Some((d, _)) => d.into_iter().filter(|(k, _)| *k >= from && *k <= to).map(|(_, r)| r).collect(),
                    None if !rebuilt => {
                        cache.rebuild_missing(bytes, now_day, tz, None, &want)?;
                        rebuilt = true;
                        continue;
                    }
                    None => {
                        return Err(GenesisError::Fault(format!(
                            "the replay cache {CACHE_DIR} names no month file for the sealed days {from}..={to} after a rebuild"
                        )))
                    }
                },
                _ => Vec::new(),
            };
            let sealed_in = sealed.map(|_| (days.as_slice(), &[] as &[String]));
            let section = log_section(Some(&sn.ckpt), cut as u64 + 1, &s.lines[cut..], s.terminated, None, &want, sealed_in);
            return Ok((section, Some(sn)));
        }
        break;
    }
    // Genesis in one call seals nothing: every day of the log is in the answer.
    if s.lines.len() <= RESEND_LINES && s.bytes_between(0, s.lines.len()) <= RESEND_BYTES {
        return Ok((log_section(None, 1, &s.lines, s.terminated, None, &want, None), None));
    }
    Err(GenesisError::ReachTooFar {
        line: 1,
        kind: "no checkpoint to compute today from".to_string(),
        reach: s.lines.len() as u64,
        bytes: s.bytes_between(0, s.lines.len()) as u64,
    })
}

/// **The one door to the log** (design §14.6 item 1, §11.1): the replay of `.tm/log.jsonl` as the
/// kernel derives it, in the scope `scope` asks for.
///
/// The checkpoint is this process's, kept across reloads so a TUI session pays genesis once
/// (K14); the cache directory is `<root>/.tm/cache/replay` (D13). The answer's facts are merged
/// with the sealed records the scope names ([`merge_records`]) and decoded by [`decode_facts`].
///
/// `want.headersFrom` is **not** asked: every row of the view comes from a day record's own
/// header, and the answer's top-level headers would only repeat their displays.
pub fn replay_scoped(
    root: &Path,
    bytes: &[u8],
    tz: Tz,
    tz_wire: &Value,
    today: NaiveDate,
    scope: Scope,
    max_line: Option<u64>,
) -> Result<Read, GenesisError> {
    let dir = root.join(CACHE_DIR);
    let mut all = caches().lock().unwrap_or_else(|p| p.into_inner());
    let cache = all.entry(root.to_path_buf()).or_insert_with(|| ReplayCache::new(Some(dir)));
    let want = Want { facts: true, headers_from: None, render: vec![] };
    let mut r = cache.replay(bytes, day_of(today), tz_wire, max_line, &want)?;
    let (days, window, notice) = match records_for(cache, &r, scope) {
        Some((d, w)) => (d, w, None),
        None => {
            r = cache.rebuild_missing(bytes, day_of(today), tz_wire, max_line, &want)?;
            let (d, w) = records_for(cache, &r, scope).ok_or_else(|| {
                GenesisError::Fault(format!("the replay cache {CACHE_DIR} names a missing month file after a rebuild"))
            })?;
            (d, w, Some(missing_month_notice()))
        }
    };
    let facts = r.answer.facts.clone().ok_or_else(|| GenesisError::Fault("the answer carries no facts".into()))?;
    let merged = merge_records(&facts, &days, &window).map_err(GenesisError::Fault)?;
    let answer = serde_json::json!({"lines": r.answer.lines, "facts": merged, "headers": r.answer.headers});
    let replay = decode_facts(&answer, tz).map_err(GenesisError::Fault)?;
    let mut notices = r.notices.clone();
    notices.extend(notice);
    let ledger_day = (r.snapshot.meta.ledger_day > 0).then_some(r.snapshot.meta.ledger_day);
    Ok(Read { replay, outcome: r.outcome, notices, ledger_day })
}
