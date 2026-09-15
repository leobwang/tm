//! **The replay cache and the kernel's `log` op, host side** (stage 5 D9 W3; design
//! `kernel/design/stage5/stage5-D9-D10-design.md` §9.6 host policy, §9.7 genesis, §9.8
//! persistence and integrity, §10 the wire, §11.1's merge).
//!
//! **Nothing in the binary calls this yet.** The switch S (W-6) makes `Ctx::replay_with`
//! call [`ReplayCache::replay`]; until then Rust's own reader decides every verb, and the
//! tests (`tests/kernel_replay_parity.rs`'s windowed T5 and T0 (b)) are the only callers.
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
//! * **The files** under `.tm/cache/replay/` (D13): `ckpt.json` (format 2: the kernel id, the
//!   zone key, the prefix's line count, byte count and FNV-1a-64, the generation and the
//!   previous one, the manifest of month files, `meta`, and the checkpoint), immutable
//!   `sealed/YYYY-MM.g<gen>.json` month files, and `tz.json` (`tz_table`'s). Every write is a
//!   temporary file and a rename; a reseal writes new month files, then `ckpt.json`, then
//!   collects month files named by neither manifest and older than ten minutes.
//! * **The snapshot rule** (CRIT 7): a process reads `ckpt.json` once, loads month files only
//!   by that manifest, and uses day records only below its `ledgerDay` and window records only
//!   below its `horizon`. A missing month file re-reads `ckpt.json` once, then rebuilds in memory.
//! * **Integrity** (G9, §9.8): the prefix digest is checked on every call; a differing length,
//!   a prefix not ending in `\n`, a differing FNV, zone key, format or kernel id goes straight
//!   to genesis.
//! * **Host policy** (§9.6): reseal when more than [`FOLDABLE_TRIGGER`] foldable lines were
//!   appended since the snapshot was written (`logLines`, W4's gap 124: a tail a reseal could not
//!   fold does not reseal again on every call), or when `now` is more than two days past the ledger
//!   day and the checkpoint was not sealed today (the back-off, CRIT 19).
//! * **An unwritable cache** (CRIT 26) is not fatal: one named notice per process, and the
//!   checkpoint is kept in memory for that process.

#![allow(dead_code)]

use serde_json::value::RawValue;
use serde_json::Value;
use std::collections::{BTreeMap, VecDeque};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, SystemTime};

/// The format `ckpt.json` carries; any other goes to genesis.
pub const FORMAT: u64 = 3;
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
pub const MAX_SEALED_IN: usize = 62;

/// The kernel this binary links (`tm-kernel-ffi/build.rs`: FNV-1a-64 of its archive). A checkpoint written by another
/// kernel goes to genesis (§9.8).
pub fn kernel_id() -> &'static str {
    tm_kernel_ffi::KERNEL_ID
}

/// FNV-1a-64 (§9.8's prefix digest).
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

/// **One `log` request** (§10.1), built as text so the checkpoint and the records go in byte for byte.
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
    let mut r = String::with_capacity(lines.iter().map(|l| l.as_ref().map_or(4, |s| s.len() + 8)).sum::<usize>() + 4096);
    r.push_str(r#"{"docs":[],"now":"#);
    r.push_str(&Value::String(now.to_string()).to_string());
    r.push_str(r#","tz":"#);
    r.push_str(&tz.to_string());
    r.push_str(r#","log":{"ckpt":"#);
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
    r.push_str("}}");
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
    pub meta: Meta,
    pub ckpt: String,
}

impl Snapshot {
    /// The text of `ckpt.json`, the checkpoint spliced in verbatim.
    pub fn to_text(&self) -> String {
        let head = serde_json::json!({
            "format": FORMAT, "kernel": self.kernel, "tzKey": self.tz_key, "prefixLines": self.prefix_lines, "logLines": self.log_lines,
            "prefixBytes": self.prefix_bytes, "prefixFnv": self.prefix_fnv, "gen": self.gen, "prevGen": self.prev_gen,
            "manifest": self.manifest, "meta": self.meta.to_json(),
        })
        .to_string();
        format!("{},\"ckpt\":{}}}\n", &head[..head.len() - 1], self.ckpt)
    }

    /// Read `ckpt.json`; `Err` names what is wrong (corrupt, another format).
    pub fn from_text(text: &str) -> Result<Snapshot, String> {
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

/// Why a reseal's write stopped before publishing: the previous manifest names a month file that is gone.
const MONTH_MISSING: &str = "a month file the manifest names is missing";

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
    pub rebuilt_because: Option<String>,
}

/// **The replay cache of one process** (§9.8): the directory when it is writable, else the checkpoint in memory.
#[derive(Clone, Debug, Default)]
pub struct ReplayCache {
    pub dir: Option<PathBuf>,
    /// The process's own checkpoint and records, used when the directory is not writable (CRIT 26).
    pub memory: Option<(Snapshot, BTreeMap<u64, String>, BTreeMap<u64, String>)>,
    pub writable: bool,
}

impl ReplayCache {
    /// A cache in `dir` (`<root>/.tm/cache/replay`), or in memory only.
    pub fn new(dir: Option<PathBuf>) -> ReplayCache {
        ReplayCache { writable: dir.is_some(), dir, memory: None }
    }

    fn ckpt_path(&self) -> Option<PathBuf> {
        self.dir.as_ref().map(|d| d.join(CKPT_FILE))
    }

    /// **Read the snapshot once** (CRIT 7): `ckpt.json`, or the in-memory checkpoint; `None` when there is none or it is
    /// unreadable.
    pub fn read_snapshot(&self) -> Option<Snapshot> {
        if let Some(p) = self.ckpt_path() {
            if let Ok(text) = std::fs::read_to_string(p) {
                return Snapshot::from_text(&text).ok();
            }
        }
        self.memory.as_ref().map(|m| m.0.clone())
    }

    /// **The records of a snapshot's months** (by its manifest only), `None` when a named file is missing.
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
            let (d, w) = read_month(&text).ok()?;
            days.extend(d.into_iter().filter(|(k, _)| *k < snap.meta.ledger_day));
            window.extend(w.into_iter().filter(|(k, _)| *k < snap.meta.horizon));
        }
        Some((days, window))
    }

    /// **Every record of a snapshot** (the `All` scope), re-reading `ckpt.json` once when a month file is missing
    /// (§9.8's snapshot rule). `None` after the retry: the caller rebuilds in memory.
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
    /// touched keys replaced, written as a new immutable file; then `ckpt.json`; then collection. On an I/O error the
    /// checkpoint and records are kept in memory and the notice returned.
    pub fn write_generation(
        &mut self,
        prev: Option<&Snapshot>,
        mut snap: Snapshot,
        days: &BTreeMap<u64, String>,
        window: &BTreeMap<u64, String>,
        all_records: bool,
    ) -> (Snapshot, Option<String>) {
        let gen = fresh_gen();
        snap.prev_gen = prev.map_or_else(String::new, |p| p.gen.clone());
        snap.gen = gen.clone();
        snap.manifest = if all_records { BTreeMap::new() } else { prev.map(|p| p.manifest.clone()).unwrap_or_default() };
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
                    if let Some(rel) = prev.and_then(|p| p.manifest.get(month)) {
                        // The input of a read-modify-write must be there: a month file the manifest names but another
                        // process collected would otherwise publish a month without its older records (CRIT 7).
                        let text = std::fs::read_to_string(dir.join(rel)).map_err(|_| std::io::Error::new(std::io::ErrorKind::NotFound, MONTH_MISSING))?;
                        let (od, ow) = read_month(&text).map_err(|_| std::io::Error::new(std::io::ErrorKind::NotFound, MONTH_MISSING))?;
                        md = od;
                        mw = ow;
                    }
                }
                md.extend(d.clone());
                mw.extend(w.clone());
                let rel = format!("{SEALED_DIR}/{month}.g{gen}.json");
                write_atomic(&dir.join(&rel), &month_text(&md, &mw))?;
                snap.manifest.insert(month.clone(), rel);
            }
            write_atomic(&dir.join(CKPT_FILE), &snap.to_text())?;
            collect(&dir, &snap, prev);
            Ok(())
        })();
        match result {
            Ok(()) => {
                self.memory = None;
                (snap, None)
            }
            Err(e) if e.to_string() == MONTH_MISSING => {
                // Nothing was published: the stored checkpoint stays valid for its prefix, and this process keeps its
                // own checkpoint and the records it sealed.
                let mut md = BTreeMap::new();
                md.extend(days.clone());
                let mut mw = BTreeMap::new();
                mw.extend(window.clone());
                self.memory = Some((snap.clone(), md, mw));
                (snap, Some(format!("replay cache {CACHE_DIR} changed underneath; kept in memory")))
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
        }
    }

    /// **One replay for a verb** (§9.8, §9.7, §9.6): check the stored checkpoint against the log, resume its tail (with a
    /// reseal when the policy says so), and fall back to genesis on a refusal, a failed digest or no checkpoint.
    #[allow(clippy::too_many_arguments)]
    pub fn replay(
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
        let snap = self.read_snapshot();
        let why = match &snap {
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
                        let (next, notice) = self.write_generation(Some(sn), next, &days, &window, false);
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
        self.rebuild(&now, tz, &s, max_line, want, bytes, why, false)
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
        let (snap, notice) = self.write_generation(prev.as_ref(), snap, &g.top.days, &g.top.window, true);
        Ok(Replayed { answer: g.answer, outcome: Outcome::Genesis, snapshot: snap, days: g.top.days, window: g.top.window, notices: notice.into_iter().collect(), rebuilt_because: why })
    }

    /// **Every record a replay's answer stands on** (§11.1's `All` scope): an unpersisted genesis' own records, else the
    /// snapshot's months by its manifest (re-reading `ckpt.json` once when a file is missing). `None` when the files moved
    /// underneath twice: the caller rebuilds in memory, with the notice `replay cache changed underneath; rebuilt in memory`.
    pub fn records_of(&self, r: &Replayed) -> Option<(BTreeMap<u64, String>, BTreeMap<u64, String>)> {
        if r.outcome == Outcome::GenesisUnpersisted || r.snapshot.gen.is_empty() {
            return Some((r.days.clone(), r.window.clone()));
        }
        self.all_records(&r.snapshot).map(|(_, d, w)| (d, w))
    }

    /// **An old-date read** (§11.1's `Dates` scope, D13): the snapshot's day records of `[from − 1, to + 1]` below its
    /// ledger day and window records of `[from, to]` below its horizon, sent as `sealed` (at most 62 per call) with the
    /// same tail, so the kernel's facts carry them merged.
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
            meta: Meta { cut: 2, ledger_day: 739870, horizon: 739855, reseal_day: 739872, max_t: Some((1, 0)), future_floor: None },
            ckpt: r#"{"v":1,"tzKey":"UTC","cut":2}"#.into(),
        };
        let back = Snapshot::from_text(&s.to_text()).expect("reads back");
        assert_eq!(back, s);
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
}
