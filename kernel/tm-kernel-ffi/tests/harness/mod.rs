//! Shared plumbing for the corpus harness: a minimal JSON codec, the request
//! builder, and the corpus walker.
//!
//! **Why a hand-written JSON codec.** The kernel's boundary is `String ->
//! String` and the string is JSON, so a test that asserts byte-faithfulness
//! has to encode and decode it. Pulling in `serde_json` would add the first
//! runtime dependency this crate has ever had, and — worse for this particular
//! test — it would let a bug hide: if the encoder and the decoder are the same
//! library, an escaping convention that is wrong *in the same way* both times
//! round-trips anyway. The codec below is ~140 lines, is the only thing between
//! the file bytes and the kernel, and is exercised on the corpus itself.
//!
//! This file lives in `tests/harness/` rather than `tests/` so that Cargo does
//! not compile it as a test target of its own.

#![allow(dead_code)]

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

// ---------------------------------------------------------------------------
// JSON
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum J {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<J>),
    Obj(Vec<(String, J)>),
}

impl J {
    pub fn get(&self, k: &str) -> Option<&J> {
        match self {
            J::Obj(kv) => kv.iter().find(|(key, _)| key == k).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn arr(&self) -> Option<&[J]> {
        match self {
            J::Arr(v) => Some(v),
            _ => None,
        }
    }
    pub fn str(&self) -> Option<&str> {
        match self {
            J::Str(s) => Some(s),
            _ => None,
        }
    }
    /// A compact rendering, used only to name an error in a report.
    pub fn compact(&self) -> String {
        match self {
            J::Null => "null".into(),
            J::Bool(b) => b.to_string(),
            J::Num(n) => {
                if n.fract() == 0.0 {
                    format!("{}", *n as i64)
                } else {
                    n.to_string()
                }
            }
            J::Str(s) => {
                let mut o = String::new();
                escape_into(s, &mut o);
                o
            }
            J::Arr(v) => {
                let parts: Vec<String> = v.iter().map(J::compact).collect();
                format!("[{}]", parts.join(","))
            }
            J::Obj(kv) => {
                let parts: Vec<String> = kv
                    .iter()
                    .map(|(k, v)| {
                        let mut o = String::new();
                        escape_into(k, &mut o);
                        format!("{o}:{}", v.compact())
                    })
                    .collect();
                format!("{{{}}}", parts.join(","))
            }
        }
    }
}

/// RFC 8259 string escaping. Non-ASCII is emitted raw (valid UTF-8 is valid
/// JSON), which is also what the kernel's own printer does.
pub fn escape_into(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

pub fn escape(s: &str) -> String {
    let mut o = String::new();
    escape_into(s, &mut o);
    o
}

pub fn parse_json(s: &str) -> Result<J, String> {
    let b: Vec<char> = s.chars().collect();
    let mut i = 0usize;
    let v = pv(&b, &mut i)?;
    skip_ws(&b, &mut i);
    if i != b.len() {
        return Err(format!("trailing input at char {i}"));
    }
    Ok(v)
}

fn skip_ws(b: &[char], i: &mut usize) {
    while *i < b.len() && matches!(b[*i], ' ' | '\t' | '\n' | '\r') {
        *i += 1;
    }
}

fn pv(b: &[char], i: &mut usize) -> Result<J, String> {
    skip_ws(b, i);
    match b.get(*i) {
        None => Err("unexpected end of input".into()),
        Some('{') => {
            *i += 1;
            let mut kv = Vec::new();
            skip_ws(b, i);
            if b.get(*i) == Some(&'}') {
                *i += 1;
                return Ok(J::Obj(kv));
            }
            loop {
                skip_ws(b, i);
                let k = match pv(b, i)? {
                    J::Str(s) => s,
                    other => return Err(format!("object key is not a string: {other:?}")),
                };
                skip_ws(b, i);
                if b.get(*i) != Some(&':') {
                    return Err(format!("expected ':' at char {i}"));
                }
                *i += 1;
                let v = pv(b, i)?;
                kv.push((k, v));
                skip_ws(b, i);
                match b.get(*i) {
                    Some(',') => *i += 1,
                    Some('}') => {
                        *i += 1;
                        return Ok(J::Obj(kv));
                    }
                    _ => return Err(format!("expected ',' or '}}' at char {i}")),
                }
            }
        }
        Some('[') => {
            *i += 1;
            let mut v = Vec::new();
            skip_ws(b, i);
            if b.get(*i) == Some(&']') {
                *i += 1;
                return Ok(J::Arr(v));
            }
            loop {
                v.push(pv(b, i)?);
                skip_ws(b, i);
                match b.get(*i) {
                    Some(',') => *i += 1,
                    Some(']') => {
                        *i += 1;
                        return Ok(J::Arr(v));
                    }
                    _ => return Err(format!("expected ',' or ']' at char {i}")),
                }
            }
        }
        Some('"') => {
            *i += 1;
            let mut s = String::new();
            loop {
                match b.get(*i) {
                    None => return Err("unterminated string".into()),
                    Some('"') => {
                        *i += 1;
                        return Ok(J::Str(s));
                    }
                    Some('\\') => {
                        *i += 1;
                        let c = *b.get(*i).ok_or("dangling escape")?;
                        *i += 1;
                        match c {
                            '"' => s.push('"'),
                            '\\' => s.push('\\'),
                            '/' => s.push('/'),
                            'b' => s.push('\u{8}'),
                            'f' => s.push('\u{c}'),
                            'n' => s.push('\n'),
                            'r' => s.push('\r'),
                            't' => s.push('\t'),
                            'u' => {
                                let hi = hex4(b, i)?;
                                if (0xD800..0xDC00).contains(&hi) {
                                    // surrogate pair
                                    if b.get(*i) != Some(&'\\') || b.get(*i + 1) != Some(&'u') {
                                        return Err("lone high surrogate".into());
                                    }
                                    *i += 2;
                                    let lo = hex4(b, i)?;
                                    if !(0xDC00..0xE000).contains(&lo) {
                                        return Err("bad low surrogate".into());
                                    }
                                    let cp = 0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00);
                                    s.push(char::from_u32(cp).ok_or("bad code point")?);
                                } else {
                                    s.push(char::from_u32(hi).ok_or("bad code point")?);
                                }
                            }
                            other => return Err(format!("bad escape \\{other}")),
                        }
                    }
                    Some(&c) => {
                        s.push(c);
                        *i += 1;
                    }
                }
            }
        }
        Some('t') => lit(b, i, "true", J::Bool(true)),
        Some('f') => lit(b, i, "false", J::Bool(false)),
        Some('n') => lit(b, i, "null", J::Null),
        Some(_) => {
            let start = *i;
            if b.get(*i) == Some(&'-') {
                *i += 1;
            }
            while *i < b.len() && (b[*i].is_ascii_digit() || matches!(b[*i], '.' | 'e' | 'E' | '+' | '-')) {
                *i += 1;
            }
            let t: String = b[start..*i].iter().collect();
            t.parse::<f64>().map(J::Num).map_err(|e| format!("bad number {t:?}: {e}"))
        }
    }
}

fn hex4(b: &[char], i: &mut usize) -> Result<u32, String> {
    let t: String = b.get(*i..*i + 4).ok_or("short \\u escape")?.iter().collect();
    *i += 4;
    u32::from_str_radix(&t, 16).map_err(|e| format!("bad \\u escape {t:?}: {e}"))
}

fn lit(b: &[char], i: &mut usize, want: &str, v: J) -> Result<J, String> {
    for (k, c) in want.chars().enumerate() {
        if b.get(*i + k) != Some(&c) {
            return Err(format!("expected `{want}` at char {i}"));
        }
    }
    *i += want.chars().count();
    Ok(v)
}

// ---------------------------------------------------------------------------
// The kernel request
// ---------------------------------------------------------------------------

/// One document as the boundary reads it: a path, the file's lines, and the
/// horizon region the file *is*.
pub struct Doc {
    pub path: String,
    pub lines: Vec<String>,
    pub region: Option<(u32, u64)>,
}

impl Doc {
    pub fn encode(&self) -> String {
        let mut s = String::from("{\"path\":");
        escape_into(&self.path, &mut s);
        if let Some((g, ix)) = self.region {
            let _ = write!(s, ",\"grain\":{g},\"ix\":{ix}");
        }
        s.push_str(",\"lines\":[");
        for (k, l) in self.lines.iter().enumerate() {
            if k > 0 {
                s.push(',');
            }
            escape_into(l, &mut s);
        }
        s.push_str("]}");
        s
    }
}

/// The request for a set of documents with **no commands at all**: the kernel
/// parses every line and renders it back, and nothing else happens.
pub fn read_only_request(docs: &[Doc]) -> String {
    let mut s = String::from("{\"docs\":[");
    for (k, d) in docs.iter().enumerate() {
        if k > 0 {
            s.push(',');
        }
        s.push_str(&d.encode());
    }
    s.push_str("],\"cmds\":[]}");
    s
}

/// What came back for one document, or the error the whole request failed with.
pub enum Reply {
    /// `docs[k].lines`, in request order.
    Docs(Vec<Vec<String>>),
    /// the `err` object, compacted
    Err(String),
}

pub fn ask(docs: &[Doc]) -> Reply {
    let raw = tm_kernel_ffi::call(&read_only_request(docs))
        .unwrap_or_else(|e| panic!("kernel fault: {e:?}"));
    let j = parse_json(&raw).unwrap_or_else(|e| panic!("kernel returned non-JSON ({e}): {raw}"));
    if let Some(e) = j.get("err") {
        return Reply::Err(e.compact());
    }
    let docs = j
        .get("ok")
        .and_then(|o| o.get("docs"))
        .and_then(J::arr)
        .unwrap_or_else(|| panic!("response has neither `err` nor `ok.docs`: {raw}"));
    Reply::Docs(
        docs.iter()
            .map(|d| {
                d.get("lines")
                    .and_then(J::arr)
                    .unwrap_or_else(|| panic!("document has no `lines`: {raw}"))
                    .iter()
                    .map(|l| l.str().unwrap_or_else(|| panic!("line is not a string: {raw}")).to_string())
                    .collect()
            })
            .collect(),
    )
}

// ---------------------------------------------------------------------------
// Bytes <-> lines: the split that happens at the very edge
// ---------------------------------------------------------------------------

/// **The file-splitting the kernel does not see.** The kernel's round trip is
/// over `List (List Char)`; turning a file's bytes into that list, and back,
/// happens out here. `split('\n')` never loses and never invents a separator,
/// so `join('\n')` of the result is the identity on every `String` — including
/// the empty file (one empty line), a file with no final newline, and a file
/// that is nothing but newlines. `split_lines`/`join_lines` are that identity,
/// and `split_join_is_identity` in `corpus.rs` checks it on every corpus file.
pub fn split_lines(text: &str) -> Vec<String> {
    text.split('\n').map(|s| s.to_string()).collect()
}

pub fn join_lines(lines: &[String]) -> String {
    lines.join("\n")
}

// ---------------------------------------------------------------------------
// The corpus
// ---------------------------------------------------------------------------

pub fn corpus_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("corpus")
}

/// The fixture plan directories, sorted.
pub fn plans() -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(corpus_root())
        .expect("kernel/corpus is missing")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_dir() && p.file_name().unwrap().to_string_lossy().starts_with("plan-"))
        .collect();
    v.sort();
    v
}

/// Every `.md` file under `dir`, sorted, as (tm-relative path, bytes).
pub fn markdown_files(dir: &Path) -> Vec<(String, String)> {
    let mut out = Vec::new();
    walk(dir, dir, &mut out);
    out.sort_by(|a, b| a.0.cmp(&b.0));
    out
}

fn walk(root: &Path, dir: &Path, out: &mut Vec<(String, String)>) {
    for e in std::fs::read_dir(dir).unwrap().flatten() {
        let p = e.path();
        if p.is_dir() {
            walk(root, &p, out);
        } else if p.extension().is_some_and(|x| x == "md") {
            let rel = p.strip_prefix(root).unwrap().to_string_lossy().replace('\\', "/");
            let bytes = std::fs::read(&p).unwrap();
            let text = String::from_utf8(bytes)
                .unwrap_or_else(|_| panic!("{} is not UTF-8", p.display()));
            out.push((rel, text));
        }
    }
}

// ---------------------------------------------------------------------------
// The horizon a file's name declares
// ---------------------------------------------------------------------------
//
// `Doc.region` is `⟨grain, index grain d⟩` (Grain.lean).  `index` is the day
// number itself, `Cal.weekOrdinal d = d / 7`, and `Cal.monthOrdinal d =
// 12·(year−1) + month−1`, over proleptic Gregorian days counted from
// 0001-01-01 = day 0 (a Monday).  The three functions below are those, so the
// harness declares the horizon the kernel would compute rather than a
// placeholder that happens to sort the same way.

/// `Cal.ys`: days before 1 January of year `y`, counted from 0000-01-01.
fn ys(y: u64) -> u64 {
    365 * y + (y + 3) / 4 + (y + 399) / 400 - (y + 99) / 100
}

fn is_leap(y: u64) -> bool {
    (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
}

/// `Cal.toDay`: the kernel's `Day` for a civil date. Day 0 is 0001-01-01.
pub fn to_day(y: u64, m: u64, d: u64) -> u64 {
    const CUM: [u64; 12] = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];
    let doy = CUM[(m - 1) as usize] + (d - 1) + u64::from(is_leap(y) && m > 2);
    ys(y) + doy - 366 // `Cal.originShift`
}

/// `Cal.isoWeek1Monday y / 7`, i.e. `weekOrdinal` of the Monday of ISO week 1.
fn iso_week1_ordinal(y: u64) -> u64 {
    let jan1 = ys(y) - 366;
    (7 * ((jan1 + 3) / 7)) / 7
}

/// The region `path` declares, from §2's layout. `None` — backlog, routines,
/// optional, inbox — is the *absence* of a bound, not a coarser grain.
pub fn region_of(rel: &str) -> Option<(u32, u64)> {
    let (dir, file) = rel.split_once('/')?;
    let stem = file.strip_suffix(".md")?;
    match dir {
        "day" => {
            let mut it = stem.split('-');
            let y = it.next()?.parse().ok()?;
            let m = it.next()?.parse().ok()?;
            let d = it.next()?.parse().ok()?;
            Some((0, to_day(y, m, d)))
        }
        // `calendar/2026-W37.md` is deliberately **not** here. Its name spells
        // a week, but §6.3 says calendar intervals are never demoted, so a
        // calendar file is not a horizon block that closes and has no region to
        // orient a demotion against. `none` is the absence of a bound, which is
        // the truthful answer for it.
        "week" => {
            let (y, w) = stem.split_once("-W")?;
            let y: u64 = y.parse().ok()?;
            let w: u64 = w.parse().ok()?;
            Some((1, iso_week1_ordinal(y) + (w - 1)))
        }
        "month" => {
            let (y, m) = stem.split_once('-')?;
            let y: u64 = y.parse().ok()?;
            let m: u64 = m.parse().ok()?;
            Some((2, 12 * (y - 1) + (m - 1)))
        }
        _ => None,
    }
}

pub fn doc_of(rel: &str, text: &str) -> Doc {
    Doc { path: rel.to_string(), lines: split_lines(text), region: region_of(rel) }
}
