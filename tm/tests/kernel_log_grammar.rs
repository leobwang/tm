//! **The kernel's `log` op against the fork point's reader and writer** (stage 5
//! D9 step B4; design `kernel/design/stage5/stage5-D9-D10-design.md` §14.2 row B4,
//! §5.3–§5.5, §17).
//!
//! The fork is the in-tree Rust: `tm_core::log::Log::parse_bytes` is still the one
//! reader the binary uses, and `LogEntry::to_json` the one writer. The kernel is
//! reached through `tm_kernel_ffi::call`, a request with a `tz` table from
//! `tm/src/cli/tz_table.rs` and a `log` section of lines (Boundary.lean's
//! `runWithLog`). Nothing in the binary calls the `log` op yet.
//!
//! * **T1** `kernel_reads_the_corpus_logs_as_the_fork_point_did`: per line, entry,
//!   warning class or blank, over the seven corpus logs and a crafted set; each
//!   entry read back by the fork equals the fork's, with the same tag, id and
//!   `tm log` column; corpus entries render byte-identically. The residue is
//!   listed by line and parity entry (P14, P15).
//! * **T2** `kernel_reads_what_the_rust_writer_writes`: 256 generated events
//!   through serde, then the kernel's rendering, byte-identical (P20).
//! * **T3** `kernel_reads_every_timestamp_spelling_chrono_reads`: every spelling
//!   of `"t"` chrono reads, `:60` included, has the kernel's instant, offset,
//!   rendering and column; the residue is P23's range.

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

use std::collections::BTreeMap;
use std::sync::OnceLock;

use chrono::{DateTime, Duration, FixedOffset, TimeZone, Utc};
use proptest::prelude::*;
use serde_json::{json, Value};
use tm_core::log::{fmt_timestamp, hours_since_wake, parse_timestamp, Event, Log, LogEntry};

/// Chicago's table, probed once per test binary.
fn chicago() -> &'static Value {
    static TZ: OnceLock<Value> = OnceLock::new();
    TZ.get_or_init(|| tz_table::probe(chrono_tz::America::Chicago).to_wire())
}

/// What the kernel said about one line.
#[derive(Clone, Debug, PartialEq)]
enum Kernel {
    Blank,
    /// `(tag, id, rendering, display)`.
    Entry(String, Option<String>, String, String),
    /// The warning's class: its name, and `:key` for a field.
    Warn(String),
}

/// One `log` call over `segs` (lines split on `\n`; `None` is not UTF-8), every
/// line asked for a header and a rendering. Lines are numbered from 1.
fn kernel_read(segs: &[Option<&str>], terminated: bool) -> Vec<Kernel> {
    let mut out = Vec::with_capacity(segs.len());
    // `want.render` holds at most 4,096 lines, so a long file is several calls.
    for (c, chunk) in segs.chunks(4096).enumerate() {
        let from = (c * 4096 + 1) as u64;
        let lines: Vec<Value> =
            chunk.iter().map(|s| s.map_or(Value::Null, |s| Value::String(s.to_string()))).collect();
        let render: Vec<u64> = (from..from + chunk.len() as u64).collect();
        let req = json!({
            "docs": [], "tz": chicago(),
            "log": {"ckpt": null, "from": from, "lines": lines,
                    "terminated": terminated || (c + 1) * 4096 < segs.len(),
                    "want": {"facts": false, "headersFrom": from, "render": render}}
        });
        let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
        let resp: Value = serde_json::from_str(&raw).expect("the response is JSON");
        let log = &resp["ok"]["log"];
        assert!(log.is_object(), "no log answer: {}", &raw[..raw.len().min(300)]);
        assert_eq!(log["lines"], from + chunk.len() as u64 - 1);
        let mut warns = BTreeMap::new();
        for w in log["warnings"].as_array().expect("warnings") {
            let mut class = w["w"].as_str().expect("w").to_string();
            if let Some(k) = w.get("key").and_then(Value::as_str) {
                class = format!("{class}:{k}");
            }
            warns.insert(w["line"].as_u64().expect("line"), class);
        }
        let mut heads = BTreeMap::new();
        for h in log["headers"].as_array().expect("headers") {
            heads.insert(
                h[0].as_u64().expect("line"),
                (h[1].as_str().expect("tag").to_string(), h[2].as_str().map(str::to_string)),
            );
        }
        let renders = log["render"].as_array().expect("render");
        assert_eq!(renders.len(), chunk.len());
        for (k, r) in renders.iter().enumerate() {
            let n = from + k as u64;
            assert_eq!(r[0], n);
            out.push(match (warns.get(&n), heads.get(&n), r[1].as_str()) {
                (Some(w), None, None) => Kernel::Warn(w.clone()),
                (None, Some((tag, id)), Some(rendering)) => Kernel::Entry(
                    tag.clone(),
                    id.clone(),
                    rendering.to_string(),
                    r[2].as_str().expect("display").to_string(),
                ),
                (None, None, None) => Kernel::Blank,
                other => panic!("line {n}: an inconsistent answer {other:?}"),
            });
        }
    }
    out
}

/// What the fork said about one line.
#[derive(Clone, Debug)]
enum Fork {
    Blank,
    Entry(LogEntry),
    /// The class of serde's message, and the message.
    Warn(String, String),
}

/// The class a fork message names, in the kernel's words (`Log.LWarn`). The
/// fork's texts are serde's (P15); this reads the class off them.
fn fork_class(err: &str) -> String {
    let err = match err.find(" at line ") {
        Some(i) => &err[..i],
        None => err,
    };
    if err.starts_with("invalid UTF-8") {
        return "invalidUtf8".into();
    }
    if let Some(rest) = err.strip_prefix("event \"") {
        let rest = rest.split_once("\": ").map_or("", |(_, r)| r);
        if let Some(k) = rest.strip_prefix("missing field `") {
            return format!("missingField:{}", k.trim_end_matches('`'));
        }
        return format!("badField:{}", rest.split(':').next().unwrap_or_default());
    }
    match err {
        "missing field `t`" => "noT".into(),
        "missing field `ev`" => "noEv".into(),
        "`ev` must be a string" => "evNotString".into(),
        "duplicate field `t`" => "duplicateT".into(),
        "number out of range" => "numberOutOfRange".into(),
        "recursion limit exceeded" => "lineTooDeep".into(),
        _ if err.starts_with("invalid timestamp") => "badT".into(),
        _ if err.starts_with("invalid type") && err.ends_with("expected struct LogEntry") => {
            "notAnObject".into()
        }
        _ if err.starts_with("invalid type") && err.ends_with("expected a string") => "tNotString".into(),
        _ => "notJson".into(),
    }
}

/// The fork's verdict on one segment: `Log::parse_bytes` over that segment alone.
fn fork_read(seg: &[u8]) -> Fork {
    let log = Log::parse_bytes(seg);
    match (log.entries.first(), log.warnings.first()) {
        (Some(e), None) => Fork::Entry(e.clone()),
        (None, Some(w)) => Fork::Warn(fork_class(&w.error), w.error.clone()),
        (None, None) => Fork::Blank,
        _ => panic!("one segment gave an entry and a warning"),
    }
}

/// The seven corpus logs: `kernel/corpus/logs/*.jsonl` and the three plans'
/// `.tm/log.jsonl`.
fn corpus_logs() -> Vec<(String, Vec<u8>)> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/corpus");
    [
        "logs/energy-14d.jsonl",
        "logs/malformed.jsonl",
        "logs/review-14d.jsonl",
        "logs/three-days.jsonl",
        "plan-home-day/.tm/log.jsonl",
        "plan-recur/.tm/log.jsonl",
        "plan-travel-day/.tm/log.jsonl",
    ]
    .iter()
    .map(|p| (p.to_string(), std::fs::read(root.join(p)).expect("corpus log")))
    .collect()
}

const A: &str = r#""t":"2026-09-07T06:05:00-05:00""#;

/// **The crafted set** (design §14.2 row B4): the B3 serde probe's lines
/// (§5.4's numeric rows, `hsw` spellings, repeated keys, serde's float band,
/// nesting, two-defect lines, bad payloads), plus what a line array cannot carry
/// as text: bytes that are not UTF-8, CRLF, and a line past the length bound.
fn crafted() -> Vec<Vec<u8>> {
    let mut l: Vec<String> = Vec::new();
    for v in ["-0", "3.0", "4294967295", "4294967296", "1e2", "-1", "null", r#""5""#, "18446744073709551616", "0.0"] {
        l.push(format!(r#"{{{A},"ev":"wake","slept_min":{v}}}"#));
    }
    for v in ["255", "256", "-0", "2.0"] {
        l.push(format!(r#"{{{A},"ev":"energy","pred":{v},"rep":1,"loc":"home"}}"#));
    }
    for v in ["null", "256", "1.0"] {
        l.push(format!(r#"{{{A},"ev":"wake","slept_min":1,"onset_min":{v}}}"#));
    }
    for v in ["-0", "1e308", "18446744073709551616", "null", r#""1""#, "2.50", "1E+05", "-3"] {
        l.push(format!(r#"{{{A},"ev":"energy","pred":1,"rep":1,"hsw":{v},"loc":"home"}}"#));
    }
    l.push(format!(r#"{{{A},"ev":"wake","slept_min":1,"slept_min":2}}"#));
    l.push(format!(r#"{{{A},"ev":"wake","slept_min":"x","slept_min":2}}"#));
    l.push(format!(r#"{{{A},"ev":"wake","slept_min":2,"slept_min":"x"}}"#));
    l.push(r#"{"t":"2026-09-07T06:05:00-05:00","t":"2026-09-08T06:05:00-05:00","ev":"note","text":"x"}"#.into());
    l.push(r#"{"t":"bad","t":"2026-09-08T06:05:00-05:00","ev":"note","text":"x"}"#.into());
    l.push(format!(r#"{{{A},"ev":"mood","ev":"note","text":"x"}}"#));
    l.push(format!(r#"{{{A},"ev":"note","ev":"mood","text":"x"}}"#));
    l.push(format!(r#"{{{A},"ev":"mood","b":1,"a":2,"b":3}}"#));
    l.push(format!(r#"{{{A},"ev":"mood","B":1,"a":2,"é":3,"z":4}}"#));
    let long_zero = format!("0.{}1e700", "0".repeat(400));
    for v in [
        "1e308", "1.7976931348623157e308", "1.7976931348623158e308", "1.7976931348623159e308", "1e309",
        "10e307", "0e999", "0.0e99999999999", "1e99999999999", "1e-99999999999", "-1e400", "0.001e310",
        "1e2147483647", "0e2147483648",
        "179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368",
        "179769313486231580793728971405303415079934132710037826936173778980444968292764750946649017977587207096330286416692887910946555547851940402630657488671505820681908902000708383676273854845817711531764475730270069855571366959622842914819860834936475292719074168444365510704342711559699508093042880177904174497792",
        "179769313486231580793728971405303415079934132710037826936173778980444968292764750946649017977587207096330286416692887910946555547851940402630657488671505820681908902000708383676273854845817711531764475730270069855571366959622842914819860834936475292719074168444365510704342711559699508093042880177904174497791",
        "179769313486231580793728971405303415079934132710037826936173778980444968292764750946649017977587207096330286416692887910946555547851940402630657488671505820681908902000708383676273854845817711531764475730270069855571366959622842914819860834936475292719074168444365510704342711559699508093042880177904174497793",
        "179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.9",
        &long_zero,
        "17976931348623158079e288", "17976931348623158080e288", "17976931348623157e292", "17976931348623158e292",
        "179769313486231580793e287", "1797693134862315807937289714053034150799e269", "18446744073709551615e289",
        "18446744073709551616e289",
    ] {
        l.push(format!(r#"{{{A},"ev":"mood","x":{v}}}"#));
    }
    l.push(format!(r#"{{{A},"ev":"mood","x":"1e400"}}"#));
    l.push(format!(r#"{{{A},"ev":"mood","x":-0,"y":1.50,"z":1e3}}"#));
    for d in [63, 64, 65, 126, 127, 128] {
        l.push(format!(r#"{{{A},"ev":"mood","x":{}1{}}}"#, "[".repeat(d), "]".repeat(d)));
    }
    l.push(r#"{"t":"bad","x":1e400}"#.into());
    l.push(r#"{"x":1e400,"t":"bad"}"#.into());
    l.push("[1,2,".into());
    l.push(format!(r#"{{{A},"ev":"wake"}} x"#));
    l.push(format!(r#"{{{A},"ev":"wake","slept_min":1}} x"#));
    l.push(format!(r#"{{{A},"ev":"done","est_min":"x"}}"#));
    l.push(r#"{"t":"bad","ev":"wake""#.into());
    l.push(r#"{"ev":7}"#.into());
    l.push(format!(r#"{{{A},"ev":null}}"#));
    l.push(format!("{{{A}}}"));
    l.push(r#"{"t":5,"ev":"note","text":"x"}"#.into());
    l.push(r#""str""#.into());
    l.push("1".into());
    l.push("null".into());
    l.push(format!("{{{A},\"ev\":\"note\",\"text\":\"x\"}}\r\r"));
    l.push(" \t ".into());
    l.push("\u{feff}".into());
    l.push(format!(r#"{{{A},"ev":"arrive","loc":"h","window":["a","b","c"],"budget":1}}"#));
    l.push(format!(r#"{{{A},"ev":"arrive","loc":"h","window":["a",1],"budget":1}}"#));
    l.push(format!(r#"{{{A},"ev":"arrive","loc":"h","window":"a","budget":1}}"#));
    l.push(format!(r#"{{{A},"ev":"done","id":"a","est_min":1,"actual_min":1,"ci":1,"tags":["x",1]}}"#));
    l.push(format!(r#"{{{A},"ev":"done","id":"a","est_min":1,"actual_min":1,"ci":1,"partial":null}}"#));
    l.push(format!(r#"{{{A},"ev":"done","id":"a","est_min":1,"actual_min":1,"ci":1,"partial":false,"went":null}}"#));
    l.push(format!(r#"{{{A},"ev":"Wake","slept_min":1}}"#));
    l.push(format!(r#"{{{A},"\u0065v":"note","text":"x"}}"#));
    l.push(format!(r#"{{{A},"ev":"start","id":"a","pred":1,"loc":"h"}}"#));
    l.push(format!(r#"{{{A},"ev":"break","planned_min":5,"where":null}}"#));
    l.push(format!(r#"{{{A},"ev":"mood","t":"x"}}"#));
    l.push(format!(r#"{{{A},"ev":"done","id":"a","actual_min":"x","est_min":"y","ci":1}}"#));
    l.push(format!(r#"{{{A},"ev":"done","est_min":1,"actual_min":1}}"#));
    l.push(r#"{"ev":"wake","t":"2026-09-07T06:05:00-05:00","slept_min":1}"#.into());
    l.push(format!(r#"{{{A},"ev":"wake","slept_min":1,"x":1e400}}"#));
    l.push(format!(r#"{{{A},"ev":"resume","lost_min":1,"dropped":null}}"#));
    l.push(format!(r#"{{{A},"ev":"undo","of":"x","id":7}}"#));
    // Beyond the probe: escapes and non-ASCII strings, a CRLF line, a line
    // past the length bound (P14), and bytes that are not UTF-8.
    l.push(format!(r#"{{{A},"ev":"note","text":"a\"b\\c\n\t\u0001\u007f é 😀 \ud83d\ude00"}}"#));
    l.push(format!("{{{A},\"ev\":\"drop\",\"id\":\"x1\"}}\r"));
    l.push(format!(r#"{{{A},"ev":"note","text":"{}"}}"#, "y".repeat(65_537)));
    let mut out: Vec<Vec<u8>> = l.into_iter().map(String::into_bytes).collect();
    out.push(b"{\"t\":\"2026-09-07T06:05:00-05:00\",\"ev\":\"note\",\"text\":\"\xff\"}".to_vec());
    out.push(vec![0xe2, 0x82]);
    out
}

/// **The residue, by line**: where the kernel's verdict is not the fork's, and why.
/// `None` in the second place means entry-or-warning itself differs (P14); a
/// class names the kernel's class where only the class differs (P15).
fn residue(line: &str) -> Option<(&'static str, &'static str)> {
    let deep = |d: usize| format!(r#"{{{A},"ev":"mood","x":{}1{}}}"#, "[".repeat(d), "]".repeat(d));
    if line == deep(64) || line == deep(65) || line == deep(126) {
        return Some(("P14", "lineTooDeep"));
    }
    if line.len() > 65_536 {
        return Some(("P14", "lineTooLong"));
    }
    match line {
        r#"{"t":"bad","x":1e400}"# => Some(("P15", "numberOutOfRange")),
        "[1,2," => Some(("P15", "notJson")),
        r#"{"t":"bad","ev":"wake""# => Some(("P15", "notJson")),
        _ if line == format!(r#"{{{A},"ev":"wake"}} x"#) => Some(("P15", "notJson")),
        _ => None,
    }
}

/// **T1.** Per line, the kernel's verdict is the fork's: blank, entry or warning,
/// and the warning's class; an entry reads back to the fork's entry, with its tag,
/// id and `tm log` column. Corpus entries render byte for byte as serde writes
/// them. Every difference is in [`residue`], and every residue line differs.
#[test]
fn kernel_reads_the_corpus_logs_as_the_fork_point_did() {
    let mut files = corpus_logs();
    let crafted_bytes = crafted().join(&b'\n');
    files.push(("crafted".into(), crafted_bytes));
    let (mut lines, mut entries, mut warns, mut blanks, mut identical, mut seen_residue) = (0, 0, 0, 0, 0, 0);
    let mut not_identical = Vec::new();
    for (name, bytes) in &files {
        let raw: Vec<&[u8]> = bytes.split(|b| *b == b'\n').collect();
        let segs: Vec<Option<&str>> = raw.iter().map(|r| std::str::from_utf8(r).ok()).collect();
        let kernel = kernel_read(&segs, bytes.ends_with(b"\n"));
        // The whole file through the fork, too: the per-segment reading below is
        // the fork's own loop body.
        let whole = Log::parse_bytes(bytes);
        let mut whole_entries = whole.entries.iter();
        for (i, (seg, k)) in raw.iter().zip(&kernel).enumerate() {
            let n = i + 1;
            lines += 1;
            let text = String::from_utf8_lossy(seg);
            let f = fork_read(seg);
            if let Some((p, class)) = residue(&text) {
                seen_residue += 1;
                match (&f, k) {
                    (Fork::Warn(fc, _), Kernel::Warn(kc)) => {
                        assert_eq!(kc, class, "{name}:{n} ({p})");
                        assert_ne!(fc, kc, "{name}:{n}: {p} residue no longer differs");
                    }
                    (Fork::Entry(_), Kernel::Warn(kc)) => assert_eq!(kc, class, "{name}:{n} ({p})"),
                    other => panic!("{name}:{n}: {p} residue changed shape: {other:?}"),
                }
                if let Fork::Entry(_) = f {
                    whole_entries.next();
                }
                continue;
            }
            match (&f, k) {
                (Fork::Blank, Kernel::Blank) => blanks += 1,
                (Fork::Warn(fc, msg), Kernel::Warn(kc)) => {
                    assert_eq!(fc, kc, "{name}:{n}: fork {msg:?}, line {:?}", &text[..text.len().min(120)]);
                    warns += 1;
                }
                (Fork::Entry(e), Kernel::Entry(tag, id, rendering, display)) => {
                    entries += 1;
                    assert_eq!(Some(e), whole_entries.next(), "{name}:{n}");
                    let back = LogEntry::parse(rendering).expect("the fork reads the kernel's rendering");
                    assert_eq!(&back, e, "{name}:{n}: {rendering}");
                    assert_eq!(back.t.offset(), e.t.offset(), "{name}:{n}");
                    assert_eq!(tag, e.ev.name(), "{name}:{n}");
                    assert_eq!(id.as_deref(), e.ev.primary_id(), "{name}:{n}");
                    assert_eq!(display, &e.t.format("%Y-%m-%d %H:%M").to_string(), "{name}:{n}");
                    let serde = e.to_json().expect("serde writes it");
                    if &serde == rendering {
                        identical += 1;
                    } else {
                        assert_eq!(name, "crafted", "{name}:{n}: corpus entry not byte-identical");
                        not_identical.push((text.to_string(), rendering.clone(), serde));
                    }
                }
                other => panic!("{name}:{n}: fork and kernel differ: {other:?} on {:?}", &text[..text.len().min(120)]),
            }
        }
        assert!(whole_entries.next().is_none(), "{name}: the whole-file reading has more entries");
    }
    // Every crafted entry the kernel does not render as serde does differs only
    // in a numeral written by hand (P29's class): as values they are equal.
    for (text, rendering, serde) in &not_identical {
        let a = numerals_as_f64(serde_json::from_str(rendering).expect("json"));
        let b = numerals_as_f64(serde_json::from_str(serde).expect("json"));
        assert_eq!(a, b, "{text}: {rendering} against {serde}");
    }
    assert_eq!(seen_residue, 8, "every residue line is in the set");
    eprintln!(
        "T1: {lines} lines, {entries} entries ({identical} byte-identical, {} differ only in hand-written numerals), {warns} warnings, {blanks} blank, {seen_residue} residue",
        not_identical.len()
    );
}

/// A JSON value with every numeral read as serde's `f64`: two renderings equal
/// under this differ only in how a numeral is spelled (`-3` and `-3.0`, `1.50`
/// and `1.5`), P29's class.
fn numerals_as_f64(v: Value) -> Value {
    match v {
        Value::Number(n) => json!(n.as_f64()),
        Value::Array(xs) => Value::Array(xs.into_iter().map(numerals_as_f64).collect()),
        Value::Object(m) => Value::Object(m.into_iter().map(|(k, v)| (k, numerals_as_f64(v))).collect()),
        v => v,
    }
}

/// A string serde must escape and the kernel must escape the same way.
fn any_text() -> impl Strategy<Value = String> {
    prop::collection::vec(any::<char>(), 0..10).prop_map(String::from_iter)
}

fn any_event() -> impl Strategy<Value = Event> {
    let s = any_text;
    let hsw = (-315_537_897_600i64..315_537_897_600).prop_map(|d| {
        let wake = Utc.timestamp_opt(0, 0).single().expect("epoch");
        hours_since_wake(&(wake + Duration::seconds(d)), &wake)
    });
    prop_oneof![
        (any::<u32>(), any::<Option<u32>>()).prop_map(|(slept_min, onset_min)| Event::Wake { slept_min, onset_min }),
        (s(), s(), s(), any::<u32>()).prop_map(|(loc, a, b, budget)| Event::Arrive { loc, window: [a, b], budget }),
        (s(), any::<u8>(), any::<Option<u8>>(), hsw.clone(), any::<u32>(), s(), any::<u32>(), any::<u32>()).prop_map(
            |(id, pred, rep, hsw, slept_min, loc, blocks_done, since_break_min)| Event::Start {
                id, pred, rep, hsw, slept_min, loc, blocks_done, since_break_min
            }
        ),
        (s(), any::<u32>(), any::<u32>(), any::<Option<u8>>(), prop::collection::vec(s(), 0..3), any::<u8>(), any::<bool>())
            .prop_map(|(id, est_min, actual_min, went, tags, ci, partial)| Event::Done {
                id, est_min, actual_min, went, tags, ci, partial
            }),
        (s(), any::<u32>()).prop_map(|(id, by_min)| Event::Extend { id, by_min }),
        (s(), any::<u32>()).prop_map(|(id, remaining_min)| Event::Stop { id, remaining_min }),
        (any::<u32>(), any::<Option<u32>>(), prop::option::of(s()))
            .prop_map(|(planned_min, actual_min, r#where)| Event::Break { planned_min, actual_min, r#where }),
        (any::<u8>(), any::<u8>(), hsw, s()).prop_map(|(pred, rep, hsw, loc)| Event::Energy { pred, rep, hsw, loc }),
        prop::option::of(s()).prop_map(|id| Event::Interrupt { id }),
        (any::<u32>(), prop::collection::vec(s(), 0..3)).prop_map(|(lost_min, dropped)| Event::Resume { lost_min, dropped }),
        s().prop_map(|id| Event::Pause { id }),
        s().prop_map(|id| Event::Unpause { id }),
        (s(), any::<u32>()).prop_map(|(attributed, min)| Event::Idle { attributed, min }),
        (s(), s(), s(), any::<Option<u32>>())
            .prop_map(|(item, inst, status, actual_min)| Event::Routine { item, inst, status, actual_min }),
        (s(), s()).prop_map(|(item, inst)| Event::Skip { item, inst }),
        (s(), any::<u32>(), any::<u32>())
            .prop_map(|(hash, replans_today, drift_min)| Event::Plan { hash, replans_today, drift_min }),
        (s(), prop::option::of(s())).prop_map(|(name, id)| Event::Named { name, id }),
        (s(), s(), s(), any::<u32>()).prop_map(|(id, from, to, est_min)| Event::Demote { id, from, to, est_min }),
        s().prop_map(|id| Event::Readopt { id }),
        (s(), s(), s()).prop_map(|(id, from, to)| Event::Move { id, from, to }),
        s().prop_map(|id| Event::Drop { id }),
        (s(), s(), s(), s()).prop_map(|(id, field, from, to)| Event::Edit { id, field, from, to }),
        s().prop_map(|text| Event::Note { text }),
        s().prop_map(|loc| Event::Loc { loc }),
        (s(), s()).prop_map(|(period, key)| Event::Close { period, key }),
        (s(), prop::option::of(s())).prop_map(|(of, id)| Event::Undo { of, id }),
    ]
}

/// A written instant: years 1000 to 8999, any nanosecond (the writer keeps whole
/// seconds), and a whole-minute offset under a day, as `Local` gives.
fn any_stamp() -> impl Strategy<Value = DateTime<FixedOffset>> {
    (-30_610_224_000i64..221_845_392_000, 0u32..1_000_000_000, -1439i32..1440).prop_map(|(secs, ns, min)| {
        let off = FixedOffset::east_opt(min * 60).expect("under a day");
        off.timestamp_opt(secs, ns).single().expect("a fixed offset is unambiguous")
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// **T2.** What the Rust writer writes, the kernel reads and renders back byte
    /// for byte (design §14.2 row B4; P20). `hsw` is `hours_since_wake` of two
    /// instants, the writer's only source for it.
    #[test]
    fn kernel_reads_what_the_rust_writer_writes(t in any_stamp(), ev in any_event()) {
        let line = LogEntry::new(t, ev).to_json().expect("serde writes it");
        let got = kernel_read(&[Some(&line)], true);
        match &got[0] {
            Kernel::Entry(_, _, rendering, _) => prop_assert_eq!(rendering, &line),
            other => prop_assert!(false, "{:?} on {}", other, line),
        }
    }
}

/// The spellings of `"t"` T3 reads: B2's edge set, every `"t"` of the corpus logs,
/// and 4,000 deterministic mutations of five seeds.
fn spellings() -> Vec<String> {
    let mut v: Vec<String> = [
        "2026-09-07T06:05:00-05:00", "2026-09-07t06:05:00-05:00", "2026-09-07 06:05:00-05:00",
        "2026-09-07x06:05:00-05:00", "2026-09-07T06:05:00Z", "2026-09-07T06:05:00z", "2026-09-07T06:05:00+00:00",
        "2026-09-07T06:05:00-00:00", "2026-09-07T06:05:00.Z", "2026-09-07T06:05:00.1Z",
        "2026-09-07T06:05:00.123456789Z", "2026-09-07T06:05:00.1234567891Z",
        "2026-09-07T06:05:00.123456789012-05:00", "2026-09-07T06:05:00.000000000000+01:30",
        "2016-12-31T23:59:60Z", "2016-12-31T23:59:60.999999999Z", "2016-12-31T12:34:60-05:00",
        "2016-12-31T23:59:60.5+05:30", "2016-12-31T23:59:61Z", "2026-09-07T24:00:00Z", "2026-09-07T23:60:00Z",
        "2026-09-07T06:05:00+24:00", "2026-09-07T06:05:00+23:59", "2026-09-07T06:05:00-23:59",
        "2026-09-07T06:05:00+05:60", "2026-09-07T06:05:00+0500", "2026-09-07T06:05:00+05",
        "2026-09-07T06:05:00\u{2212}05:00", "2026-09-07T06:05:00 +05:00", "2026-09-07T06:05:00+05:00 ",
        "0000-12-31T23:00:00-05:00", "0000-01-01T00:00:00Z", "0001-01-01T00:00:00Z", "0001-01-01T00:00:00+00:01",
        "0001-01-01T00:00:00-00:01", "9999-12-31T23:59:59Z", "9999-12-31T23:59:59-00:01",
        "9999-12-31T23:59:59+00:01", "2026-02-29T00:00:00Z", "2024-02-29T00:00:00Z", "2026-13-01T00:00:00Z",
        "2026-9-07T06:05:00Z", "2026-09-07T06:05-05:00", "2026-09-07T06:05+05:30", "2026-09-07T06:05Z",
        "2026-09-07T6:5-05:00", " 2026-09-07T06:05-05:00", "2026- 09- 07T 06: 05 -05:00",
        "2026-09-07T06:05-05 00", "2026-09-07T06:05-05: :00", "2026-09-07T06:05-05:00 ",
        "2026-09-07 06:05-05:00", "2026-09-07t06:05-05:00", "+2026-09-07T06:05-05:00",
        "+02026-09-07T06:05-05:00", "+0000000002026-09-07T06:05-05:00", "-2026-09-07T06:05-05:00",
        "26-09-07T06:05-05:00", "0-12-31T23:00-05:00", "+10000-01-01T00:00+00:00",
        "2026-09-07T06:05\u{2212}05:00", "2026-09-07T06:05 -05:00", "\u{3000}2026-09-07T06:05-05:00",
        "2026-09-07T06:05-05: 00", "2026-09-07T06:05:30-05:00x", "2026-09-07T06:05-0500", "2026-09-07T06:05-5:00",
        "2026-09-07T06:05-05:6", "2026-09-07T06:05+99:00", "2026-09-07T06:05:00.5", "2026-09-07T06", "",
        "2026-09-07", "2026-09-07T06:05:00-05:00:00", "2026-09-07\t06:05-05:00", "2026-09-07T\t06:05-05:00",
        "2026-09-07T06:05:00.-05:00", "\u{ff12}026-09-07T06:05:00Z", "-0-12-31T23:00-05:00",
        "-0000-12-31T23:00-05:00", "+0-12-31T23:00-05:00", "-00-12-31T23:00+05:00", "2916-12-31T23:59:60Z",
        "2026-09-07T06:05:00\u{a0}-05:00", "2026-09-07T06:05\u{200a}-05:00",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    for (_, bytes) in corpus_logs() {
        for line in bytes.split(|b| *b == b'\n') {
            if let Ok(Value::Object(m)) = serde_json::from_slice::<Value>(line) {
                if let Some(Value::String(t)) = m.get("t") {
                    v.push(t.clone());
                }
            }
        }
    }
    // splitmix64: mutations of five seeds (a digit, a separator or a character
    // deleted, duplicated or swapped), deterministic.
    let seeds = [
        "2026-09-07T06:05:00-05:00", "2016-12-31T23:59:60Z", "2026-09-07T06:05-05:00", "0000-12-31T23:30:00-01:00",
        "9999-12-31T23:59:59Z",
    ];
    let alphabet: Vec<char> = "0123456789-:T tZz+.\u{2212}\u{3000}".chars().collect();
    let mut x: u64 = 7;
    let mut next = move || {
        x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = x;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    for k in 0..4000 {
        let mut s: Vec<char> = seeds[k % seeds.len()].chars().collect();
        for _ in 0..(1 + next() % 3) {
            let i = (next() % s.len().max(1) as u64) as usize;
            match next() % 4 {
                0 if !s.is_empty() => {
                    s.remove(i.min(s.len() - 1));
                }
                1 => s.insert(i.min(s.len()), alphabet[(next() % alphabet.len() as u64) as usize]),
                2 if !s.is_empty() => {
                    let j = i.min(s.len() - 1);
                    s[j] = alphabet[(next() % alphabet.len() as u64) as usize];
                }
                _ if s.len() > 1 => {
                    let j = i.min(s.len() - 2);
                    s.swap(j, j + 1);
                }
                _ => {}
            }
        }
        v.push(s.into_iter().collect());
    }
    v
}

/// **T3.** Every spelling chrono reads (the fork's `parse_timestamp`: RFC 3339,
/// else `%Y-%m-%dT%H:%M%:z`), `:60` included, the kernel reads to the same
/// instant and offset, and renders as `fmt_timestamp` and the `tm log` column do.
/// A spelling chrono refuses, the kernel refuses (`badT`). The residue is P23: an
/// instant before 0001-01-01T00:00:00Z or at or after 10000-01-01T00:00:00Z, which
/// chrono reads and `Cal.Instant` cannot hold.
#[test]
fn kernel_reads_every_timestamp_spelling_chrono_reads() {
    let spellings = spellings();
    let lines: Vec<String> = spellings
        .iter()
        .map(|s| format!(r#"{{"t":{},"ev":"note","text":"x"}}"#, serde_json::to_string(s).expect("json")))
        .collect();
    let segs: Vec<Option<&str>> = lines.iter().map(|l| Some(l.as_str())).collect();
    let kernel = kernel_read(&segs, true);
    let lo = Utc.with_ymd_and_hms(1, 1, 1, 0, 0, 0).single().expect("origin");
    let hi = Utc.with_ymd_and_hms(9999, 12, 31, 23, 59, 59).single().expect("end") + Duration::seconds(1);
    let (mut read, mut refused, mut outside, mut leap) = (0, 0, 0, 0);
    for (s, k) in spellings.iter().zip(&kernel) {
        match (parse_timestamp(s), k) {
            (Ok(dt), Kernel::Entry(_, _, rendering, display)) => {
                assert!(dt >= lo && dt < hi, "{s:?}: the kernel read an instant outside its range");
                let back = LogEntry::parse(rendering).expect("the fork reads the kernel's rendering");
                let want = LogEntry::parse(&LogEntry::new(dt, Event::Note { text: "x".into() }).to_json().unwrap())
                    .expect("round trip");
                assert_eq!(back.t, want.t, "{s:?}");
                assert_eq!(back.t.offset(), dt.offset(), "{s:?}");
                assert!(rendering.contains(&fmt_timestamp(&dt)), "{s:?}: {rendering}");
                assert_eq!(display, &dt.format("%Y-%m-%d %H:%M").to_string(), "{s:?}");
                if dt.timestamp_subsec_nanos() >= 1_000_000_000 {
                    leap += 1;
                }
                read += 1;
            }
            (Ok(dt), Kernel::Warn(w)) => {
                assert!(dt < lo || dt >= hi, "{s:?}: chrono reads {dt}, the kernel warns {w}");
                assert_eq!(w, "badT", "{s:?}");
                outside += 1;
            }
            (Err(_), Kernel::Warn(w)) => {
                assert_eq!(w, "badT", "{s:?}");
                refused += 1;
            }
            (r, k) => panic!("{s:?}: chrono {r:?}, kernel {k:?}"),
        }
    }
    assert!(leap >= 4, "the `:60` spellings were read ({leap})");
    assert!(outside >= 5, "the P23 residue is exercised ({outside})");
    eprintln!("T3: {} spellings: {read} read ({leap} leap seconds), {refused} refused by both, {outside} P23 residue", spellings.len());
}
