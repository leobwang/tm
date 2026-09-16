//! **The kernel's `log` op against the fork point's reader and writer** (stage 5
//! D9 step B4; design `kernel/design/stage5/stage5-D9-D10-design.md` §14.2 row B4,
//! §5.3–§5.5, §17).
//!
//! **Retargeted to fork point `4748911` (2026-09-16, W-11; owner decision D23,
//! README gap 148).** Until this run the comparand on the Rust side was the
//! *in-tree* reader — `Log::parse_bytes`, `LogEntry::parse` and
//! `parse_timestamp`, at **11 sites** — and design §12 deletes all three at the
//! switch. Every one of those sites would then have had to be retargeted inside
//! the switch commit itself, which is the "least reviewable commit of the stage"
//! problem gap 146 was raised about. So the parse half now reads **fork point
//! 4748911's own verdicts**, taken through AGENTS §7.3's oracle
//! (`tm-oracle parse-entry`, added for this) and frozen into
//! `tests/fixtures/fork-4748911-log-lines.jsonl`, exactly as W-10 froze the
//! fork's replays for T5. Nothing here names a function §12 deletes.
//!
//! **Which half needed an oracle, and which did not.** T1–T3 are two halves:
//!
//! * the **parse** half — serde's and chrono's *per-line acceptance*: is this
//!   line an entry, a warning or blank, and what entry is it. Its only Rust
//!   implementation on this branch was the one §12 deletes, so it is the half
//!   that needed D23's new mode.
//! * the **writer** half — `LogEntry::{new, to_json}`, `Event`, `EVENT_NAMES`,
//!   `fmt_timestamp`, `hours_since_wake`. Design §12 **keeps** every one of
//!   these (they are the "stays" column of the `tm-core/src/log.rs` row), so
//!   **T2 needs no oracle at all** and is untouched by this retarget. It builds
//!   a line with the in-tree writer and asks the kernel to render it back.
//!
//! The tests, and what each compares:
//!
//! * **T1** `kernel_reads_the_corpus_logs_as_the_fork_point_did`: per line,
//!   entry, warning class or blank, over the seven corpus logs and a crafted
//!   set, against the **frozen fork**; each entry carries the fork's tag, id and
//!   `tm log` column, and corpus entries render byte-identically to the fork's
//!   own `to_json`. The residue is listed by line and parity entry (P14, P15).
//! * **T2** `kernel_reads_what_the_rust_writer_writes`: 256 generated events
//!   through the **in-tree writer**, then the kernel's rendering, byte-identical
//!   (P20). No oracle: §12 keeps the writer.
//! * **T3** `kernel_reads_every_timestamp_spelling_chrono_reads`: every spelling
//!   of `"t"` the fork's chrono reads, `:60` included, has the kernel's instant,
//!   offset, rendering and column; the residue is P23's range.
//!
//! **What the frozen fixture costs, stated rather than hidden.** One assertion
//! cannot be made from bytes on disk: "the fork reads the kernel's *rendering*
//! back to the same entry" (`LogEntry::parse(rendering) == e`), because the
//! rendering is produced at test time and the fork is not linked here. In
//! `cargo test --workspace` that is replaced by the **stronger byte-level**
//! claim it implied — the kernel's rendering *is* the fork's own `to_json`
//! bytes, or differs from them only in a hand-written numeral (P29's class,
//! checked as values). The original round trip is kept exactly, under
//! `TM_ORACLE`, by [`the_fork_reads_back_every_rendering_the_kernel_writes`].

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

#[allow(dead_code)]
#[path = "support/loggen.rs"]
mod loggen;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use chrono::{DateTime, Duration, FixedOffset, TimeZone, Utc};
use proptest::prelude::*;
use serde_json::{json, Value};
use tm_core::log::{hours_since_wake, Event, LogEntry, EVENT_NAMES};

/// Chicago's table, probed once per test binary.
fn chicago() -> &'static Value {
    static TZ: OnceLock<Value> = OnceLock::new();
    TZ.get_or_init(|| tz_table::probe(chrono_tz::America::Chicago).to_wire())
}

/// The zone the frozen fork answers were taken in, and the only one this file
/// asks the kernel about.
const TZ_NAME: &str = "America/Chicago";

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
///
/// `want.render` holds at most 4,096 lines, so a long file is several calls. Each
/// sends the file from line 1 up to the end of its window: since stage 5 D9 C6 a
/// header carries its entry's day and mask bit, which the lines before a tail
/// decide, so headers are answered only for a log from line 1 (until W3's
/// checkpoint).
fn kernel_read(segs: &[Option<&str>], terminated: bool) -> Vec<Kernel> {
    let mut out = Vec::with_capacity(segs.len());
    for (c, chunk) in segs.chunks(4096).enumerate() {
        let from = (c * 4096 + 1) as u64;
        let upto = c * 4096 + chunk.len();
        let lines: Vec<Value> =
            segs[..upto].iter().map(|s| s.map_or(Value::Null, |s| Value::String(s.to_string()))).collect();
        let render: Vec<u64> = (from..from + chunk.len() as u64).collect();
        let req = json!({
            "docs": [], "now": "2026-09-15", "tz": chicago(),
            "log": {"ckpt": null, "from": 1, "lines": lines,
                    "terminated": terminated || upto < segs.len(),
                    "want": {"facts": false, "headersFrom": from, "render": render}}
        });
        let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
        let resp: Value = serde_json::from_str(&raw).expect("the response is JSON");
        let log = &resp["ok"]["log"];
        assert!(log.is_object(), "no log answer: {}", &raw[..raw.len().min(300)]);
        assert_eq!(log["lines"], upto as u64);
        let mut warns = BTreeMap::new();
        for w in log["warnings"].as_array().expect("warnings").iter().filter(|w| w["line"].as_u64() >= Some(from)) {
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

// ===========================================================================
// GAP 148 / D23: the comparand that survives §12's deletion.
//
// Design §12 deletes `Log::parse_bytes`, `LogEntry::parse` and
// `parse_timestamp` at S.  They were T1-T3's entire Rust side, so at that
// moment these tests would either stop compiling or have to be retargeted
// inside the switch commit.  Neither is acceptable: AGENTS §9.2 names the
// second shape, "a check no input can fail", and gap 146 is the ledger entry
// for it.
//
// So the fork's per-line verdicts are taken ONCE through AGENTS §7.3's oracle
// and frozen here, the way W-10 froze the fork's replays for T5.  Both sides of
// every comparison below are then (a) the kernel, through the FFI, and (b)
// bytes on disk written by fork point 4748911 — and neither is the reader §12
// removes.
//
// Re-bless with, from the repository root:
//
//   TM_ORACLE=$(kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh) \
//   TM_FORK_BLESS=1 cargo test --test kernel_log_grammar -- --ignored \
//     the_frozen_fork_line_answers_are_reblessed_from_the_oracle
//
// A re-bless is a decision about what the fork point says, never a way to make
// a failure go away (AGENTS §7.2).
// ===========================================================================

/// The frozen fork-point verdicts: one JSON object a line, keyed by `src` and
/// the 1-based physical line `n` within it. `n = 0` is the whole-file reading.
const FROZEN_FORK_LINES: &str = "fork-4748911-log-lines.jsonl";

fn fixtures_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// What fork point 4748911 said about one physical log line.
#[derive(Clone, Debug)]
enum Fork {
    Blank,
    Entry(ForkEntry),
    /// The class of serde's message, and the message.
    Warn(String, String),
}

/// The fork's accepted entry, in the stable form `tm-oracle parse-entry` prints.
///
/// `json` is the fork's own `LogEntry::to_json` of the entry it just read — the
/// parse-*then*-write round trip. `epoch`/`nanos`/`offset` are the instant as
/// chrono read it: `json` keeps whole seconds only, so a leap second
/// (`nanos >= 1e9`) and the written offset would otherwise not survive it.
#[derive(Clone, Debug, PartialEq)]
struct ForkEntry {
    json: String,
    tag: String,
    id: Option<String>,
    t: String,
    display: String,
    epoch: i64,
    nanos: u64,
    offset: i64,
}

impl ForkEntry {
    fn of(v: &Value) -> ForkEntry {
        ForkEntry {
            json: v["json"].as_str().expect("the fork's to_json").to_string(),
            tag: v["tag"].as_str().expect("the fork's ev tag").to_string(),
            id: v["id"].as_str().map(str::to_string),
            t: v["t"].as_str().expect("the fork's fmt_timestamp").to_string(),
            display: v["display"].as_str().expect("the fork's tm log column").to_string(),
            epoch: v["epoch"].as_i64().expect("the fork's epoch seconds"),
            nanos: v["nanos"].as_u64().expect("the fork's subsecond nanos"),
            offset: v["offset"].as_i64().expect("the fork's written offset"),
        }
    }
}

/// The frozen answers, read once per test binary.
struct Frozen {
    /// `src` → `n` → the fork's verdict on that physical line.
    lines: BTreeMap<String, BTreeMap<u64, Fork>>,
    /// `src` → the fork's whole-file reading: `(entries, refused lines)`.
    wholes: BTreeMap<String, (u64, Vec<u64>)>,
}

impl Frozen {
    /// The fork's verdict on line `n` of `src`. A missing answer is a stale
    /// fixture, never a pass.
    fn line(&self, src: &str, n: u64) -> &Fork {
        self.lines
            .get(src)
            .and_then(|m| m.get(&n))
            .unwrap_or_else(|| panic!("no frozen fork answer for {src}:{n} — re-bless (see the GAP 148 banner)"))
    }

    /// How many lines of `src` the fixture answers for.
    fn count(&self, src: &str) -> usize {
        self.lines.get(src).map_or(0, BTreeMap::len)
    }

    /// The fork's whole-file reading of `src`, where it has one.
    fn whole(&self, src: &str) -> Option<&(u64, Vec<u64>)> {
        self.wholes.get(src)
    }
}

fn frozen() -> &'static Frozen {
    static F: OnceLock<Frozen> = OnceLock::new();
    F.get_or_init(|| {
        let path = fixtures_dir().join(FROZEN_FORK_LINES);
        let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
            panic!("{}: {e} — re-bless it (see this file's GAP 148 banner)", path.display())
        });
        let mut lines: BTreeMap<String, BTreeMap<u64, Fork>> = BTreeMap::new();
        let mut wholes: BTreeMap<String, (u64, Vec<u64>)> = BTreeMap::new();
        for l in text.lines().filter(|l| !l.trim().is_empty()) {
            let v: Value = serde_json::from_str(l).expect("a frozen fork answer is JSON");
            let src = v["src"].as_str().expect("a frozen answer names its source").to_string();
            let n = v["n"].as_u64().expect("a frozen answer numbers its line");
            let verdict = match v["v"].as_str().expect("a frozen answer has a verdict") {
                "entry" => Fork::Entry(ForkEntry::of(&v)),
                "blank" => Fork::Blank,
                "warn" => {
                    let e = v["error"].as_str().expect("a refusal carries the fork's text").to_string();
                    Fork::Warn(fork_class(&e), e)
                }
                "whole" => {
                    let refused = v["warningLines"]
                        .as_array()
                        .expect("the whole-file refused lines")
                        .iter()
                        .map(|l| l.as_u64().expect("a refused line"))
                        .collect();
                    wholes.insert(src, (v["entries"].as_u64().expect("the whole-file entry count"), refused));
                    continue;
                }
                other => panic!("unknown frozen verdict {other:?}"),
            };
            assert!(
                lines.entry(src.clone()).or_default().insert(n, verdict).is_none(),
                "the frozen fixture answers {src}:{n} twice"
            );
        }
        Frozen { lines, wholes }
    })
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

// ---------------------------------------------------------------------------
// The input sets, defined once so the bless and the tests cannot drift apart
// ---------------------------------------------------------------------------

/// One input source: its name in the fixture, its physical lines as raw bytes,
/// and whether the text they came from ended in a newline.
struct Source {
    name: String,
    segs: Vec<Vec<u8>>,
    terminated: bool,
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

/// **T1's sources**: the seven corpus logs, then the crafted set. A corpus log
/// is split exactly as `Log::parse_bytes` splits it, trailing empty segment and
/// all; the crafted set is its own lines joined by `\n`, which ends without one.
fn t1_sources() -> Vec<Source> {
    let mut out: Vec<Source> = corpus_logs()
        .into_iter()
        .map(|(name, bytes)| Source {
            name: format!("corpus:{name}"),
            segs: bytes.split(|b| *b == b'\n').map(<[u8]>::to_vec).collect(),
            terminated: bytes.ends_with(b"\n"),
        })
        .collect();
    out.push(Source { name: "crafted".into(), segs: crafted(), terminated: false });
    out
}

/// **T3's source**: one `note` line per timestamp spelling, so that the only
/// thing that can make the line unreadable is its `"t"`.
fn t3_source() -> Source {
    Source {
        name: "spellings".into(),
        segs: spellings()
            .iter()
            .map(|s| format!(r#"{{"t":{},"ev":"note","text":"x"}}"#, serde_json::to_string(s).expect("json")).into_bytes())
            .collect(),
        terminated: true,
    }
}

/// **The generated months**: `support/loggen.rs`'s two event rates, 30 days each.
fn month_sources() -> Vec<Source> {
    [loggen::Rate::Forty, loggen::Rate::SixtyOne]
        .into_iter()
        .map(|rate| Source {
            name: format!("month:{}", rate.label()),
            segs: loggen::log(rate, 30).into_iter().map(String::into_bytes).collect(),
            terminated: true,
        })
        .collect()
}

/// Every source the fixture answers for, in the order it is written.
fn all_sources() -> Vec<Source> {
    let mut out = t1_sources();
    out.push(t3_source());
    out.extend(month_sources());
    out
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

/// **T1.** Per line, the kernel's verdict is **fork point 4748911's**: blank,
/// entry or warning, and the warning's class; an entry carries the fork's tag,
/// id and `tm log` column, and the kernel's rendering is the fork's own
/// `to_json` bytes. Corpus entries are byte-identical. Every difference is in
/// [`residue`], and every residue line differs.
///
/// The fork's whole-file reading is compared too: the number of lines it turned
/// into entries, and the physical lines it refused, must be what this
/// line-by-line sweep saw.
#[test]
fn kernel_reads_the_corpus_logs_as_the_fork_point_did() {
    let frozen = frozen();
    let (mut lines, mut entries, mut warns, mut blanks, mut identical, mut seen_residue) = (0, 0, 0, 0, 0, 0);
    let mut not_identical = Vec::new();
    let mut wholes_checked = 0;
    for src in t1_sources() {
        let name = &src.name;
        assert_eq!(
            frozen.count(name),
            src.segs.len(),
            "{name}: the frozen fork answers {} lines but the input has {} — re-bless",
            frozen.count(name),
            src.segs.len()
        );
        let segs: Vec<Option<&str>> = src.segs.iter().map(|s| std::str::from_utf8(s).ok()).collect();
        let kernel = kernel_read(&segs, src.terminated);
        let (mut fork_entries, mut fork_refused) = (0u64, Vec::new());
        for (i, (seg, k)) in src.segs.iter().zip(&kernel).enumerate() {
            let n = (i + 1) as u64;
            lines += 1;
            let text = String::from_utf8_lossy(seg);
            let f = frozen.line(name, n);
            match f {
                Fork::Entry(_) => fork_entries += 1,
                Fork::Warn(..) => fork_refused.push(n),
                Fork::Blank => {}
            }
            if let Some((p, class)) = residue(&text) {
                seen_residue += 1;
                match (f, k) {
                    (Fork::Warn(fc, _), Kernel::Warn(kc)) => {
                        assert_eq!(kc, class, "{name}:{n} ({p})");
                        assert_ne!(fc, kc, "{name}:{n}: {p} residue no longer differs");
                    }
                    (Fork::Entry(_), Kernel::Warn(kc)) => assert_eq!(kc, class, "{name}:{n} ({p})"),
                    other => panic!("{name}:{n}: {p} residue changed shape: {other:?}"),
                }
                continue;
            }
            match (f, k) {
                (Fork::Blank, Kernel::Blank) => blanks += 1,
                (Fork::Warn(fc, msg), Kernel::Warn(kc)) => {
                    assert_eq!(fc, kc, "{name}:{n}: fork {msg:?}, line {:?}", &text[..text.len().min(120)]);
                    warns += 1;
                }
                (Fork::Entry(e), Kernel::Entry(tag, id, rendering, display)) => {
                    entries += 1;
                    assert_eq!(tag, &e.tag, "{name}:{n}");
                    assert_eq!(id.as_deref(), e.id.as_deref(), "{name}:{n}");
                    assert_eq!(display, &e.display, "{name}:{n}");
                    // The fork's own `to_json` of the entry it read from this
                    // line. Byte identity here is what used to be checked by
                    // parsing the kernel's rendering with the fork's reader;
                    // the round trip itself is kept, under `TM_ORACLE`, by
                    // `the_fork_reads_back_every_rendering_the_kernel_writes`.
                    if rendering == &e.json {
                        identical += 1;
                    } else {
                        assert_eq!(name, "crafted", "{name}:{n}: corpus entry not byte-identical");
                        not_identical.push((text.to_string(), rendering.clone(), e.json.clone()));
                    }
                }
                other => panic!("{name}:{n}: fork and kernel differ: {other:?} on {:?}", &text[..text.len().min(120)]),
            }
        }
        // The fork read the whole file, not a line at a time. Where the fixture
        // has that reading, this sweep must account for exactly the same
        // entries and the same refused lines (P15 makes the warning *text*
        // differ by design; which line is refused must not).
        if let Some((whole_entries, whole_refused)) = frozen.whole(name) {
            assert_eq!(fork_entries, *whole_entries, "{name}: the fork's whole-file entry count");
            assert_eq!(&fork_refused, whole_refused, "{name}: the fork's whole-file refused lines");
            wholes_checked += 1;
        }
    }
    // Every crafted entry the kernel does not render as serde does differs only
    // in a numeral written by hand (P29's class): as values they are equal.
    for (text, rendering, serde) in &not_identical {
        let a = numerals_as_f64(serde_json::from_str(rendering).expect("json"));
        let b = numerals_as_f64(serde_json::from_str(serde).expect("json"));
        assert_eq!(a, b, "{text}: {rendering} against {serde}");
    }
    assert_eq!(seen_residue, 8, "every residue line is in the set");
    assert_eq!(wholes_checked, 7, "every corpus log's whole-file reading was compared");
    eprintln!(
        "T1 (fork 4748911, frozen): {lines} lines, {entries} entries ({identical} byte-identical, {} differ only in hand-written numerals), {warns} warnings, {blanks} blank, {seen_residue} residue, {wholes_checked} whole-file readings",
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
    ///
    /// **No oracle, by design.** Design §12 *keeps* `LogEntry::{new, to_json}`,
    /// `Event` and `hours_since_wake` — they are the writer, and the switch does
    /// not touch them. So T2's comparand survives S untouched, and this is the
    /// half of T1-T3 that gap 148 never applied to.
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

/// **T3.** Every spelling **fork point 4748911's** `parse_timestamp` reads (RFC
/// 3339, else `%Y-%m-%dT%H:%M%:z`), `:60` included, the kernel reads to the same
/// instant and offset, and renders exactly as the fork's writer does. A spelling
/// the fork refuses, the kernel refuses (`badT`). The residue is P23: an instant
/// before 0001-01-01T00:00:00Z or at or after 10000-01-01T00:00:00Z, which
/// chrono reads and `Cal.Instant` cannot hold.
///
/// The spelling sits in a fixed `note` line, so the *only* thing that can make
/// the line unreadable is its `"t"`: line acceptance and timestamp acceptance
/// are the same question, which is what lets the frozen per-line verdict stand
/// in for a `parse_timestamp` call.
#[test]
fn kernel_reads_every_timestamp_spelling_chrono_reads() {
    let frozen = frozen();
    let spellings = spellings();
    let src = t3_source();
    assert_eq!(frozen.count(&src.name), src.segs.len(), "the frozen fork answers a different spelling set — re-bless");
    let segs: Vec<Option<&str>> = src.segs.iter().map(|s| std::str::from_utf8(s).ok()).collect();
    let kernel = kernel_read(&segs, src.terminated);
    // `Cal.Instant`'s range, as (epoch seconds, subsecond nanos) pairs so that a
    // leap second orders the way chrono orders it.
    let lo = (Utc.with_ymd_and_hms(1, 1, 1, 0, 0, 0).single().expect("origin").timestamp(), 0u64);
    let hi = ((Utc.with_ymd_and_hms(9999, 12, 31, 23, 59, 59).single().expect("end") + Duration::seconds(1)).timestamp(), 0u64);
    let (mut read, mut refused, mut outside, mut leap) = (0, 0, 0, 0);
    for (i, (s, k)) in spellings.iter().zip(&kernel).enumerate() {
        let n = (i + 1) as u64;
        match (frozen.line(&src.name, n), k) {
            (Fork::Entry(e), Kernel::Entry(_, _, rendering, display)) => {
                let at = (e.epoch, e.nanos);
                assert!(at >= lo && at < hi, "{s:?}: the kernel read an instant outside its range");
                // The whole line is fixed but for `"t"`, so byte identity with
                // the fork's own `to_json` is exactly "the kernel wrote the
                // instant, the offset and the payload as the fork would".
                assert_eq!(rendering, &e.json, "{s:?}");
                assert!(rendering.contains(&e.t), "{s:?}: {rendering}");
                assert_eq!(display, &e.display, "{s:?}");
                if e.nanos >= 1_000_000_000 {
                    leap += 1;
                }
                read += 1;
            }
            (Fork::Entry(e), Kernel::Warn(w)) => {
                let at = (e.epoch, e.nanos);
                assert!(at < lo || at >= hi, "{s:?}: the fork reads {}, the kernel warns {w}", e.t);
                assert_eq!(w, "badT", "{s:?}");
                outside += 1;
            }
            (Fork::Warn(_, _), Kernel::Warn(w)) => {
                assert_eq!(w, "badT", "{s:?}");
                refused += 1;
            }
            (f, k) => panic!("{s:?}: fork {f:?}, kernel {k:?}"),
        }
    }
    assert!(leap >= 4, "the `:60` spellings were read ({leap})");
    assert!(outside >= 5, "the P23 residue is exercised ({outside})");
    eprintln!("T3 (fork 4748911, frozen): {} spellings: {read} read ({leap} leap seconds), {refused} refused by both, {outside} P23 residue", spellings.len());
}

// ---------------------------------------------------------------------------
// D16 (owner answer Q5 (b); design §22.1's step S2): the evidence the writer
// swap needs, built BEFORE the swap.
//
// S2 replaces `LogEntry::to_json` with the kernel's `renderLine` as the one
// definition of the line format.  That swap is only safe if the kernel already
// renders, byte for byte, what the Rust writer writes — otherwise it silently
// rewrites `.tm/log.jsonl`.  T1 pins that over the corpus (a corpus entry that
// is not byte-identical fails there) and T2 over 256 random events.  Neither
// pins it over a realistic month, and nothing checked that T2's generator
// covers every event the binary can write.  Both are added here, so the claim
// "the bytes do not change" is a claim that can fail.
// ---------------------------------------------------------------------------

/// **Every writable event is actually generated.** T2's byte identity is only
/// as wide as [`any_event`], and nothing tied that list to [`EVENT_NAMES`]: a
/// kind added to `define_events!` without an arm here would leave T2 quietly
/// silent about it, and S2 would swap the writer for that kind on no evidence.
#[test]
fn the_writer_proptest_covers_every_writable_event() {
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;

    let mut runner = TestRunner::deterministic();
    let strategy = any_event();
    let mut seen = BTreeSet::new();
    for _ in 0..4_000 {
        let ev = strategy.new_tree(&mut runner).expect("a generated event").current();
        seen.insert(ev.name().to_string());
    }
    let all: BTreeSet<String> = EVENT_NAMES.iter().map(|n| n.to_string()).collect();
    assert_eq!(seen, all, "T2 does not generate every writable event");
    // `Unknown` is deliberately absent: the writer never writes one.
    assert_eq!(EVENT_NAMES.len(), 26);
}

/// **T2 over a generated month** (design §22.1's S2 acceptance: "the bytes are
/// identical to what the binary wrote before this step, over the corpus and a
/// generated month").  `support/loggen.rs` is the design pass's own generator,
/// so these are the files every §18 figure was taken on: 30 days at both event
/// rates, every line read by **fork point 4748911's** reader and written back by
/// its writer, against the kernel's rendering of the same line.
///
/// This is the realistic-shape half of the writer evidence; T2's proptest is the
/// random-value half and T1's corpus the recorded-history half.
#[test]
fn the_kernel_renders_a_generated_month_exactly_as_the_rust_writer_would() {
    let frozen = frozen();
    let mut seen = BTreeSet::new();
    let mut counted = 0usize;
    for src in month_sources() {
        let name = &src.name;
        assert_eq!(frozen.count(name), src.segs.len(), "{name}: the frozen fork answers a different month — re-bless");
        let segs: Vec<Option<&str>> = src.segs.iter().map(|s| std::str::from_utf8(s).ok()).collect();
        let kernel = kernel_read(&segs, src.terminated);
        assert_eq!(kernel.len(), src.segs.len(), "{name}");
        for (i, k) in kernel.iter().enumerate() {
            let n = (i + 1) as u64;
            let line = String::from_utf8_lossy(&src.segs[i]);
            match (frozen.line(name, n), k) {
                (Fork::Entry(e), Kernel::Entry(tag, _, rendering, _)) => {
                    assert_eq!(rendering, &e.json, "{name} line {n}: {line}");
                    assert_eq!(tag, &e.tag, "{name} line {n}");
                    seen.insert(tag.clone());
                }
                (f, k) => panic!("{name} line {n}: fork {f:?}, kernel {k:?} on {line}"),
            }
            counted += 1;
        }
    }
    // The two months are `loggen`'s pinned 1mo files (tm/tests/loggen.rs).
    assert_eq!(counted, 1_191 + 1_845, "both months, every line");
    assert!(seen.len() >= 20, "a month covers only {} event kinds: {seen:?}", seen.len());
    eprintln!("S2 evidence (fork 4748911, frozen): {counted} generated lines byte-identical, {} event kinds", seen.len());
}

/// **The fixture answers exactly the lines the tests feed it, and no others.**
///
/// A frozen comparand fails in two directions: a missing answer (caught where it
/// is read) and a *stale* one for an input nobody feeds any more, which would
/// sit in the fixture looking like coverage. This counts both.
#[test]
fn the_frozen_fork_answers_cover_exactly_the_inputs_the_tests_feed() {
    let frozen = frozen();
    let sources = all_sources();
    let mut expected = 0usize;
    for src in &sources {
        assert_eq!(
            frozen.count(&src.name),
            src.segs.len(),
            "{}: frozen answers {} lines, the input has {}",
            src.name,
            frozen.count(&src.name),
            src.segs.len()
        );
        expected += src.segs.len();
    }
    let names: BTreeSet<&str> = sources.iter().map(|s| s.name.as_str()).collect();
    let frozen_names: BTreeSet<&str> = frozen.lines.keys().map(String::as_str).collect();
    assert_eq!(frozen_names, names, "the fixture answers for sources the tests do not feed");
    let total: usize = frozen.lines.values().map(BTreeMap::len).sum();
    assert_eq!(total, expected, "the fixture holds answers for lines nothing feeds");
    assert_eq!(frozen.wholes.len(), 7, "one whole-file reading per corpus log");
    eprintln!(
        "frozen fork answers: {} sources, {total} per-line verdicts, {} whole-file readings",
        sources.len(),
        frozen.wholes.len()
    );
}

// ---------------------------------------------------------------------------
// The oracle arms: `#[ignore]`d and inert without `TM_ORACLE`, because they need
// a Rust build of fork point 4748911 outside this repository — the dependency
// AGENTS §7.3 keeps out of `check.sh` and out of `cargo test --workspace`.
// ---------------------------------------------------------------------------

/// **The oracle's own usage banner**, read from the binary itself.
///
/// Provenance is not freshness. W-11's audit followed the brief, verified that
/// the scratch tree's `.oracle-ref` and extracted sources were fork point
/// `4748911` — and the *binary* built from them was older than owner decision
/// **D23**, so it had no `parse-entry` mode: every call printed this banner and
/// exited 2, and the success assertion below reported `the fork oracle failed: `
/// with an **empty** message, because that oracle printed its banner on stdout.
/// So the mode is checked before it is used and named when it is missing, and
/// both streams are quoted when a call fails.
///
/// Neither the exit code (2, no subcommand) nor the stream matters here; only
/// the text does.
fn oracle_banner(bin: &std::path::Path) -> String {
    let out = std::process::Command::new(bin)
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap_or_else(|e| panic!("the fork oracle {}: {e}", bin.display()));
    format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
}

/// Refuse a stale oracle **by name**, before it is fed anything.
fn assert_oracle_mode(bin: &std::path::Path, mode: &str) {
    let banner = oracle_banner(bin);
    assert!(
        banner.contains(&format!("tm-oracle {mode}")),
        "the oracle at {} has no `{mode}` mode — it is STALE, whatever its `.oracle-ref` says. \
         Rebuild it: kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh. Its banner reads:\n{banner}",
        bin.display()
    );
}

/// Run one mode of the fork-point oracle over `inputs`, one JSON value per line
/// in, one JSON object per line out.
///
/// A segment that is UTF-8 goes as a JSON string, like every other mode; one
/// that is not cannot be a JSON string at all and goes as a JSON array of byte
/// values, which `parse-entry` accepts for exactly this reason.
fn fork_oracle(bin: &std::path::Path, args: &[&str], inputs: &[Vec<u8>]) -> Vec<Value> {
    use std::io::Write as _;
    assert_oracle_mode(bin, args.first().expect("the oracle is run in a mode"));
    let mut child = std::process::Command::new(bin)
        .args(args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("the fork oracle {}: {e}", bin.display()));
    let mut input = String::new();
    for b in inputs {
        let encoded = match std::str::from_utf8(b) {
            Ok(s) => serde_json::to_string(s).expect("a JSON string"),
            Err(_) => serde_json::to_string(&b.iter().map(|x| *x as u64).collect::<Vec<u64>>()).expect("a byte array"),
        };
        input.push_str(&encoded);
        input.push('\n');
    }
    // The input is larger than a pipe buffer and so is the oracle's answer, so
    // the write has to happen while this side is free to drain stdout — writing
    // it all first deadlocks: the child blocks writing its reply, we block
    // writing the request.
    let mut stdin = child.stdin.take().expect("stdin");
    let feeder = std::thread::spawn(move || stdin.write_all(input.as_bytes()).expect("write to the oracle"));
    let out = child.wait_with_output().expect("the oracle runs");
    feeder.join().expect("the feeding thread");
    assert!(
        out.status.success(),
        "the fork oracle {} {:?} failed (exit {:?})\n--- stderr ---\n{}\n--- stdout ---\n{}",
        bin.display(),
        args,
        out.status.code(),
        String::from_utf8_lossy(&out.stderr),
        String::from_utf8_lossy(&out.stdout)
    );
    String::from_utf8(out.stdout)
        .expect("the oracle's output is UTF-8")
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).expect("the oracle prints JSON"))
        .collect()
}

/// **Re-bless the frozen fork answers** from AGENTS §7.3's oracle scaffolding.
///
/// `#[ignore]`d and inert without **both** `TM_ORACLE` and `TM_FORK_BLESS`: it
/// rewrites a committed fixture, which is a decision and never a repair.
#[test]
#[ignore]
fn the_frozen_fork_line_answers_are_reblessed_from_the_oracle() {
    let (Some(bin), Some(_)) = (std::env::var_os("TM_ORACLE"), std::env::var_os("TM_FORK_BLESS")) else {
        eprintln!(
            "the frozen fork line answers: INERT — set TM_ORACLE to the fork-point oracle binary \
             (kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh prints its path) and \
             TM_FORK_BLESS=1 to rewrite tests/fixtures/{FROZEN_FORK_LINES}"
        );
        return;
    };
    let bin = std::path::PathBuf::from(bin);
    let sources = all_sources();
    let mut out = String::new();
    let mut verdicts = 0usize;
    for src in &sources {
        let answers = fork_oracle(&bin, &["parse-entry"], &src.segs);
        assert_eq!(answers.len(), src.segs.len(), "{}: one fork answer per physical line", src.name);
        for (i, a) in answers.iter().enumerate() {
            let mut row = a.clone();
            let obj = row.as_object_mut().expect("the oracle prints objects");
            obj.insert("src".into(), json!(src.name));
            obj.insert("n".into(), json!(i as u64 + 1));
            out.push_str(&serde_json::to_string(&row).expect("a frozen answer serialises"));
            out.push('\n');
            verdicts += 1;
        }
    }
    // The fork read each line on its own above. It also reads whole files, and
    // T1 compares its line-by-line sweep against that: how many entries the
    // fork got, and which physical lines it refused. Only the corpus logs can
    // take this arm — `replay` reads whole texts, and the crafted set is not
    // UTF-8.
    let corpus = corpus_logs();
    let texts: Vec<Vec<u8>> = corpus.iter().map(|(_, b)| b.clone()).collect();
    let wholes = fork_oracle(&bin, &["replay", TZ_NAME], &texts);
    assert_eq!(wholes.len(), corpus.len(), "one whole-file reading per corpus log");
    for ((name, _), a) in corpus.iter().zip(&wholes) {
        let row = json!({
            "src": format!("corpus:{name}"),
            "n": 0,
            "v": "whole",
            "entries": a["entries"],
            "warningLines": a["warningLines"],
        });
        out.push_str(&serde_json::to_string(&row).expect("a frozen answer serialises"));
        out.push('\n');
    }
    let path = fixtures_dir().join(FROZEN_FORK_LINES);
    std::fs::write(&path, &out).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
    eprintln!(
        "re-blessed {} from fork point 4748911: {} sources, {verdicts} per-line verdicts, {} whole-file readings, {} bytes",
        path.display(),
        sources.len(),
        wholes.len(),
        out.len()
    );
}

/// **The round trip the frozen fixture cannot make**: the fork reads back every
/// rendering the kernel writes, to the entry the fork itself read from that line.
///
/// This is T1's old `LogEntry::parse(rendering) == e` and `back.t.offset() ==
/// e.t.offset()`, kept exactly — but asked of fork point 4748911 rather than of
/// the in-tree reader design §12 deletes. It cannot be frozen, because the
/// rendering is produced by the kernel at test time; in `cargo test --workspace`
/// its place is taken by T1's and T3's byte-level comparison against the fork's
/// own `to_json`, which implies it whenever serde's `to_json`/`parse` round trip
/// is the identity.
#[test]
#[ignore]
fn the_fork_reads_back_every_rendering_the_kernel_writes() {
    let Some(bin) = std::env::var_os("TM_ORACLE") else {
        eprintln!(
            "the fork round trip: INERT — set TM_ORACLE to the fork-point oracle binary \
             (kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh prints its path)"
        );
        return;
    };
    let bin = std::path::PathBuf::from(bin);
    let frozen = frozen();
    let mut sources = t1_sources();
    sources.push(t3_source());
    let (mut checked, mut skipped) = (0usize, 0usize);
    for src in &sources {
        let name = &src.name;
        let segs: Vec<Option<&str>> = src.segs.iter().map(|s| std::str::from_utf8(s).ok()).collect();
        let kernel = kernel_read(&segs, src.terminated);
        // Every line both sides accept: the kernel's rendering, and the entry
        // the fork read from the original line.
        let mut renderings: Vec<Vec<u8>> = Vec::new();
        let mut want: Vec<(u64, ForkEntry)> = Vec::new();
        for (i, k) in kernel.iter().enumerate() {
            let n = (i + 1) as u64;
            if let (Fork::Entry(e), Kernel::Entry(_, _, rendering, _)) = (frozen.line(name, n), k) {
                renderings.push(rendering.clone().into_bytes());
                want.push((n, e.clone()));
            } else {
                skipped += 1;
            }
        }
        // Both renderings go back through the fork: the kernel's, and the
        // fork's own `to_json` of the same entry. Comparing the two READINGS,
        // rather than comparing the kernel's reading with the original entry,
        // is what T3 always did (`back.t == want.t`, where `want` was itself
        // round-tripped) and is the only correct statement: `fmt_timestamp`
        // keeps whole seconds, so a line carrying a fraction of a second is
        // truncated by *either* writer, and comparing a round trip with an
        // un-round-tripped original would fail on the writer's own contract
        // rather than on any disagreement.
        let mut pairs: Vec<Vec<u8>> = Vec::with_capacity(renderings.len() * 2);
        for (r, (_, e)) in renderings.iter().zip(&want) {
            pairs.push(r.clone());
            pairs.push(e.json.clone().into_bytes());
        }
        let back = fork_oracle(&bin, &["parse-entry"], &pairs);
        assert_eq!(back.len(), want.len() * 2, "{name}: one answer per rendering");
        for (a, (n, _)) in back.chunks(2).zip(&want) {
            assert_eq!(a[0]["v"], "entry", "{name}:{n}: the fork cannot read the kernel's rendering: {}", a[0]);
            assert_eq!(a[1]["v"], "entry", "{name}:{n}: the fork cannot read its own rendering: {}", a[1]);
            let (mine, theirs) = (ForkEntry::of(&a[0]), ForkEntry::of(&a[1]));
            // `LogEntry`'s `PartialEq` compares the instant and the event, and
            // T1 checked the written offset beside it. All three, plus the tag
            // and the id the header carries, are here.
            assert_eq!(mine.epoch, theirs.epoch, "{name}:{n}: the instant differs");
            assert_eq!(mine.nanos, theirs.nanos, "{name}:{n}: the subsecond differs");
            assert_eq!(mine.offset, theirs.offset, "{name}:{n}: the written offset differs");
            assert_eq!(mine.tag, theirs.tag, "{name}:{n}");
            assert_eq!(mine.id, theirs.id, "{name}:{n}");
            assert_eq!(mine.json, theirs.json, "{name}:{n}: the fork writes the two back differently");
            checked += 1;
        }
    }
    eprintln!(
        "the fork round trip (4748911): {checked} kernel renderings read back to the fork's own entry, \
         {skipped} lines skipped (blank, refused by either side, or P14/P15 residue)"
    );
}
