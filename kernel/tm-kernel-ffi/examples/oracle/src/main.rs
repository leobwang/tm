//! **The fork-point half of the differential oracle.**
//!
//! The fork point `4748911` carries `tm-core/src/grammar.rs` — 1,246 lines of
//! hand-written tokenizer, parser and byte-faithful serializer — and
//! `tm-core/src/log.rs`'s reader, and that is the code that shipped. (It used
//! to be built from `main`, which was DISCARDED on 2026-09-12; AGENTS §7.3
//! recorded the script as broken and owed until this retarget.) This binary
//! makes that code *observable*: it reads candidate item lines, or whole logs,
//! and prints, as JSONL, exactly what the Rust says about each one. The Lean
//! side (`kernel/tm-kernel-ffi/examples/oracle-compare.rs`, and `tm`'s T5)
//! asks the kernel the same questions and reports every disagreement.
//!
//! Modes:
//!
//! * `gen <n> <seed>` — generate `n` random item lines with the **same
//!   strategies as `tm-core/tests/grammar_proptest.rs`** (copied verbatim
//!   below, so the corpus is the one the shipped proptest samples from), and
//!   report on each. Deterministic in `seed`.
//! * `parse` — read one JSON string per line from stdin and report on each.
//! * `parse-entry` — read one **log line** per line of stdin and report what
//!   the fork's `log::Log::parse_bytes` says about that single segment:
//!   accepted (with the entry in a stable form), refused (with serde's or
//!   chrono's own message), or blank. This is **T1-T3's oracle at the switch**
//!   (design §12 deletes `Log::parse_bytes`, `LogEntry::parse` and
//!   `parse_timestamp`, which are the only comparand those three tests have
//!   today; README gap 148, owner decision **D23**). A segment that is not
//!   UTF-8 cannot be a JSON string, so it may be given as a JSON array of byte
//!   values instead.
//! * `fit <tz> <today>` — the same input, run through the fork's
//!   `energy::fit_replay` at the default configuration, printing the fitted
//!   `Model` as JSON. This is design §14.6's T12 against the fork point: the
//!   kernel's half fits the observations **the kernel** derived.
//! * `replay <tz>` — read one JSON string per line from stdin, each the whole
//!   text of a `.tm/log.jsonl`, and print what the fork's `log::replay` derives
//!   from it, as JSON. This is **T5's oracle** at the switch (design §14.6
//!   item 4): the in-tree Rust reader is deleted there, so the fork point
//!   becomes the only other implementation to compare against.
//!
//! One JSON object per line, on stdout:
//!
//! ```text
//! {"in": <the line>,
//!  "item": <parse_line returned Ok>,
//!  "id": <item.id, "" when the line carries none>,
//!  "roundtrip": <item.line_text() == in>,
//!  "out": <item.line_text()>,
//!  "problems": [<tm check's diagnostics for this line>],
//!  "est_edit": <the line after set_token("est","45m"), or null>}
//! ```
//!
//! and for `replay`, one object per input log:
//!
//! ```text
//! {"replay": <tm_core::log::Replay, serialised>,
//!  "warningLines": [<1-based physical line of every line the reader refused>],
//!  "entries": <surviving + cancelled entries the reader read>}
//! ```
//!
//! and for `parse-entry`, one object per input segment:
//!
//! ```text
//! {"v": "entry", "json": <LogEntry::to_json>, "tag": <ev>, "id": <primary id>,
//!  "t": <fmt_timestamp>, "display": <tm log's column>,
//!  "epoch": <seconds>, "nanos": <subsec, >= 1e9 on a leap second>,
//!  "offset": <written offset in seconds east>}
//! {"v": "warn", "error": <serde's or chrono's own text>}
//! {"v": "blank"}
//! ```
//!
//! The fork's `Replay` and this branch's differ by exactly two serialised
//! fields — this branch adds `seams` and `last_effective_t` (step R1–R4), and
//! its `rows`/`line_count` are `#[serde(skip)]` — and every nested record
//! struct has the identical field list, on the same `chrono`/`chrono-tz`
//! versions. So the two `serde_json` values are comparable key for key once
//! those two added keys are set aside, which is what makes this a whole-
//! `Replay` comparison rather than a hand-listed one.

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use serde_json::{json, Value};
use std::io::{BufRead, Write};

use tm_core::grammar::{parse_line, ItemLine, ParseCtx};
use tm_core::log::{fmt_timestamp, Log};

// ---------------------------------------------------------------------------
// The generator, copied from tm-core/tests/grammar_proptest.rs at the fork point.
// Do not "improve" it: its value is that it is the shipped generator.
// ---------------------------------------------------------------------------

fn ws() -> impl Strategy<Value = String> {
    prop_oneof![
        6 => Just(" ".to_string()),
        2 => Just("  ".to_string()),
        1 => Just("\t".to_string()),
        1 => Just("    ".to_string()),
    ]
}

fn state() -> impl Strategy<Value = &'static str> {
    prop::sample::select(vec!["[ ]", "[>]", "[x]", "[-]", "[~]", "[?]"])
}

fn est() -> impl Strategy<Value = String> {
    prop_oneof![
        "[1-9][0-9]?[bmh]".prop_map(|s| s),
        "[1-9]h[0-5][0-9]m".prop_map(|s| s),
    ]
}

fn word() -> impl Strategy<Value = String> {
    prop_oneof![
        5 => "[A-Za-z][a-z0-9.\\-]{0,6}".prop_map(|s| s),
        2 => prop::sample::select(vec![
            "é", "über", "Été", "→", "✈", "—", "§3", "Ж37", "日本語", "ORD→SFO", "🎂", "naïve",
        ])
        .prop_map(|s| s.to_string()),
        2 => "[0-9]{1,2}[a-z]{0,2}".prop_map(|s| s),
        1 => "[A-Z][a-z]{1,4}:".prop_map(|s| s),
    ]
}

fn title() -> impl Strategy<Value = Vec<String>> {
    prop::collection::vec(word(), 1..4)
}

fn date() -> impl Strategy<Value = String> {
    "2026-(0[1-9]|1[0-2])-(0[1-9]|1[0-9]|2[0-8])".prop_map(|s| s)
}

fn time() -> impl Strategy<Value = String> {
    "([01][0-9]|2[0-3]):[0-5][0-9]".prop_map(|s| s)
}

fn dur() -> impl Strategy<Value = String> {
    prop_oneof![
        "[1-9][0-9]?[bmhd]".prop_map(|s| s),
        "[1-9]h[0-5][0-9]m".prop_map(|s| s),
    ]
}

fn token() -> impl Strategy<Value = String> {
    prop_oneof![
        "@[A-Za-z][a-z0-9]{0,3}".prop_map(|s| s),
        "#[a-z]{1,6}".prop_map(|s| s),
        "![1-4]".prop_map(|s| s),
        "\\^[a-z][a-z0-9]{0,3}".prop_map(|s| s),
        (date(), prop::option::of(time()))
            .prop_map(|(d, t)| match t {
                Some(t) => format!("due:{d}T{t}"),
                None => format!("due:{d}"),
            }),
        (date(), time(), time()).prop_map(|(d, a, b)| format!("at:{d}T{a}/{b}")),
        (date(), time(), date(), time()).prop_map(|(d, a, e, b)| format!("at:{d}T{a}/{e}T{b}")),
        (time(), time(), dur()).prop_map(|(a, b, d)| format!("win:{a}-{b} dur:{d}")),
        (date(), time(), time(), dur()).prop_map(|(d, a, b, x)| format!("win:{d}T{a}/{b} dur:{x}")),
        dur().prop_map(|d| format!("dur:{d}")),
        prop_oneof![
            dur().prop_map(|d| format!("pref:wake+{d}")),
            time().prop_map(|t| format!("pref:{t}"))
        ],
        prop::sample::select(vec![
            "every:day",
            "every:weekday",
            "every:week",
            "every:Mon,Wed,Fri",
            "every:2w:Sun",
            "every:3d",
            "every:month:15",
            "every:Sat",
        ])
        .prop_map(|s| s.to_string()),
        (dur(), prop::option::of(dur())).prop_map(|(a, b)| match b {
            Some(b) => format!("after-done:{a}~{b}"),
            None => format!("after-done:{a}"),
        }),
        ("[a-z]{2,6}", prop::option::of(dur())).prop_map(|(n, t)| match t {
            Some(t) => format!("on-event:{n}/{t}"),
            None => format!("on-event:{n}"),
        }),
        prop::sample::select(vec!["on-miss:expire", "on-miss:persist", "on-miss:next"])
            .prop_map(|s| s.to_string()),
        (dur(), prop::sample::select(vec!["d", "w", "m"])).prop_map(|(d, p)| format!("min:{d}/{p}")),
        (dur(), prop::sample::select(vec!["d", "w", "m"])).prop_map(|(d, p)| format!("max:{d}/{p}")),
        (dur(), prop::sample::select(vec!["d", "w", "m"])).prop_map(|(d, p)| format!("cap:{d}/{p}")),
        prop::collection::vec(
            prop_oneof!["\\^[a-z][a-z0-9]{0,3}".prop_map(|s| s), "event:[a-z]{2,5}".prop_map(|s| s)],
            1..3
        )
        .prop_map(|v| format!("after:{}", v.join(","))),
        prop::sample::select(vec!["loc:lounge", "loc:home", "loc:out", "loc:zoom", "loc:JCL"])
            .prop_map(|s| s.to_string()),
        est().prop_map(|d| format!("est:{d}")),
        prop::collection::vec("[WD][0-9]{2}", 1..3).prop_map(|v| format!("demoted:{}", v.join(","))),
        date().prop_map(|d| format!("waiting:{d}")),
        dur().prop_map(|d| format!("buffer:{d}")),
        "[0-5]".prop_map(|c| format!("ci:{c}")),
        prop::sample::select(vec!["open", "atomic", "manual", "travel-day", "hot"])
            .prop_map(|s| s.to_string()),
        "zz:[a-z0-9]{1,4}".prop_map(|s| s),
        word(),
        prop::sample::select(vec!["@", "#", "!", "^", "!5", "!!!", "^é", "^%"]).prop_map(|s| s.to_string()),
    ]
}

fn line() -> impl Strategy<Value = (String, bool)> {
    let with_state = (
        state(),
        prop::option::of("[0-5]"),
        prop::option::of(est()),
        title(),
        prop::collection::vec(token(), 0..8).prop_shuffle(),
        prop::collection::vec(ws(), 16),
        prop::option::of(ws()),
        prop::sample::select(vec!["", " ", "\t"]),
    )
        .prop_map(|(st, ci, est, title, tokens, ws, trailing, after_bullet)| {
            let mut w = ws.into_iter().cycle();
            let mut s = format!("- {after_bullet}{st}");
            if let Some(c) = ci {
                s.push_str(&w.next().unwrap());
                s.push_str(&c);
            }
            if let Some(e) = est {
                s.push_str(&w.next().unwrap());
                s.push_str(&e);
            }
            for word in title {
                s.push_str(&w.next().unwrap());
                s.push_str(&word);
            }
            for t in tokens {
                s.push_str(&w.next().unwrap());
                s.push_str(&t);
            }
            if let Some(t) = trailing {
                s.push_str(&t);
            }
            (s, true)
        });
    let stateless = (
        title(),
        prop::collection::vec(token(), 0..6).prop_shuffle(),
        prop::collection::vec(ws(), 12),
        prop::option::of(ws()),
    )
        .prop_map(|(title, tokens, ws, trailing)| {
            let mut w = ws.into_iter().cycle();
            let mut s = "-".to_string();
            let mut first = true;
            for word in title {
                let lead = if first { " ".to_string() } else { w.next().unwrap() };
                s.push_str(&lead);
                first = false;
                s.push_str(&word);
            }
            for t in tokens {
                s.push_str(&w.next().unwrap());
                s.push_str(&t);
            }
            if let Some(t) = trailing {
                s.push_str(&t);
            }
            (s, false)
        });
    prop_oneof![3 => with_state, 1 => stateless]
}

// ---------------------------------------------------------------------------
// What the Rust says about one line
// ---------------------------------------------------------------------------

/// The path both halves of the oracle use. A week file has no §4.3 shape rule
/// on either side, so neither the Rust's horizon defaults nor the kernel's
/// `shapeWfFor` colours the answer.
const FILE: &str = "week/2026-W37.md";

fn observe(text: &str) -> Value {
    let ctx = ParseCtx::new(FILE, 60);
    match parse_line(text, &ctx) {
        Err(_) => json!({ "in": text, "item": false }),
        Ok(item) => {
            let out = item.line_text();
            let est_edit = ItemLine::parse(text).ok().map(|mut l| {
                l.set_token("est", "45m");
                l.to_string()
            });
            json!({
                "in": text,
                "item": true,
                "id": item.id.as_str(),
                "roundtrip": out == text,
                "out": out,
                "problems": item.problems,
                "est_edit": est_edit,
            })
        }
    }
}

/// What the fork's reader derives from one whole log's text, in `tz`.
///
/// `replay(None, tz)` is exactly what `Ctx::replay_of` called on this branch
/// before the switch: the whole log, every day, no range.
fn observe_log(text: &str, tz: chrono_tz::Tz) -> Value {
    let log = Log::parse(text);
    json!({
        "replay": log.replay(None, tz),
        "warningLines": log.warnings.iter().map(|w| w.line as u64).collect::<Vec<u64>>(),
        "entries": log.entries.len(),
    })
}

/// **What the fork's reader says about ONE physical log line** (owner decision
/// **D23**; README gap 148).
///
/// This is `Log::parse_bytes`'s own loop body over a single `\n`-separated
/// segment — exactly the call `tm/tests/kernel_log_grammar.rs`'s `fork_read`
/// made against the **in-tree** copy of this reader until design §12 deleted
/// it. It gives the three verdicts that reader can give (blank, entry,
/// warning) and, for an entry, everything T1 and T3 compare:
///
/// * `json` — `LogEntry::to_json`, serde's own bytes for the entry just read.
///   That is the parse-*then*-write round trip T1's byte-identity arm needs.
///   The writer alone (`to_json`, `fmt_timestamp`, `Event`) is **kept** by §12
///   and so needs no oracle; it is the *parse* that has to come from here.
/// * `tag`, `id` — `Event::name` and `Event::primary_id`: the kernel's header.
/// * `t`, `display` — `fmt_timestamp` and `tm log`'s column.
/// * `epoch`, `nanos`, `offset` — the instant exactly as chrono read it. `json`
///   keeps only whole seconds, so a leap second (`nanos >= 1e9`) and the
///   *written* offset would otherwise not survive the round trip, and both are
///   what T3 is about.
///
/// A refusal carries serde's or chrono's message **verbatim**. The kernel's
/// warning classes are named constructors and the fork's are free text (parity
/// **P15**), so the class is read off this text on the kernel's side, by the
/// same `fork_class` the test has always used.
fn observe_entry(seg: &[u8]) -> Value {
    let log = Log::parse_bytes(seg);
    match (log.entries.first(), log.warnings.first()) {
        (Some(e), None) => json!({
            "v": "entry",
            "json": e.to_json().expect("serde writes back the entry it just read"),
            "tag": e.ev.name(),
            "id": e.ev.primary_id(),
            "t": fmt_timestamp(&e.t),
            "display": e.t.format("%Y-%m-%d %H:%M").to_string(),
            "epoch": e.t.timestamp(),
            "nanos": e.t.timestamp_subsec_nanos(),
            "offset": e.t.offset().local_minus_utc(),
        }),
        (None, Some(w)) => json!({ "v": "warn", "error": w.error }),
        (None, None) => json!({ "v": "blank" }),
        (Some(_), Some(_)) => panic!("one segment gave both an entry and a warning"),
    }
}

/// What the fork's `tm model --fit` makes of one whole log, in `tz`, as of
/// `today`: fork `energy::fit_replay` over the fork's own replay, at the
/// default configuration — both halves of the comparison must use the same
/// one, and the corpus logs carry no config of their own.
///
/// This is design §14.6's **T12** asked of the fork point rather than of a
/// saved `model.json`: on this branch `fit_replay` is gone (phase F1,
/// `983a8be`), and the fit reads the three observation lists. So the kernel's
/// half runs `energy::fit_observations` over the observations **the kernel
/// derived**, and the two `Model`s must be equal field for field.
fn observe_fit(text: &str, tz: chrono_tz::Tz, today: chrono::NaiveDate) -> Value {
    let replay = Log::parse(text).replay(None, tz);
    let cfg = tm_core::config::Config::default();
    json!({ "model": tm_core::energy::fit_replay(&cfg, &replay, today) })
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let stdout = std::io::stdout();
    let mut w = std::io::BufWriter::new(stdout.lock());

    match args.get(1).map(String::as_str) {
        Some("gen") => {
            let n: usize = args[2].parse().expect("gen <n> <seed>");
            let seed: u64 = args[3].parse().expect("gen <n> <seed>");
            let mut bytes = [0u8; 32];
            bytes[..8].copy_from_slice(&seed.to_le_bytes());
            let rng = TestRng::from_seed(RngAlgorithm::ChaCha, &bytes);
            let mut runner = TestRunner::new_with_rng(Config::default(), rng);
            let strategy = line();
            for _ in 0..n {
                let (text, _stateful) = strategy.new_tree(&mut runner).unwrap().current();
                writeln!(w, "{}", observe(&text)).unwrap();
            }
        }
        Some("parse") => {
            for l in std::io::stdin().lock().lines() {
                let l = l.unwrap();
                if l.trim().is_empty() {
                    continue;
                }
                let text: String = serde_json::from_str(&l)
                    .unwrap_or_else(|e| panic!("stdin must be one JSON string per line: {e} in {l:?}"));
                writeln!(w, "{}", observe(&text)).unwrap();
            }
        }
        Some("parse-entry") => {
            for l in std::io::stdin().lock().lines() {
                let l = l.unwrap();
                if l.trim().is_empty() {
                    continue;
                }
                // One physical log line per input line. A UTF-8 segment arrives
                // as a JSON string, like every other mode. A segment that is
                // NOT UTF-8 (a torn write; the crafted set's `\xff`) cannot be
                // a JSON string at all, so it arrives as a JSON array of byte
                // values. Either way the reader is handed the raw bytes of one
                // segment, which is what `Log::parse_bytes` splits out.
                let v: Value = serde_json::from_str(&l).unwrap_or_else(|e| {
                    panic!("stdin must be a JSON string or byte array per line: {e} in {l:?}")
                });
                let seg: Vec<u8> = match v {
                    Value::String(s) => s.into_bytes(),
                    Value::Array(bytes) => bytes
                        .iter()
                        .map(|b| {
                            let n = b.as_u64().unwrap_or_else(|| panic!("a byte array holds numbers: {b} in {l:?}"));
                            u8::try_from(n).unwrap_or_else(|_| panic!("a byte is 0..=255, not {n}, in {l:?}"))
                        })
                        .collect(),
                    other => panic!("stdin must be a JSON string or byte array per line, not {other} in {l:?}"),
                };
                writeln!(w, "{}", observe_entry(&seg)).unwrap();
            }
        }
        Some("replay") => {
            let tz: chrono_tz::Tz = args
                .get(2)
                .expect("replay <tz>  (e.g. America/Chicago)")
                .parse()
                .expect("a tz database name");
            for l in std::io::stdin().lock().lines() {
                let l = l.unwrap();
                if l.trim().is_empty() {
                    continue;
                }
                let text: String = serde_json::from_str(&l)
                    .unwrap_or_else(|e| panic!("stdin must be one JSON string per line: {e} in {l:?}"));
                writeln!(w, "{}", observe_log(&text, tz)).unwrap();
            }
        }
        Some("fit") => {
            let tz: chrono_tz::Tz = args
                .get(2)
                .expect("fit <tz> <today>  (e.g. America/Chicago 2026-09-15)")
                .parse()
                .expect("a tz database name");
            let today = chrono::NaiveDate::parse_from_str(
                args.get(3).expect("fit <tz> <today>"),
                "%Y-%m-%d",
            )
            .expect("today as YYYY-MM-DD");
            for l in std::io::stdin().lock().lines() {
                let l = l.unwrap();
                if l.trim().is_empty() {
                    continue;
                }
                let text: String = serde_json::from_str(&l)
                    .unwrap_or_else(|e| panic!("stdin must be one JSON string per line: {e} in {l:?}"));
                writeln!(w, "{}", observe_fit(&text, tz, today)).unwrap();
            }
        }
        _ => {
            eprintln!(
                "usage: tm-oracle gen <n> <seed>   |   tm-oracle parse  (JSON strings on stdin)\n\
                 \x20      tm-oracle parse-entry  (ONE log line per line: a JSON string, or a JSON array of bytes)\n\
                 \x20      tm-oracle replay <tz>  (whole log texts, one JSON string per line)\n\
                 \x20      tm-oracle fit <tz> <today>  (the same, fitted: `tm model --fit`)"
            );
            std::process::exit(2);
        }
    }
}
