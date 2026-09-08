//! **The `main`-side half of the differential oracle.**
//!
//! `main` still carries `tm-core/src/grammar.rs` — 1,246 lines of hand-written
//! tokenizer, parser and byte-faithful serializer — and that is the code that
//! shipped. This binary makes it *observable*: it reads candidate item lines
//! and prints, as JSONL, exactly what the Rust says about each one. The Lean
//! side (`kernel/tm-kernel-ffi/examples/oracle-compare.rs`) asks the kernel the
//! same questions through the FFI and reports every disagreement.
//!
//! Modes:
//!
//! * `gen <n> <seed>` — generate `n` random item lines with the **same
//!   strategies as `tm-core/tests/grammar_proptest.rs`** (copied verbatim
//!   below, so the corpus is the one the shipped proptest samples from), and
//!   report on each. Deterministic in `seed`.
//! * `parse` — read one JSON string per line from stdin and report on each.
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

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use serde_json::{json, Value};
use std::io::{BufRead, Write};

use tm_core::grammar::{parse_line, ItemLine, ParseCtx};

// ---------------------------------------------------------------------------
// The generator, copied from tm-core/tests/grammar_proptest.rs on `main`.
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
        _ => {
            eprintln!("usage: tm-oracle gen <n> <seed>   |   tm-oracle parse  (JSON strings on stdin)");
            std::process::exit(2);
        }
    }
}
