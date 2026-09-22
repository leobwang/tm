//! **The item-line generators, in one place** (AGENTS §5.3: two definitions of
//! one concept is the bug).
//!
//! These strategies were `tm-core/tests/grammar_proptest.rs`'s own until stage 6
//! **W-25 (step R2)**, when `tm/tests/kernel_item_grammar.rs` began drawing the
//! *same* lines and handing them to the **kernel** through the FFI.  A copy
//! would have made "the kernel sees what the fork's proptest sees" a claim about
//! two files that drift; this module makes it a fact about one.
//!
//! It lives under `tests/grammar_common/` rather than `tests/` so cargo does not
//! build it as a test binary of its own, and `tm/tests/kernel_item_grammar.rs`
//! reaches it by `#[path]` across the two crates — `tm` cannot see `tm-core`'s
//! test binaries, but it can see this file.
//!
//! Nothing here asserts.  Every property that reads these lines states its own,
//! and the two readers state **different** ones: the fork test asks whether
//! `parse_line` and `ItemLine` agree with each other, the kernel test asks
//! whether the kernel's `Line.lean` agrees with both.

use proptest::prelude::*;
use tm_core::grammar::ParseCtx;
use tm_core::model::{Item, SourceLoc};

pub fn ws() -> impl Strategy<Value = String> {
    prop_oneof![
        6 => Just(" ".to_string()),
        2 => Just("  ".to_string()),
        1 => Just("\t".to_string()),
        1 => Just("    ".to_string()),
    ]
}

pub fn state() -> impl Strategy<Value = &'static str> {
    prop::sample::select(vec!["[ ]", "[>]", "[x]", "[-]", "[~]", "[?]"])
}

pub fn est() -> impl Strategy<Value = String> {
    prop_oneof![
        "[1-9][0-9]?[bmh]".prop_map(|s| s),
        "[1-9]h[0-5][0-9]m".prop_map(|s| s),
    ]
}

/// A word that is not a token: ASCII, non-ASCII (multi-byte first char),
/// digit-leading (may look like a ci digit or a duration), or an uppercase
/// `Word:` (only `[a-z-]+:` ends the title).
pub fn word() -> impl Strategy<Value = String> {
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

/// Title words (1..4 of [`word`]).
pub fn title() -> impl Strategy<Value = Vec<String>> {
    prop::collection::vec(word(), 1..4)
}

pub fn date() -> impl Strategy<Value = String> {
    "2026-(0[1-9]|1[0-2])-(0[1-9]|1[0-9]|2[0-8])".prop_map(|s| s)
}

pub fn time() -> impl Strategy<Value = String> {
    "([01][0-9]|2[0-3]):[0-5][0-9]".prop_map(|s| s)
}

pub fn dur() -> impl Strategy<Value = String> {
    prop_oneof![
        "[1-9][0-9]?[bmhd]".prop_map(|s| s),
        "[1-9]h[0-5][0-9]m".prop_map(|s| s),
    ]
}

pub fn token() -> impl Strategy<Value = String> {
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
        // Malformed structured tokens and lone sigils stay in the title.
        prop::sample::select(vec!["@", "#", "!", "^", "!5", "!!!", "^é", "^%"]).prop_map(|s| s.to_string()),
    ]
}

/// A random item line and whether it carries a state.
pub fn line() -> impl Strategy<Value = (String, bool)> {
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

pub fn ctx_for(stateful: bool) -> ParseCtx<'static> {
    if stateful {
        ParseCtx::new("week/2026-W37.md", 60)
    } else {
        ParseCtx::new("routines.md", 60)
    }
}

pub fn without_src(mut it: Item) -> Item {
    it.src = SourceLoc::default();
    it
}
