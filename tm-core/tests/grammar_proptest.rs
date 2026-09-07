//! Property tests for the grammar (spec §17 M1): random item lines parse
//! and serialize byte-identically, and an edit changes only what it must.

use proptest::prelude::*;
use tm_core::grammar::{parse_line, ItemLine, ParseCtx};
use tm_core::model::{Dur, Id, Item, SourceLoc, State};

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

/// Title words: start with a letter, no `:`; never look like an estimate.
fn title() -> impl Strategy<Value = Vec<String>> {
    prop::collection::vec("[A-Za-z][a-z0-9.\\-]{0,6}", 1..4)
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
        "[A-Za-z][a-z0-9.]{0,5}".prop_map(|s| s),
    ]
}

/// A random item line and whether it carries a state.
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

fn ctx_for(stateful: bool) -> ParseCtx<'static> {
    if stateful {
        ParseCtx::new("week/2026-W37.md", 60)
    } else {
        ParseCtx::new("routines.md", 60)
    }
}

fn without_src(mut it: Item) -> Item {
    it.src = SourceLoc::default();
    it
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn parse_serialize_is_byte_identical((text, stateful) in line()) {
        let ctx = ctx_for(stateful);
        let item = parse_line(&text, &ctx).unwrap();
        prop_assert_eq!(item.line_text(), text.clone());
        let tokens = ItemLine::parse(&text).unwrap();
        prop_assert_eq!(tokens.to_string(), text);
        // Parsing is idempotent on the serialized form.
        let again = parse_line(&item.line_text(), &ctx).unwrap();
        prop_assert_eq!(again, item);
    }

    #[test]
    fn set_est_preserves_everything_else((text, stateful) in line()) {
        let ctx = ctx_for(stateful);
        let before = parse_line(&text, &ctx).unwrap();
        let mut line = before.line().clone();
        line.set_token("est", "1b");
        let after = parse_line(&line.to_string(), &ctx).unwrap();
        prop_assert_eq!(after.est, Some(Dur::blocks(1, 60)));
        let mut expected = without_src(before);
        expected.est = Some(Dur::blocks(1, 60));
        // If `est:` was unparsable before, the bad value moved out of `extra`.
        expected.extra.retain(|(k, _)| k != "est");
        expected.problems.retain(|p| !p.starts_with("`est:"));
        prop_assert_eq!(without_src(after), expected);
    }

    #[test]
    fn same_value_edit_is_a_no_op((text, stateful) in line()) {
        let before = ItemLine::parse(&text).unwrap();
        let mut line = before.clone();
        for key in ["due", "est", "loc", "max", "every"] {
            if let Some(v) = before.get(key).map(|v| v.to_string()) {
                line.set_token(key, &v);
            }
        }
        prop_assert_eq!(line.to_string(), text.clone());
        let _ = stateful;
    }

    #[test]
    fn set_state_and_tag_and_priority((text, stateful) in line()) {
        let ctx = ctx_for(stateful);
        let before = parse_line(&text, &ctx).unwrap();
        let mut line = before.line().clone();
        line.set_state(State::Done);
        line.add_tag("zz9");
        line.set_priority(Some(2));
        let after = parse_line(&line.to_string(), &ctx).unwrap();
        let mut expected = without_src(before);
        expected.state = State::Done;
        expected.tags.push("zz9".to_string());
        expected.priority = Some(2);
        expected.problems.retain(|p| p != "missing state");
        prop_assert_eq!(without_src(after), expected);
    }

    #[test]
    fn append_id_sets_id((text, stateful) in line()) {
        let ctx = ctx_for(stateful);
        let before = parse_line(&text, &ctx).unwrap();
        let mut line = before.line().clone();
        line.append_id(&Id::new("q9x2"));
        let after = parse_line(&line.to_string(), &ctx).unwrap();
        prop_assert_eq!(&after.id, &Id::new("q9x2"));
        let mut expected = without_src(before);
        expected.id = Id::new("q9x2");
        prop_assert_eq!(without_src(after), expected);
    }
}
