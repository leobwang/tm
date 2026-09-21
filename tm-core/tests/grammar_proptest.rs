//! Property tests for the grammar (spec §17 M1): random item lines parse
//! and serialize byte-identically, and an edit changes only what it must.

use proptest::prelude::*;
use tm_core::grammar::{parse_line, EditError, ItemLine, ParseCtx};
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

/// A word that is not a token: ASCII, non-ASCII (multi-byte first char),
/// digit-leading (may look like a ci digit or a duration), or an uppercase
/// `Word:` (only `[a-z-]+:` ends the title).
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

/// Title words (1..4 of [`word`]).
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
        // Malformed structured tokens and lone sigils stay in the title.
        prop::sample::select(vec!["@", "#", "!", "^", "!5", "!!!", "^é", "^%"]).prop_map(|s| s.to_string()),
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

/// Title text with whitespace runs collapsed: removing a token can merge a
/// bare word back into the title segment with its original lead whitespace
/// (`a @A  a` → `a  a`), which is the same title.
fn norm(title: &str) -> String {
    title.split_whitespace().collect::<Vec<_>>().join(" ")
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
        let first = before.title.split_whitespace().next().unwrap_or("").to_string();
        match line.set_state(State::Done) {
            Ok(()) => {}
            Err(EditError::Ambiguous { word }) => {
                // Only a state-less line whose title starts with a ci digit
                // or a duration is refused; pinning the ci makes the digit
                // case representable, the duration case never is.
                prop_assert!(!stateful);
                prop_assert_eq!(&word, &first);
                let is_digit = first.len() == 1 && ("0".."6").contains(&first.as_str());
                let is_dur = Dur::parse_no_days(&first, 60).is_ok();
                prop_assert!(is_digit || is_dur, "{}", first);
                match line.set_state_with_ci(State::Done, before.ci) {
                    Ok(()) => {
                        prop_assert!(is_digit);
                        let after = parse_line(&line.to_string(), &ctx).unwrap();
                        // `norm`, not raw, because `set_state_with_ci` REMOVES
                        // the `ci:` key first and `norm`'s own doc names that
                        // exact class: a removed token merges a bare word back
                        // into the title with its original lead whitespace.
                        // The sibling assertion for `set_parent` below has
                        // always normalised; this one did not, and a fresh
                        // proptest seed found the shape in 1 run of 3 —
                        // `("- 0 A A ci:0  a @A @a", false)`, title
                        // `0 A A a` -> `0 A A  a`. The seed is pinned in
                        // `grammar_proptest.proptest-regressions`, so the case
                        // runs every time rather than when a draw finds it
                        // (README gap **1316**). The words, their order and
                        // their count are still compared exactly.
                        prop_assert_eq!(norm(&after.title), norm(&before.title));
                        prop_assert_eq!(
                            after.title.split_whitespace().count(),
                            before.title.split_whitespace().count()
                        );
                        prop_assert_eq!(after.ci, before.ci);
                        prop_assert!(after.ci_explicit);
                        prop_assert_eq!(after.state, State::Done);
                    }
                    Err(e) => {
                        prop_assert!(is_dur, "{:?}", e);
                        prop_assert_eq!(line.to_string(), text.clone(), "a refused edit changes nothing");
                    }
                }
                return Ok(());
            }
            Err(e) => prop_assert!(false, "unexpected {:?}", e),
        }
        line.add_tag("zz9");
        line.set_priority(Some(2)).unwrap();
        let after = parse_line(&line.to_string(), &ctx).unwrap();
        let mut expected = without_src(before);
        expected.state = State::Done;
        expected.tags.push("zz9".to_string());
        expected.priority = Some(2);
        expected.problems.retain(|p| p != "missing state");
        prop_assert_eq!(without_src(after), expected);
    }

    #[test]
    fn set_title_survives_reparse((text, stateful) in line(), words in prop::collection::vec(word(), 1..4)) {
        let ctx = ctx_for(stateful);
        let before = parse_line(&text, &ctx).unwrap();
        let mut line = before.line().clone();
        let title = words.join(" ");
        match line.set_title(&title) {
            Ok(()) => {
                let after = parse_line(&line.to_string(), &ctx).unwrap();
                prop_assert_eq!(&after.title, &title);
                prop_assert_eq!(after.ci, before.ci);
                prop_assert_eq!(after.est_original, before.est_original);
                prop_assert_eq!(after.state, before.state);
                prop_assert_eq!(&after.id, &before.id);
                prop_assert_eq!(&after.flags, &before.flags);
                prop_assert_eq!(&after.tags, &before.tags);
                prop_assert_eq!(&after.parent, &before.parent);
            }
            Err(EditError::Ambiguous { word }) => {
                prop_assert!(words.contains(&word), "{} not in {:?}", word, words);
                prop_assert_eq!(line.to_string(), text.clone(), "a refused edit changes nothing");
            }
            Err(EditError::FlagNeedsBoundary { flag }) => {
                prop_assert!(before.flags.contains(&flag));
                prop_assert!(!before.has_id());
                prop_assert_eq!(line.to_string(), text.clone(), "a refused edit changes nothing");
            }
            Err(e) => prop_assert!(false, "unexpected {:?}", e),
        }
    }

    #[test]
    fn add_flag_and_remove_parent_keep_flags((text, stateful) in line()) {
        let ctx = ctx_for(stateful);
        let before = parse_line(&text, &ctx).unwrap();
        let mut line = before.line().clone();
        match line.add_flag("hot") {
            Ok(()) => {
                let after = parse_line(&line.to_string(), &ctx).unwrap();
                prop_assert!(after.is_hot());
                prop_assert_eq!(&after.title, &before.title);
                let mut expected_flags = before.flags.clone();
                if !expected_flags.iter().any(|f| f == "hot") {
                    expected_flags.push("hot".to_string());
                }
                prop_assert_eq!(&after.flags, &expected_flags);
            }
            Err(EditError::FlagNeedsBoundary { .. }) => {
                prop_assert!(!before.has_id());
                prop_assert_eq!(line.to_string(), text.clone());
            }
            Err(e) => prop_assert!(false, "unexpected {:?}", e),
        }
        let mut line = before.line().clone();
        match line.set_parent(None) {
            Ok(()) => {
                let after = parse_line(&line.to_string(), &ctx).unwrap();
                prop_assert_eq!(after.parent, None);
                prop_assert_eq!(norm(&after.title), norm(&before.title));
                prop_assert_eq!(&after.flags, &before.flags);
                prop_assert_eq!(&after.tags, &before.tags);
            }
            Err(EditError::FlagNeedsBoundary { .. }) => {
                prop_assert!(!before.has_id());
                prop_assert_eq!(line.to_string(), text.clone());
            }
            Err(e) => prop_assert!(false, "unexpected {:?}", e),
        }
    }

    #[test]
    fn arbitrary_lines_never_panic(text in "- [^\\r\\n]{0,40}") {
        let ctx = ctx_for(true);
        if let Ok(item) = parse_line(&text, &ctx) {
            prop_assert_eq!(item.line_text(), text.clone());
            let again = parse_line(&item.line_text(), &ctx).unwrap();
            prop_assert_eq!(again, item);
        }
        let _ = parse_line(&text, &ctx_for(false));
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
