//! Property tests for the grammar (spec §17 M1): random item lines parse
//! and serialize byte-identically, and an edit changes only what it must.


#[path = "grammar_common/mod.rs"]
mod grammar_common;

use proptest::prelude::*;
use tm_core::grammar::{parse_line, EditError, ItemLine};
use tm_core::model::{Dur, Id, State};

/// **The generators moved to `grammar_common/` at stage 6 W-25 (step R2)** and
/// nothing about them changed: `tm/tests/kernel_item_grammar.rs` draws the same
/// lines and hands them to the kernel through the FFI, so a copy here would have
/// been AGENTS §5.3's own defect — two definitions of the lines these two files
/// are supposed to be comparing two readers on.
use grammar_common::{ctx_for, line, without_src, word};

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
                        // RAW, not normalised. `set_state_with_ci` removes the
                        // `ci:` key first, and a removal used to merge the bare
                        // word behind it back into the title segment carrying
                        // whatever whitespace run it happened to have: a fresh
                        // seed drew `("- 0 A A ci:0  a @A @a", false)` and the
                        // title `0 A A a` came back `0 A A  a` (README gap
                        // **1316**, owner **D46**). W-23 normalised this
                        // comparison; W-24 fixed the edit instead
                        // (`ItemLine::fix_absorbed_leads`) and took the
                        // normalisation back out, here and at the `set_parent`
                        // sibling below. The seed stays pinned in
                        // `grammar_proptest.proptest-regressions`, so the case
                        // runs every time rather than when a draw finds it.
                        prop_assert_eq!(&after.title, &before.title);
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
                // Also RAW since W-24. This is the older half of gap 1316's
                // class — its own pinned seed `("- [ ] a @A  a zz:0 @A", true)`
                // is a title `a a` that came back `a  a` — and it normalised
                // from the fork point on, which is why the ci site's identical
                // shape had nothing standing in its way.
                prop_assert_eq!(&after.title, &before.title);
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
