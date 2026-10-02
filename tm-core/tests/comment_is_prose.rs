//! Owner **D47** (README gap 1317): a column-zero item line inside an
//! `<!-- … -->` comment is PROSE, and the host now agrees with the kernel
//! about it. `Plan.lean`'s reading is CommonMark's HTML block type 2 and
//! nothing wider — a comment opens on a line whose first non-SPACE characters
//! are `<!--` and closes on the first line, the opening line included, that
//! contains `-->` anywhere — and `grammar::comment_after` is that automaton on
//! this side.
//!
//! Both directions (§5.8): the same lines commented produce nothing and
//! uncommented produce the two errors, so this file cannot pass by the host
//! having stopped reading items at all.

use tm_core::check::{self, CheckProblem};
use tm_core::grammar::{self, LineContent};
use tm_core::store::{MemStore, Store};
use tm_core::tree::Tree;

const WEEK: &str = "week/2026-W37.md";

fn problems(text: &str) -> Vec<CheckProblem> {
    let store = MemStore::new().with_file(WEEK, text);
    let plan = store.read_tree().expect("tree parses");
    let tree = Tree::build(&plan.files, &plan.config);
    check::check(&plan.files, &tree, &plan.config)
}

fn errors(text: &str) -> Vec<String> {
    problems(text)
        .iter()
        .filter(|p| p.is_error())
        .map(|p| p.to_string())
        .collect()
}

/// A duplicate id and a dangling parent, written twice: once inside a comment
/// and once outside it. `tm check` used to report the commented copies.
#[test]
fn a_commented_item_is_not_checked_and_an_uncommented_one_is() {
    let live = "# M\n- [ ] 3 1b One ^m1\n- [ ] 3 1b Two ^m1\n- [ ] 3 1b Three @nope ^m3\n";
    let errs = errors(live);
    assert_eq!(errs.len(), 3, "{errs:#?}");
    assert!(errs.iter().filter(|e| e.contains("[dup-id]")).count() == 2, "{errs:#?}");
    assert!(errs.iter().any(|e| e.contains("[dangling-parent]")), "{errs:#?}");

    let commented = "# M\n- [ ] 3 1b One ^m1\n<!-- an example, and a line commented out\n- [ ] 3 1b Two ^m1\n- [ ] 3 1b Three @nope ^m3\n-->\n";
    assert_eq!(errors(commented), Vec::<String>::new());

    // The CLOSING line is inside the comment too — the state consulted is the
    // one before the line, so an item line carrying the `-->` is prose and
    // closes the comment behind it. `commentAfter`'s own automaton, and the
    // case that separates it from "skip while the comment is still open".
    let closer_is_an_item = "# M\n- [ ] 3 1b One ^m1\n<!--\n- [ ] 3 1b Two ^m1 -->\n- [ ] 3 1b Three @nope ^m3\n";
    let errs = errors(closer_is_an_item);
    assert_eq!(errs.len(), 1, "only the line after the closer is live: {errs:#?}");
    assert!(errs[0].contains("[dangling-parent]"), "{errs:#?}");
}

/// The kernel's comment opener drops `isIndent`, the space alone (its separator
/// `isSp` has been `char::is_whitespace` since the owner's D83, W-42, but an
/// opener's indent is not a separator), so a TAB-indented `<!--` opens nothing
/// and the item behind it is still live. The host used to trim, which is how
/// `tm triage` and the TUI inbox could disagree with the parser.
#[test]
fn only_spaces_indent_an_opener() {
    let spaces = "# M\n   <!--\n- [ ] 3 1b Two ^m1\n-->\n- [ ] 3 1b One ^m1\n";
    assert_eq!(errors(spaces), Vec::<String>::new());
    let tab = "# M\n\t<!--\n- [ ] 3 1b Two ^m1\n-->\n- [ ] 3 1b One ^m1\n";
    let errs = errors(tab);
    assert_eq!(errs.len(), 2, "a tab does not indent an opener: {errs:#?}");
    assert!(errs.iter().all(|e| e.contains("[dup-id]")), "{errs:#?}");
}

/// Serialization stays byte-faithful: a commented item is `Verbatim`, so the
/// bytes that come back are the bytes that went in.
#[test]
fn a_commented_item_round_trips_verbatim() {
    let text = "<!-- keep me\n- [ ]   3 1b  Two   ^m1\t\n-->\n- [ ] 3 1b One ^m1\n";
    let cfg = tm_core::config::Config::default();
    let file = grammar::parse_file(WEEK, text, &cfg);
    assert_eq!(grammar::serialize_file(&file), text);
    let kinds: Vec<bool> = file
        .lines
        .iter()
        .map(|l| matches!(l.content, LineContent::Item(_)))
        .collect();
    assert_eq!(kinds, vec![false, false, false, true]);
}

/// A heading inside a comment is not a section either — `Plan.lean`'s
/// `liveHeading` says so by name ("a `# Pinned` in a guidance comment is not a
/// section"), and the host reads sections out of the same loop.
#[test]
fn a_heading_inside_a_comment_is_not_a_section() {
    let text = "# Real\n<!--\n# Commented\n-->\n- [ ] 3 1b One ^m1\n";
    let cfg = tm_core::config::Config::default();
    let file = grammar::parse_file(WEEK, text, &cfg);
    let item = file
        .lines
        .iter()
        .find_map(|l| match &l.content {
            LineContent::Item(i) => Some(i),
            _ => None,
        })
        .expect("one item");
    assert_eq!(item.src.section.as_deref(), Some("Real"));
}

/// An opener that closes on its own line leaves nothing open, which is why a
/// `<!-- tm:plan start … -->` marker is still a generated marker and the block
/// it opens is still a generated range.
#[test]
fn a_self_closing_opener_is_still_a_generated_marker() {
    let text = "<!-- tm:plan start 10:42 -->\n- [ ] 3 1b Two ^m1\n<!-- tm:plan end -->\n- [ ] 3 1b One ^m1\n";
    let cfg = tm_core::config::Config::default();
    let file = grammar::parse_file(WEEK, text, &cfg);
    assert_eq!(file.generated.len(), 1);
    assert_eq!(file.generated[0].name, "plan");
    assert_eq!(file.generated[0].end_line, Some(3));
    assert!(file.problems.is_empty(), "{:#?}", file.problems);
}

/// The kernel's loader refuses a file whose comment never closes, by name
/// (`LErr.unterminatedComment`, naming the opener). The host reports it the
/// way it reports the other two unterminated things.
#[test]
fn an_unterminated_comment_is_reported_at_its_opener() {
    let cfg = tm_core::config::Config::default();
    let text = "# M\n- [ ] 3 1b One ^m1\n<!-- and then nothing\n- [ ] 3 1b Two ^m1\n";
    let file = grammar::parse_file(WEEK, text, &cfg);
    let msgs: Vec<(usize, &str)> = file.problems.iter().map(|p| (p.line, p.message.as_str())).collect();
    assert_eq!(msgs, vec![(3, "unterminated comment")]);
    // A terminated one reports nothing.
    let closed = "# M\n- [ ] 3 1b One ^m1\n<!-- and then this\n-->\n";
    assert!(grammar::parse_file(WEEK, closed, &cfg).problems.is_empty());
}

/// The one automaton, asserted directly: the three functions the parser,
/// `tm triage` and the TUI inbox share.
#[test]
fn the_automaton_is_plan_leans() {
    assert!(grammar::opens_comment("<!-- x"));
    assert!(grammar::opens_comment("   <!-- x"));
    assert!(!grammar::opens_comment("\t<!-- x"));
    assert!(!grammar::opens_comment("text <!-- x"));
    assert!(!grammar::opens_comment("- [ ] 3 x <!-- not an opener ^m1"));
    assert!(grammar::closes_comment("anything --> here"));
    assert!(grammar::closes_comment("<!-- both -->"));
    assert!(!grammar::closes_comment("- >"));
    // `(open || opens) && !closes`, the whole of it.
    assert!(grammar::comment_after(false, "<!-- open"));
    assert!(!grammar::comment_after(false, "<!-- open and shut -->"));
    assert!(grammar::comment_after(true, "still inside"));
    assert!(!grammar::comment_after(true, "the closer --> and after"));
    assert!(!grammar::comment_after(false, "ordinary prose"));
}
