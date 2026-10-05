//! **One separator rule for the kernel and the host: the four hand-typed worlds** — stage 6
//! W-42 track G, the owner's D83 (README gap 32 closed, gap 4130 closed).
//!
//! README gap 4130 found the premise of D80 (b) false on a hand-edited line: a tab or a no-break
//! space typed after `^t4`'s state box or after its `ci` digit is a day the binary builds and
//! fork 4748911 plans, and the kernel — which read only a space as a separator — read no `ci`
//! there and `ciDisagrees` (parity P72) refused the day; P78 made `tm check` name it.  D83 made
//! the kernel read separators exactly as the host does: `Text.isSp` is Rust's
//! `char::is_whitespace`, the separators between the bullet and a box are read, and a box ends
//! only where fork `state_at` ends one — the end of the line or ASCII whitespace after its `]`.
//!
//! **The four worlds**, each `plan-basic` with `^t4`'s line edited by hand:
//!
//! | world | the line | the host reads | the kernel reads, since D83 |
//! |---|---|---|---|
//! | `tab-box` | `- [ ]<TAB>3 1b …` | a box, `ci` 3, `1b` | the same |
//! | `tab-ci` | `- [ ] 3<TAB>1b …` | a box, `ci` 3, `1b` | the same |
//! | `nbsp-ci` | `- [ ] 3<NBSP>1b …` | a box, `ci` 3, `1b` | the same |
//! | `nbsp-box` | `- [ ]<NBSP>3 1b …` | NO box (`state_at` reads the no-break space's first byte), title `[ ] 3 1b …`, no slots | the same |
//!
//! Gap 4130 said all four were refused by the kernel; MEASURED on the binary before this step, the
//! three in the first rows were, and `nbsp-box` was not — the kernel then read a box where the host
//! reads none, and happened to agree on the `ci` (both read none, so both inherit `@m2`'s).
//!
//! What each world is held to here:
//!
//! * [`no_world_is_refused_by_the_planner`] — `tm check`, which asks the kernel for the day R3's
//!   `tm plan` asks for (P78), names no `planner-refusal` on any of the four; on the first three it
//!   says `no problems`, and on `nbsp-box` it names only the host's own `missing state`, as it did
//!   before D83.
//! * [`the_kernel_plans_a_separator_world_as_its_spaced_twin`] — on the three worlds the host
//!   reads as the unedited tree, the host's own reader returns the item it returns there (state,
//!   `ci`, estimate, title, parent), and the kernel's planned day is the unedited tree's day, BY
//!   VALUE.  Both sides of the second comparison are the kernel, so it survives R3; what makes it a
//!   comparison with the fork is the first, which is the fork's own reader.
//! * [`the_nbsp_box_world_is_box_less_to_both_readers`] — the host's reader finds no box and no
//!   slots, and the kernel plans no row for `^t4`, a box-less item with nothing to do; and
//!   `the_kernel_plans_the_nbsp_box_day_as_the_fork_does` compares that day with fork 4748911's by
//!   `forkday::compare_day_with_fork`, the comparator the frozen class lines use, against the
//!   in-tree fork while it stands (R3 deleted it with its region; the claim then rests on the
//!   reader comparison, README gap 4168).
//! * P72 still refuses a real disagreement — `ci:+5`, which the host reads `5` (`u8::from_str`
//!   accepts a leading `+`) and the kernel does not (`Field.parseCi`), falling back to the
//!   positional `3`: `cli_check_planner.rs` holds that world, where P78 names it (README gap 4162).

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[allow(dead_code)]
#[path = "support/planreq.rs"]
mod planreq;

#[allow(dead_code)]
#[path = "support/forkday.rs"]
mod forkday;

#[allow(dead_code)]
#[path = "support/forkclass.rs"]
mod forkclass;

#[allow(dead_code)]
#[path = "support/plangen.rs"]
mod plangen;

#[allow(dead_code)]
#[path = "support/forkplan.rs"]
mod forkplan;

#[allow(dead_code)]
#[path = "support/forkgrid.rs"]
mod forkgrid;

mod cli_common;

use std::path::Path;

use chrono::DateTime;
use chrono_tz::Tz;

use tm_core::grammar::{parse_line, ParseCtx};
use tm_core::model::Item;
use tm_core::planwire::KernelDay;
use tm_core::store::RuntimeState;

use cli_common::Tm;
use forkclass::{Built, ClassWorld};

/// `^t4`'s line in `plan-basic`'s week file, unedited.
const LINE: &str = "- [ ] 3 1b Claude Code drafts tests     @m2 ^t4";

/// The week file `^t4` stands in.
const WEEK: &str = "week/2026-W37.md";

/// The four worlds: a name, and the edited line.
const WORLDS: [(&str, &str); 4] = [
    ("tab-box", "- [ ]\t3 1b Claude Code drafts tests     @m2 ^t4"),
    ("tab-ci", "- [ ] 3\t1b Claude Code drafts tests     @m2 ^t4"),
    ("nbsp-ci", "- [ ] 3\u{a0}1b Claude Code drafts tests     @m2 ^t4"),
    ("nbsp-box", "- [ ]\u{a0}3 1b Claude Code drafts tests     @m2 ^t4"),
];

fn tz() -> Tz {
    tm_core::config::Config::default().tz
}

/// `plan-basic`'s documents as `(path, text)`, with `^t4`'s line replaced by `line`.
fn texts(line: &str) -> Vec<(String, String)> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-core/tests/fixtures/plan-basic");
    let files = [
        "month/2026-09.md",
        WEEK,
        "backlog.md",
        "routines.md",
        "optional.md",
        "calendar/2026-W37.md",
        "day/2026-09-07.md",
        "inbox.md",
    ];
    files
        .iter()
        .map(|rel| {
            let text = std::fs::read_to_string(dir.join(rel)).unwrap_or_else(|e| panic!("{rel}: {e}"));
            let text = if *rel == WEEK {
                assert!(text.contains(LINE), "the fixture's ^t4 line");
                text.replacen(LINE, line, 1)
            } else {
                text
            };
            (rel.to_string(), text)
        })
        .collect()
}

/// The world planned at [`cli_common::NOW`] over `plan-basic` with `^t4`'s line `line`: no log,
/// the default state — the tree `tm check` asks about.
fn world(line: &str) -> Built {
    let now = DateTime::parse_from_rfc3339(cli_common::NOW).expect("NOW").with_timezone(&tz());
    Built::of(ClassWorld { docs: texts(line), log: String::new(), state: RuntimeState::default(), now, mult: None, ratio: None })
}

/// **The kernel's day on a world**, asked as R3's host asks it (`forkplan::request_with_loc`).
fn kernel_of(b: &Built) -> Result<KernelDay, String> {
    let (req, order) = forkplan::request_with_loc(b, None);
    planreq::kernel_day_of(&planreq::call(&req), &b.request_world(), &order).map(|(k, _)| k)
}

/// The host's reader on one line of the week file.
fn host_item(line: &str) -> Item {
    parse_line(line, &ParseCtx::new(WEEK, 60)).expect("the host reads the line as an item")
}

/// `plan-basic` with `^t4`'s line edited, as a binary-driven tree.
fn tree(line: &str) -> Tm {
    let tm = Tm::new();
    let path = tm.plan.join(WEEK);
    let text = std::fs::read_to_string(&path).expect("the week file");
    assert!(text.contains(LINE), "the fixture's ^t4 line");
    std::fs::write(&path, text.replacen(LINE, line, 1)).expect("the hand edit");
    tm
}

/// **No world is refused by the planner** (P78 names nothing).
#[test]
fn no_world_is_refused_by_the_planner() {
    for (name, line) in WORLDS {
        let tm = tree(line);
        let out = tm.run_at(cli_common::NOW, &["check"]);
        assert!(!out.stdout.contains("planner-refusal"), "{name}: {}{}", out.stdout, out.stderr);
        if name == "nbsp-box" {
            assert_eq!(out.code, 2, "{name}: {}{}", out.stdout, out.stderr);
            assert_eq!(
                out.stdout.trim_end(),
                "week/2026-W37.md:19: error[bad-value]: missing state\n1 error, 0 warnings",
                "{name}: the host's own reading, as before D83"
            );
        } else {
            assert_eq!((out.code, out.stdout.trim()), (0, "no problems"), "{name}: {}", out.stderr);
        }
    }
}

/// **The three worlds the host reads as the unedited tree are planned as it is**, by value.
#[test]
fn the_kernel_plans_a_separator_world_as_its_spaced_twin() {
    let base_item = host_item(LINE);
    let base = kernel_of(&world(LINE)).expect("the unedited tree's day");
    let base_day = serde_json::to_value(&base.day).expect("a day serialises");
    for (name, line) in WORLDS.iter().filter(|(n, _)| *n != "nbsp-box") {
        let item = host_item(line);
        assert_eq!(
            (&item.state, item.ci, item.ci_explicit, &item.est, &item.est_original, &item.title, &item.parent, &item.id),
            (
                &base_item.state,
                base_item.ci,
                base_item.ci_explicit,
                &base_item.est,
                &base_item.est_original,
                &base_item.title,
                &base_item.parent,
                &base_item.id
            ),
            "{name}: the host reads the line as it reads the unedited one"
        );
        let k = kernel_of(&world(line)).unwrap_or_else(|e| panic!("{name}: the kernel refused the day: {e}"));
        assert_eq!(serde_json::to_value(&k.day).expect("a day serialises"), base_day, "{name}: the kernel's day");
    }
}

/// **`nbsp-box`: no box to either reader.**  The host's reader finds no state box — `state_at`
/// reads the no-break space's first byte, which is no ASCII whitespace — so no positional slots
/// either: the title begins `[ ]`, there is no estimate, the id is kept.  The kernel reads the
/// line the same way since D83 (`Line.a_bracket_in_a_bare_line_is_title_text` is this line) and
/// plans no row for `^t4`, an item with nothing left to do.
#[test]
fn the_nbsp_box_world_is_box_less_to_both_readers() {
    let line = WORLDS[3].1;
    let item = host_item(line);
    assert_eq!(item.title, "[ ]\u{a0}3 1b Claude Code drafts tests", "the host's title");
    assert_eq!((&item.est, &item.est_original, item.id.as_str()), (&None, &None, "t4"), "no estimate slot, the id kept");
    let k = kernel_of(&world(line)).expect("the kernel plans the day");
    let kv = serde_json::to_value(&k.day).expect("a day serialises");
    let rows = kv["segments"].as_array().expect("rows");
    assert!(!rows.is_empty(), "a day with rows: {kv}");
    assert!(rows.iter().all(|r| r["item"] != "t4"), "the kernel plans no row for ^t4: {kv}");
    let base = kernel_of(&world(LINE)).expect("the unedited day");
    let bv = serde_json::to_value(&base.day).expect("a day serialises");
    assert!(
        bv["segments"].as_array().expect("rows").iter().any(|r| r["item"] == "t4"),
        "…where the unedited tree plans one: the world moves the day, as it moves the fork's"
    );
}


/// **`ci:+5`: a signed `ci:` value is read ONE way** (the W-42 repair, README gaps 4162 and 4330).
/// The host reads a `ci:` value with Rust's `u8::from_str` (`grammar.rs`), which takes one leading
/// `+`; the kernel read it with `readNat`, refused the sign, read NO `ci` on the line and inherited
/// `@m2`'s 4 — so `tm check` named `ciDisagrees t4 wire 5 plan 4`, a refusal of the day R3's `tm
/// plan` asks for, on a tree fork 4748911 plans (driven by W-42's verifier). Since the repair the
/// kernel reads the value as `u8::from_str` does (`Text.readRustNat`, `Line.parseCi`), so the two
/// readers agree: `tm check` says nothing, and the kernel plans the line as it plans the same line
/// spelled `ci:5`, by value.
#[test]
fn a_signed_ci_value_is_read_as_the_host_reads_it() {
    let signed = "- [ ] 1b Claude Code drafts tests @m2 ci:+5 ^t4";
    let plain = "- [ ] 1b Claude Code drafts tests @m2 ci:5 ^t4";
    let (h, p) = (host_item(signed), host_item(plain));
    assert_eq!((h.ci, h.ci_explicit), (5, true), "the host reads `ci:+5` as 5");
    assert_eq!((p.ci, p.ci_explicit), (5, true));
    let out = tree(signed).run_at(cli_common::NOW, &["check"]);
    assert_eq!((out.code, out.stdout.trim()), (0, "no problems"), "`tm check` on `ci:+5`: {}", out.stderr);
    let k = kernel_of(&world(signed)).unwrap_or_else(|e| panic!("the kernel refused the `ci:+5` day: {e}"));
    let q = kernel_of(&world(plain)).expect("the `ci:5` day");
    assert_eq!(
        serde_json::to_value(&k.day).expect("a day serialises"),
        serde_json::to_value(&q.day).expect("a day serialises"),
        "the kernel plans `ci:+5` as it plans `ci:5`"
    );
}

/// **No host writer leaves a box glued to the separator after it** — P80, which the kernel's unset
/// took at W-42 track G, held for every edit the host makes (the W-42 repair, README gap 4333).
/// Driven by W-42's reuse critic: `^a4` hand-edited to `- [?] est:15m<NBSP>Ask …` loads clean;
/// `tm event reply` resolves it through `recur::on_event_arrived`'s `ItemLine::remove_token`, which
/// carried the removed token's space away and wrote `- [ ]<NBSP>Ask …` at exit 0 — and the next
/// `tm check` refused `missing state`, the state lost to both readers. Since the repair every
/// removal that leaves the token after the box led by a separator that ends no box puts a space in
/// front of it, as `Field.endBox` does.
#[test]
fn an_event_that_rewrites_a_line_keeps_its_box_ended() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    let path = tm.plan.join("backlog.md");
    let text = std::fs::read_to_string(&path).expect("backlog.md");
    let a4 = text.lines().find(|l| l.ends_with("^a4")).expect("the example's ^a4").to_string();
    let edited = "- [?] est:15m\u{a0}Ask Prof. Lee about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4";
    std::fs::write(&path, text.replacen(&a4, edited, 1)).expect("the hand edit");
    let out = tm.run_at(cli_common::NOW, &["check"]);
    assert_eq!((out.code, out.stdout.trim()), (0, "no problems"), "the hand-edited tree: {}", out.stderr);
    let out = tm.run_at(cli_common::NOW, &["event", "reply"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let after = std::fs::read_to_string(&path).expect("backlog.md");
    let line = after.lines().find(|l| l.ends_with("^a4")).expect("^a4 after the event");
    assert!(line.starts_with("- [ ] \u{a0}Ask"), "the box is not ended: {line:?}");
    let out = tm.run_at(cli_common::NOW, &["check"]);
    assert_eq!((out.code, out.stdout.trim()), (0, "no problems"), "the tree the event wrote: {}", out.stderr);
}
