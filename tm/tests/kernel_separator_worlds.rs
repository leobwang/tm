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
//!   in-tree fork while it stands (R3 deletes it with its region; the claim then rests on the
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

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gap 4168)
/// **The `nbsp-box` day is fork 4748911's, BY VALUE** — and the unedited day too, as the
/// comparator's control: the kernel's day against the in-tree fork's, ranked by the shipped
/// binary's grants (D53), through `forkday::compare_day_with_fork`, the comparator the frozen class
/// lines use (every row in order, the date, the window, the budget, the diagnostics, the
/// priorities and the hash).  Until D83 the kernel read a box on this line where the fork reads
/// none.  R3 deletes this region; what stands after it is the reader comparison above.
#[test]
fn the_kernel_plans_the_nbsp_box_day_as_the_fork_does() {
    let mut tally = forkday::DayTally::default();
    for (name, line) in [("unedited", LINE), WORLDS[3]] {
        let b = world(line);
        let k = kernel_of(&b).unwrap_or_else(|e| panic!("{name}: the kernel refused the day: {e}"));
        let prios = forkplan::capacity_grants(&b, None).expect("the shipped grants");
        let ask = forkplan::ForkAsk {
            state: &b.world.state,
            now: b.world.now,
            d60: false,
            p64: false,
            prios: &prios,
            extend: None,
            log_line: None,
        };
        let fork = forkplan::ForkPlan::plan(&forkplan::InTree, &b, &ask).expect("the fork's day");
        let findings =
            forkday::compare_day_with_fork(name, &k, &forkplan::frozen_day_json(&fork.day), b.world.now, &mut tally);
        forkday::no_disagreement(&findings);
    }
    println!("{}", tally.line("the separator worlds", 0));
    assert_eq!(tally.days, 2, "both days compared");
}
// END THE FORK PLANNER
