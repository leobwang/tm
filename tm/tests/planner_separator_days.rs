//! **The separator worlds' days, frozen out of the tree** — stage 6 W-43 track C (README gap 4168).
//!
//! `kernel_separator_worlds.rs` (W-42 track G, the owner's D83) holds four hand-typed worlds —
//! `plan-basic` with `^t4`'s line edited to carry a tab or a no-break space after its state box or
//! after its `ci` digit — to one separator rule for the host and the kernel. Its only comparison
//! with fork 4748911's PLANNER, `the_kernel_plans_the_nbsp_box_day_as_the_fork_does`, asks the
//! in-tree fork, in a `BEGIN THE FORK PLANNER` region R3 deletes: after R3 the `nbsp-box` claim (a
//! box the host reads as no box, so `^t4` is planned no row) would rest on the reader comparison
//! alone (README gap 4168).
//!
//! # What is frozen
//!
//! `tests/fixtures/fork-4748911-planner-separators.jsonl`, one line per [`SEPARATORS`] entry — the
//! unedited tree, the comparator's control, and every edited world, the three the host reads as
//! the unedited tree and `nbsp-box` — each carrying its WORLD by value (`plan-basic`'s documents
//! with the edit, no log, planned at `cli_common::NOW`, `.tm/state.json` as the binary rebuilds it
//! there — its `date` the day's, which the separator suite's own construction leaves out and the
//! binary writes on every load: a frozen world is one the shipped binary holds, D64(b)), the edited
//! line, and **fork 4748911's day on it by value**
//! (`shipped`), asked of a freshly built `tm-oracle plan` over the grants the shipped binary ranks
//! the fork's candidates by (`forkplan::capacity_grants`, D53) — and, asked at the bless, no
//! registered departure: the comparand on each world IS the shipped day (its `shipped` would be
//! null), so the kernel is held to fork 4748911's own day with nothing applied.
//!
//! # What each line is held to, outside every region (outlives R3)
//!
//! * [`the_kernel_plans_every_frozen_separator_day_as_the_fork_did`] — the kernel's day, asked as
//!   R3's host asks it, against the frozen fork day by `forkday::compare_day_with_fork` (the frozen
//!   class lines' comparator: every row in order, the date, the window, the budget, the
//!   diagnostics, the priorities, the hash), on every world.
//! * [`the_fork_reads_the_edited_worlds_as_the_host_does`] — the FORK's own days say what the
//!   host's reader says: the three spaced twins plan the unedited tree's day, and `nbsp-box` plans
//!   another, with no row for `^t4` where the unedited day has one.
//! * [`every_frozen_separator_world_is_the_edited_fixture`] — each world is `plan-basic` with its
//!   line edited, rebuilt now and compared by value, and one the shipped binary holds.
//!
//! The bless and the oracle arm ask fork 4748911 out of the tree; the in-tree fork is asked only in
//! the one region below, which R3 deletes, and which holds the frozen days to it while it stands.

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

/// The committed history a bless holds its lines against (README gap 4151).
#[allow(dead_code)]
#[path = "support/frozenhist.rs"]
mod frozenhist;

#[allow(dead_code)]
mod cli_common;

use std::path::{Path, PathBuf};

use chrono::DateTime;
use chrono_tz::Tz;
use serde_json::{json, Value};

use tm_core::planwire::KernelDay;
use tm_core::store::RuntimeState;

use forkclass::{Built, ClassWorld};

/// `^t4`'s line in `plan-basic`'s week file, unedited.
const LINE: &str = "- [ ] 3 1b Claude Code drafts tests     @m2 ^t4";

/// The week file `^t4` stands in.
const WEEK: &str = "week/2026-W37.md";

/// **The worlds**: a name and `^t4`'s line — `kernel_separator_worlds.rs`' four, and the unedited
/// tree as the comparator's control.
const SEPARATORS: [(&str, &str); 5] = [
    ("unedited", LINE),
    ("tab-box", "- [ ]\t3 1b Claude Code drafts tests     @m2 ^t4"),
    ("tab-ci", "- [ ] 3\t1b Claude Code drafts tests     @m2 ^t4"),
    ("nbsp-ci", "- [ ] 3\u{a0}1b Claude Code drafts tests     @m2 ^t4"),
    ("nbsp-box", "- [ ]\u{a0}3 1b Claude Code drafts tests     @m2 ^t4"),
];

/// The frozen file's name, under `tm/tests/fixtures`.
const FROZEN_SEPARATORS: &str = "fork-4748911-planner-separators.jsonl";

fn tz() -> Tz {
    tm_core::config::Config::default().tz
}

fn frozen_path() -> PathBuf {
    frozenhist::fixtures_dir().join(FROZEN_SEPARATORS)
}

/// `plan-basic`'s documents as `(path, text)`, with `^t4`'s line replaced by `line` —
/// `kernel_separator_worlds.rs`' construction.
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

/// The world planned at `cli_common::NOW` over `plan-basic` with `^t4`'s line `line`: no log, and
/// `.tm/state.json` as the binary rebuilds it from that log — the default but for its `date`, which
/// every load writes (`forkclass::binary_holds`' clause 5 names it).
fn world_of(line: &str) -> ClassWorld {
    let w = suite_world_of(line);
    ClassWorld { state: RuntimeState { date: Some(w.now.date_naive()), ..RuntimeState::default() }, ..w }
}

/// **The separator suite's own construction** (`kernel_separator_worlds.rs`' `world`): the same, with
/// `.tm/state.json`'s default — the tree `tm check` is handed before the binary rolls the state.
fn suite_world_of(line: &str) -> ClassWorld {
    let now = DateTime::parse_from_rfc3339(cli_common::NOW).expect("NOW").with_timezone(&tz());
    ClassWorld { docs: texts(line), log: String::new(), state: RuntimeState::default(), now, mult: None, ratio: None }
}

/// The frozen lines in file order; a name carried twice FAILS.
fn lines_of(text: &str) -> Vec<Value> {
    let mut names = std::collections::BTreeSet::new();
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Value = serde_json::from_str(l).expect("a frozen separator line is JSON");
            let name = v["name"].as_str().expect("a frozen separator line names its world").to_string();
            assert!(names.insert(name.clone()), "two frozen separator lines for `{name}`");
            v
        })
        .collect()
}

fn frozen() -> Vec<Value> {
    let path = frozen_path();
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e} — bless it (`the_frozen_separator_days_are_blessed`)", path.display()));
    lines_of(&text)
}

/// A frozen line's world, rebuilt into what both planners read.
fn built(line: &Value) -> Built {
    Built::of(ClassWorld::of_json(&line["world"], tz()).expect("a stored world"))
}

/// **The kernel's day on a world, asked as R3's host asks it** (`forkplan::request_with_loc`, the
/// separator suite's own reading).
fn kernel_of(b: &Built) -> Result<KernelDay, String> {
    let (req, order) = forkplan::request_with_loc(b, None);
    planreq::kernel_day_of(&planreq::call(&req), &b.request_world(), &order).map(|(k, _)| k)
}

/// **The fork's day on a world** — `fp` planning over the grants the shipped binary ranks the
/// fork's candidates by (D53, `forkplan::capacity_grants`): fork 4748911's own drawing
/// (`forkplan::Planned::fork_day`), as a frozen line spells a day (`{hash, day}`). These worlds hold
/// no log, so no replayed pause is drawn for P56 to cut; a world that held one would be held to its
/// whole pause here and to P56's cut by the kernel, and would fail by name.
fn shipped_day(b: &Built, fp: &dyn forkplan::ForkPlan) -> Result<Value, String> {
    let prios = forkplan::capacity_grants(b, None)?;
    let ask = forkplan::ForkAsk { state: &b.world.state, now: b.world.now, d60: false, p64: false, prios: &prios, extend: None, log_line: None };
    Ok(forkplan::frozen_day_json(&fp.plan(b, &ask)?.fork_day))
}

/// One frozen line: the world's name, its edited line, the world, and fork 4748911's day on it.
fn line_of(name: &str, line: &str, world: &ClassWorld, shipped: &Value) -> Value {
    json!({"name": name, "line": line, "world": world.to_json(), "shipped": shipped})
}

/// **The kernel plans every frozen separator day as fork 4748911 planned it**, by value — the
/// comparison that outlives R3 (README gap 4168): the kernel's day, asked as R3's host asks it,
/// against the frozen fork day by the frozen class lines' comparator — on the frozen world, and on
/// the separator suite's own construction of it (no `.tm/state.json` date), so the frozen day holds
/// the claim `kernel_separator_worlds.rs` makes of its own world too.
#[test]
fn the_kernel_plans_every_frozen_separator_day_as_the_fork_did() {
    let lines = frozen();
    let names: Vec<&str> = lines.iter().map(|l| l["name"].as_str().unwrap_or_default()).collect();
    assert_eq!(names, SEPARATORS.iter().map(|(n, _)| *n).collect::<Vec<_>>(), "the frozen separator lines are SEPARATORS, in order");
    let mut t = forkday::DayTally::default();
    let mut findings = Vec::new();
    for l in &lines {
        let name = l["name"].as_str().unwrap_or("?");
        let b = built(l);
        let suite = Built::of(suite_world_of(l["line"].as_str().unwrap_or_default()));
        for (who, b) in [(name.to_string(), &b), (format!("{name} (the suite's construction)"), &suite)] {
            match kernel_of(b) {
                Ok(k) => findings.extend(forkday::compare_day_with_fork(&who, &k, &l["shipped"], b.world.now, &mut t)),
                Err(e) => findings.push(format!("{who}: the kernel refused the day: {e}")),
            }
        }
    }
    println!("{}", t.line("the frozen separator days", findings.len()));
    forkday::no_disagreement(&findings);
    assert_eq!(t.days, 2 * SEPARATORS.len(), "every frozen separator day was compared, both constructions: {t:?}");
    assert_eq!(t.hashes_equal, t.days, "every separator day hashes as the fork's: {t:?}");
}

/// **The FORK's own days say what the host's reader says** — fork 4748911 planned the three
/// spaced twins as the unedited tree, by value (it reads a tab or a no-break space between the box
/// and `ci`, or between `ci` and the estimate, as a separator, as the host does), and `nbsp-box`
/// otherwise: no row for `^t4`, where the unedited tree plans one (a no-break space after `]` ends
/// no box for fork `state_at`, so the line is box-less and has nothing to do).
#[test]
fn the_fork_reads_the_edited_worlds_as_the_host_does() {
    let lines = frozen();
    let day = |name: &str| lines.iter().find(|l| l["name"] == name).map(|l| l["shipped"].clone()).unwrap_or_else(|| panic!("no `{name}` line"));
    let base = day("unedited");
    for twin in ["tab-box", "tab-ci", "nbsp-ci"] {
        assert_eq!(day(twin), base, "{twin}: fork 4748911 planned it otherwise than the unedited tree ({:?})", forkplan::first_difference("day", &base, &day(twin)));
    }
    let t4 = |v: &Value| v["day"]["segments"].as_array().map(Vec::as_slice).unwrap_or_default().iter().filter(|r| r["item"] == "t4").count();
    assert!(t4(&base) > 0, "the unedited tree's fork day plans no row for ^t4 — the control is vacuous");
    assert_eq!(t4(&day("nbsp-box")), 0, "fork 4748911 planned a row for the box-less ^t4");
    assert_ne!(day("nbsp-box"), base, "the nbsp-box world moved nothing of the fork's day");
}

/// **Every frozen world is `plan-basic` with its line edited** — rebuilt now from the fixture and
/// compared by value, so a change to the fixture or to [`SEPARATORS`] fails by name instead of
/// leaving a frozen day that no longer describes the world the suite builds — and **one the shipped
/// binary holds** (`forkclass::binary_holds`: at rest, the cache what it rebuilds from the log).
#[test]
fn every_frozen_separator_world_is_the_edited_fixture() {
    let lines = frozen();
    let mut bad = Vec::new();
    for ((name, line), l) in SEPARATORS.iter().zip(&lines) {
        if l["name"] != *name || l["line"] != *line {
            bad.push(format!("{name}: the frozen line names `{}` with {:?}", l["name"], l["line"]));
            continue;
        }
        let w = world_of(line);
        if w.to_json() != l["world"] {
            bad.push(format!("{name}: the suite builds another world now ({})", forkplan::first_difference("world", &l["world"], &w.to_json()).unwrap_or_default()));
        }
        let week = w.docs.iter().find(|(p, _)| p == WEEK).map(|(_, t)| t.as_str()).unwrap_or_default();
        if !week.lines().any(|x| x == *line) {
            bad.push(format!("{name}: the world's week file does not carry its line"));
        }
        if let Err(e) = forkclass::binary_holds(&built(l)) {
            bad.push(format!("{name}: not a world the binary holds: {}", e.join("; ")));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n  "));
}

/// **The comparison bites a bent day** (AGENTS §5.8): the `nbsp-box` day given a row for `^t4`, and
/// the unedited day with one row a minute longer, are each refused by name — and the unbent lines
/// compare clean.
#[test]
fn the_separator_comparison_bites_a_bent_day() {
    let lines = frozen();
    let find = |name: &str| lines.iter().find(|l| l["name"] == name).cloned().expect("a frozen line");
    let compare = |l: &Value| -> Vec<String> {
        let b = built(l);
        let k = kernel_of(&b).expect("the kernel plans the day");
        let mut t = forkday::DayTally::default();
        forkday::compare_day_with_fork(l["name"].as_str().unwrap_or("?"), &k, &l["shipped"], b.world.now, &mut t)
    };
    for l in &lines {
        assert!(compare(l).is_empty(), "{}: the unbent line differs", l["name"]);
    }
    let mut boxed = find("nbsp-box");
    let rows = boxed["shipped"]["day"]["segments"].as_array_mut().expect("rows");
    let r = rows.iter_mut().find(|r| r["kind"] == "block" && !r["item"].is_null()).expect("a block row");
    r["item"] = json!("t4");
    assert!(compare(&boxed).iter().any(|f| f.starts_with("nbsp-box") && f.contains("rows differ")), "a ^t4 row in the nbsp-box day passed: {:?}", compare(&boxed));
    let mut longer = find("unedited");
    let rows = longer["shipped"]["day"]["segments"].as_array_mut().expect("rows");
    let r = rows.iter_mut().find(|r| r["kind"] == "block").expect("a block row");
    let end = forkplan::at(&r["end"]).expect("an end") + chrono::Duration::minutes(1);
    r["end"] = json!(end.to_rfc3339());
    assert!(compare(&longer).iter().any(|f| f.starts_with("unedited") && f.contains("rows differ")), "a row a minute longer passed: {:?}", compare(&longer));
}

/// **A frozen separator name carried twice is refused** (AGENTS §5.8).
#[test]
#[should_panic(expected = "two frozen separator lines for")]
fn a_frozen_separator_name_carried_twice_is_refused() {
    let one = serde_json::to_string(&frozen()[0]).expect("a line");
    lines_of(&format!("{one}\n{one}\n"));
}

/// The oracle at `TM_ORACLE`, when set (D23's shape).
fn the_oracle() -> Option<forkplan::Oracle> {
    forkplan::oracle_path().map(forkplan::Oracle::new)
}

/// **The frozen separator days are fork 4748911's answer today, out of the tree** (`TM_ORACLE`;
/// outlives R3): each line's `shipped` day asked again of `tm-oracle plan` over the shipped binary's
/// grants, by value — and the comparand on each world departs from it by no registered number
/// (`forkplan::comparand_answers`' `shipped` is null, its `day` this day).
#[test]
#[ignore]
fn the_frozen_separator_days_are_the_forks_oracle_answer_today() {
    let Some(oracle) = the_oracle() else {
        eprintln!("inert: set TM_ORACLE to an oracle built by kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh");
        return;
    };
    for l in frozen() {
        let name = l["name"].as_str().unwrap_or("?");
        let b = built(&l);
        let day = shipped_day(&b, &oracle).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(day, l["shipped"], "{name}: the fork oracle does not plan the frozen day ({:?})", forkplan::first_difference("day", &l["shipped"], &day));
        no_departure(name, &b, &day, &oracle);
        // …and the separator suite's own construction of the world, the same day.
        let suite = Built::of(suite_world_of(l["line"].as_str().unwrap_or_default()));
        let theirs = shipped_day(&suite, &oracle).unwrap_or_else(|e| panic!("{name} (the suite's construction): {e}"));
        assert_eq!(theirs, l["shipped"], "{name}: the oracle plans the suite's construction otherwise ({:?})", forkplan::first_difference("day", &l["shipped"], &theirs));
    }
    println!("tm-oracle plan asked {} time(s)", *oracle.asked.lock().expect("census"));
}

/// **No registered number departs on the world**: the comparand (`forkplan::comparand_answers`,
/// over the same grants) is the shipped day itself — its `shipped` null and its `day` this day — so
/// holding the kernel to the shipped day applies nothing it should have.
fn no_departure(name: &str, b: &Built, day: &Value, fp: &dyn forkplan::ForkPlan) {
    let prios = forkplan::capacity_grants(b, None).unwrap_or_else(|e| panic!("{name}: {e}"));
    let a = forkplan::comparand_answers(b, &prios, fp).unwrap_or_else(|e| panic!("{name}: the comparand: {e}"));
    if let Some(why) = departure(name, &a, day) {
        panic!("{why}");
    }
}

/// **[`no_departure`]'s check, without the backend that computes the answers** (W-45 track C, README
/// gap 4682): `None` where the comparand's answers `a` depart from the shipped day `day` by nothing —
/// its `shipped` null and its `day` this day — else why, by name. Split out so its bite is witnessed
/// on frozen comparand answers with no fork ([`a_departing_comparand_is_refused`]).
fn departure(name: &str, a: &Value, day: &Value) -> Option<String> {
    (!(a["shipped"].is_null() && a["day"] == *day))
        .then(|| format!("{name}: the comparand departs from the shipped day ({:?})", forkplan::first_difference("day", day, &a["day"])))
}

/// **[`departure`] bites, and does not over-bite** (AGENTS §5.8), on frozen comparand answers and
/// with no fork (W-45 track C, README gap 4682): a frozen class line whose comparand departs from the
/// shipped day (D60's order, parity P51 — its `shipped` held beside a `day` that is not it) is
/// refused, and a frozen line whose comparand departs on nothing passes. Until W-45 the bite was
/// witnessed only in the fork region, the in-tree fork computing the comparand
/// (the region's no_departure_refuses_a_world_a_registered_number_departs_on), and R3 would have left the check
/// the oracle arm and the bless still call with no witness that it bites.
#[test]
fn a_departing_comparand_is_refused() {
    let lines = forkclass::frozen_lines();
    let p51 = lines.iter().find(|l| l["d60"]["p51"] == true && !l["shipped"].is_null()).expect("a frozen class line D60's order departs on");
    assert!(departure("a P51 line", p51, &p51["shipped"]).is_some(), "a comparand that departs from the shipped day passed");
    let plain = lines.iter().find(|l| l["shipped"].is_null()).expect("a frozen class line no number departs on");
    assert_eq!(departure("a plain line", plain, &plain["day"]), None, "a comparand that departs on nothing was refused");
}

/// **Freeze the separator days** — inert without `TM_SEPARATORS_BLESS`; it asks `TM_ORACLE`, fork
/// 4748911 out of the tree, so it outlives R3. Every [`SEPARATORS`] world is built
/// ([`world_of`]) and written with fork 4748911's day on it ([`shipped_day`]), after asserting no
/// registered number departs on it ([`no_departure`]). **What a line is held against is the file's
/// COMMITTED history** (W-42 track C, README gap 4151; `frozenhist::held`) — never the working copy,
/// so deleting the file is not a fresh freeze — and a committed line may not move at all: its world
/// moving is a re-draw (D64(b)'s, decided elsewhere), and its day moving over the same world is the
/// SHIPPED fork's day moving, which no comparand number moves (D64, clause 2) and which a frozen
/// line of this file carries no departure to license (D85's (c) moves departures only). A line HEAD
/// holds that no world builds is refused. `TM_SEPARATORS_BLESS_OUT` writes elsewhere, for a dry run.
#[test]
#[ignore]
fn the_frozen_separator_days_are_blessed() {
    if std::env::var_os("TM_SEPARATORS_BLESS").is_none() {
        eprintln!("inert: set TM_SEPARATORS_BLESS=1 (with TM_ORACLE) to write {FROZEN_SEPARATORS}");
        return;
    }
    let oracle = the_oracle().expect("TM_SEPARATORS_BLESS asks fork 4748911: set TM_ORACLE");
    let path = frozen_path();
    let held = frozenhist::held(&path, frozenhist::key_of("name")).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", held.census(FROZEN_SEPARATORS));
    let (mut out, mut refused, mut added) = (String::new(), Vec::new(), 0usize);
    for (name, line) in SEPARATORS {
        let w = world_of(line);
        let b = Built::of(w.clone());
        let day = shipped_day(&b, &oracle).unwrap_or_else(|e| panic!("{name}: {e}"));
        no_departure(name, &b, &day, &oracle);
        let l = line_of(name, line, &w, &day);
        match held.get(name) {
            None => added += 1,
            Some(old) if old["world"] != l["world"] || old["line"] != l["line"] => {
                refused.push(format!("{name}: the suite builds another world now — a re-draw, which D64(b) must decide"))
            }
            Some(old) if old["shipped"] != l["shipped"] => refused.push(format!(
                "{name}: the SHIPPED fork's day moved over the same world ({}), and no comparand parity number moves it (D64, clause 2)",
                forkplan::first_difference("shipped", &old["shipped"], &l["shipped"]).unwrap_or_default()
            )),
            Some(_) => {}
        }
        out.push_str(&serde_json::to_string(&l).expect("a line serialises"));
        out.push('\n');
    }
    for k in &held.head {
        if !SEPARATORS.iter().any(|(n, _)| n == k) {
            refused.push(format!("{k}: a frozen line no world builds any more"));
        }
    }
    eprintln!("separator days: {added} line(s) added, {} refused", refused.len());
    assert!(refused.is_empty(), "the separator bless is refused and wrote nothing:\n  {}", refused.join("\n  "));
    let out_path = std::env::var_os("TM_SEPARATORS_BLESS_OUT").map(PathBuf::from).unwrap_or(path);
    std::fs::write(out_path, out).expect("the frozen separator days are written");
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gap 4168)
/// **The frozen separator days are the in-tree fork's answer today** — while the in-tree fork
/// stands, it plans each frozen world's day exactly as frozen (the claim
/// `kernel_separator_worlds.rs`' region makes of `nbsp-box`, now of every world and against the
/// frozen day), and no registered number departs on it. Deleted with the region.
#[test]
fn the_frozen_separator_days_are_the_in_tree_forks_answer_today() {
    for l in frozen() {
        let name = l["name"].as_str().unwrap_or("?");
        let b = built(&l);
        let day = shipped_day(&b, &forkplan::InTree).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(day, l["shipped"], "{name}: the in-tree fork plans another day ({:?})", forkplan::first_difference("day", &l["shipped"], &day));
        no_departure(name, &b, &day, &forkplan::InTree);
        let suite = Built::of(suite_world_of(l["line"].as_str().unwrap_or_default()));
        let theirs = shipped_day(&suite, &forkplan::InTree).unwrap_or_else(|e| panic!("{name} (the suite's construction): {e}"));
        assert_eq!(theirs, l["shipped"], "{name}: the in-tree fork plans the suite's construction otherwise");
    }
}

/// **[`no_departure`] bites** (AGENTS §5.8): on a frozen class line whose comparand departs from the
/// shipped fork's day (D60's order, parity P51 — its `shipped` held beside a `day` that is not it),
/// the assertion that holds the separator days to the shipped day with nothing applied refuses.
#[test]
fn no_departure_refuses_a_world_a_registered_number_departs_on() {
    let line = forkclass::frozen_lines()
        .iter()
        .find(|l| l["d60"]["p51"] == true && l["secondary"].is_null() && l["world"]["state"]["active"].is_null())
        .expect("a frozen class line D60's order departs on, no block running");
    let b = Built::of(ClassWorld::of_json(&line["world"], tz()).expect("a stored world"));
    let day = shipped_day(&b, &forkplan::InTree).expect("the in-tree fork plans the day");
    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| no_departure("a P51 line", &b, &day, &forkplan::InTree)));
    assert!(refused.is_err(), "no_departure let a world D60's order departs on through");
}
// END THE FORK PLANNER
