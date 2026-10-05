//! **The planner's comparand that survives R3** (README gap 2722; D21's shape,
//! stage 5's gap 146).
//!
//! R3 deleted `tm-core/src/planner.rs`, and every differential arm that planned
//! a day compared the kernel against it. The moment it went, an arm either went
//! with it or started comparing the kernel with itself — AGENTS §9.2's worst
//! disguised gap, on the least reviewable commit of the stage. Stage 5 met the
//! same shape at its switch (gap 146) and D21 put the instrument BEFORE the
//! change it watches; this is that move, one comparand along.
//!
//! **What is frozen, and why it is the shipped configuration (D53).** Each
//! named input's fork day is taken the way the binary planned until R3 —
//! fork planner::plan(input.with_ranking(cands, prios)) with the kernel's own
//! grants for `prios`, read by the binary's own reader (`planwire::prio_of`) —
//! and written **by value**, the whole serialised `DayPlan` and its hash, never
//! a digest of it: a digest would have to normalise the classes below out,
//! and normalising a class out hides the one thing its gap exists to watch.
//!
//! **The frozen priorities are the kernel's own grants as read at the bless**
//! — that is what `with_ranking` hands the fork, and what the shipped binary
//! hands it — so comparing `priorities` compares the kernel's ranking now with
//! its ranking then, not the kernel with the fork's own §7 pass, which no
//! shipped path runs (D53).
//!
//! **Neither side of a comparison here is the fork's code.** One side is a
//! `DayPlan` the *kernel* produced and the host's codec (`tm_core::planwire`)
//! decoded; the other is bytes on disk. So R3's deletion cannot turn it into a
//! self-comparison — and the suites that used it kept their fork-reading half in
//! one `BEGIN THE FORK PLANNER` … `END THE FORK PLANNER` region, which
//! [`fork_scan`] held to that: R3 deleted the regions and nothing else, and with
//! no region left [`fork_scan`] holds that no reference to the fork remains.
//!
//! Re-bless with, from the repository root, asking fork 4748911 out of the tree
//! (`tm-oracle plan`, built by `kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh`):
//!
//! ```text
//! TM_ORACLE=<oracle> TM_PLANNER_BLESS=1 cargo test -p tm --test planner_fixtures -- --ignored \
//!   the_frozen_fork_days_are_reblessed
//! ```
//!
//! A re-bless is a decision about what the fork says, never a way to make a
//! failure go away (AGENTS §7.2). Until W-45 it planned with the in-tree fork,
//! in the region R3 deleted, and this file would have been the fork's last word
//! on these days; since W-45 track C (README gap 4680) it asks the oracle, so it
//! outlives R3.
//!
//! # The one class the kernel's day may differ by, and nothing else
//!
//! **Gaps 551, 435 and 550 are CLOSED (stage 6 W-37 track R)**, and their rows
//! are compared BY VALUE like every other row. Until W-37 each was a declared
//! class this comparator took off the fork's row before comparing; the kernel
//! now draws each as the fork does (`Planner.PlanReq.keptBreakRows`,
//! `Planner.PlanReq.routineHot`, `Planner.PlanReq.candMult`). [`DayTally`]
//! still COUNTS them — as rows of the old class compared by value — so a
//! caller's floor (`> 0`) says the frozen days still exercise each, and a
//! caller's exact count still fails when the frozen set moves:
//!
//! * **gap 551's rows** — a planned Break row (kind `break`, not done, starting
//!   at or after `now`): fork `emit_segments`' `kept_breaks`, now the kernel's
//!   too. Digested, so a day holding one now hashes as the fork's.
//! * **gap 435's marks** (README gap 2870) — a routine row marked `hot`: fork
//!   `emit_segments` marks a scheduled window task's routine row at `p = 0`
//!   (plan-basic's `^a3`, "Pick up package"); not digested, compared by value.
//! * **gap 550's rows** — §8.2 choice 5b's reservation row carrying the running
//!   candidate's `multiplier`: kind `block`, marked `current`, a multiplier
//!   present. Digested.
//!
//! What stays a declared difference is one class, by design and not a gap:
//!
//! * **an under-used row's note** — BY DESIGN, not a gap: fork `emit_segments`
//!   writes `↓ slot E, item C` into `flags.note`, and the kernel's
//!   `Planner.assignedSeg` writes no note (its `assignedSeg_note` is a law
//!   about NOT writing one) because the renderer derives that sentence from
//!   the row's own energy and the item's `ci` (`emit::note_cell`, and
//!   `Emit.underusedCell` on the kernel's side). Matched as a fork row marked
//!   `underused` whose note is `↓ slot <its energy>, item <n>` and whose kernel
//!   twin is equal with no note; not digested. `support/forkclass.rs` checks
//!   that the renderer derives the fork's exact sentence for each.
//!
//! Everything else — the date, the window, the budget, all twelve diagnostic
//! fields, the priorities, every other row **in order** — must be equal.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use chrono::DateTime;
use chrono_tz::Tz;
use serde_json::Value;

use tm_core::dayplan::DayPlan;
use tm_core::planwire::KernelDay;

#[allow(dead_code)]
#[path = "fork.rs"]
mod fork;

#[allow(dead_code)]
#[path = "srcwalk.rs"]
mod srcwalk;

/// The frozen days: one JSON line per named input, `{name, hash, day}`.
pub const FROZEN_DAYS: &str = "fork-4748911-planner-days.jsonl";

/// Where it lives.
pub fn frozen_path() -> std::path::PathBuf {
    fork::fixtures_dir().join(FROZEN_DAYS)
}

/// The frozen days by name, read once.
pub fn frozen_days() -> &'static BTreeMap<String, Value> {
    static FROZEN: OnceLock<BTreeMap<String, Value>> = OnceLock::new();
    FROZEN.get_or_init(|| {
        let path = frozen_path();
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("{}: {e} — re-bless it (see support/forkday.rs)", path.display()));
        let mut out = BTreeMap::new();
        for l in text.lines().filter(|l| !l.trim().is_empty()) {
            let v: Value = serde_json::from_str(l).expect("a frozen day is JSON");
            let name = v["name"].as_str().expect("a frozen day names its input").to_string();
            assert!(out.insert(name.clone(), v).is_none(), "two frozen days named `{name}`");
        }
        out
    })
}

/// **`plan-basic` planned every ten minutes, frozen** (W-38, README gaps 3200 and 3282):
/// `planner_w37_rows.rs`' arm — §4.3's own tree, `^a3` "Pick up package" a dated window
/// task due today, planned at every ten minutes from both of the fixture suite's states, each
/// day the fork's as the shipped binary plans it (D53) — compared the kernel with the LIVE
/// fork, in a region R3 deletes. These are those days, by value: one line per `(state,
/// instant)`, `{name, state, now, hash, day}`, the state and the instant carried with the day
/// so the arm that survives R3 plans exactly what was frozen and needs no definition of either.
pub const FROZEN_BASIC: &str = "fork-4748911-planner-basic-days.jsonl";

/// Where it lives.
pub fn frozen_basic_path() -> std::path::PathBuf {
    fork::fixtures_dir().join(FROZEN_BASIC)
}

/// The frozen `plan-basic` days, in file order; a name carried twice FAILS.
pub fn frozen_basic_days() -> Vec<Value> {
    let path = frozen_basic_path();
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("{}: {e} — see support/forkday.rs' FROZEN_BASIC", path.display()));
    let mut names = std::collections::BTreeSet::new();
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Value = serde_json::from_str(l).expect("a frozen plan-basic day is JSON");
            let name = v["name"].as_str().expect("a frozen day names its input").to_string();
            assert!(names.insert(name.clone()), "two frozen plan-basic days named `{name}`");
            v
        })
        .collect()
}

/// One line of the frozen `plan-basic` file: the state and the instant planned at, and the day.
pub fn basic_line(name: &str, state: &tm_core::store::RuntimeState, now: DateTime<Tz>, day: &DayPlan) -> String {
    basic_line_of(name, state, now, &day.hash(), &serde_json::to_value(day).expect("a day serialises"))
}

/// [`basic_line`] of a day as its JSON spells it and its digest — the ONE writer of the line, so a
/// bless that asks fork 4748911 out of the tree (`tm-oracle plan`, which answers a day as JSON)
/// writes the bytes the in-tree fork's line had (W-45 track C, README gap 4680).
pub fn basic_line_of(name: &str, state: &tm_core::store::RuntimeState, now: DateTime<Tz>, hash: &str, day: &Value) -> String {
    let row = serde_json::json!({
        "name": name,
        "state": serde_json::to_value(state).expect("a state serialises"),
        "now": now.to_rfc3339(),
        "hash": hash,
        "day": day,
    });
    serde_json::to_string(&row).expect("a frozen line serialises") + "\n"
}

/// One line of the frozen file.
pub fn frozen_line(name: &str, day: &DayPlan) -> String {
    frozen_line_of(name, &day.hash(), &serde_json::to_value(day).expect("a day serialises"))
}

/// [`frozen_line`] of a day as its JSON spells it and its digest — the one writer, as
/// [`basic_line_of`] is (W-45 track C, README gap 4680).
pub fn frozen_line_of(name: &str, hash: &str, day: &Value) -> String {
    let row = serde_json::json!({
        "name": name,
        "hash": hash,
        "day": day,
    });
    serde_json::to_string(&row).expect("a frozen line serialises") + "\n"
}

/// What one comparison counted, so "no disagreement" is never confused with
/// "never ran" (AGENTS §7.3).
#[derive(Default, Debug)]
pub struct DayTally {
    /// Days compared.
    pub days: usize,
    /// Fork rows looked at.
    pub rows: usize,
    /// Scalar values compared outside the rows.
    pub values: usize,
    /// Gap 551's rows — planned Breaks the fork draws — COMPARED BY VALUE since
    /// W-37 (the gap is closed; until then they were set aside, not compared).
    pub break_rows_551: usize,
    /// Gap 435's marks — a routine row's `⚠` — compared by value since W-37.
    pub hot_marks_435: usize,
    /// Gap 550's rows — a reservation row carrying a multiplier — compared by
    /// value since W-37 (W-36 track H; a running block, which no fixture day
    /// holds).
    pub mult_rows_550: usize,
    /// Under-used rows whose `↓` note the kernel leaves to the renderer (by
    /// design, `Planner.assignedSeg_note`; W-36 track H).
    pub underused_notes: usize,
    /// Days whose kernel hash is the fork's.
    pub hashes_equal: usize,
    /// Inputs with no frozen day, so the fork did not answer them at all — the
    /// number that must never be read as agreement.
    pub skipped: usize,
}

impl DayTally {
    /// One line saying what was compared and what was not, and how many
    /// differences fell outside the three classes — the number `findings` holds,
    /// never a constant a failing run would print too.
    pub fn line(&self, what: &str, findings: usize) -> String {
        format!(
            "frozen fork days — {what}: {} days, {} fork rows, {} other values compared; compared by \
             value since gaps 551, 435 and 550 closed (W-37): {} planned break row(s), {} routine `⚠` \
             mark(s), {} reservation multiplier(s); {} under-used note(s) left to the renderer; {} of {} \
             hashes equal; {} inputs had no frozen day; {findings} other difference(s)",
            self.days,
            self.rows,
            self.values,
            self.break_rows_551,
            self.hot_marks_435,
            self.mult_rows_550,
            self.underused_notes,
            self.hashes_equal,
            self.days,
            self.skipped
        )
    }
}

/// **Compare a day the kernel planned with the frozen fork's**, by value.
/// `now` is the instant both were planned at (gap 551's rows, counted, start at
/// or after it). Returns every difference but an under-used row's note, by name.
pub fn compare_day_with_fork(
    name: &str,
    k: &KernelDay,
    fork: &Value,
    now: DateTime<Tz>,
    t: &mut DayTally,
) -> Vec<String> {
    let mut findings = Vec::new();
    let kv = serde_json::to_value(&k.day).expect("the kernel's day serialises");
    let fv = &fork["day"];
    t.days += 1;

    for key in ["date", "window", "budget_blocks", "diagnostics", "priorities"] {
        t.values += fork::leaves(&fv[key]);
        if kv[key] == fv[key] {
            continue;
        }
        let mut paths = Vec::new();
        fork::diff_paths(key, &kv[key], &fv[key], &mut paths);
        for (_, message) in paths.into_iter().take(6) {
            findings.push(format!("{name}: {message}"));
        }
    }

    // The rows: the fork's, with only an under-used row's note taken off (the
    // one class left, by design), must be the kernel's exactly and in order.
    // Gaps 551, 435 and 550 are closed (W-37 track R): their rows are counted
    // and compared by value, never set aside.
    let fork_rows = fv["segments"].as_array().map(Vec::as_slice).unwrap_or_default();
    let kernel_rows = kv["segments"].as_array().map(Vec::as_slice).unwrap_or_default();
    t.rows += fork_rows.len();
    let at = |v: &Value| DateTime::parse_from_rfc3339(v.as_str().unwrap_or_default()).ok();
    let now_fixed = now.fixed_offset();
    let mut expected: Vec<Value> = Vec::new();
    let (mut breaks, mut mults) = (0usize, 0usize);
    for row in fork_rows {
        if row["kind"] == "break"
            && row["flags"]["done"] == false
            && at(&row["start"]).is_some_and(|s| s >= now_fixed)
        {
            breaks += 1;
        }
        if row["kind"] == "block" && row["flags"]["current"] == true && !row["flags"]["multiplier"].is_null() {
            mults += 1;
        }
        if row["kind"] == "routine" && row["flags"]["hot"] == true {
            t.hot_marks_435 += 1;
        }
        let row = match underused_note_left_to_the_renderer(row, kernel_rows) {
            Some(bare) => {
                t.underused_notes += 1;
                bare
            }
            None => row.clone(),
        };
        expected.push(row);
    }
    t.break_rows_551 += breaks;
    t.mult_rows_550 += mults;
    if expected.as_slice() != kernel_rows {
        let first = expected.iter().zip(kernel_rows).position(|(a, b)| a != b).unwrap_or(expected.len().min(kernel_rows.len()));
        findings.push(format!(
            "{name}: the rows differ at {first} (fork {} rows, kernel {}):\n      fork   {}\n      kernel {}",
            fork_rows.len(),
            kernel_rows.len(),
            expected.get(first).map_or("—".to_string(), Value::to_string),
            kernel_rows.get(first).map_or("—".to_string(), Value::to_string),
        ));
    }

    // The hash: every digested field of every row is compared above, and an
    // under-used row's note is not digested, so rows that agree must hash alike.
    let fork_hash = fork["hash"].as_str().unwrap_or_default();
    if k.hash == fork_hash {
        t.hashes_equal += 1;
    } else {
        findings.push(format!("{name}: hash kernel {} fork {fork_hash}", k.hash));
    }
    findings
}

/// **The one row class the kernel's day may differ by** (the module header): a fork
/// row marked `underused` whose note is `↓ slot <its energy>, item <n>` and whose
/// kernel twin — the same row with no note — is among `kernel_rows`. `Some(twin)`
/// for such a row, which the caller compares in its place; `None` otherwise. One
/// definition, for the day comparison here and the class comparison's rows after a
/// running break (`forkclass::compare_line`, W-38).
pub fn underused_note_left_to_the_renderer(row: &Value, kernel_rows: &[Value]) -> Option<Value> {
    let noted = row["flags"]["underused"] == true
        && row["flags"]["note"]
            .as_str()
            .and_then(|n| n.strip_prefix(&format!("↓ slot {}, item ", row["energy"])))
            .is_some_and(|c| !c.is_empty() && c.bytes().all(|b| b.is_ascii_digit()));
    if !noted {
        return None;
    }
    let mut bare = row.clone();
    bare["flags"]["note"] = Value::Null;
    kernel_rows.contains(&bare).then_some(bare)
}

/// Panic unless `findings` is empty, quoting every one.
pub fn no_disagreement(findings: &[String]) {
    assert!(
        findings.is_empty(),
        "{} disagreement(s) with the frozen fork days (gaps 551, 435 and 550 are closed; only an under-used row's note may differ):\n  {}",
        findings.len(),
        findings.join("\n  ")
    );
}

/// What [`fork_scan`] found in one source file.
pub struct ForkScan {
    /// Bytes inside the region.
    pub region_bytes: usize,
    /// References to the fork's planner outside it.
    pub escapes: Vec<String>,
    /// True once the region is gone — which is to say, after R3.
    pub deleted: bool,
}

/// **Is R3's deletion mechanical in this file?** `fork::reader_scan`'s shape,
/// for the planner: every code line that reaches the fork's planner — a
/// `planner::` path, `tm_core::planner`, `PlanInput`, `with_ranking`, or the
/// fixture's `input(..)` builder — must sit inside the file's
/// `BEGIN THE FORK PLANNER` … `END THE FORK PLANNER` region, so R3 deletes the
/// region and nothing has to be found by reading. With no region left, NO
/// reference may remain anywhere: after R3 this is the assertion that the
/// comparand really did move. Comment lines are skipped; the needles live here
/// so a file that scans itself cannot match its own test.
pub fn fork_scan(source: &str) -> ForkScan {
    fork_scan_with(source, &[])
}

/// **The module a test-tree file is reached through** — its stem, or its directory's name for a
/// `mod.rs` (`tm/tests/planner_common/mod.rs` is `planner_common`, `support/forkclass.rs` is
/// `forkclass`, which every includer names it).
pub fn module_of(label: &str) -> String {
    let p = std::path::Path::new(label);
    if p.file_name().is_some_and(|f| f == "mod.rs") {
        p.parent().and_then(|d| d.file_name()).map(|d| d.to_string_lossy().to_string()).unwrap_or_default()
    } else {
        p.file_stem().map(|d| d.to_string_lossy().to_string()).unwrap_or_default()
    }
}

/// **The top-level names a file's fork region declares** — what R3 deletes with it, read as
/// [`fork_scan`] reads its own file's (W-38 land step, README gap 3510).
pub fn region_names(source: &str) -> Vec<String> {
    let at_line_start = |needle: &str| {
        source.match_indices(needle).map(|(i, _)| i).find(|&i| i == 0 || source.as_bytes()[i - 1] == b'\n')
    };
    match (at_line_start("// BEGIN THE FORK PLANNER"), at_line_start("// END THE FORK PLANNER")) {
        (Some(i), Some(j)) if i < j => srcwalk::code_lines(&source[i..j])
            .into_iter()
            .filter_map(|(_, code)| top_level_name(&code))
            .collect(),
        _ => Vec::new(),
    }
}

/// [`fork_scan`], with the names OTHER files' regions declare — **a region's names are the whole
/// test tree's, not its file's** (W-38 land step, README gap 3510): until then the guard read only
/// the file's own region, and track K's `kernel_unplaced_banner.rs` imported `planner_common`'s
/// region's `Fork` outside any region, with the guard green and R3's simulated deletion failing to
/// build. Another file's item is reached only through that file's MODULE, so `foreign` is
/// `(module, name)` and an outside code line escapes when it spells `module::` and names the word
/// — `planner_common::Fork`, or the `use planner_common::{…, Fork}` that imports it. **And a `use`
/// statement that imports the fork's planner module by no needle** (W-45 track C, README gap 4683):
/// a grouped or renamed import (`use tm_core::{config, planner as fp};`, one line or several) is an
/// escape at the line it begins on ([`use_names_the_fork`]), since every later `fp::…` is a reach no
/// needle sees. What this cannot see: a glob import (`use m::*`) followed by a bare use of the name,
/// and the crate imported under another name (`extern crate tm_core as c;`).
pub fn fork_scan_with(source: &str, foreign: &[(String, String)]) -> ForkScan {
    const BEGIN: &str = "// BEGIN THE FORK PLANNER";
    const END: &str = "// END THE FORK PLANNER";
    // A banner is a banner only at the start of a line: the constants above
    // spell both inside a string, and that is not a region.
    let at_line_start = |needle: &str| {
        source.match_indices(needle).map(|(i, _)| i).find(|&i| i == 0 || source.as_bytes()[i - 1] == b'\n')
    };
    let (outside, region_bytes, deleted) = match (at_line_start(BEGIN), at_line_start(END)) {
        (Some(i), Some(j)) => {
            assert!(i < j, "the END banner precedes the BEGIN banner");
            let mut outside = source[..i].to_string();
            outside.push_str(&source[j..]);
            (outside, j - i, false)
        }
        (None, None) => (source.to_string(), 0, true),
        _ => panic!("one fork-planner banner without the other"),
    };
    // CODE only (W-36 track H): `srcwalk::code_lines` drops comments -- a
    // trailing one too, which the old `starts_with("//")` filter read as code --
    // and `blank_strings` empties every string literal, so this file's own
    // FORK_NEEDLES line is not a reference to the fork and needs no exemption.
    // **And what the region DEFINES** (W-38, README gap 3472): a name the region declares at the
    // top level — a free `fn`, a `static`, a `const`, a type — is deleted with it, so code outside
    // that names one would not build after R3. The needles above could not see that shape: W-38's
    // simulation of the deletion found a test outside `planner_invariants.rs`' region reading
    // the kernel's §7 answers through the region's own `kernel_prios`. A property of the file,
    // per file: the region's own top-level names, read off its code at column zero.
    let region_names = region_names(source);
    let lines: Vec<(usize, String)> = srcwalk::code_lines(&outside).into_iter().map(|(i, code)| (i - 1, blank_strings(&code))).collect();
    let imports: Vec<String> = use_statements(lines.iter().map(|(i, l)| (*i, l.as_str())))
        .into_iter()
        .filter(|(_, s)| use_names_the_fork(s) && !FORK_NEEDLES.iter().any(|n| s.contains(*n)))
        .map(|(i, s)| format!("line {i}: a `use` of the fork's planner module, in {}", s.split_whitespace().collect::<Vec<_>>().join(" ")))
        .collect();
    let mut escapes: Vec<String> = lines
        .into_iter()
        .flat_map(|(i, l)| {
            let mut found: Vec<String> = FORK_NEEDLES
                .iter()
                .filter(|n| l.contains(**n))
                .map(|n| format!("line {i}: `{n}` in {}", l.trim()))
                .collect();
            found.extend(
                region_names
                    .iter()
                    .filter(|n| names_word(&l, n))
                    .map(|n| format!("line {i}: `{n}`, which the region defines, in {}", l.trim())),
            );
            found.extend(
                foreign
                    .iter()
                    .filter(|(m, n)| l.contains(&format!("{m}::")) && names_word(&l, n))
                    .map(|(m, n)| format!("line {i}: `{m}::{n}`, which {m}'s region defines, in {}", l.trim())),
            );
            found
        })
        .collect();
    escapes.extend(imports);
    ForkScan { region_bytes, escapes, deleted }
}

/// **Every `use` statement among `lines`**, `(index, code)` pairs: from the line its keyword begins
/// (`use`, `pub use` or `pub(crate) use`, after the indentation) to the line its `;` ends, joined,
/// with the index of the line it begins on.
pub fn use_statements<'a>(lines: impl IntoIterator<Item = (usize, &'a str)>) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut cur: Option<(usize, String)> = None;
    for (i, l) in lines {
        let t = l.trim_start();
        let (start, mut text) = match cur.take() {
            Some(c) => c,
            None if ["use ", "pub use ", "pub(crate) use "].iter().any(|p| t.starts_with(p)) => (i, String::new()),
            None => continue,
        };
        text.push_str(t);
        text.push(' ');
        if t.contains(';') {
            out.push((start, text));
        } else {
            cur = Some((start, text));
        }
    }
    out
}

/// **Whether a `use` statement imports the fork's planner module** (W-45 track C, README gap 4683):
/// rooted at `tm_core` and naming the word `planner` — which a grouped or renamed import does with no
/// needle (`use tm_core::{config, planner as fp};`), after which `fp::diff(…)` reaches the fork.
pub fn use_names_the_fork(stmt: &str) -> bool {
    let Some(at) = stmt.find("use ") else { return false };
    stmt[at + "use ".len()..].trim_start().trim_start_matches("::").starts_with("tm_core") && names_word(stmt, "planner")
}

/// **The tests a fork region holds that reach NO fork planner** (stage 6 W-45 track C, README gap
/// 4682) — the other half of [`fork_scan`]: that guard keeps every reference to the fork INSIDE the
/// region, and this keeps nothing BUT the fork there. R3 deletes the region whole, so a test in it that
/// asks the kernel alone, or a harness check, or a bless that reaches no fork (W-45 moved one of each
/// out: the class worlds' re-draw, `planner_w40_runs.rs`' P64 precondition and the kernel halves of
/// three other tests) would be deleted for nothing.
///
/// A test reaches the fork when its code names one of [`fork_scan`]'s needles or imports the fork's
/// module ([`use_names_the_fork`]), a top-level item of its region that reaches it, or an item another
/// file's region declares (`foreign`, as [`fork_scan_with`] reads it). An item of the region reaches it by the same rule, to a fixpoint;
/// an `impl` of a type the region declares carries its reach to that type, and an `impl` of a type
/// declared elsewhere to its methods, read as `.method(`. Every `#[test]` function of the region —
/// at column zero or inside a `proptest!` block — is read; comments and string contents are not.
/// What it cannot see: a reach through a macro, a glob import, or a trait method called by a name
/// the impl does not declare — and it reads a string literal that spans lines as code on its later
/// lines (`srcwalk::code_lines` blanks strings line by line), so such a literal's braces can end a
/// test's body early or late.
pub fn region_tests_unreached(source: &str, foreign: &[(String, String)]) -> Vec<String> {
    const BEGIN: &str = "// BEGIN THE FORK PLANNER";
    const END: &str = "// END THE FORK PLANNER";
    let at_line_start = |needle: &str| {
        source.match_indices(needle).map(|(i, _)| i).find(|&i| i == 0 || source.as_bytes()[i - 1] == b'\n')
    };
    let (Some(i), Some(j)) = (at_line_start(BEGIN), at_line_start(END)) else { return Vec::new() };
    if i >= j {
        return Vec::new();
    }
    let code: Vec<String> = srcwalk::code_lines(&source[i..j]).into_iter().map(|(_, c)| blank_strings(&c)).collect();
    let direct = |text: &str| -> bool {
        FORK_NEEDLES.iter().any(|n| text.contains(*n))
            || foreign.iter().any(|(m, n)| text.contains(&format!("{m}::")) && text.lines().any(|l| names_word(l, n)))
            || use_statements(text.lines().enumerate()).iter().any(|(_, s)| use_names_the_fork(s))
    };
    // The region's column-zero items: each runs from its first line to the line before the next.
    let starts: Vec<usize> =
        (0..code.len()).filter(|k| code[*k].chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')).collect();
    let mut items: Vec<(Vec<String>, String)> = Vec::new();
    let declared: Vec<String> = starts.iter().filter_map(|k| top_level_name(&code[*k])).collect();
    for (n, k) in starts.iter().enumerate() {
        let end = starts.get(n + 1).copied().unwrap_or(code.len());
        let text = code[*k..end].join("\n");
        let head = code[*k].trim_end();
        let mut names: Vec<String> = top_level_name(head).into_iter().collect();
        if let Some(rest) = head.strip_prefix("use ").or_else(|| head.strip_prefix("pub use ")) {
            let inner = rest.trim_end_matches(';').rsplit("::").next().unwrap_or_default().to_string();
            let path_tail = rest.trim_end_matches(';').to_string();
            let list = if path_tail.contains('{') {
                path_tail.split_once('{').map(|(_, r)| r.trim_end_matches('}').to_string()).unwrap_or_default()
            } else {
                inner
            };
            for part in list.split(',').map(str::trim).filter(|p| !p.is_empty() && *p != "self") {
                names.push(part.rsplit(" as ").next().unwrap_or(part).trim().to_string());
            }
        }
        if let Some(rest) = head.strip_prefix("impl") {
            let ty = rest.rsplit(" for ").next().unwrap_or(rest).trim().trim_end_matches('{').trim();
            let ty: String = ty.trim_start_matches(|c: char| c == '<' || c.is_whitespace()).chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
            if declared.contains(&ty) {
                names.push(ty);
            } else {
                for l in &code[*k..end] {
                    if let Some(m) = l.trim_start().strip_prefix("pub fn ").or_else(|| l.trim_start().strip_prefix("fn ")) {
                        let m: String = m.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
                        names.push(format!(".{m}("));
                    }
                }
            }
        }
        items.push((names, text));
    }
    let mut reach: Vec<bool> = items.iter().map(|(_, t)| direct(t)).collect();
    let names_one = |text: &str, n: &str| -> bool {
        if n.starts_with('.') {
            text.contains(n)
        } else {
            text.lines().any(|l| names_word(l, n))
        }
    };
    loop {
        let reached: Vec<&String> = items.iter().zip(&reach).filter(|(_, r)| **r).flat_map(|((ns, _), _)| ns.iter()).collect();
        let mut moved = false;
        for (k, (_, text)) in items.iter().enumerate() {
            if !reach[k] && reached.iter().any(|n| names_one(text, n)) {
                reach[k] = true;
                moved = true;
            }
        }
        if !moved {
            break;
        }
    }
    let reached: Vec<&String> = items.iter().zip(&reach).filter(|(_, r)| **r).flat_map(|((ns, _), _)| ns.iter()).collect();
    // Every `#[test]` function of the region, and whether it reaches the fork.
    let mut out = Vec::new();
    let mut k = 0;
    while k < code.len() {
        if code[k].trim() != "#[test]" {
            k += 1;
            continue;
        }
        let Some(f) = (k..code.len()).find(|x| code[*x].trim_start().starts_with("fn ")) else { break };
        let name: String = code[f].trim_start()[3..].chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
        let (mut depth, mut opened, mut e) = (0i64, false, f);
        for (x, l) in code.iter().enumerate().skip(f) {
            depth += l.matches('{').count() as i64 - l.matches('}').count() as i64;
            opened |= l.contains('{');
            if opened && depth <= 0 {
                e = x;
                break;
            }
        }
        let body = code[f..=e].join("\n");
        if !direct(&body) && !reached.iter().any(|n| names_one(&body, n)) {
            out.push(name);
        }
        k = e + 1;
    }
    out
}

/// **What a code line names when it reaches the fork's planner**: its module, its input, its ranking
/// seam and the fixture's builder of the fork's input — [`fork_scan`]'s needles and
/// [`region_tests_unreached`]'s, one list (the harness's in-tree backend and
/// planner_common's fork planner are reached as other files' region names).
const FORK_NEEDLES: [&str; 6] = ["planner::", "tm_core::planner", "PlanInput", "with_ranking", ".input(&", "fn input"];

/// The name a column-zero code line DECLARES — `fn`, `static`, `const`, `struct`, `enum`,
/// `type` or `trait`, public or not — or `None`. The keyword must begin the line, so an
/// indented line (a method, a local, a test inside `proptest!`) declares nothing R3 deletes
/// at the file's top level.
pub fn top_level_name(code: &str) -> Option<String> {
    let rest = code.strip_prefix("pub ").unwrap_or(code);
    let rest = rest.strip_prefix("pub(crate) ").unwrap_or(rest);
    ["fn ", "static ", "const ", "struct ", "enum ", "type ", "trait "]
        .iter()
        .find_map(|kw| rest.strip_prefix(kw))
        .map(|r| r.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect::<String>())
        .filter(|n| !n.is_empty())
}

/// Whether `line` names `name` as a whole word (no identifier character on either side) and
/// not as a field or method (`x.name`), which is never the file's free item.
pub fn names_word(line: &str, name: &str) -> bool {
    let ident = |c: char| c.is_alphanumeric() || c == '_';
    line.match_indices(name).any(|(i, _)| {
        !line[..i].chars().next_back().is_some_and(|c| ident(c) || c == '.')
            && !line[i + name.len()..].chars().next().is_some_and(ident)
    })
}

/// A code line with every string literal's CONTENT removed (its quotes kept),
/// so a needle spelled in a string is not a reference to the fork.
pub fn blank_strings(code: &str) -> String {
    let mut out = String::new();
    let mut in_str = false;
    let mut escaped = false;
    for c in code.chars() {
        if in_str {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_str = false;
                out.push(c);
            }
            continue;
        }
        if c == '"' {
            in_str = true;
        }
        out.push(c);
    }
    out
}
