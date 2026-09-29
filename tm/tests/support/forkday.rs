//! **The planner's comparand that survives R3** (README gap 2722; D21's shape,
//! stage 5's gap 146).
//!
//! R3 deletes `tm-core/src/planner.rs`, and every differential arm that plans
//! a day compares the kernel against it. The moment it goes, an arm either goes
//! with it or starts comparing the kernel with itself — AGENTS §9.2's worst
//! disguised gap, on the least reviewable commit of the stage. Stage 5 met the
//! same shape at its switch (gap 146) and D21 put the instrument BEFORE the
//! change it watches; this is that move, one comparand along.
//!
//! **What is frozen, and why it is the shipped configuration (D53).** Each
//! named input's fork day is taken the way the binary plans today —
//! `planner::plan(input.with_ranking(cands, prios))` with the kernel's own
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
//! self-comparison — and the suites that use it keep their fork-reading half in
//! one `BEGIN THE FORK PLANNER` … `END THE FORK PLANNER` region, which
//! [`fork_scan`] holds to that: R3 deletes the region and nothing else.
//!
//! Re-bless with, from the repository root, while the fork is still there:
//!
//! ```text
//! TM_PLANNER_BLESS=1 cargo test -p tm --test planner_fixtures -- --ignored \
//!   the_frozen_fork_days_are_reblessed
//! ```
//!
//! A re-bless is a decision about what the fork says, never a way to make a
//! failure go away (AGENTS §7.2) — and after R3 it cannot be run at all: this
//! file is the fork's last word on these days.
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
    let row = serde_json::json!({
        "name": name,
        "state": serde_json::to_value(state).expect("a state serialises"),
        "now": now.to_rfc3339(),
        "hash": day.hash(),
        "day": serde_json::to_value(day).expect("a day serialises"),
    });
    serde_json::to_string(&row).expect("a frozen line serialises") + "\n"
}

/// One line of the frozen file.
pub fn frozen_line(name: &str, day: &DayPlan) -> String {
    let row = serde_json::json!({
        "name": name,
        "hash": day.hash(),
        "day": serde_json::to_value(day).expect("a day serialises"),
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
    const BEGIN: &str = "// BEGIN THE FORK PLANNER";
    const END: &str = "// END THE FORK PLANNER";
    const NEEDLES: [&str; 6] = ["planner::", "tm_core::planner", "PlanInput", "with_ranking", ".input(&", "fn input"];
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
    // NEEDLES line is not a reference to the fork and needs no exemption.
    // **And what the region DEFINES** (W-38, README gap 3472): a name the region declares at the
    // top level — a free `fn`, a `static`, a `const`, a type — is deleted with it, so code outside
    // that names one would not build after R3. The needles above could not see that shape: W-38's
    // simulation of the deletion found a test outside `planner_invariants.rs`' region reading
    // the kernel's §7 answers through the region's own `kernel_prios`. A property of the file,
    // per file: the region's own top-level names, read off its code at column zero.
    let region_names: Vec<String> = match (at_line_start(BEGIN), at_line_start(END)) {
        (Some(i), Some(j)) => srcwalk::code_lines(&source[i..j])
            .into_iter()
            .filter_map(|(_, code)| top_level_name(&code))
            .collect(),
        _ => Vec::new(),
    };
    let escapes = srcwalk::code_lines(&outside)
        .into_iter()
        .map(|(i, code)| (i - 1, blank_strings(&code)))
        .flat_map(|(i, l)| {
            let mut found: Vec<String> = NEEDLES
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
            found
        })
        .collect();
    ForkScan { region_bytes, escapes, deleted }
}

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
