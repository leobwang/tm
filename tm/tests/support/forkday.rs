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
//! a digest of it: a digest would have to normalise the two classes below out,
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
//! # The two classes the kernel's day may differ by, and nothing else
//!
//! Measured on the four fixture days at W-35 (README gaps 551 and 435), each
//! counted by [`DayTally`] and bounded by its caller, so a class that widens
//! and a class that closes both fail loudly:
//!
//! * **gap 551** — a planned Break row the fork's day draws and the kernel's
//!   does not (`PlanReq.todayCut.breaks` holds the cut's breaks and no Break
//!   row of them is placed). Matched as a fork row of kind `break`, not done,
//!   starting at or after `now`. It is a digested row, so the day's hash
//!   differs exactly when one is present, and that is checked.
//! * **gap 435** — a routine row's `⚠`: fork `emit_segments` marks a scheduled
//!   window task's routine row `hot` at `p = 0` (plan-basic's `^a3`, "Pick up
//!   package"), and the kernel writes `hot := false` on every routine row.
//!   Matched as a fork routine row with `hot: true` whose kernel twin is equal
//!   in every other field. `hot` is not digested, so it never moves the hash —
//!   and it IS a mark the day file prints, so it is a display difference, which
//!   is why it is an R3 prerequisite and not a parity row.
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
    /// Gap 551's rows: planned Breaks the fork draws and the kernel does not.
    pub break_rows_551: usize,
    /// Gap 435's marks: a routine row's `⚠` the kernel does not set.
    pub hot_marks_435: usize,
    /// Days whose kernel hash is the fork's.
    pub hashes_equal: usize,
    /// Inputs with no frozen day, so the fork did not answer them at all — the
    /// number that must never be read as agreement.
    pub skipped: usize,
}

impl DayTally {
    /// One line saying what was compared and what was not, and how many
    /// differences fell outside the two classes — the number `findings` holds,
    /// never a constant a failing run would print too.
    pub fn line(&self, what: &str, findings: usize) -> String {
        format!(
            "frozen fork days — {what}: {} days, {} fork rows, {} other values compared; gap 551 {} \
             planned break row(s) the kernel does not draw, gap 435 {} routine `⚠` mark(s) it does not \
             set; {} of {} hashes equal; {} inputs had no frozen day; {findings} other difference(s)",
            self.days,
            self.rows,
            self.values,
            self.break_rows_551,
            self.hot_marks_435,
            self.hashes_equal,
            self.days,
            self.skipped
        )
    }
}

/// **Compare a day the kernel planned with the frozen fork's**, by value.
/// `now` is the instant both were planned at (gap 551's rows start at or after
/// it). Returns every difference that is not one of the two classes, by name.
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

    // The rows: the fork's, less gap 551's rows and with gap 435's mark taken
    // off, must be the kernel's exactly and in order.
    let fork_rows = fv["segments"].as_array().map(Vec::as_slice).unwrap_or_default();
    let kernel_rows = kv["segments"].as_array().map(Vec::as_slice).unwrap_or_default();
    t.rows += fork_rows.len();
    let at = |v: &Value| DateTime::parse_from_rfc3339(v.as_str().unwrap_or_default()).ok();
    let now_fixed = now.fixed_offset();
    let mut expected: Vec<Value> = Vec::new();
    let mut breaks = 0usize;
    for (i, row) in fork_rows.iter().enumerate() {
        let planned_break = row["kind"] == "break"
            && row["flags"]["done"] == false
            && at(&row["start"]).is_some_and(|s| s >= now_fixed);
        if planned_break {
            breaks += 1;
            continue;
        }
        let mut row = row.clone();
        if row["kind"] == "routine" && row["flags"]["hot"] == true {
            // Gap 435 only when the kernel's row at the same place is this row
            // without its mark; anything else about it is a real difference.
            let mut bare = row.clone();
            bare["flags"]["hot"] = Value::Bool(false);
            if kernel_rows.contains(&bare) {
                t.hot_marks_435 += 1;
                row = bare;
            } else {
                findings.push(format!("{name}: fork routine row {i} ({}) has no kernel twin", row["item"]));
            }
        }
        expected.push(row);
    }
    t.break_rows_551 += breaks;
    if expected.as_slice() != kernel_rows {
        let first = expected.iter().zip(kernel_rows).position(|(a, b)| a != b).unwrap_or(expected.len().min(kernel_rows.len()));
        findings.push(format!(
            "{name}: the rows differ at {first} (fork {} rows less {breaks} planned break(s), kernel {}):\n      fork   {}\n      kernel {}",
            fork_rows.len(),
            kernel_rows.len(),
            expected.get(first).map_or("—".to_string(), Value::to_string),
            kernel_rows.get(first).map_or("—".to_string(), Value::to_string),
        ));
    }

    // The hash: gap 551's rows are digested, gap 435's mark is not.
    let fork_hash = fork["hash"].as_str().unwrap_or_default();
    if k.hash == fork_hash {
        t.hashes_equal += 1;
        if breaks > 0 {
            findings.push(format!("{name}: the hashes agree over a day the kernel drew without {breaks} break(s)"));
        }
    } else if breaks == 0 {
        findings.push(format!("{name}: hash kernel {} fork {fork_hash} over rows that agree", k.hash));
    }
    findings
}

/// Panic unless `findings` is empty, quoting every one.
pub fn no_disagreement(findings: &[String]) {
    assert!(
        findings.is_empty(),
        "{} disagreement(s) with the frozen fork days (each must be gap 551's or gap 435's class):\n  {}",
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
    let (outside, region_bytes, deleted) = match (source.find(BEGIN), source.find(END)) {
        (Some(i), Some(j)) => {
            assert!(i < j, "the END banner precedes the BEGIN banner");
            let mut outside = source[..i].to_string();
            outside.push_str(&source[j..]);
            (outside, j - i, false)
        }
        (None, None) => (source.to_string(), 0, true),
        _ => panic!("one fork-planner banner without the other"),
    };
    let escapes = outside
        .lines()
        .enumerate()
        .filter(|(_, l)| !l.trim_start().starts_with("//"))
        .flat_map(|(i, l)| {
            NEEDLES
                .iter()
                .filter(move |n| l.contains(**n))
                .map(move |n| format!("line {i}: `{n}` in {}", l.trim()))
        })
        .collect();
    ForkScan { region_bytes, escapes, deleted }
}
