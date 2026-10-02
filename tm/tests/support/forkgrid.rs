//! **The week grid's comparand that survives R3** (stage 6 W-40 track H, README gap 3718;
//! D21's shape, stage 5's gap 146 one surface along).
//!
//! # The finding this answers
//!
//! Since W-39 track T the week grid (`tm review week`, its `--json` `heat`, the TUI's Review
//! screen) draws a Pause over the KERNEL's cut (`GridCut.segSpans`, parity P63), and every test
//! of it — `cli_week_grid.rs`, `cli_week_cut.rs` — compares that cut with the day plan's.
//! Until R3 the day plan's past half is the fork's (`past_segments`); after it, the kernel's
//! (`Planner.pastSpans`), so those tests compare the kernel's cut with itself through two
//! surfaces (`GridCut.pastSpans_is_segSpans` says they are one definition, by `rfl`). No frozen
//! line held a heat cell: the frozen P56 lines hold days. So after R3 nothing outside the
//! kernel would say what the week grid should draw.
//!
//! # What is frozen, and what it is compared with
//!
//! One line per world (`tests/fixtures/fork-4748911-week-grid.jsonl`): the world AS THE
//! BINARY WROTE IT — every file of the plan directory but the derived replay cache and the
//! undo stack ([`GridWorld`]) — the review asked of it (`--date`, the instant), whether the
//! binary's replay had sealed the week, and two answers:
//!
//! * `fork` — **fork 4748911's week grid, by value**: `tm-oracle review` (fork
//!   `review::week_review`'s `heat` over the world read as the fork reads it, every Pause drawn
//!   whole as `pause`), with the Pause segments the fork's replay holds for the week, which is
//!   what a registered departure that moves a Pause's minutes is applied to.
//! * `p63` — **the cells parity P63 names**: the comparand's departure from the fork's grid,
//!   by P63's property ([`p63_cells`]) — the minutes of a Pause of day `d`'s record that a wall
//!   of `d` covers move from `pause` to `wall`, and the minutes outside the kernel's clip are not
//!   drawn. P56's drawing reaches the grid ONLY through P63 (the W-38 host cut that carried it,
//!   D69's call on README gap 3244, is gone), and P59 names no cell of the grid: fork
//!   4748911's `heat_of` already drew a typed pause as `pause` (P59 is the day plan's Lost row).
//!
//! [`compare_line`] runs the SHIPPED BINARY on the stored world and holds every cell of its
//! `heat` — eight styles a cell, `wall` the eighth, which the fork's seven do not have — to the
//! fork's cell with the named cells moved, by value; `blocks_done` and `block_min` to the
//! fork's; and the log the binary read to the log the fork read (the review appends nothing).
//! Neither side is in-tree code a test process runs: one is the binary, the other is bytes on
//! disk. So R3 cannot make it a self-comparison, and it needs no fork region.
//!
//! # Where the worlds came from
//!
//! Two kinds, each re-derived by a test ([`build`], `fork_week_grid.rs`'
//! `every_frozen_week_is_the_world_its_steps_build`):
//!
//! * **the grid tests' own worlds** ([`cli_worlds`]) — `cli_week_grid.rs`' three days and
//!   `cli_week_cut.rs`' week (unsealed, then SEALED) and its midnight call, by the same verbs at
//!   the same instants;
//! * **generated weeks** ([`week_draws`], [`week_steps`]) — W-39 track T's census generator
//!   (`scratchpad/w39-t/census/census.py`, the measurement P63's row quotes) ported here and
//!   seeded as the class draw is (`forkclass::class_draws`' convention: the seed text's bytes,
//!   space-padded to 32, as a ChaCha seed): calendar walls added at random, three days of a block
//!   run through pauses, interruptions and replans, reviewed on the Thursday.

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::path::Path;

use chrono::{DateTime, Datelike, Duration, NaiveDate, NaiveTime, Timelike};
use chrono_tz::Tz;
use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config as ProptestConfig, RngAlgorithm, TestRng, TestRunner};
use serde_json::{json, Value};

use tm_core::capacity::local_dt;
use tm_core::config::Config;
use tm_core::tree::Tree;

// ---------------------------------------------------------------------------
// The stored world
// ---------------------------------------------------------------------------

/// **A plan directory as the binary left it**: every file, by its path under the plan root,
/// with its text — except the replay cache (`.tm/cache/`, derived and rebuilt from the log,
/// the owner's D13) and the undo stack (`.tm/undo.json`, which only pins log lines from
/// folding). Sorted by path.
#[derive(Clone, Debug, PartialEq)]
pub struct GridWorld {
    pub files: Vec<(String, String)>,
}

/// A path the stored world leaves out.
fn derived(rel: &str) -> bool {
    rel.starts_with(".tm/cache/") || rel == ".tm/undo.json"
}

impl GridWorld {
    /// Read a plan directory.
    pub fn read(dir: &Path) -> GridWorld {
        fn walk(root: &Path, dir: &Path, out: &mut Vec<(String, String)>) {
            for e in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
                let e = e.expect("a directory entry");
                let p = e.path();
                if e.file_type().expect("a file type").is_dir() {
                    walk(root, &p, out);
                } else {
                    let rel = p.strip_prefix(root).expect("under the root").to_string_lossy().replace('\\', "/");
                    if !derived(&rel) {
                        let text = std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
                        out.push((rel, text));
                    }
                }
            }
        }
        let mut files = Vec::new();
        walk(dir, dir, &mut files);
        files.sort();
        GridWorld { files }
    }

    /// Write it into an empty plan directory.
    pub fn write(&self, dir: &Path) {
        for (rel, text) in &self.files {
            let p = dir.join(rel);
            if let Some(parent) = p.parent() {
                std::fs::create_dir_all(parent).expect("a directory");
            }
            std::fs::write(&p, text).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
        }
    }

    /// The world as a frozen line carries it: `[[path, text], ..]`.
    pub fn to_json(&self) -> Value {
        Value::Array(self.files.iter().map(|(p, t)| json!([p, t])).collect())
    }

    /// The world a frozen line carries.
    pub fn of_json(v: &Value) -> Result<GridWorld, String> {
        let files = v
            .as_array()
            .ok_or("world is not an array")?
            .iter()
            .map(|f| match (f[0].as_str(), f[1].as_str()) {
                (Some(p), Some(t)) => Ok((p.to_string(), t.to_string())),
                _ => Err(format!("world holds {f}, not a [path, text] pair")),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(GridWorld { files })
    }

    /// One file's text.
    pub fn file(&self, rel: &str) -> Option<&str> {
        self.files.iter().find(|(p, _)| p == rel).map(|(_, t)| t.as_str())
    }

    /// `.tm/log.jsonl`'s text (empty when there is none).
    pub fn log(&self) -> &str {
        self.file(".tm/log.jsonl").unwrap_or_default()
    }

    /// The plan's documents — every `.md` file — as `(path, text)`.
    pub fn docs(&self) -> Vec<(String, String)> {
        self.files.iter().filter(|(p, _)| p.ends_with(".md")).cloned().collect()
    }

    /// The configuration the binary reads: `config.toml`, else the default.
    pub fn cfg(&self) -> Config {
        self.file("config.toml").map_or_else(Config::default, |t| Config::parse(t).expect("the world's config.toml parses"))
    }

    /// The tree the host parses from the documents.
    pub fn tree(&self, cfg: &Config) -> Tree {
        let docs = self.docs();
        let refs: Vec<(&str, &str)> = docs.iter().map(|(p, t)| (p.as_str(), t.as_str())).collect();
        Tree::from_texts(&refs, cfg)
    }

    /// The world as `tm-oracle review` reads it: `{docs, log, config}`.
    pub fn oracle_world(&self) -> Value {
        json!({
            "docs": self.docs().iter().map(|(p, t)| json!([p, t])).collect::<Vec<_>>(),
            "log": self.log(),
            "config": self.file("config.toml"),
        })
    }
}

// ---------------------------------------------------------------------------
// The binary
// ---------------------------------------------------------------------------

/// One run of the shipped binary in `dir` at `now`: `(exit code, stdout, stderr)`.
pub fn tm_run(dir: &Path, now: &str, args: &[&str]) -> (i32, String, String) {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_tm"))
        .arg("--dir")
        .arg(dir)
        .arg("--now")
        .arg(now)
        .args(args)
        .output()
        .expect("run tm");
    (
        out.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

/// The kernel's day number of a date: days since 0001-01-01 (`Cal`'s origin, day 0).
pub fn kernel_day(d: NaiveDate) -> i64 {
    i64::from(d.num_days_from_ce()) - 1
}

/// **What the binary answers when the week is reviewed** over a stored world.
#[derive(Clone, Debug)]
pub struct Reviewed {
    /// `review.heat` of `tm --json review week --date <date>`.
    pub heat: Value,
    /// The log after the review — the log the binary read, its housekeeping included.
    pub log_after: String,
    /// Whether the binary's replay cache sealed the week: the checkpoint's ledger day is past
    /// the week's Sunday and its manifest names a sealed month (`cli_week_cut.rs`' test).
    pub sealed: bool,
}

/// **Review the week holding `date` at `at`, with the shipped binary**, on a fresh copy of
/// `world` in a temporary directory — no replay cache and no undo stack, as stored.
pub fn review(world: &GridWorld, date: &str, at: &str) -> Result<Reviewed, String> {
    let tmp = tempfile::TempDir::new().map_err(|e| e.to_string())?;
    let dir = tmp.path().join("plan");
    world.write(&dir);
    review_in(&dir, date, at)
}

/// [`review`] in a plan directory already on disk.
pub fn review_in(dir: &Path, date: &str, at: &str) -> Result<Reviewed, String> {
    let (code, out, err) = tm_run(dir, at, &["--json", "review", "week", "--date", date]);
    if code != 0 {
        return Err(format!("tm review week --date {date} at {at} exited {code}: {err}{out}"));
    }
    let doc: Value = serde_json::from_str(&out).map_err(|e| format!("the review is not JSON ({e}): {out}"))?;
    let heat = doc["review"]["heat"].clone();
    if !heat.is_array() {
        return Err(format!("the review carries no heat: {doc}"));
    }
    let log_after = std::fs::read_to_string(dir.join(".tm/log.jsonl")).unwrap_or_default();
    let sunday = NaiveDate::parse_from_str(date, "%Y-%m-%d")
        .map(|d| d + Duration::days(6 - i64::from(d.weekday().num_days_from_monday())))
        .map_err(|e| format!("{date}: {e}"))?;
    let ckpt: Value = std::fs::read_to_string(dir.join(".tm/cache/replay/ckpt.json"))
        .ok()
        .and_then(|t| serde_json::from_str(&t).ok())
        .unwrap_or(Value::Null);
    let sealed = ckpt["meta"]["ledgerDay"].as_i64().is_some_and(|l| l > kernel_day(sunday))
        && ckpt["manifest"].as_object().is_some_and(|m| !m.is_empty());
    Ok(Reviewed { heat, log_after, sealed })
}

// ---------------------------------------------------------------------------
// How a world is built: steps
// ---------------------------------------------------------------------------

/// **One step of a world's construction**, as a frozen line records it: a verb run by the
/// shipped binary at an instant (exit code recorded, so a refusal stays a refusal), a file
/// removed, or text appended to a plan file.
#[derive(Clone, Debug, PartialEq)]
pub enum Step {
    /// `tm --now <at> <args..>`, and the exit code it gave.
    Run { at: String, args: Vec<String>, code: i32 },
    /// A file removed (`.tm/undo.json`, as `cli_week_cut.rs` removes it to let the week seal).
    Rm(String),
    /// Text appended to a plan file (a calendar wall).
    Append(String, String),
}

impl Step {
    pub fn run(at: &str, args: &[&str]) -> Step {
        Step::Run { at: at.to_string(), args: args.iter().map(|a| (*a).to_string()).collect(), code: 0 }
    }

    pub fn to_json(&self) -> Value {
        match self {
            Step::Run { at, args, code } => json!({"at": at, "args": args, "code": code}),
            Step::Rm(p) => json!({"rm": p}),
            Step::Append(p, t) => json!({"append": p, "text": t}),
        }
    }

    pub fn of_json(v: &Value) -> Result<Step, String> {
        if let Some(p) = v["rm"].as_str() {
            return Ok(Step::Rm(p.to_string()));
        }
        if let (Some(p), Some(t)) = (v["append"].as_str(), v["text"].as_str()) {
            return Ok(Step::Append(p.to_string(), t.to_string()));
        }
        let at = v["at"].as_str().ok_or_else(|| format!("a step {v} names no instant"))?.to_string();
        let args = v["args"]
            .as_array()
            .ok_or_else(|| format!("a step {v} has no args"))?
            .iter()
            .map(|a| a.as_str().map(str::to_string).ok_or_else(|| format!("an arg {a}")))
            .collect::<Result<Vec<_>, _>>()?;
        let code = v["code"].as_i64().and_then(|c| i32::try_from(c).ok()).ok_or_else(|| format!("a step {v} has no code"))?;
        Ok(Step::Run { at, args, code })
    }
}

/// The `plan-basic` fixture every world starts from (`cli_common::Tm::new`'s).
pub fn fixture_dir() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-core/tests/fixtures/plan-basic")
}

fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).expect("a directory");
    for e in std::fs::read_dir(from).expect("the fixture") {
        let e = e.expect("an entry");
        let t = to.join(e.file_name());
        if e.file_type().expect("a type").is_dir() {
            copy_dir(&e.path(), &t);
        } else {
            std::fs::copy(e.path(), &t).expect("a copy");
        }
    }
}

/// **Run `steps` over a fresh copy of `plan-basic` in `dir`**, recording each verb's exit
/// code as it runs (a `Step::Run`'s own `code` is overwritten with what the binary gave).
pub fn run_steps(dir: &Path, steps: &[Step]) -> Vec<Step> {
    copy_dir(&fixture_dir(), dir);
    steps
        .iter()
        .map(|s| match s {
            Step::Run { at, args, .. } => {
                let refs: Vec<&str> = args.iter().map(String::as_str).collect();
                let (code, _, _) = tm_run(dir, at, &refs);
                Step::Run { at: at.clone(), args: args.clone(), code }
            }
            Step::Rm(p) => {
                let _ = std::fs::remove_file(dir.join(p));
                s.clone()
            }
            Step::Append(p, t) => {
                let path = dir.join(p);
                let mut text = std::fs::read_to_string(&path).unwrap_or_default();
                text.push_str(t);
                std::fs::write(&path, text).expect("an appended plan file");
                s.clone()
            }
        })
        .collect()
}

/// **Build a frozen world** the way a frozen line's world was built: the steps over
/// `plan-basic`, the derived cache and the undo stack removed, then ONE review of the week at
/// `at` — whose housekeeping (an automatic close, D61's marks of a meeting a running block
/// passed) is part of the world the fork is asked about — and the world read back. Returns the
/// world and the steps with their exit codes.
pub fn build(steps: &[Step], date: &str, at: &str) -> Result<(GridWorld, Vec<Step>), String> {
    let tmp = tempfile::TempDir::new().map_err(|e| e.to_string())?;
    let dir = tmp.path().join("plan");
    let ran = run_steps(&dir, steps);
    let _ = std::fs::remove_dir_all(dir.join(".tm/cache"));
    let _ = std::fs::remove_file(dir.join(".tm/undo.json"));
    review_in(&dir, date, at)?;
    Ok((GridWorld::read(&dir), ran))
}

// ---------------------------------------------------------------------------
// The grid tests' own worlds
// ---------------------------------------------------------------------------

/// **A world one of the grid tests builds**, named: its steps, and the review the test asks.
#[derive(Clone, Debug)]
pub struct CliWorld {
    pub name: &'static str,
    /// The test that builds it.
    pub from: &'static str,
    pub steps: Vec<Step>,
    pub date: &'static str,
    pub at: &'static str,
}

const WAKE: [&str; 4] = ["wake", "06:05", "--slept", "8h"];
const START: [&str; 4] = ["start", "^t4", "--energy", "4"];

/// **The worlds `cli_week_grid.rs` and `cli_week_cut.rs` build**, by the same verbs at the
/// same instants (each test's own code is the reference; `fork_week_grid.rs`'
/// `the_cli_worlds_draw_what_the_grid_tests_assert` holds each to the cells its test pins).
pub fn cli_worlds() -> Vec<CliWorld> {
    let meeting = vec![
        Step::run("2026-09-07T06:05:00-05:00", &WAKE),
        Step::run("2026-09-07T12:00:00-05:00", &START),
        Step::run("2026-09-07T13:20:00-05:00", &["now"]),
        Step::run("2026-09-07T14:10:00-05:00", &["now"]),
    ];
    let straddle = vec![
        Step::run("2026-09-07T06:05:00-05:00", &WAKE),
        Step::run("2026-09-07T12:00:00-05:00", &START),
        Step::run("2026-09-07T12:40:00-05:00", &["pause"]),
        Step::run("2026-09-07T14:00:00-05:00", &["pause"]),
    ];
    let plain = vec![
        Step::run("2026-09-07T06:05:00-05:00", &WAKE),
        Step::run("2026-09-07T09:00:00-05:00", &START),
        Step::run("2026-09-07T09:10:00-05:00", &["pause"]),
        Step::run("2026-09-07T09:30:00-05:00", &["pause"]),
    ];
    let week = vec![
        Step::run("2026-09-07T06:05:00-05:00", &WAKE),
        Step::run("2026-09-07T12:00:00-05:00", &START),
        Step::run("2026-09-07T13:20:00-05:00", &["now"]),
        Step::run("2026-09-07T14:00:00-05:00", &["now"]),
        Step::run("2026-09-07T14:10:00-05:00", &["pause"]),
        Step::run("2026-09-07T14:25:00-05:00", &["pause"]),
        Step::run("2026-09-07T14:40:00-05:00", &["--json", "plan"]),
        Step::run("2026-09-07T15:00:00-05:00", &["done"]),
        Step::run("2026-09-08T06:05:00-05:00", &WAKE),
        Step::run("2026-09-08T09:00:00-05:00", &START),
        Step::run("2026-09-08T09:10:00-05:00", &["pause"]),
        Step::run("2026-09-08T09:30:00-05:00", &["pause"]),
        Step::run("2026-09-08T10:00:00-05:00", &["interrupt"]),
        Step::run("2026-09-08T10:15:00-05:00", &["resume"]),
        Step::run("2026-09-08T10:30:00-05:00", &["--json", "plan"]),
        Step::run("2026-09-08T11:00:00-05:00", &["done"]),
    ];
    let mut sealed = week.clone();
    sealed.extend([
        Step::run("2026-09-09T09:00:00-05:00", &["--json", "review", "week", "--date", "2026-09-07"]),
        Step::Rm(".tm/undo.json".to_string()),
        Step::run("2026-09-16T06:05:00-05:00", &WAKE),
        Step::run("2026-09-16T09:00:00-05:00", &START),
        Step::run("2026-09-16T09:30:00-05:00", &["done"]),
        Step::Rm(".tm/undo.json".to_string()),
    ]);
    let midnight = vec![
        Step::Append(
            "calendar/2026-W37.md".to_string(),
            "- [ ] 3 Late call            at:2026-09-08T23:30/2026-09-09T00:30 ^g9\n".to_string(),
        ),
        Step::run("2026-09-08T06:05:00-05:00", &WAKE),
        Step::run("2026-09-08T23:00:00-05:00", &START),
        Step::run("2026-09-08T23:40:00-05:00", &["now"]),
        Step::run("2026-09-09T00:40:00-05:00", &["now"]),
        Step::run("2026-09-09T00:50:00-05:00", &["done"]),
    ];
    vec![
        CliWorld {
            name: "cli/meeting",
            from: "cli_week_grid.rs: a_meetings_pause_is_the_wall_in_the_week_grid",
            steps: meeting,
            date: "2026-09-07",
            at: "2026-09-07T14:20:00-05:00",
        },
        CliWorld {
            name: "cli/straddle",
            from: "cli_week_grid.rs: a_typed_pause_that_straddles_the_meeting_is_a_pause_outside_it",
            steps: straddle,
            date: "2026-09-07",
            at: "2026-09-07T14:10:00-05:00",
        },
        CliWorld {
            name: "cli/plain",
            from: "cli_week_grid.rs: a_pause_no_wall_touches_is_a_pause_in_the_week_grid",
            steps: plain,
            date: "2026-09-07",
            at: "2026-09-07T09:40:00-05:00",
        },
        CliWorld {
            name: "cli/week",
            from: "cli_week_cut.rs: the_grid_is_the_plans_cut_on_every_day_of_the_week (Wednesday)",
            steps: week,
            date: "2026-09-07",
            at: "2026-09-09T09:00:00-05:00",
        },
        CliWorld {
            name: "cli/week-sealed",
            from: "cli_week_cut.rs: the_grid_is_the_plans_cut_on_every_day_of_the_week (the Thursday after, sealed)",
            steps: sealed,
            date: "2026-09-07",
            at: "2026-09-17T09:00:00-05:00",
        },
        CliWorld {
            name: "cli/midnight",
            from: "cli_week_cut.rs: a_pause_past_midnight_is_cut_by_its_days_walls",
            steps: midnight,
            date: "2026-09-07",
            at: "2026-09-09T09:00:00-05:00",
        },
    ]
}

// ---------------------------------------------------------------------------
// Generated weeks
// ---------------------------------------------------------------------------

/// The generated weeks' ChaCha seed text (the class draw's convention).
pub const WEEK_SEED: &str = "W-40 track H weeks, gap 3718";

/// How many draws of [`WEEK_SEED`] the frozen file holds.
pub const WEEK_DRAWS: usize = 32;

/// **The midnight weeks' seed** — draws whose Wednesday holds the one shape P63 and the
/// campaign's D77 call read differently (README gaps 3620 and 3718): a pause typed before a
/// calendar wall that runs past local midnight, and ended after midnight inside it. The census
/// draw reaches it on one week in 32 (Monday's and Tuesday's blocks end before midnight, see
/// [`week_steps`]), so it is drawn on purpose, as the class draw draws a targeted class.
pub const MIDNIGHT_SEED: &str = "W-40 track H midnight weeks, gap 3718";

/// How many draws of [`MIDNIGHT_SEED`] the frozen file holds.
pub const MIDNIGHT_DRAWS: usize = 8;

/// The three days a generated week runs a block on, and the Thursday it is reviewed.
pub const WEEK_DAYS: [&str; 4] = ["2026-09-07", "2026-09-08", "2026-09-09", "2026-09-10"];

/// The instant every generated week is reviewed at: Thursday 21:00 (the census's).
pub const WEEK_AT: &str = "2026-09-10T21:00:00-05:00";

/// The verbs a day's block passes through, weighted as the census drew them.
pub const VERBS: [&str; 7] = ["pause", "pause", "now", "now", "interrupt", "resume", "plan"];

/// **One generated week**: the calendar walls added (day `0..3`, start minute, length) and,
/// for each of the three days, the block's start minute, the verbs it passes through (minutes
/// after the previous one, an index into [`VERBS`]) and the minutes from the last verb to `done`.
#[derive(Clone, Debug, PartialEq)]
pub struct WeekDraw {
    pub index: usize,
    pub walls: Vec<(usize, u32, u32)>,
    pub days: Vec<(u32, Vec<(u32, usize)>, u32)>,
}

/// **The week draw from `seed`** — W-39 track T's census generator, seeded as the class draw
/// is: walls on Monday to Wednesday, half of them starting between 08:00 and 20:00 and half
/// between 23:00 and 23:50 (so many cross midnight), 20 to 90 minutes long; on each day a block
/// started half the time between 08:00 and 20:00 and half between 22:00 and 23:50, two to
/// seven verbs 3 to 40 minutes apart, and `done` 3 to 60 minutes after the last.
///
/// With `midnight` (the [`MIDNIGHT_SEED`] draws) Wednesday is drawn into the one shape the
/// census reaches rarely: one more wall on Wednesday from 23:05–23:50 for an hour or an hour
/// and a half, so it runs past local midnight; the block started 22:00–22:40; a `pause` 3–20
/// minutes later, before the wall begins (so D61 logs nothing at it: the timer is already
/// stopped); and the next `pause` 120–150 minutes after that, past midnight and inside the wall
/// — then up to three of the census's own verbs.
pub fn week_draws(seed: &str, midnight: bool) -> impl Iterator<Item = WeekDraw> {
    let mut bytes = [b' '; 32];
    for (d, s) in bytes.iter_mut().zip(seed.bytes()) {
        *d = s;
    }
    let mut runner = TestRunner::new_with_rng(ProptestConfig::default(), TestRng::from_seed(RngAlgorithm::ChaCha, &bytes));
    let wall_s = (
        0usize..3,
        prop_oneof![1 => 8 * 60u32..=20 * 60, 1 => 23 * 60u32..=23 * 60 + 50],
        prop::sample::select(vec![20u32, 30, 45, 60, 90]),
    );
    let walls_s = prop::collection::vec(wall_s, if midnight { 1..=3 } else { 1..=4 });
    let day_s = (
        prop_oneof![1 => 8 * 60u32..=20 * 60, 1 => 22 * 60u32..=23 * 60 + 50],
        prop::collection::vec((3u32..=40, 0usize..VERBS.len()), 2..=7),
        3u32..=60,
    );
    let days_s = prop::collection::vec(day_s, 3..=3);
    let late_wall_s = (23 * 60 + 5u32..=23 * 60 + 50, prop::sample::select(vec![60u32, 90]));
    let late_day_s = (
        22 * 60u32..=22 * 60 + 40,
        3u32..=20,
        120u32..=150,
        prop::collection::vec((3u32..=40, 0usize..VERBS.len()), 0..=3),
    );
    (0usize..).map(move |index| {
        let mut walls = walls_s.new_tree(&mut runner).expect("walls").current();
        let mut days = days_s.new_tree(&mut runner).expect("days").current();
        if midnight {
            let (lo, len) = late_wall_s.new_tree(&mut runner).expect("a late wall").current();
            let (start, g1, g2, rest) = late_day_s.new_tree(&mut runner).expect("a late day").current();
            walls.push((2, lo, len));
            let pause = VERBS.iter().position(|v| *v == "pause").expect("pause is a verb");
            let mut verbs = vec![(g1, pause), (g2, pause)];
            verbs.extend(rest);
            days[2].0 = start;
            days[2].1 = verbs;
        }
        WeekDraw { index, walls, days }
    })
}

/// `HH:MM` of a minute of the day.
fn hm(m: u32) -> String {
    format!("{:02}:{:02}", m / 60, m % 60)
}

/// The instant `m` minutes after midnight of `WEEK_DAYS[day]` (past midnight onto the next).
fn stamp(day: usize, m: u32) -> String {
    let (d, m) = (day + (m / 1440) as usize, m % 1440);
    format!("{}T{}:00-05:00", WEEK_DAYS[d.min(WEEK_DAYS.len() - 1)], hm(m))
}

/// The last minute a day's verbs may reach: Monday's and Tuesday's block is `done` before
/// local midnight, so no generated `done` is logged across midnight — what a block's worked
/// minutes read there is the owner's D75 (README gap 3715), which another track changes this
/// run, and a frozen world must not move with it; Wednesday's may run past midnight, and is
/// then left running (no verb crosses into Thursday's wake either: none is drawn).
const DAY_LAST: u32 = 23 * 60 + 59;

/// **The steps a week draw runs**: its walls appended to the week's calendar, then each day's
/// `wake`, `start`, verbs and `done`. On Monday and Tuesday only the verbs before [`DAY_LAST`]
/// run and `done` follows the last of them by its drawn gap, at [`DAY_LAST`] at the latest; on
/// Wednesday the verbs run as drawn, past midnight too, and `done` only when it falls before
/// midnight — after it the block is left running.
pub fn week_steps(d: &WeekDraw) -> Vec<Step> {
    let mut steps = Vec::new();
    let mut cal = String::new();
    for (k, (day, lo, len)) in d.walls.iter().enumerate() {
        let hi = lo + len;
        let end = if hi < 1440 { hm(hi) } else { stamp(*day, hi)[..16].to_string() };
        cal.push_str(&format!("- [ ] 3 Wall {k} at:{}T{}/{end} ^w{k}\n", WEEK_DAYS[*day], hm(*lo)));
    }
    steps.push(Step::Append("calendar/2026-W37.md".to_string(), cal));
    for (day, (start, verbs, done)) in d.days.iter().enumerate() {
        steps.push(Step::run(&stamp(day, 6 * 60 + 5), &WAKE));
        steps.push(Step::run(&stamp(day, *start), &START));
        let last_day = day + 1 == d.days.len();
        let mut t = *start;
        for (gap, v) in verbs {
            if !last_day && t + gap >= DAY_LAST {
                break;
            }
            t += gap;
            steps.push(Step::run(&stamp(day, t), &[VERBS[*v]]));
        }
        let end = if last_day { t + done } else { (t + done).min(DAY_LAST) };
        if end <= DAY_LAST {
            steps.push(Step::run(&stamp(day, end), &["done"]));
        }
    }
    steps
}

// ---------------------------------------------------------------------------
// The fork's grid, and P63's departure by its property
// ---------------------------------------------------------------------------

/// The kernel's styles a heat cell counts (`review::Style`, `HEAT_STYLES`): the fork's seven
/// in the same order, and `wall` eighth.
pub const STYLES: [&str; 8] = ["block", "break", "routine", "interrupt", "pause", "leak", "idle", "wall"];
const PAUSE: usize = 4;
const WALL: usize = 7;

/// The top of `t`'s clock hour (`review.rs`' `hour_start`, which the fork's `heat_of` walks by).
fn hour_start(t: DateTime<Tz>) -> DateTime<Tz> {
    let secs = i64::from(t.minute()) * 60 + i64::from(t.second());
    let nanos = i64::from(t.nanosecond()) % 1_000_000_000;
    t - Duration::seconds(secs) - Duration::nanoseconds(nanos)
}

/// **The minutes one piece `[a, b)` puts in each clock hour**, as `review::heat_of` counts a
/// piece — walked hour by hour in absolute time, whole minutes per stretch. `(hour, minutes)`.
pub fn hour_minutes(a: DateTime<Tz>, b: DateTime<Tz>) -> Vec<(usize, u64)> {
    let mut out = Vec::new();
    let mut cursor = a;
    while cursor < b {
        let hour = cursor.hour() as usize;
        let next = hour_start(cursor) + Duration::hours(1);
        let stop = next.max(cursor).min(b);
        let min = stop.signed_duration_since(cursor).num_minutes().max(0) as u64;
        out.push((hour, min));
        if stop <= cursor {
            break;
        }
        cursor = stop;
    }
    out
}

/// Maximal pieces of `[a, b)` that no span in `spans` covers, in order.
fn cut(a: DateTime<Tz>, b: DateTime<Tz>, spans: &[(DateTime<Tz>, DateTime<Tz>)]) -> Vec<(DateTime<Tz>, DateTime<Tz>)> {
    let mut pieces = vec![(a, b)];
    for (lo, hi) in spans {
        pieces = pieces
            .into_iter()
            .flat_map(|(x, y)| {
                if *hi <= x || y <= *lo {
                    return vec![(x, y)];
                }
                let mut left = Vec::new();
                if x < *lo {
                    left.push((x, *lo));
                }
                if *hi < y {
                    left.push((*hi, y));
                }
                left
            })
            .collect();
    }
    pieces.retain(|(x, y)| x < y);
    pieces
}

/// **Which walls cut a Pause, by the registered reading of P63.**
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P63Reading {
    /// P63 as W-39 track T registered it: the walls of the day whose record holds the Pause,
    /// clipped to that day, cut the Pause clipped to `[that day's local midnight, now]`; past
    /// midnight no wall reaches, so the fork's `pause` stands there.
    RecordDay,
    /// The campaign's D77 call on README gap 3620 ("a pause crossing local midnight is cut by
    /// EACH calendar day's own walls", P63 restated), which another track builds this run.
    /// When it lands, [`P63_READING`] becomes this and the lines it moves are re-blessed under
    /// D64(a), naming P63 (`fork_week_grid.rs`' bless, `TM_GRID_BLESS=p63`).
    EachDay,
}

/// The reading the comparison holds the binary to.
/// **`P63Reading::EachDay` since the W-40 land step**: track T's D77 cut (`GridCut.daySpans`) is merged,
/// and the lines it moves were re-blessed naming P63 (README, W-40 land block).
pub const P63_READING: P63Reading = P63Reading::EachDay;

/// **The cells P63 names** — the comparand's departure from fork 4748911's grid, by the
/// property P63's row states (README gaps 3432, 3528; `GridCut.segSpans`): for every Pause of
/// day `d`'s record (`pauses`, the fork's own segments, `[date, start, end, id]`), its clip to
/// `[local midnight of d, now]` is drawn — the stretches a wall covers as `wall`, the rest as
/// `pause` — and nothing outside the clip is drawn, where the fork drew the whole Pause as
/// `pause`. A wall of a day is the host's reader of fork `Ctx::walls_on` (`Tree::walls_on`:
/// open `Interval` items over the day, the start moved back by `buffer:`), clipped to the day.
/// `(date, hour, Δpause, Δwall)` for every cell the departure moves, in order.
pub fn p63_cells(world: &GridWorld, pauses: &Value, now: DateTime<Tz>, reading: P63Reading) -> Result<Vec<(String, usize, i64, i64)>, String> {
    let cfg = world.cfg();
    let tz = cfg.tz;
    let tree = world.tree(&cfg);
    let midnight = |d: NaiveDate| local_dt(tz, d, NaiveTime::MIN);
    let walls_of = |d: NaiveDate| -> Vec<(DateTime<Tz>, DateTime<Tz>)> {
        let (lo, hi) = (midnight(d), midnight(d + Duration::days(1)));
        tree.walls_on(tz, d).into_iter().map(|(a, b)| (a.max(lo), b.min(hi))).filter(|(a, b)| a < b).collect()
    };
    let mut delta: BTreeMap<(String, usize), (i64, i64)> = BTreeMap::new();
    for p in pauses.as_array().ok_or("`pauses` is not an array")? {
        let date = p[0].as_str().ok_or("a pause's date")?;
        let d = NaiveDate::parse_from_str(date, "%Y-%m-%d").map_err(|e| format!("a pause's date {date}: {e}"))?;
        let at = |k: usize| -> Result<DateTime<Tz>, String> {
            p[k].as_str()
                .and_then(|s| DateTime::parse_from_rfc3339(s).ok())
                .map(|t| t.with_timezone(&tz))
                .ok_or_else(|| format!("a pause's instant {}", p[k]))
        };
        let (s, e) = (at(1)?, at(2)?);
        if e <= s {
            continue;
        }
        let (a, b) = (s.max(midnight(d)), e.min(now));
        let walls: Vec<(DateTime<Tz>, DateTime<Tz>)> = match reading {
            P63Reading::RecordDay => walls_of(d),
            P63Reading::EachDay => {
                let mut w = Vec::new();
                let mut day = d;
                while a < b && midnight(day) < b {
                    w.extend(walls_of(day));
                    day += Duration::days(1);
                }
                w
            }
        };
        let kept = if a < b { cut(a, b, &walls) } else { Vec::new() };
        let covered = if a < b { cut(a, b, &kept) } else { Vec::new() };
        let mut add = |(h, m): (usize, u64), pause: i64, wall: i64| {
            let cell = delta.entry((date.to_string(), h)).or_default();
            cell.0 += pause * m as i64;
            cell.1 += wall * m as i64;
        };
        for x in hour_minutes(s, e) {
            add(x, -1, 0);
        }
        for (x, y) in kept {
            for c in hour_minutes(x, y) {
                add(c, 1, 0);
            }
        }
        for (x, y) in covered {
            for c in hour_minutes(x, y) {
                add(c, 0, 1);
            }
        }
    }
    Ok(delta.into_iter().filter(|(_, (p, w))| *p != 0 || *w != 0).map(|((d, h), (p, w))| (d, h, p, w)).collect())
}

/// The named cells as a frozen line spells them: `[[date, hour, Δpause, Δwall], ..]`.
pub fn cells_json(cells: &[(String, usize, i64, i64)]) -> Value {
    Value::Array(cells.iter().map(|(d, h, p, w)| json!([d, h, p, w])).collect())
}

/// The named cells a frozen line carries.
pub fn cells_of(v: &Value) -> Result<Vec<(String, usize, i64, i64)>, String> {
    v.as_array()
        .ok_or("the named cells are not an array")?
        .iter()
        .map(|c| match (c[0].as_str(), c[1].as_u64(), c[2].as_i64(), c[3].as_i64()) {
            (Some(d), Some(h), Some(p), Some(w)) => Ok((d.to_string(), h as usize, p, w)),
            _ => Err(format!("a named cell {c}")),
        })
        .collect()
}

/// **The comparand's grid**: the fork's seven-style heat, each cell widened to the kernel's
/// eight (`wall` 0), with the named cells moved. `Err` when a move would take a cell below 0
/// (a named cell the fork's grid cannot hold).
pub fn comparand(fork_heat: &Value, cells: &[(String, usize, i64, i64)]) -> Result<Vec<(String, Vec<[i64; 8]>, Value, Value)>, String> {
    let mut rows = Vec::new();
    for day in fork_heat.as_array().ok_or("the fork's heat is not an array")? {
        let date = day["date"].as_str().ok_or("a fork row's date")?.to_string();
        let mut hours = Vec::new();
        for h in day["hours"].as_array().ok_or("a fork row's hours")? {
            let c = h.as_array().ok_or("a fork cell")?;
            if c.len() != 7 {
                return Err(format!("{date}: a fork cell holds {} styles, not the fork's seven", c.len()));
            }
            let mut cell = [0i64; 8];
            for (i, v) in c.iter().enumerate() {
                cell[i] = v.as_i64().ok_or("a fork minute count")?;
            }
            hours.push(cell);
        }
        rows.push((date, hours, day["blocks_done"].clone(), day["block_min"].clone()));
    }
    for (d, h, p, w) in cells {
        let row = rows.iter_mut().find(|r| &r.0 == d).ok_or_else(|| format!("a named cell on {d}, which the week does not hold"))?;
        let cell = row.1.get_mut(*h).ok_or_else(|| format!("a named cell at hour {h}"))?;
        cell[PAUSE] += p;
        cell[WALL] += w;
        if cell[PAUSE] < 0 || cell[WALL] < 0 {
            return Err(format!("the named cell {d} hour {h} takes the fork's grid below zero"));
        }
    }
    Ok(rows)
}

/// **Compare the binary's heat with the comparand**, cell by cell: every difference named by
/// its day, hour and style. `who` names the line.
pub fn compare_heat(who: &str, binary: &Value, want: &[(String, Vec<[i64; 8]>, Value, Value)]) -> Vec<String> {
    let mut out = Vec::new();
    let rows = binary.as_array().map(Vec::as_slice).unwrap_or_default();
    if rows.len() != want.len() {
        out.push(format!("{who}: the binary's grid holds {} day(s), the fork's {}", rows.len(), want.len()));
    }
    for (row, (date, hours, done, min)) in rows.iter().zip(want) {
        if row["date"].as_str() != Some(date.as_str()) {
            out.push(format!("{who}: the binary's row {} where the fork's is {date}", row["date"]));
            continue;
        }
        if row["blocks_done"] != *done || row["block_min"] != *min {
            out.push(format!(
                "{who} {date}: blocks_done/block_min {}/{} against the fork's {done}/{min}",
                row["blocks_done"], row["block_min"]
            ));
        }
        let cells = row["hours"].as_array().map(Vec::as_slice).unwrap_or_default();
        if cells.len() != hours.len() {
            out.push(format!("{who} {date}: {} hours against the fork's {}", cells.len(), hours.len()));
        }
        for (h, (cell, want)) in cells.iter().zip(hours).enumerate() {
            let got: Vec<i64> = cell.as_array().map(Vec::as_slice).unwrap_or_default().iter().map(|v| v.as_i64().unwrap_or(-1)).collect();
            if got.len() != STYLES.len() {
                out.push(format!("{who} {date} hour {h:02}: the binary's cell holds {} styles", got.len()));
                continue;
            }
            for (s, name) in STYLES.iter().enumerate() {
                if got[s] != want[s] {
                    out.push(format!("{who} {date} hour {h:02} `{name}`: the binary draws {} and the comparand {}", got[s], want[s]));
                }
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// The frozen file
// ---------------------------------------------------------------------------

/// The frozen week grids, one JSON line per world.
pub const FROZEN_GRID: &str = "fork-4748911-week-grid.jsonl";

/// Where they live.
pub fn frozen_path() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(FROZEN_GRID)
}

/// The frozen lines, in file order; a name carried twice FAILS ([`lines_of`]).
pub fn frozen_lines() -> Vec<Value> {
    let path = frozen_path();
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e} — see support/forkgrid.rs", path.display()));
    lines_of(&text)
}

/// **A frozen grid file's text, read**: one JSON line per world, blank lines skipped, every
/// line naming itself — and a name carried twice FAILS, so a line cannot be shadowed by a second
/// one of its name that the comparison would also read.
pub fn lines_of(text: &str) -> Vec<Value> {
    let mut seen = std::collections::BTreeSet::new();
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Value = serde_json::from_str(l).expect("a frozen grid line is JSON");
            let name = v["name"].as_str().expect("a frozen grid line names itself").to_string();
            assert!(seen.insert(name.clone()), "two frozen grid lines named `{name}`");
            v
        })
        .collect()
}

/// The instant a line reviews at, in the world's zone.
pub fn line_at(line: &Value, tz: Tz) -> Result<DateTime<Tz>, String> {
    line["at"]
        .as_str()
        .and_then(|s| DateTime::parse_from_rfc3339(s).ok())
        .map(|t| t.with_timezone(&tz))
        .ok_or_else(|| format!("a line's `at` {}", line["at"]))
}

/// **Compare one frozen line with the shipped binary**, by value. `reading` is the P63 reading
/// the named cells are recomputed by (the comparison's own [`P63_READING`]). Every difference,
/// by name; empty when the binary draws the comparand exactly.
pub fn compare_line(line: &Value, reading: P63Reading) -> Vec<String> {
    let who = line["name"].as_str().unwrap_or("<unnamed>").to_string();
    let world = match GridWorld::of_json(&line["world"]) {
        Ok(w) => w,
        Err(e) => return vec![format!("{who}: {e}")],
    };
    let tz = world.cfg().tz;
    let (Some(date), Ok(at)) = (line["date"].as_str(), line_at(line, tz)) else {
        return vec![format!("{who}: no review date or instant")];
    };
    let mut out = Vec::new();
    let named = match cells_of(&line["p63"]) {
        Ok(c) => c,
        Err(e) => return vec![format!("{who}: {e}")],
    };
    match p63_cells(&world, &line["fork"]["pauses"], at, reading) {
        Ok(rule) if rule != named => out.push(format!(
            "{who}: the named cells are not P63's rule over the fork's pauses — rule {} against named {}",
            cells_json(&rule),
            cells_json(&named)
        )),
        Ok(_) => {}
        Err(e) => out.push(format!("{who}: P63's rule: {e}")),
    }
    let want = match comparand(&line["fork"]["heat"], &named) {
        Ok(w) => w,
        Err(e) => return vec![format!("{who}: {e}")],
    };
    match review(&world, date, line["at"].as_str().unwrap_or_default()) {
        Err(e) => out.push(format!("{who}: {e}")),
        Ok(r) => {
            out.extend(compare_heat(&who, &r.heat, &want));
            if r.log_after != world.log() {
                out.push(format!("{who}: the review appended to the log, so the fork read another log than the binary"));
            }
            if Some(r.sealed) != line["sealed"].as_bool() {
                out.push(format!("{who}: the week sealed {} where the line says {}", r.sealed, line["sealed"]));
            }
        }
    }
    out
}

/// **A frozen line**: its name and provenance, the world, the review, and the two answers.
#[allow(clippy::too_many_arguments)]
pub fn line_of(
    name: &str,
    from: Value,
    steps: &[Step],
    world: &GridWorld,
    date: &str,
    at: &str,
    sealed: bool,
    fork: &Value,
    cells: &[(String, usize, i64, i64)],
) -> Value {
    json!({
        "name": name,
        "from": from,
        "steps": steps.iter().map(Step::to_json).collect::<Vec<_>>(),
        "date": date,
        "at": at,
        "sealed": sealed,
        "world": world.to_json(),
        "fork": fork,
        "p63": cells_json(cells),
    })
}

/// **What a re-bless of one line changed, and whether the owner's D64 allows it** — the
/// grid's form of `forkclass::d64_allows`, over the grid's two answers:
///
/// * a changed WORLD (or provenance) is a re-draw, allowed only with D64(b)'s reason named
///   (`redraw`): the world the steps build moved, so the fork is asked again about the new one;
/// * otherwise `fork` stays BY VALUE — fork 4748911's grid over the same bytes cannot move,
///   and an oracle that answers otherwise is not the fork — and `p63` may move only under
///   D64(a), the re-bless naming P63 (`because`), which the register holds.
///
/// `Ok` names what changed (empty when nothing did).
///
/// **And D64(c), since the owner's D85** (W-42 track C, README gap 4281): `harness` is a corrected
/// HARNESS reading's reason, which the caller has read strictly (`forkclass::harness_of`). Under
/// it the named cells — the one departure a grid line records — may move when every other key of
/// the line, `fork` and the world included, is byte-identical: P63's reading of a world is the
/// harness's, and fork 4748911's grid over the same bytes cannot move.
pub fn rebless_allows(
    old: &Value,
    new: &Value,
    because: &[u32],
    redraw: Option<&str>,
    harness: Option<&str>,
    registered: &std::collections::BTreeSet<u32>,
) -> Result<Vec<String>, String> {
    let who = old["name"].as_str().unwrap_or("<unnamed>");
    let keys = ["name", "from", "steps", "date", "at", "sealed", "world", "fork", "p63"];
    let changed: Vec<String> = keys.iter().filter(|k| old[**k] != new[**k]).map(|k| (*k).to_string()).collect();
    if changed.is_empty() {
        return Ok(changed);
    }
    if harness.is_some_and(|why| !why.trim().is_empty()) {
        let bytes = |v: &Value| serde_json::to_string(v).expect("a value serialises");
        let all: std::collections::BTreeSet<&String> =
            old.as_object().into_iter().flatten().chain(new.as_object().into_iter().flatten()).map(|(k, _)| k).collect();
        let moved: Vec<&String> = all.into_iter().filter(|k| bytes(&old[k.as_str()]) != bytes(&new[k.as_str()])).collect();
        if moved.iter().all(|k| *k == "p63") {
            return Ok(changed);
        }
    }
    let drawn = ["name", "from", "steps", "date", "at", "sealed", "world"];
    if changed.iter().any(|k| drawn.contains(&k.as_str())) {
        return match redraw {
            Some(r) if !r.trim().is_empty() => Ok(changed),
            _ => Err(format!(
                "{who}: `{}` changed — the world the steps build moved, a re-draw the owner's D64(b) allows only with its reason (TM_GRID_BLESS_REDRAW)",
                changed.join("`, `")
            )),
        };
    }
    if changed.iter().any(|k| k == "fork") {
        return Err(format!("{who}: the fork's grid moved over the same world — fork 4748911 does not move; the oracle is not the fork"));
    }
    if !because.contains(&63) || !registered.contains(&63) {
        return Err(format!("{who}: the named cells moved and the re-bless names no registered P63 (D64(a))"));
    }
    Ok(changed)
}
