//! Shared helpers for the `planner_*` integration tests: loading a fixture
//! tree with its `.tm/` state and log, and rendering a [`DayPlan`] as the
//! §4.3-shaped timeline the snapshots pin.
#![allow(dead_code)]

/// The test chokepoint (step R12): every replay here is read through it.
#[path = "../support/replay.rs"]
pub mod chokepoint;

use chrono::{DateTime, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use tm_core::capacity::local_dt;
use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::Replay;
use tm_core::model::Id;
use tm_core::dayplan::{fmt_clock, DayPlan, SegKind, Segment};
use tm_core::store::{MemStore, RuntimeState, Store};
use tm_core::tree::Tree;

pub const TZ: Tz = Tz::America__Chicago;

pub fn fixture_path(name: &str) -> String {
    format!("{}/../tm-core/tests/fixtures/{name}", env!("CARGO_MANIFEST_DIR"))
}

pub fn date(s: &str) -> NaiveDate {
    NaiveDate::parse_from_str(s, "%Y-%m-%d").expect("date")
}

pub fn time(h: u32, m: u32) -> NaiveTime {
    NaiveTime::from_hms_opt(h, m, 0).expect("time")
}

pub fn at(day: &str, h: u32, m: u32) -> DateTime<Tz> {
    local_dt(TZ, date(day), time(h, m))
}

/// A fixture tree with its config, replay and `.tm/state.json`.
pub struct Fixture {
    pub tree: Tree,
    pub cfg: Config,
    pub replay: Replay,
    pub state: RuntimeState,
    pub model: Model,
}

pub fn load(name: &str) -> Fixture {
    load_with_log(name, None)
}

/// The fixture, optionally with a different log than the one on disk (the
/// dynamics tests write their own history).
pub fn load_with_log(name: &str, log_text: Option<&str>) -> Fixture {
    let store = MemStore::from_dir(fixture_path(name)).expect("fixture readable");
    let plan = store.read_tree().expect("tree parses");
    let tree = Tree::build(&plan.files, &plan.config);
    assert!(tree.problems().is_empty(), "{:?}", tree.problems());
    let text = match log_text {
        Some(t) => t.to_string(),
        // The fixture's own log file, read as text like every other test's
        // (a fixture without one has an empty log).
        None => std::fs::read_to_string(format!("{}/.tm/log.jsonl", fixture_path(name)))
            .unwrap_or_default(),
    };
    let warnings = chokepoint::warning_lines_of_text(&text);
    assert!(warnings.is_empty(), "{:?}", warnings);
    let replay = chokepoint::replay_of_text(&text, plan.config.tz);
    let state = store.load_state().expect("state.json parses");
    Fixture {
        tree,
        cfg: plan.config,
        replay,
        state,
        model: Model::default(),
    }
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gap 2722)
/// The fork's planning input for this fixture. The suites that plan with the
/// fork read it; `planner_fixtures.rs`' surviving arm does not, and its
/// `the_fork_half_of_this_suite_is_one_region` holds this file to one region.
impl Fixture {
    pub fn input<'a>(&'a self, state: &'a RuntimeState, now: DateTime<Tz>) -> tm_core::planner::PlanInput<'a> {
        tm_core::planner::PlanInput::new(
            &self.tree,
            &self.replay,
            &self.cfg,
            &self.model,
            state,
            now,
        )
    }
}
// END THE FORK PLANNER

/// The `plan-basic` history the planner tests plan against: eight weeks of
/// laundry, a shower two days ago, and this morning up to `tm arrive`.
///
/// It lives here rather than in `tm-core/tests/fixtures/plan-basic/.tm/log.jsonl`
/// because `horizon_close.rs` copies that fixture and asserts on the whole
/// log file; a shipped history would break it. The two fixtures this
/// milestone adds — `plan-home-day` and `plan-travel-day` — do carry their
/// own `.tm/`.
pub const BASIC_LOG: &str = concat!(
    r#"{"t":"2026-07-06T11:00:00-05:00","ev":"routine","item":"laundry","inst":"2026-07-06","status":"done","actual_min":30}"#,
    "\n",
    r#"{"t":"2026-07-13T11:00:00-05:00","ev":"routine","item":"laundry","inst":"2026-07-13","status":"done","actual_min":30}"#,
    "\n",
    r#"{"t":"2026-07-20T11:00:00-05:00","ev":"routine","item":"laundry","inst":"2026-07-20","status":"done","actual_min":30}"#,
    "\n",
    r#"{"t":"2026-07-27T11:00:00-05:00","ev":"routine","item":"laundry","inst":"2026-07-27","status":"done","actual_min":30}"#,
    "\n",
    r#"{"t":"2026-08-03T11:00:00-05:00","ev":"routine","item":"laundry","inst":"2026-08-03","status":"done","actual_min":30}"#,
    "\n",
    r#"{"t":"2026-08-10T11:00:00-05:00","ev":"routine","item":"laundry","inst":"2026-08-10","status":"done","actual_min":30}"#,
    "\n",
    r#"{"t":"2026-08-17T11:00:00-05:00","ev":"routine","item":"laundry","inst":"2026-08-17","status":"done","actual_min":30}"#,
    "\n",
    r#"{"t":"2026-08-24T11:00:00-05:00","ev":"routine","item":"laundry","inst":"2026-08-24","status":"done","actual_min":30}"#,
    "\n",
    r#"{"t":"2026-08-31T11:00:00-05:00","ev":"routine","item":"laundry","inst":"2026-08-31","status":"done","actual_min":30}"#,
    "\n",
    r##"{"t":"2026-09-05T07:20:00-05:00","ev":"routine","item":"shower","inst":"#1","status":"done","actual_min":20}"##,
    "\n",
    r#"{"t":"2026-09-07T06:05:00-05:00","ev":"wake","slept_min":490,"onset_min":25}"#,
    "\n",
    r#"{"t":"2026-09-07T06:40:00-05:00","ev":"routine","item":"breakfast","inst":"2026-09-07","status":"done","actual_min":30}"#,
    "\n",
    r#"{"t":"2026-09-07T07:00:00-05:00","ev":"arrive","loc":"lounge","window":["07:00","16:00"],"budget":6}"#,
    "\n",
);

/// `.tm/state.json` as `tm arrive` would have left it on 2026-09-07.
pub fn basic_state() -> RuntimeState {
    RuntimeState {
        date: Some(date("2026-09-07")),
        wake: Some(time(6, 5)),
        arrival: Some(time(7, 0)),
        loc: Some("lounge".to_string()),
        window: Some((time(7, 0), time(16, 0))),
        budget: Some(6),
        ..RuntimeState::default()
    }
}

pub fn kind(seg: &Segment) -> String {
    match &seg.kind {
        SegKind::Block => "block".to_string(),
        SegKind::Batch(ids) => format!(
            "batch[{}]",
            ids.iter().map(Id::as_str).collect::<Vec<_>>().join("·")
        ),
        SegKind::Break => "break".to_string(),
        SegKind::Routine => "routine".to_string(),
        SegKind::Wall => "wall".to_string(),
        SegKind::Rest => "rest".to_string(),
        SegKind::Optional => "optional".to_string(),
        SegKind::WindDown => "wind-down".to_string(),
        SegKind::Sleep => "sleep".to_string(),
        SegKind::Lost => "lost".to_string(),
    }
}

pub fn marks(seg: &Segment) -> String {
    let f = &seg.flags;
    let mut s = String::new();
    for (on, mark) in [
        (f.done, "✓"),
        (f.current, "▶"),
        (f.underused, "↓"),
        (f.hot, "⚠"),
        (f.mandatory, "!"),
        (f.deferred, "~"),
    ] {
        if on {
            s.push_str(mark);
        }
    }
    s
}

/// The whole timeline, one line per segment.
pub fn timeline(day: &DayPlan) -> String {
    let mut out = format!(
        "date {} · window {}–{} · budget {}b\n",
        day.date,
        fmt_clock(day.window.0),
        fmt_clock(day.window.1),
        day.budget_blocks,
    );
    for seg in &day.segments {
        out.push_str(&format!(
            "{}-{} {:<10} {:>3} {:<10} {:<4} {}\n",
            fmt_clock(seg.start),
            fmt_clock(seg.end),
            kind(seg),
            seg.energy.map_or("·".to_string(), |e| e.to_string()),
            seg.item.as_ref().map_or("·", Id::as_str),
            marks(seg),
            seg.flags.note.clone().unwrap_or_default(),
        ));
    }
    out
}

/// The §8.2 step 8 diagnostics, as prose.
pub fn diagnostics(day: &DayPlan) -> String {
    let d = &day.diagnostics;
    let ids = |v: &[Id]| {
        if v.is_empty() {
            "·".to_string()
        } else {
            v.iter().map(Id::as_str).collect::<Vec<_>>().join(" ")
        }
    };
    let mut out = String::new();
    out.push_str(&format!(
        "underused      {}\n",
        if d.underused.is_empty() {
            "·".to_string()
        } else {
            d.underused
                .iter()
                .map(|(i, e, c)| format!("{}({e}→{c})", i.as_str()))
                .collect::<Vec<_>>()
                .join(" ")
        }
    ));
    out.push_str(&format!("a_capacity_lost {}m\n", d.a_capacity_lost));
    out.push_str(&format!("hot            {}\n", ids(&d.hot)));
    out.push_str(&format!(
        "impossible     {}\n",
        if d.impossible.is_empty() {
            "·".to_string()
        } else {
            d.impossible
                .iter()
                .map(|(i, s, u)| format!("{}(short {s}m by {u})", i.as_str()))
                .collect::<Vec<_>>()
                .join(" ")
        }
    ));
    out.push_str(&format!(
        "conflicts      {}\n",
        if d.conflicts.is_empty() {
            "·".to_string()
        } else {
            d.conflicts
                .iter()
                .map(|(a, b)| format!("{}×{}", a.as_str(), b.as_str()))
                .collect::<Vec<_>>()
                .join(" ")
        }
    ));
    out.push_str(&format!(
        "blocked        {}\n",
        if d.blocked.is_empty() {
            "·".to_string()
        } else {
            d.blocked
                .iter()
                .map(|(i, deps)| format!("{}({})", i.as_str(), deps.len()))
                .collect::<Vec<_>>()
                .join(" ")
        }
    ));
    out.push_str(&format!("deferred       {}\n", ids(&d.deferred)));
    out.push_str(&format!("waiting        {}\n", ids(&d.waiting)));
    out.push_str(&format!("dropped_tail   {}\n", ids(&d.dropped_tail)));
    out.push_str(&format!(
        "plan_honesty   {}\n",
        d.plan_honesty.map_or("·".to_string(), |h| format!("{h:.2}"))
    ));
    out.push_str(&format!("rest_debt      {}m\n", d.rest_debt_min));
    for n in &d.notes {
        out.push_str(&format!("note           {n}\n"));
    }
    out
}

/// No more than `break_after_blocks` work segments run without a rest of at
/// least `break_min` between them (a break, a routine or a wall all count as
/// rest — `capacity.rs` cuts each free stretch separately).
pub fn assert_break_rule(day: &DayPlan, now: DateTime<Tz>, cfg: &Config) {
    let mut run = 0;
    let mut last_end: Option<DateTime<Tz>> = None;
    for seg in day.segments.iter().filter(|s| s.start >= now) {
        match seg.kind {
            SegKind::Block | SegKind::Batch(_) => {
                // A gap of at least `break_min` is a rest, whatever fills it.
                if last_end.is_some_and(|e| (seg.start - e).num_minutes() >= i64::from(cfg.day.break_min))
                {
                    run = 0;
                }
                run += 1;
                assert!(
                    run <= cfg.day.break_after_blocks,
                    "{run} blocks in a row, no break, at {}:\n{}",
                    seg.start,
                    timeline(day)
                );
                last_end = Some(seg.end);
            }
            SegKind::Break | SegKind::Routine | SegKind::Wall | SegKind::Rest => {
                if seg.minutes() >= cfg.day.break_min {
                    run = 0;
                }
                last_end = Some(seg.end.max(last_end.unwrap_or(seg.end)));
            }
            _ => {}
        }
    }
}
