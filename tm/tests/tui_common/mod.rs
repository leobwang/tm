//! The harness the `tui_today_*` tests share (tm-spec-v1.md §17 M6).
//!
//! `tm` is a binary crate, so an integration test cannot `use tm::…`; the
//! five TUI modules are therefore pulled straight into the test crate with
//! `#[path]`. That works because everything under `tm/src/tui/` except
//! `mod.rs` is pure — it never names `crate::cli`, the terminal or a clock —
//! which is exactly the property M6's "snapshots of each pane" needs.
//!
//! What it builds:
//!
//! * [`fixture`] — the `plan-basic` tree of §4.3 (from
//!   `tm-core/tests/fixtures/plan-basic`), the fixture's own `config.toml`,
//!   a synthetic log matching that day file's `## Log`, and the runtime state
//!   §10.2 would hold at 10:42 with `^t3` running.
//! * [`day_plan`] — a **hand-built** `DayPlan` reproducing §4.3's printed
//!   timeline, so the snapshots do not depend on the planner's exact output.
//! * [`app`] — the two glued together, plus [`app_at`] for another instant
//!   and [`ghost_plan`] for §12.1's ghost row.
//! * [`render`] / [`lines`] — a `TestBackend` frame, and a `Vec<Line>`, as
//!   snapshot text.

#![allow(dead_code)]

#[path = "../../src/tui/theme.rs"]
pub mod theme;

#[path = "../../src/tui/app.rs"]
pub mod app;

#[path = "../../src/tui/daybar.rs"]
pub mod daybar;

#[path = "../../src/tui/prompts.rs"]
pub mod prompts;

#[path = "../../src/tui/today.rs"]
pub mod today;

use std::fs;
use std::path::{Path, PathBuf};

use chrono::{DateTime, FixedOffset, NaiveDate, NaiveTime, TimeZone};
use chrono_tz::Tz;
use ratatui::backend::TestBackend;
use ratatui::text::Line;
use ratatui::Terminal;

use tm_core::config::Config;
use tm_core::log::{Event, Log, LogEntry, Replay};
use tm_core::model::{Dep, Id, InstanceKey};
use tm_core::planner::{DayPlan, Diagnostics, SegFlags, SegKind, Segment};
use tm_core::priority::{Prio, PrioClass};
use tm_core::store::{ActiveBlock, RuntimeState};
use tm_core::tree::Tree;

use app::{App, AppData};

/// The day every snapshot is taken on (§4.3's day file).
pub const DATE: (i32, u32, u32) = (2026, 9, 7);
/// The instant §12.1's mock is drawn at.
pub const NOW: (u32, u32) = (10, 42);

/// The `plan-basic` fixture directory.
pub fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-core/tests/fixtures/plan-basic")
}

/// The fixture's `config.toml` (§16), which pins `tz = America/Chicago`.
pub fn config() -> Config {
    let text = fs::read_to_string(fixture_dir().join("config.toml")).expect("fixture config");
    Config::parse(&text).expect("parse config")
}

/// The date under test.
pub fn date() -> NaiveDate {
    NaiveDate::from_ymd_opt(DATE.0, DATE.1, DATE.2).expect("date")
}

/// A local time on that date, in `cfg.tz`.
pub fn at(cfg: &Config, h: u32, m: u32) -> DateTime<Tz> {
    cfg.tz
        .from_local_datetime(
            &date()
                .and_hms_opt(h, m, 0)
                .expect("time"),
        )
        .single()
        .expect("unambiguous local time")
}

/// The same instant with a fixed offset, for log entries (§10.1).
pub fn stamp(cfg: &Config, h: u32, m: u32) -> DateTime<FixedOffset> {
    at(cfg, h, m).fixed_offset()
}

/// `HH:MM`.
fn time(h: u32, m: u32) -> NaiveTime {
    NaiveTime::from_hms_opt(h, m, 0).expect("time")
}

/// The §4.3 fixture tree.
pub fn tree(cfg: &Config) -> Tree {
    let dir = fixture_dir();
    let files = [
        "month/2026-09.md",
        "week/2026-W37.md",
        "backlog.md",
        "routines.md",
        "optional.md",
        "calendar/2026-W37.md",
        "day/2026-09-07.md",
        "inbox.md",
    ];
    let texts: Vec<(String, String)> = files
        .iter()
        .filter_map(|rel| {
            fs::read_to_string(dir.join(rel))
                .ok()
                .map(|t| ((*rel).to_string(), t))
        })
        .collect();
    let refs: Vec<(&str, &str)> = texts
        .iter()
        .map(|(p, t)| (p.as_str(), t.as_str()))
        .collect();
    Tree::from_texts(&refs, cfg)
}

/// The day's log, as §4.3's `## Log` records it.
pub fn log(cfg: &Config) -> Log {
    let e = |h: u32, m: u32, ev: Event| LogEntry::new(stamp(cfg, h, m), ev);
    Log::from_entries(vec![
        e(
            6,
            5,
            Event::Wake {
                slept_min: 490,
                onset_min: Some(25),
            },
        ),
        e(
            7,
            0,
            Event::Arrive {
                loc: "lounge".into(),
                window: ["07:00".into(), "16:00".into()],
                budget: 6,
            },
        ),
        e(
            7,
            2,
            Event::Start {
                id: "t1".into(),
                pred: 5,
                rep: Some(5),
                hsw: 0.95,
                slept_min: 490,
                loc: "lounge".into(),
                blocks_done: 0,
                since_break_min: 0,
            },
        ),
        e(
            8,
            9,
            Event::Done {
                id: "t1".into(),
                est_min: 60,
                actual_min: 67,
                went: Some(1),
                tags: vec!["lean".into()],
                ci: 5,
                partial: false,
            },
        ),
        e(
            9,
            8,
            Event::Break {
                planned_min: 20,
                actual_min: Some(24),
                r#where: Some("walk".into()),
            },
        ),
        e(
            9,
            32,
            Event::Start {
                id: "t3".into(),
                pred: 5,
                rep: Some(4),
                hsw: 3.45,
                slept_min: 490,
                loc: "lounge".into(),
                blocks_done: 1,
                since_break_min: 24,
            },
        ),
    ])
}

/// §10.2's runtime state at 10:42, with `^t3` running since 09:32.
pub fn state() -> RuntimeState {
    RuntimeState {
        date: Some(date()),
        wake: Some(time(6, 5)),
        arrival: Some(time(7, 0)),
        loc: Some("lounge".into()),
        window: Some((time(7, 0), time(16, 0))),
        budget: Some(6),
        active: Some(ActiveBlock {
            id: Id::new("t3"),
            started: time(9, 32),
            est_min: 192,
            paused: false,
        }),
        ..RuntimeState::default()
    }
}

/// One `(Id, Prio)` for a hand-built plan.
pub fn prio(id: &str, p: u8, class: PrioClass) -> (Id, Prio) {
    (
        Id::new(id),
        Prio {
            id: Id::new(id),
            p,
            class,
            k: 3,
            u: None,
            bin: None,
            need_min: 0,
            avail_min: 0,
            allocation_min: 0,
            shortfall_min: 0,
            until: None,
            hysteresis_applied: false,
            raw_p: p,
        },
    )
}

/// A segment builder with everything defaulted.
#[allow(clippy::too_many_arguments)]
pub fn seg(
    cfg: &Config,
    from: (u32, u32),
    to: (u32, u32),
    kind: SegKind,
    energy: Option<u8>,
    item: Option<&str>,
    flags: SegFlags,
) -> Segment {
    let instance = matches!(kind, SegKind::Routine | SegKind::Wall | SegKind::Optional)
        .then(|| InstanceKey::Date(date()));
    Segment {
        start: at(cfg, from.0, from.1),
        end: at(cfg, to.0, to.1),
        kind,
        energy,
        item: item.map(Id::new),
        instance,
        flags,
    }
}

/// Marks for a finished segment.
fn done_flags(planned: u32) -> SegFlags {
    SegFlags {
        done: true,
        planned_min: Some(planned),
        ..SegFlags::default()
    }
}

/// §4.3's printed timeline, built by hand so the snapshots never move with
/// the planner (§17 M6: "a hand-built `DayPlan`").
pub fn day_plan(cfg: &Config) -> DayPlan {
    let s = |from, to, kind, energy, item, flags| seg(cfg, from, to, kind, energy, item, flags);
    let segments = vec![
        s(
            (7, 0),
            (8, 7),
            SegKind::Block,
            Some(5),
            Some("t1"),
            done_flags(60),
        ),
        s(
            (8, 7),
            (9, 8),
            SegKind::Block,
            Some(5),
            Some("m3"),
            done_flags(60),
        ),
        s(
            (9, 8),
            (9, 32),
            SegKind::Break,
            None,
            None,
            done_flags(20),
        ),
        s(
            (9, 32),
            (11, 20),
            SegKind::Block,
            Some(4),
            Some("t3"),
            SegFlags {
                current: true,
                planned_min: Some(192),
                multiplier: Some(1.6),
                ..SegFlags::default()
            },
        ),
        s(
            (11, 20),
            (11, 50),
            SegKind::Routine,
            None,
            Some("lunch"),
            SegFlags::default(),
        ),
        s(
            (11, 50),
            (12, 50),
            SegKind::Block,
            Some(4),
            Some("t4"),
            SegFlags {
                underused: true,
                planned_min: Some(60),
                note: Some("↓ slot 4, item 3".into()),
                ..SegFlags::default()
            },
        ),
        s(
            (12, 50),
            (13, 50),
            SegKind::Wall,
            None,
            Some("g1"),
            SegFlags::default(),
        ),
        s((13, 50), (14, 10), SegKind::Break, None, None, SegFlags::default()),
        s(
            (14, 10),
            (15, 10),
            SegKind::Block,
            Some(3),
            Some("t5"),
            SegFlags {
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        s(
            (15, 10),
            (15, 30),
            SegKind::Block,
            Some(1),
            Some("a3"),
            SegFlags {
                hot: true,
                planned_min: Some(20),
                note: Some("due today".into()),
                ..SegFlags::default()
            },
        ),
        s(
            (17, 30),
            (18, 0),
            SegKind::Routine,
            None,
            Some("dinner"),
            SegFlags::default(),
        ),
        s(
            (18, 0),
            (19, 0),
            SegKind::Optional,
            None,
            Some("Severance S3E4"),
            SegFlags::default(),
        ),
        s(
            (21, 30),
            (22, 0),
            SegKind::WindDown,
            None,
            None,
            SegFlags::default(),
        ),
    ];
    DayPlan {
        date: date(),
        window: (at(cfg, 7, 0), at(cfg, 16, 0)),
        budget_blocks: 6,
        segments,
        diagnostics: Diagnostics {
            underused: vec![(Id::new("t4"), 4, 3)],
            hot: vec![Id::new("a3")],
            blocked: vec![(Id::new("t5"), vec![Dep::Item(Id::new("t4"))])],
            waiting: vec![Id::new("a4")],
            ..Diagnostics::default()
        },
        priorities: vec![
            prio("m1", 1, PrioClass::Rank),
            prio("m2", 3, PrioClass::Rank),
            prio("m3", 1, PrioClass::Rank),
            prio("m4", 5, PrioClass::Rank),
            prio("d1", 1, PrioClass::Dated),
            prio("t1", 1, PrioClass::Rank),
            prio("t3", 1, PrioClass::Rank),
            prio("t4", 3, PrioClass::Rank),
            prio("t5", 3, PrioClass::Rank),
            prio("a3", 0, PrioClass::Mandatory),
        ],
    }
}

/// §12.1's ghost row: the same day as it stood at arrival — nothing done yet,
/// and `^t4` still in the 11:20 slot lunch later took.
pub fn ghost_plan(cfg: &Config) -> DayPlan {
    let mut plan = day_plan(cfg);
    plan.segments.truncate(6);
    for seg in &mut plan.segments {
        seg.flags.done = false;
        seg.flags.current = false;
        seg.flags.ghost = true;
    }
    plan
}

/// The app the snapshots are taken from.
pub fn app() -> App {
    app_at(NOW.0, NOW.1)
}

/// [`app`] at another time of day.
pub fn app_at(h: u32, m: u32) -> App {
    let cfg = config();
    let now = at(&cfg, h, m);
    let log = log(&cfg);
    let replay: Replay = log.replay(None, cfg.tz);
    let plan = day_plan(&cfg);
    let ghost = ghost_plan(&cfg);
    let data = AppData {
        model: Default::default(),
        state: state(),
        tree: tree(&cfg),
        log,
        replay,
        now,
        cfg,
    };
    App::with_plan(data, plan, Some(ghost))
}

/// [`app_at`] with the running block sized differently, so §9.1's prompt can
/// be made to fire while the day still has a tail to drop.
pub fn overtime_app(h: u32, m: u32, est_min: u32) -> App {
    let mut app = app_at(h, m);
    if let Some(active) = app.state.active.as_mut() {
        active.est_min = est_min;
    }
    app.refresh();
    app
}

/// An app whose block budget is nearly spent, so §9.1's "x extend +1 block"
/// really does cost the tail of the day: one block done of two, `^t3` an hour
/// into a one-block estimate at 10:42.
pub fn tight_overtime_app() -> App {
    let mut app = overtime_app(10, 42, 60);
    app.state.budget = Some(2);
    app.refresh();
    app
}

/// An app with nothing running, for §9.2's idle prompt.
pub fn idle_app(h: u32, m: u32) -> App {
    let mut app = app_at(h, m);
    app.state.active = None;
    app.refresh();
    app
}

/// Draw the whole frame into a `TestBackend` and return it as snapshot text.
pub fn render(app: &App, width: u16, height: u16) -> String {
    let mut term = Terminal::new(TestBackend::new(width, height)).expect("terminal");
    term.draw(|f| today::draw(f, app)).expect("draw");
    term.backend().to_string()
}

/// Draw one pane's lines into a `TestBackend` of its own.
pub fn render_lines(lines: &[Line<'static>], width: u16) -> String {
    let height = u16::try_from(lines.len().max(1)).unwrap_or(u16::MAX);
    let mut term = Terminal::new(TestBackend::new(width, height)).expect("terminal");
    term.draw(|f| {
        f.render_widget(
            ratatui::widgets::Paragraph::new(lines.to_vec()),
            f.area(),
        );
    })
    .expect("draw");
    term.backend().to_string()
}

/// A `Vec<Line>` as plain snapshot text, without a backend.
pub fn lines(lines: &[Line<'static>]) -> String {
    lines
        .iter()
        .map(|l| l.to_string())
        .collect::<Vec<_>>()
        .join("\n")
}
