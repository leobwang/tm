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
//! * [`fixture_dir`] — the `plan-basic` tree of §4.3 (from
//!   `tm-core/tests/fixtures/plan-basic`), the fixture's own `config.toml`,
//!   a synthetic log matching that day file's `## Log`, and the runtime state
//!   §10.2 would hold at 10:42 with `^t3` running.
//! * [`day_plan`] — a **hand-built** `DayPlan` reproducing §4.3's printed
//!   timeline, so the snapshots do not depend on the planner's exact output.
//!   [`log`] agrees with it: every block `day_plan` marks done is a `start`
//!   and a `done` in the log, because §11's monitors are read off the log.
//!   The log is **text**: every app reads it through the test chokepoint
//!   (`tests/support/replay.rs`, step R12), as the binary reads
//!   `.tm/log.jsonl` through `Ctx::replay_of`.
//! * [`app`] — the two glued together, plus [`app_at`] for another instant,
//!   [`app_with_log_text`] for another state or log, [`ghost_plan`] for §12.1's ghost
//!   row and [`arrival`] for the record it is really built from.
//! * [`render`] / [`lines`] — a `TestBackend` frame, and a `Vec<Line>`, as
//!   snapshot text.

#![allow(dead_code)]

/// The test chokepoint (step R12): the app's replay is read through it.
#[path = "../support/replay.rs"]
pub mod chokepoint;

/// The capacity request the binary sends, and the kernel's answer read back by
/// the host's codec — where the app's ranking comes from since W-36 track H.
#[path = "../support/planreq.rs"]
pub mod planreq;

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

#[allow(dead_code, unused_imports)]
#[path = "../../src/tui/queue.rs"]
pub mod queue;

#[allow(dead_code, unused_imports)]
#[path = "../../src/tui/necessities.rs"]
pub mod necessities;

#[allow(dead_code, unused_imports)]
#[path = "../../src/tui/inbox.rs"]
pub mod inbox;

#[allow(dead_code, unused_imports)]
#[path = "../../src/tui/review.rs"]
pub mod review;

use std::fs;
use std::path::{Path, PathBuf};

use chrono::{DateTime, FixedOffset, NaiveDate, NaiveTime, TimeZone};
use chrono_tz::Tz;
use ratatui::backend::TestBackend;
use ratatui::text::Line;
use ratatui::Terminal;

use tm_core::config::Config;
use tm_core::log::{Event, LogEntry, Replay};
use tm_core::model::{Dep, Id, InstanceKey};
use tm_core::dayplan::{DayPlan, Diagnostics, SegFlags, SegKind, Segment};
use tm_core::priority::{Prio, PrioClass};
use tm_core::store::{ActiveBlock, MemStore, PlanFiles, RuntimeState, Store};
use tm_core::tree::Tree;

use app::{App, AppData, ArrivalBlock};

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

/// The §4.3 fixture tree's files, as `(path, text)` — what [`tree`] parses and
/// what the kernel is handed.
pub fn tree_texts() -> Vec<(String, String)> {
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
    files
        .iter()
        .filter_map(|rel| {
            fs::read_to_string(dir.join(rel))
                .ok()
                .map(|t| ((*rel).to_string(), t))
        })
        .collect()
}

/// The §4.3 fixture tree.
pub fn tree(cfg: &Config) -> Tree {
    let texts = tree_texts();
    let refs: Vec<(&str, &str)> = texts
        .iter()
        .map(|(p, t)| (p.as_str(), t.as_str()))
        .collect();
    Tree::from_texts(&refs, cfg)
}

/// The fixture's parsed files — what §12.2's Queue and §12.5's Inbox read.
pub fn plan_files() -> PlanFiles {
    MemStore::from_dir(fixture_dir())
        .expect("fixture readable")
        .read_tree()
        .expect("fixture parses")
}

/// The day's log, as §4.3's `## Log` records it, as the text of
/// `.tm/log.jsonl`.
pub fn log(cfg: &Config) -> String {
    chokepoint::text_of(&log_entries(cfg))
}

/// The entries of [`log`], in file order.
pub fn log_entries(cfg: &Config) -> Vec<LogEntry> {
    let e = |h: u32, m: u32, ev: Event| LogEntry::new(stamp(cfg, h, m), ev);
    vec![
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
        // §4.3's second block. The hand-built `day_plan` marks it done, so the
        // log has to say so too: every monitor of §11 (blocks done, the leak
        // ledger, adherence) is derived from this replay, and a plan that
        // claims a block the log never records would make the status line of
        // the whole-screen snapshots unreadable as a spec check.
        e(
            8,
            9,
            Event::Start {
                id: "m3".into(),
                pred: 5,
                rep: Some(5),
                hsw: 2.07,
                slept_min: 490,
                loc: "lounge".into(),
                blocks_done: 1,
                since_break_min: 67,
            },
        ),
        e(
            9,
            8,
            Event::Done {
                id: "m3".into(),
                est_min: 60,
                actual_min: 59,
                went: Some(1),
                tags: vec!["lean".into()],
                ci: 5,
                partial: true,
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
    ]
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

/// `.tm/arrival_plan.json` as `tm arrive` wrote it at 07:00: the block starts
/// the day was planned with (§12.1's ghost row, §11's adherence denominator).
///
/// It is the ghost of [`ghost_plan`] in the shape the record keeps — the same
/// four blocks, in the same order, at the same starts.
pub fn arrival() -> Vec<ArrivalBlock> {
    [("t1", (7, 0)), ("m3", (8, 7)), ("t3", (9, 32)), ("t4", (11, 50))]
        .into_iter()
        .map(|(id, (h, m))| ArrivalBlock {
            start: time(h, m),
            id: Some(Id::new(id)),
        })
        .collect()
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
            avail_min_exact: Default::default(),
            allocation_min: 0,
            allocation_min_exact: Default::default(),
            shortfall_min: 0,
            shortfall_min_exact: Default::default(),
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
    app_with_log_text(at(&cfg, h, m), state(), &log(&cfg))
}

/// [`app_at`] with the runtime state and the log's text given: the two things
/// §9's timers (`active`, `break`, the worked minutes) and §11's monitors are
/// derived from. The log is read through the test chokepoint.
pub fn app_with_log_text(now: DateTime<Tz>, state: RuntimeState, log: &str) -> App {
    let cfg = config();
    let plan = day_plan(&cfg);
    let ghost = ghost_plan(&cfg);
    app_of_world(
        &tree_texts(),
        plan_files(),
        cfg,
        World { now, state, log, week_cut: tm_core::review::PauseCut::default() },
        plan,
        Some(ghost),
        arrival(),
    )
}

/// **What an app is built over, beside the tree**: the instant, `.tm/state.json`, the log's
/// text and the kernel's cut of the week's Pauses (`AppData::week_cut`, which the Review
/// screen's heat grid draws — `PauseCut::default()` cuts nothing, README gap 3721).
pub struct World<'a> {
    pub now: DateTime<Tz>,
    pub state: RuntimeState,
    pub log: &'a str,
    pub week_cut: tm_core::review::PauseCut,
}

/// **An app over any tree** — `texts` its documents as `(path, text)`, `files` their parse,
/// `cfg` its configuration — built as [`app_with_log_text`] builds §4.3's: the replay through
/// the test chokepoint, and the ranking and capacity the kernel answers the capacity request
/// the binary sends (`kernel_capacity::rank`'s, no `planner` section), around the plan, ghost
/// and arrival record given. One body for both: the fixture's app is this over `plan-basic`.
pub fn app_of_world(
    texts: &[(String, String)],
    files: PlanFiles,
    cfg: Config,
    w: World<'_>,
    plan: DayPlan,
    ghost: Option<DayPlan>,
    arrival: Vec<ArrivalBlock>,
) -> App {
    let World { now, state, log, week_cut } = w;
    let replay: Replay = chokepoint::replay_of_text(log, cfg.tz);
    let refs: Vec<(&str, &str)> = texts.iter().map(|(p, t)| (p.as_str(), t.as_str())).collect();
    let tree = Tree::from_texts(&refs, &cfg);
    // The ranking `tui::data_of` loads from the kernel (stage 5 D10 L8):
    // `Ctx::priorities` sends the capacity section and reads its grants and its
    // first days in units. Until W-36 track H this stood in the FORK's own §7
    // pass (`planner::plan(..).priorities`) and `planner::week_plan`'s grid — a
    // configuration no shipped path builds (D53) — so the TUI's replans and
    // §9.1's what-ifs (`App::input`) ranked by it. Now it is the kernel's answer
    // to the request the binary sends, with no `planner` section, as
    // `kernel_capacity::rank` asks it (README gap 2872).
    let model = tm_core::energy::Model::default();
    let date = tm_core::planwire::plan_date(&state, now);
    let candidates = tm_core::priority::collect_candidates(&tree, &replay, &cfg, &model, date, now);
    let world = planreq::World {
        docs: texts,
        log,
        tree: &tree,
        cfg: &cfg,
        state: &state,
        now,
        cands: &candidates,
        replay: &replay,
    };
    let (mut req, order) = planreq::request(&world, None);
    req.as_object_mut().expect("a request is an object").remove("planner");
    let resp = planreq::call(&req);
    let answer = tm_core::planwire::read_capacity_answer(&resp, &order, true)
        .unwrap_or_else(|e| panic!("the kernel's capacity answer reads: {e}: {}", resp["err"]));
    let prios: Vec<Prio> = answer.prios;
    assert_eq!(candidates.len(), prios.len(), "the ranking is 1:1 with the candidates");
    let caps = answer.days;
    let data = AppData {
        model,
        state,
        tree,
        replay,
        arrival,
        files,
        candidates,
        prios,
        caps,
        week_cut,
        now,
        cfg,
    };
    App::with_plan(data, plan, ghost)
}

/// One log entry on the day under test (§10.1).
pub fn entry(cfg: &Config, h: u32, m: u32, ev: Event) -> LogEntry {
    LogEntry::new(stamp(cfg, h, m), ev)
}

/// [`log`] with more entries, kept in time order.
pub fn log_plus(cfg: &Config, extra: Vec<LogEntry>) -> String {
    let mut entries = log_entries(cfg);
    entries.extend(extra);
    entries.sort_by_key(|e| e.t);
    chokepoint::text_of(&entries)
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

/// [`overtime_app`] with another item running, so §9.1's "stop, demote rest"
/// line can be exercised on an estimate that leaves a real remainder rather
/// than the `MIN_REMAINING_MIN` floor.
pub fn overtime_app_for(id: &str, est_min: u32, h: u32, m: u32) -> App {
    let mut app = overtime_app(h, m, est_min);
    if let Some(active) = app.state.active.as_mut() {
        active.id = Id::new(id);
    }
    app.refresh();
    app
}

/// An app whose block budget is nearly spent, so §9.1's "x extend +1 block"
/// really does cost the tail of the day: two blocks done of three, `^t3` an
/// hour into a one-block estimate at 10:42.
pub fn tight_overtime_app() -> App {
    let mut app = overtime_app(10, 42, 60);
    app.state.budget = Some(3);
    app.refresh();
    app
}

/// **The world `worked_midnight_timer.rs` plans over** (stage 6 W-40 track T's D75 test; held here
/// since W-41 track H, README gap 4090, so the TUI's fork-planned worlds are built through one
/// harness): the §4.3 fixture's log with `^t3` done at 22:30 and `^t4` started at 23:00, paused
/// 23:30–00:30 by a typed `tm pause` pair, and the runtime state as the first verb after midnight
/// leaves it — `state.date` rolled to `now`'s, `active.started` still `23:00`, `est_min` 60. `now`
/// is an instant of the day AFTER the fixture's. The app and the log's text.
pub fn after_midnight_app(now: DateTime<Tz>) -> (App, String) {
    let cfg = config();
    let mut entries = log_entries(&cfg);
    entries.extend([
        entry(
            &cfg,
            22,
            30,
            Event::Done { id: "t3".into(), est_min: 192, actual_min: 778, went: Some(1), tags: Vec::new(), ci: 4, partial: false },
        ),
        entry(
            &cfg,
            23,
            0,
            Event::Start {
                id: "t4".into(),
                pred: 4,
                rep: Some(4),
                hsw: 16.92,
                slept_min: 490,
                loc: "lounge".into(),
                blocks_done: 3,
                since_break_min: 0,
            },
        ),
        entry(&cfg, 23, 30, Event::Pause { id: "t4".into() }),
        LogEntry::new(
            cfg.tz
                .from_local_datetime(&date().succ_opt().expect("tomorrow").and_hms_opt(0, 30, 0).expect("time"))
                .single()
                .expect("unambiguous local time")
                .fixed_offset(),
            Event::Unpause { id: "t4".into() },
        ),
    ]);
    let log = chokepoint::text_of(&entries);
    let state = RuntimeState {
        date: Some(now.date_naive()),
        active: Some(ActiveBlock { id: Id::new("t4"), started: time(23, 0), est_min: 60, paused: false }),
        ..state()
    };
    (app_with_log_text(now, state, &log), log)
}

/// **The world `tui_today_prompts::a_block_started_before_midnight_still_goes_overtime` plans over**
/// (stage 6 W-45 track C, README gap 4321): the world the TUI holds since the owner's D84, which
/// re-collects at the date change, under D42, by which the running block is the LOG's — the §4.3
/// fixture's log with `^t3` stopped at 22:30 an hour short and started again at 23:30, and the
/// runtime state as the TUI holds it past midnight: `state.date` rolled to `now`'s, `active.started`
/// `23:30`, `est_min` 60. Until W-45 that test built `.tm/state.json` still dated the day before over
/// an EMPTY log, a world D42's reconcile ends on every load and D84's roll never plans over (README
/// gap 4262). `now` is an instant of the day AFTER the fixture's. The app and the log's text.
pub fn before_midnight_app(now: DateTime<Tz>) -> (App, String) {
    let cfg = config();
    let mut entries = log_entries(&cfg);
    entries.extend([
        entry(&cfg, 22, 30, Event::Stop { id: "t3".into(), remaining_min: 60 }),
        entry(
            &cfg,
            23,
            30,
            Event::Start {
                id: "t3".into(),
                pred: 4,
                rep: Some(4),
                hsw: 17.42,
                slept_min: 490,
                loc: "lounge".into(),
                blocks_done: 2,
                since_break_min: 0,
            },
        ),
    ]);
    let log = chokepoint::text_of(&entries);
    let state = RuntimeState {
        date: Some(now.date_naive()),
        active: Some(ActiveBlock { id: Id::new("t3"), started: time(23, 30), est_min: 60, paused: false }),
        ..state()
    };
    (app_with_log_text(now, state, &log), log)
}

/// An app with nothing running, for §9.2's idle prompt and the Now pane's
/// "nothing running" row: no `active` in `state.json`, and no segment flagged
/// `current` — the planner marks the block it is inside, and there is none.
pub fn idle_app(h: u32, m: u32) -> App {
    let mut app = app_at(h, m);
    app.state.active = None;
    for seg in &mut app.plan.segments {
        seg.flags.current = false;
    }
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
