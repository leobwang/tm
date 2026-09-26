//! The §4.3 example day, hand-built: the tree it refers to and the
//! [`DayPlan`] whose rows are the day file's generated section.
//!
//! The plan here is written out **by hand** on purpose: it reproduces §4.3's
//! printed timeline row for row, which is what makes the emit snapshots
//! readable against the spec in a diff. It is the day of
//! `tests/fixtures/plan-basic` on Monday 2026-09-07, planned at 10:42 with
//! the window 07:00–16:00 and a budget of 6 blocks.
//!
//! Because it is hand-built it cannot catch a *disagreement* between the
//! planner and the renderer — change a field `planner.rs` sets on a `Segment`
//! and every snapshot here still passes. `emit_planner.rs` covers that: the
//! same three §17 M4 fixture days, through `planner::plan`.
//!
//! One deliberate artefact: the three finished segments start on the planned
//! grid (07:00, 08:00, 09:00) but last as long as the log says they did (67m,
//! 58m, 24m), exactly as the spec's example prints them — so they overlap by a
//! few minutes. A real plan's finished segments carry their true start too
//! (07:02, 08:09, 09:08 in `plan-basic`'s log) and do not overlap; see
//! [`log_faithful_plan`].

#![allow(dead_code)]

use chrono::{DateTime, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use tm_core::capacity::local_dt;
use tm_core::config::Config;
use tm_core::model::Id;
use tm_core::dayplan::{DayPlan, SegFlags, SegKind, Segment};
use tm_core::priority::{Prio, PrioClass};
use tm_core::tree::Tree;

pub const TZ: Tz = Tz::America__Chicago;

/// 2026-09-07.
pub fn date() -> NaiveDate {
    NaiveDate::from_ymd_opt(2026, 9, 7).expect("date")
}

/// A local instant on the planned day.
pub fn at(h: u32, m: u32) -> DateTime<Tz> {
    local_dt(TZ, date(), NaiveTime::from_hms_opt(h, m, 0).expect("time"))
}

/// The §16 defaults with the fixture's zone.
pub fn config() -> Config {
    Config {
        tz: TZ,
        ..Config::default()
    }
}

/// The `plan-basic` files the §4.3 timeline names, plus the second `Read
/// ch.6` task (`^t2`) the example's 08:00 row shows.
pub fn tree(cfg: &Config) -> Tree {
    Tree::from_texts(
        &[
            (
                "month/2026-09.md",
                "---\nmonth: 2026-09\n---\n# Outcomes\n\
                 - [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1\n\
                 - [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2\n\
                 - [ ] 2 !3 Winter course selection + admin done        ^O3\n",
            ),
            (
                "week/2026-W37.md",
                "---\nweek: 2026-W37\n---\n# Milestones\n\
                 - [ ] 5 6b Finish ch.5 exercises        @O1 ^m1\n\
                 - [ ] 4 6b Rollback path passes tests   @O2 ^m2\n\
                 - [ ] 5 3b Read ch.6                    @O1 ^m3\n\
                 \n# Tasks\n\
                 - [ ] 5 1b Read ch.6 §1–2               @m3 ^t1\n\
                 - [ ] 5 1b Read ch.6 §3                 @m3 ^t2\n\
                 - [>] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3\n\
                 - [ ] 3 1b Claude Code drafts tests     @m2 ^t4\n\
                 - [ ] 3 1b Review the drafts            @m2 after:^t4 ^t5\n",
            ),
            (
                "backlog.md",
                "# Untied\n\
                 - [ ] 2 30m Insurance claim for the bike  ^a1\n\
                 - [ ] 1 Pick up package  win:2026-09-07T09:00/21:00 dur:20m ^a3\n\
                 - [ ] 2 20m Call the bank about the card  ^p1\n",
            ),
            (
                "routines.md",
                "- sleep      win:22:00-08:00 dur:8h30m every:day ci:0\n\
                 - lunch      win:11:30-13:30 dur:30m  every:day\n\
                 - dinner     win:17:30-19:30 dur:30m  every:day\n",
            ),
            ("optional.md", "- Severance S3E4  dur:1h\n"),
            (
                "calendar/2026-W37.md",
                "- [ ] 3 Meeting w/ host      at:2026-09-07T12:50/13:50 loc:zoom ^g1\n\
                 - [ ] 2 Dentist             at:2026-09-07T09:00/10:20 loc:out ^g5\n",
            ),
        ],
        cfg,
    )
}

/// A `Prio` with just the fields the timeline and the banners read.
pub fn prio(id: &str, p: u8, class: PrioClass) -> (Id, Prio) {
    let id = Id::new(id);
    (
        id.clone(),
        Prio {
            id,
            p,
            class,
            k: 1,
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

/// A block segment.
fn block(
    from: (u32, u32),
    to: (u32, u32),
    item: &str,
    energy: Option<u8>,
    flags: SegFlags,
) -> Segment {
    Segment {
        start: at(from.0, from.1),
        end: at(to.0, to.1),
        kind: SegKind::Block,
        energy,
        item: Some(Id::new(item)),
        instance: None,
        flags,
    }
}

/// A segment with no `ci`/`p` columns: routine, break, wall, optional, …
fn other(from: (u32, u32), to: (u32, u32), kind: SegKind, item: Option<&str>, flags: SegFlags) -> Segment {
    Segment {
        start: at(from.0, from.1),
        end: at(to.0, to.1),
        kind,
        energy: None,
        item: item.map(Id::new),
        instance: None,
        flags,
    }
}

/// The §4.3 day, row for row.
pub fn plan() -> DayPlan {
    let mut day = DayPlan::empty(date(), (at(7, 0), at(16, 0)), 6);
    day.segments = vec![
        // 07:00  5 p1 ✓ Read ch.6 §1–2   @m3  1b  (67m)
        block(
            (7, 0),
            (8, 7),
            "t1",
            Some(5),
            SegFlags {
                done: true,
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        // 08:00  5 p1 ✓ Read ch.6 §3     @m3  1b  (58m)
        block(
            (8, 0),
            (8, 58),
            "t2",
            Some(5),
            SegFlags {
                done: true,
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        // 09:00  ·     ✓ break 20m            (24m)
        other(
            (9, 0),
            (9, 24),
            SegKind::Break,
            None,
            SegFlags {
                done: true,
                planned_min: Some(20),
                ..SegFlags::default()
            },
        ),
        // 09:20  4 p1 ▶ Exercises 5.3–5.5  @m1  2b×1.6
        block(
            (9, 20),
            (11, 20),
            "t3",
            Some(4),
            SegFlags {
                current: true,
                planned_min: Some(192),
                multiplier: Some(1.6),
                ..SegFlags::default()
            },
        ),
        // 11:20  ·       lunch 30m
        other(
            (11, 20),
            (11, 50),
            SegKind::Routine,
            Some("lunch"),
            SegFlags {
                planned_min: Some(30),
                ..SegFlags::default()
            },
        ),
        // 11:50  4↓p3    Claude Code drafts tests  @m2  1b   ↓ slot 4, item 3
        block(
            (11, 50),
            (12, 50),
            "t4",
            Some(4),
            SegFlags {
                underused: true,
                planned_min: Some(60),
                note: Some("↓ slot 4, item 3".to_string()),
                ..SegFlags::default()
            },
        ),
        // 12:50  ⏰      Meeting w/ host   1h
        other((12, 50), (13, 50), SegKind::Wall, Some("g1"), SegFlags::default()),
        // 13:50  ·       break 20m
        other(
            (13, 50),
            (14, 10),
            SegKind::Break,
            None,
            SegFlags {
                planned_min: Some(20),
                ..SegFlags::default()
            },
        ),
        // 14:10  3 p3    Review the drafts  @m2  1b
        block(
            (14, 10),
            (15, 10),
            "t5",
            Some(3),
            SegFlags {
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        // 15:10  ───     window ends 16:00   (generated by the renderer)
        // 15:10  1 p0 ⚠  Pick up package    20m   due today
        block(
            (15, 10),
            (15, 30),
            "a3",
            None,
            SegFlags {
                hot: true,
                mandatory: true,
                planned_min: Some(20),
                note: Some("due today".to_string()),
                ..SegFlags::default()
            },
        ),
        // 17:30  ·       dinner 30m
        other(
            (17, 30),
            (18, 0),
            SegKind::Routine,
            Some("dinner"),
            SegFlags {
                planned_min: Some(30),
                ..SegFlags::default()
            },
        ),
        // 18:00  ○       Severance S3E4    1h
        other(
            (18, 0),
            (19, 0),
            SegKind::Optional,
            Some("Severance S3E4"),
            SegFlags::default(),
        ),
        // 21:30  🌙      wind-down · bed 22:00
        other((21, 30), (22, 0), SegKind::WindDown, None, SegFlags::default()),
    ];
    day.priorities = vec![
        prio("t1", 1, PrioClass::Dated),
        prio("t2", 1, PrioClass::Dated),
        prio("t3", 1, PrioClass::Dated),
        prio("t4", 3, PrioClass::Rank),
        prio("t5", 3, PrioClass::Rank),
        prio("a3", 0, PrioClass::Mandatory),
    ];
    day.diagnostics.underused = vec![(Id::new("t4"), 4, 3)];
    day.diagnostics.blocked = vec![(
        Id::new("t5"),
        vec![tm_core::model::Dep::Item(Id::new("t4"))],
    )];
    day
}

/// The same day as the log actually ran it: finished segments at their true
/// start (`07:02 start ^t1`, `08:09 done`, `09:08 break`, `09:32 start ^t3`),
/// so nothing overlaps. This is the shape a real `plan()` produces.
pub fn log_faithful_plan() -> DayPlan {
    let mut day = plan();
    day.segments[0].start = at(7, 2);
    day.segments[0].end = at(8, 9);
    day.segments[1].start = at(8, 9);
    day.segments[1].end = at(9, 7);
    day.segments[2].start = at(9, 8);
    day.segments[2].end = at(9, 32);
    day.segments[3].start = at(9, 32);
    day
}

/// M4's second fixture day: a **late start with a wall**.
///
/// The dentist (`^g5`) runs 09:00–10:20, ten minutes are lost getting back, and
/// the window only opens at 10:30 — so the day starts after a wall instead of
/// before one. The budget is 3 blocks, which runs out at 16:30, well inside a
/// window that closes at 18:30; the divider therefore lands mid-afternoon
/// rather than at the window's edge. Neither the `↓` nor the `⚠` segment
/// carries a written note, so both are derived (§4.3).
pub fn late_start_plan() -> DayPlan {
    let mut day = DayPlan::empty(date(), (at(10, 30), at(18, 30)), 3);
    day.segments = vec![
        other((9, 0), (10, 20), SegKind::Wall, Some("g5"), SegFlags::default()),
        other(
            (10, 20),
            (10, 30),
            SegKind::Lost,
            None,
            SegFlags {
                planned_min: Some(10),
                note: Some("leak".to_string()),
                ..SegFlags::default()
            },
        ),
        block(
            (10, 30),
            (11, 30),
            "t1",
            Some(5),
            SegFlags {
                done: true,
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        other(
            (11, 30),
            (12, 0),
            SegKind::Routine,
            Some("lunch"),
            SegFlags {
                planned_min: Some(30),
                ..SegFlags::default()
            },
        ),
        block(
            (12, 0),
            (12, 50),
            "t3",
            Some(4),
            SegFlags {
                current: true,
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        other((12, 50), (13, 50), SegKind::Wall, Some("g1"), SegFlags::default()),
        other(
            (13, 50),
            (14, 10),
            SegKind::Break,
            None,
            SegFlags {
                planned_min: Some(20),
                ..SegFlags::default()
            },
        ),
        // `↓` with no written note: emit derives `↓ slot 5, item 3`.
        block(
            (14, 10),
            (15, 10),
            "t4",
            Some(5),
            SegFlags {
                underused: true,
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        block(
            (15, 30),
            (16, 30),
            "t5",
            Some(3),
            SegFlags {
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        // `⚠` with no written note: emit derives `due today` from the window.
        block(
            (16, 30),
            (16, 50),
            "a3",
            None,
            SegFlags {
                hot: true,
                mandatory: true,
                planned_min: Some(20),
                ..SegFlags::default()
            },
        ),
        other(
            (17, 30),
            (18, 0),
            SegKind::Routine,
            Some("dinner"),
            SegFlags {
                planned_min: Some(30),
                ..SegFlags::default()
            },
        ),
        other(
            (19, 0),
            (20, 0),
            SegKind::Optional,
            Some("Severance S3E4"),
            SegFlags::default(),
        ),
        other((21, 30), (22, 0), SegKind::WindDown, None, SegFlags::default()),
    ];
    day.priorities = vec![
        prio("t1", 1, PrioClass::Dated),
        prio("t3", 1, PrioClass::Dated),
        prio("t4", 3, PrioClass::Rank),
        prio("t5", 3, PrioClass::Rank),
        prio("a3", 0, PrioClass::Mandatory),
    ];
    day.diagnostics.underused = vec![(Id::new("t4"), 5, 3)];
    day
}

/// M4's third fixture day: a **home day**.
///
/// `location.home_max_ci = 3` (§16), so every slot is predicted at 3 or below
/// however high the item's own `ci` is — the `ci` column, the bar's brightness
/// and §11's energy mix all read differently from the lounge day. It also
/// carries the two shapes the other fixture days do not: a batch (§7.5) and
/// the sleep routine.
pub fn home_day_plan() -> DayPlan {
    let mut day = DayPlan::empty(date(), (at(8, 0), at(17, 0)), 5);
    let sleep_end = at(22, 0) + chrono::Duration::minutes(510);
    day.segments = vec![
        block(
            (8, 0),
            (9, 0),
            "t4",
            Some(3),
            SegFlags {
                done: true,
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        other(
            (9, 0),
            (9, 20),
            SegKind::Break,
            None,
            SegFlags {
                done: true,
                planned_min: Some(20),
                ..SegFlags::default()
            },
        ),
        block(
            (9, 20),
            (10, 20),
            "t5",
            Some(3),
            SegFlags {
                current: true,
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        block(
            (10, 20),
            (11, 20),
            "t3",
            Some(3),
            SegFlags {
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        other(
            (11, 30),
            (12, 0),
            SegKind::Routine,
            Some("lunch"),
            SegFlags {
                planned_min: Some(30),
                ..SegFlags::default()
            },
        ),
        Segment {
            start: at(12, 0),
            end: at(12, 50),
            kind: SegKind::Batch(vec![Id::new("a1"), Id::new("p1")]),
            energy: Some(2),
            item: None,
            instance: None,
            flags: SegFlags {
                planned_min: Some(50),
                ..SegFlags::default()
            },
        },
        block(
            (13, 0),
            (14, 0),
            "t1",
            Some(3),
            SegFlags {
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        other(
            (14, 0),
            (14, 20),
            SegKind::Break,
            None,
            SegFlags {
                planned_min: Some(20),
                ..SegFlags::default()
            },
        ),
        block(
            (14, 20),
            (15, 20),
            "t2",
            Some(3),
            SegFlags {
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        block(
            (15, 20),
            (15, 40),
            "a3",
            Some(2),
            SegFlags {
                hot: true,
                mandatory: true,
                planned_min: Some(20),
                ..SegFlags::default()
            },
        ),
        other(
            (17, 30),
            (18, 0),
            SegKind::Routine,
            Some("dinner"),
            SegFlags {
                planned_min: Some(30),
                ..SegFlags::default()
            },
        ),
        other((21, 30), (22, 0), SegKind::WindDown, None, SegFlags::default()),
        Segment {
            start: at(22, 0),
            end: sleep_end,
            kind: SegKind::Sleep,
            energy: None,
            item: Some(Id::new("sleep")),
            instance: None,
            flags: SegFlags {
                planned_min: Some(510),
                ..SegFlags::default()
            },
        },
    ];
    day.priorities = vec![
        prio("t1", 1, PrioClass::Dated),
        prio("t2", 1, PrioClass::Dated),
        prio("t3", 1, PrioClass::Dated),
        prio("t4", 3, PrioClass::Rank),
        prio("t5", 3, PrioClass::Rank),
        prio("a1", 3, PrioClass::Rank),
        prio("a3", 0, PrioClass::Mandatory),
    ];
    day
}

/// The plan as it stood at arrival (§12.1's ghost row): the same morning, but
/// `^t4` at 11:20 and no package — the plan before the day drifted.
pub fn ghost_plan() -> DayPlan {
    let mut day = DayPlan::empty(date(), (at(7, 0), at(16, 0)), 6);
    day.segments = vec![
        block(
            (7, 0),
            (8, 0),
            "t1",
            Some(5),
            SegFlags {
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        block(
            (8, 0),
            (9, 0),
            "t2",
            Some(5),
            SegFlags {
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        other(
            (9, 0),
            (9, 20),
            SegKind::Break,
            None,
            SegFlags {
                planned_min: Some(20),
                ..SegFlags::default()
            },
        ),
        block(
            (9, 20),
            (11, 20),
            "t3",
            Some(4),
            SegFlags {
                planned_min: Some(192),
                multiplier: Some(1.6),
                ..SegFlags::default()
            },
        ),
        other(
            (11, 20),
            (11, 50),
            SegKind::Routine,
            Some("lunch"),
            SegFlags {
                planned_min: Some(30),
                ..SegFlags::default()
            },
        ),
        block(
            (11, 50),
            (12, 50),
            "t4",
            Some(4),
            SegFlags {
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
        other((12, 50), (13, 50), SegKind::Wall, Some("g1"), SegFlags::default()),
        block(
            (13, 50),
            (14, 50),
            "t5",
            Some(3),
            SegFlags {
                planned_min: Some(60),
                ..SegFlags::default()
            },
        ),
    ];
    day.priorities = plan().priorities;
    day
}
