//! The generator behind `tests/fixtures/logs/review-14d.jsonl` (§17 M8: "a
//! synthetic 14-day log fixture").
//!
//! [`DAYS`] is the whole fixture as data: fourteen days, 2026-08-25 (Tue)
//! through 2026-09-07 (Mon), every one of them spelled out block by block,
//! break by break. [`entries`] turns that table into `log::Event`s and
//! [`jsonl`] into the committed file, so the fixture is reproducible and the
//! expected values in the tests can be read straight off the table:
//!
//! * a **standard day** ([`STD_*`](STD_BLOCKS)) is four 60-minute blocks —
//!   `ci` 5 (`#lean`, est 45m), 4 (`#soundcode`, est 60m), 3 (`#admin`, est
//!   75m) and 2 (untagged, est 60m) — with two 20-minute breaks and a
//!   30-minute lunch, so its load is `(300+240+180+120)/5 = 168` and its
//!   estimate ratios are 4/3, 1, 4/5 and 1;
//! * the deviations are deliberate: a home day (d2), a short-sleep day (d3),
//!   two weekend days (d4, d11), a rest day with nothing but a wake (d5), an
//!   interrupted day (d6), an unattributed 45-minute gap (d8), a skipped
//!   routine (d10) and the fully-worked review day (d13) whose numbers are
//!   §12.4's.
//!
//! Times are wall-clock in `America/Chicago`, which is `-05:00` for every
//! date in the range (no DST boundary is crossed).

#![allow(dead_code)]

/// The test chokepoint (step R12): every replay here is read through it.
#[path = "../../../tm/tests/support/replay.rs"]
pub mod chokepoint;

use std::path::{Path, PathBuf};

use chrono::{DateTime, FixedOffset, NaiveDate, NaiveTime, TimeZone};
use chrono_tz::Tz;
use tm_core::config::Config;
use tm_core::log::{self, Event, LogEntry, Replay};

/// The zone every timestamp in the fixture is written in.
pub const TZ: Tz = chrono_tz::America::Chicago;

/// The fixed offset of `America/Chicago` over the fixture's range (CDT).
pub const OFFSET_SECS: i32 = -5 * 3600;

/// The fixture's first day.
pub const FIRST_DAY: (i32, u32, u32) = (2026, 8, 25);

/// The fixture's last day — the day §12.4's review screen is written for.
pub const LAST_DAY: (i32, u32, u32) = (2026, 9, 7);

// ---------------------------------------------------------------------------
// The table
// ---------------------------------------------------------------------------

/// One timed block: `start`/`done` are wall-clock, `actual_min` is what the
/// `done` event reports (it differs from `done − start` on an interrupted
/// block, whose clock time includes the interruption).
pub struct BlockSpec {
    pub id: &'static str,
    pub start: &'static str,
    pub done: &'static str,
    pub actual_min: u32,
    pub est_min: u32,
    pub ci: u8,
    pub tag: &'static str,
    pub went: u8,
    pub pred: u8,
    pub rep: u8,
}

/// One break; `start` is when it began, so its segment is
/// `[start, start + actual_min]`.
pub struct BreakSpec {
    pub start: &'static str,
    pub planned_min: u32,
    pub actual_min: u32,
    pub place: &'static str,
}

/// One energy report outside a block start.
pub struct EnergySpec {
    pub at: &'static str,
    pub pred: u8,
    pub rep: u8,
}

/// One answered idle prompt; its segment is `[at − min, at]`.
pub struct IdleSpec {
    pub at: &'static str,
    pub attributed: &'static str,
    pub min: u32,
}

/// One interruption.
pub struct InterruptSpec {
    pub at: &'static str,
    pub id: &'static str,
    pub resume_at: &'static str,
    pub lost_min: u32,
    pub dropped: &'static [&'static str],
}

/// One routine instance; its segment is `[at − actual_min, at]`.
pub struct RoutineSpec {
    pub at: &'static str,
    pub item: &'static str,
    pub status: &'static str,
    pub actual_min: Option<u32>,
}

/// One skipped routine instance.
pub struct SkipSpec {
    pub at: &'static str,
    pub item: &'static str,
}

/// One demotion (a close moving a line to the enclosing horizon).
pub struct DemoteSpec {
    pub at: &'static str,
    pub id: &'static str,
    pub from: &'static str,
    pub to: &'static str,
    pub est_min: u32,
}

/// One `plan` event.
pub struct PlanSpec {
    pub at: &'static str,
    pub hash: &'static str,
    pub replans_today: u32,
    pub drift_min: u32,
}

/// One day of the fixture.
pub struct DaySpec {
    pub date: &'static str,
    pub wake: &'static str,
    pub slept_min: u32,
    pub onset_min: Option<u32>,
    /// `None` = a day with no `arrive` (and so no location or budget).
    pub arrive: Option<&'static str>,
    pub loc: &'static str,
    pub window: [&'static str; 2],
    pub budget: u32,
    pub blocks: &'static [BlockSpec],
    pub breaks: &'static [BreakSpec],
    pub energy: &'static [EnergySpec],
    pub idles: &'static [IdleSpec],
    pub interrupts: &'static [InterruptSpec],
    pub routines: &'static [RoutineSpec],
    pub skips: &'static [SkipSpec],
    pub demotes: &'static [DemoteSpec],
    pub plans: &'static [PlanSpec],
}

const NO_BREAKS: &[BreakSpec] = &[];
const NO_ENERGY: &[EnergySpec] = &[];
const NO_IDLE: &[IdleSpec] = &[];
const NO_INTERRUPTS: &[InterruptSpec] = &[];
const NO_ROUTINES: &[RoutineSpec] = &[];
const NO_SKIPS: &[SkipSpec] = &[];
const NO_DEMOTES: &[DemoteSpec] = &[];
const NO_BLOCKS: &[BlockSpec] = &[];

/// The two breaks of a standard day (after blocks 1 and 2, §16's
/// `break_after_blocks = 2`… the second is early on purpose: the fixture
/// keeps every day contiguous so unattributed gaps are only where they are
/// meant to be).
const STD_BREAKS: &[BreakSpec] = &[
    BreakSpec { start: "08:05", planned_min: 20, actual_min: 20, place: "walk" },
    BreakSpec { start: "09:25", planned_min: 20, actual_min: 20, place: "seat" },
];

/// Lunch, filling 10:45–11:15 on a standard day.
const STD_LUNCH: &[RoutineSpec] = &[RoutineSpec {
    at: "11:15",
    item: "lunch",
    status: "done",
    actual_min: Some(30),
}];

/// The four blocks of a standard day: ci 5/4/3/2, tags lean/soundcode/admin,
/// estimates 45/60/75/60 against 60 actual minutes each.
macro_rules! std_blocks {
    ($a:literal, $b:literal, $c:literal, $d:literal, $ra:literal, $rb:literal, $rc:literal, $rd:literal) => {
        &[
            BlockSpec { id: $a, start: "07:05", done: "08:05", actual_min: 60, est_min: 45, ci: 5, tag: "lean", went: 1, pred: 5, rep: $ra },
            BlockSpec { id: $b, start: "08:25", done: "09:25", actual_min: 60, est_min: 60, ci: 4, tag: "soundcode", went: 1, pred: 5, rep: $rb },
            BlockSpec { id: $c, start: "09:45", done: "10:45", actual_min: 60, est_min: 75, ci: 3, tag: "admin", went: 1, pred: 4, rep: $rc },
            BlockSpec { id: $d, start: "11:15", done: "12:15", actual_min: 60, est_min: 60, ci: 2, tag: "", went: 1, pred: 4, rep: $rd },
        ]
    };
}

/// The block layout a standard day uses (documentation anchor for the module
/// header's `STD_*` reference).
pub const STD_BLOCKS: &[BlockSpec] = std_blocks!("b00a", "b00b", "b00c", "b00d", 5, 5, 4, 4);

/// The whole fixture.
pub const DAYS: &[DaySpec] = &[
    // d0 · Tue 2026-08-25 · a standard lounge day, everything on plan.
    DaySpec {
        date: "2026-08-25",
        wake: "06:05",
        slept_min: 480,
        onset_min: None,
        arrive: Some("07:00"),
        loc: "lounge",
        window: ["07:00", "15:00"],
        budget: 6,
        blocks: std_blocks!("b00a", "b00b", "b00c", "b00d", 5, 5, 4, 4),
        breaks: STD_BREAKS,
        energy: NO_ENERGY,
        idles: NO_IDLE,
        interrupts: NO_INTERRUPTS,
        routines: STD_LUNCH,
        skips: NO_SKIPS,
        demotes: NO_DEMOTES,
        plans: &[PlanSpec { at: "12:20", hash: "p00", replans_today: 1, drift_min: 0 }],
    },
    // d1 · Wed 2026-08-26 · standard, plus 15 attributed leak minutes.
    DaySpec {
        date: "2026-08-26",
        wake: "06:05",
        slept_min: 480,
        onset_min: None,
        arrive: Some("07:00"),
        loc: "lounge",
        window: ["07:00", "15:00"],
        budget: 6,
        blocks: std_blocks!("b01a", "b01b", "b01c", "b01d", 5, 5, 4, 3),
        breaks: STD_BREAKS,
        energy: NO_ENERGY,
        idles: &[IdleSpec { at: "12:30", attributed: "leak", min: 15 }],
        interrupts: NO_INTERRUPTS,
        routines: STD_LUNCH,
        skips: NO_SKIPS,
        demotes: NO_DEMOTES,
        plans: &[PlanSpec { at: "12:35", hash: "p01", replans_today: 1, drift_min: 0 }],
    },
    // d2 · Thu 2026-08-27 · a home day: three blocks, ci capped at 3.
    DaySpec {
        date: "2026-08-27",
        wake: "06:05",
        slept_min: 470,
        onset_min: None,
        arrive: Some("07:00"),
        loc: "home",
        window: ["07:00", "15:00"],
        budget: 6,
        blocks: &[
            BlockSpec { id: "b02a", start: "07:05", done: "08:05", actual_min: 60, est_min: 75, ci: 3, tag: "admin", went: 1, pred: 4, rep: 4 },
            BlockSpec { id: "b02b", start: "08:30", done: "09:30", actual_min: 60, est_min: 75, ci: 3, tag: "admin", went: 1, pred: 4, rep: 3 },
            BlockSpec { id: "b02c", start: "09:30", done: "10:30", actual_min: 60, est_min: 60, ci: 2, tag: "soundcode", went: 1, pred: 3, rep: 3 },
        ],
        breaks: &[BreakSpec { start: "08:05", planned_min: 20, actual_min: 25, place: "seat" }],
        energy: NO_ENERGY,
        idles: NO_IDLE,
        interrupts: NO_INTERRUPTS,
        routines: NO_ROUTINES,
        skips: NO_SKIPS,
        demotes: NO_DEMOTES,
        plans: &[PlanSpec { at: "10:40", hash: "p02", replans_today: 1, drift_min: 0 }],
    },
    // d3 · Fri 2026-08-28 · short sleep (6h20m) with a long onset.
    DaySpec {
        date: "2026-08-28",
        wake: "06:05",
        slept_min: 380,
        onset_min: Some(45),
        arrive: Some("07:00"),
        loc: "lounge",
        window: ["07:00", "15:00"],
        budget: 6,
        blocks: &[
            BlockSpec { id: "b03a", start: "07:05", done: "08:05", actual_min: 60, est_min: 45, ci: 5, tag: "lean", went: 2, pred: 4, rep: 3 },
            BlockSpec { id: "b03b", start: "08:25", done: "09:25", actual_min: 60, est_min: 60, ci: 4, tag: "soundcode", went: 1, pred: 4, rep: 4 },
            BlockSpec { id: "b03c", start: "09:25", done: "10:25", actual_min: 60, est_min: 75, ci: 3, tag: "admin", went: 1, pred: 3, rep: 3 },
        ],
        breaks: &[BreakSpec { start: "08:05", planned_min: 20, actual_min: 20, place: "walk" }],
        energy: &[EnergySpec { at: "11:00", pred: 3, rep: 2 }],
        idles: NO_IDLE,
        interrupts: NO_INTERRUPTS,
        routines: NO_ROUTINES,
        skips: NO_SKIPS,
        demotes: NO_DEMOTES,
        plans: &[PlanSpec { at: "10:30", hash: "p03", replans_today: 2, drift_min: 20 }],
    },
    // d4 · Sat 2026-08-29 · a late weekend day at home, two blocks.
    DaySpec {
        date: "2026-08-29",
        wake: "08:30",
        slept_min: 540,
        onset_min: None,
        arrive: Some("10:00"),
        loc: "home",
        window: ["10:00", "18:00"],
        budget: 6,
        blocks: &[
            BlockSpec { id: "b04a", start: "10:05", done: "11:05", actual_min: 60, est_min: 75, ci: 3, tag: "admin", went: 1, pred: 4, rep: 4 },
            BlockSpec { id: "b04b", start: "11:25", done: "12:25", actual_min: 60, est_min: 60, ci: 2, tag: "", went: 1, pred: 3, rep: 3 },
        ],
        breaks: &[BreakSpec { start: "11:05", planned_min: 20, actual_min: 20, place: "walk" }],
        energy: NO_ENERGY,
        idles: NO_IDLE,
        interrupts: NO_INTERRUPTS,
        routines: NO_ROUTINES,
        skips: NO_SKIPS,
        demotes: NO_DEMOTES,
        plans: &[PlanSpec { at: "12:30", hash: "p04", replans_today: 1, drift_min: 0 }],
    },
    // d5 · Sun 2026-08-30 · a day off: a wake and nothing else.
    DaySpec {
        date: "2026-08-30",
        wake: "09:00",
        slept_min: 560,
        onset_min: None,
        arrive: None,
        loc: "lounge",
        window: ["00:00", "00:00"],
        budget: 0,
        blocks: NO_BLOCKS,
        breaks: NO_BREAKS,
        energy: NO_ENERGY,
        idles: NO_IDLE,
        interrupts: NO_INTERRUPTS,
        routines: NO_ROUTINES,
        skips: NO_SKIPS,
        demotes: NO_DEMOTES,
        plans: &[],
    },
    // d6 · Mon 2026-08-31 · W36 opens: a 30-minute interruption inside the
    // third block, and last week's close demoting ^m9.
    DaySpec {
        date: "2026-08-31",
        wake: "06:05",
        slept_min: 480,
        onset_min: None,
        arrive: Some("07:00"),
        loc: "lounge",
        window: ["07:00", "15:00"],
        budget: 6,
        blocks: &[
            BlockSpec { id: "b06a", start: "07:05", done: "08:05", actual_min: 60, est_min: 45, ci: 5, tag: "lean", went: 1, pred: 5, rep: 5 },
            BlockSpec { id: "b06b", start: "08:25", done: "09:25", actual_min: 60, est_min: 60, ci: 4, tag: "soundcode", went: 1, pred: 5, rep: 5 },
            BlockSpec { id: "b06c", start: "09:45", done: "11:15", actual_min: 60, est_min: 75, ci: 3, tag: "admin", went: 1, pred: 4, rep: 3 },
            BlockSpec { id: "b06d", start: "11:45", done: "12:45", actual_min: 60, est_min: 60, ci: 2, tag: "", went: 1, pred: 4, rep: 4 },
        ],
        breaks: STD_BREAKS,
        energy: NO_ENERGY,
        idles: NO_IDLE,
        interrupts: &[InterruptSpec { at: "10:00", id: "b06c", resume_at: "10:30", lost_min: 30, dropped: &["b06z"] }],
        routines: &[RoutineSpec { at: "11:45", item: "lunch", status: "done", actual_min: Some(30) }],
        skips: NO_SKIPS,
        demotes: &[DemoteSpec { at: "07:00", id: "m9", from: "2026-W35", to: "2026-08", est_min: 60 }],
        plans: &[PlanSpec { at: "12:50", hash: "p06", replans_today: 2, drift_min: 25 }],
    },
    // d7 · Tue 2026-09-01 · standard.
    DaySpec {
        date: "2026-09-01",
        wake: "06:05",
        slept_min: 480,
        onset_min: None,
        arrive: Some("07:00"),
        loc: "lounge",
        window: ["07:00", "15:00"],
        budget: 6,
        blocks: std_blocks!("b07a", "b07b", "b07c", "b07d", 5, 5, 4, 4),
        breaks: STD_BREAKS,
        energy: NO_ENERGY,
        idles: NO_IDLE,
        interrupts: NO_INTERRUPTS,
        routines: STD_LUNCH,
        skips: NO_SKIPS,
        demotes: NO_DEMOTES,
        plans: &[PlanSpec { at: "12:20", hash: "p07", replans_today: 1, drift_min: 0 }],
    },
    // d8 · Wed 2026-09-02 · no lunch, and a 45-minute hole nobody attributed.
    DaySpec {
        date: "2026-09-02",
        wake: "06:05",
        slept_min: 480,
        onset_min: None,
        arrive: Some("07:00"),
        loc: "lounge",
        window: ["07:00", "15:00"],
        budget: 6,
        blocks: &[
            BlockSpec { id: "b08a", start: "07:05", done: "08:05", actual_min: 60, est_min: 45, ci: 5, tag: "lean", went: 1, pred: 5, rep: 5 },
            BlockSpec { id: "b08b", start: "08:25", done: "09:25", actual_min: 60, est_min: 60, ci: 4, tag: "soundcode", went: 1, pred: 5, rep: 5 },
            BlockSpec { id: "b08c", start: "09:45", done: "10:45", actual_min: 60, est_min: 75, ci: 3, tag: "admin", went: 1, pred: 4, rep: 4 },
            BlockSpec { id: "b08d", start: "11:30", done: "12:30", actual_min: 60, est_min: 60, ci: 2, tag: "", went: 1, pred: 4, rep: 3 },
        ],
        breaks: STD_BREAKS,
        energy: NO_ENERGY,
        idles: NO_IDLE,
        interrupts: NO_INTERRUPTS,
        routines: NO_ROUTINES,
        skips: NO_SKIPS,
        demotes: NO_DEMOTES,
        plans: &[PlanSpec { at: "12:35", hash: "p08", replans_today: 1, drift_min: 0 }],
    },
    // d9 · Thu 2026-09-03 · short sleep again; every report one under.
    DaySpec {
        date: "2026-09-03",
        wake: "06:05",
        slept_min: 400,
        onset_min: None,
        arrive: Some("07:00"),
        loc: "lounge",
        window: ["07:00", "15:00"],
        budget: 6,
        blocks: std_blocks!("b09a", "b09b", "b09c", "b09d", 4, 4, 4, 3),
        breaks: STD_BREAKS,
        energy: NO_ENERGY,
        idles: NO_IDLE,
        interrupts: NO_INTERRUPTS,
        routines: STD_LUNCH,
        skips: NO_SKIPS,
        demotes: NO_DEMOTES,
        plans: &[PlanSpec { at: "12:20", hash: "p09", replans_today: 1, drift_min: 0 }],
    },
    // d10 · Fri 2026-09-04 · standard, with the groceries run skipped.
    DaySpec {
        date: "2026-09-04",
        wake: "06:05",
        slept_min: 480,
        onset_min: None,
        arrive: Some("07:00"),
        loc: "lounge",
        window: ["07:00", "15:00"],
        budget: 6,
        blocks: std_blocks!("b10a", "b10b", "b10c", "b10d", 5, 5, 4, 4),
        breaks: STD_BREAKS,
        energy: NO_ENERGY,
        idles: NO_IDLE,
        interrupts: NO_INTERRUPTS,
        routines: STD_LUNCH,
        skips: &[SkipSpec { at: "18:00", item: "groceries" }],
        demotes: NO_DEMOTES,
        plans: &[PlanSpec { at: "12:20", hash: "p10", replans_today: 1, drift_min: 0 }],
    },
    // d11 · Sat 2026-09-05 · a weekend in the lounge, two blocks.
    DaySpec {
        date: "2026-09-05",
        wake: "08:30",
        slept_min: 520,
        onset_min: None,
        arrive: Some("10:00"),
        loc: "lounge",
        window: ["10:00", "18:00"],
        budget: 6,
        blocks: &[
            BlockSpec { id: "b11a", start: "10:05", done: "11:05", actual_min: 60, est_min: 75, ci: 3, tag: "admin", went: 1, pred: 4, rep: 4 },
            BlockSpec { id: "b11b", start: "11:25", done: "12:25", actual_min: 60, est_min: 60, ci: 2, tag: "", went: 1, pred: 3, rep: 3 },
        ],
        breaks: &[BreakSpec { start: "11:05", planned_min: 20, actual_min: 20, place: "walk" }],
        energy: NO_ENERGY,
        idles: NO_IDLE,
        interrupts: NO_INTERRUPTS,
        routines: NO_ROUTINES,
        skips: NO_SKIPS,
        demotes: NO_DEMOTES,
        plans: &[PlanSpec { at: "12:30", hash: "p11", replans_today: 1, drift_min: 0 }],
    },
    // d12 · Sun 2026-09-06 · W36 closes: ^m2 and ^m4 are demoted to the month.
    DaySpec {
        date: "2026-09-06",
        wake: "08:00",
        slept_min: 500,
        onset_min: None,
        arrive: Some("09:30"),
        loc: "lounge",
        window: ["09:30", "17:30"],
        budget: 6,
        blocks: &[
            BlockSpec { id: "b12a", start: "09:35", done: "10:35", actual_min: 60, est_min: 45, ci: 5, tag: "lean", went: 1, pred: 5, rep: 5 },
            BlockSpec { id: "b12b", start: "10:55", done: "11:55", actual_min: 60, est_min: 60, ci: 4, tag: "soundcode", went: 1, pred: 5, rep: 4 },
        ],
        breaks: &[BreakSpec { start: "10:35", planned_min: 20, actual_min: 20, place: "seat" }],
        energy: NO_ENERGY,
        idles: NO_IDLE,
        interrupts: NO_INTERRUPTS,
        routines: NO_ROUTINES,
        skips: NO_SKIPS,
        demotes: &[
            DemoteSpec { at: "21:00", id: "m2", from: "2026-W36", to: "2026-09", est_min: 180 },
            DemoteSpec { at: "21:00", id: "m4", from: "2026-W36", to: "2026-09", est_min: 120 },
        ],
        plans: &[PlanSpec { at: "12:00", hash: "p12", replans_today: 1, drift_min: 0 }],
    },
    // d13 · Mon 2026-09-07 · the day §12.4's Review screen is written for:
    // five blocks of six, a 55-minute interruption, 14 leaked minutes, three
    // breaks (24/31/20) and four replans drifting 75 minutes.
    DaySpec {
        date: "2026-09-07",
        wake: "06:05",
        slept_min: 490,
        onset_min: Some(25),
        arrive: Some("07:00"),
        loc: "lounge",
        window: ["07:00", "16:00"],
        budget: 6,
        blocks: &[
            BlockSpec { id: "t1", start: "07:02", done: "08:09", actual_min: 67, est_min: 60, ci: 5, tag: "lean", went: 1, pred: 5, rep: 5 },
            BlockSpec { id: "t2", start: "08:33", done: "09:31", actual_min: 58, est_min: 60, ci: 5, tag: "lean", went: 1, pred: 4, rep: 5 },
            BlockSpec { id: "t3", start: "10:02", done: "13:32", actual_min: 155, est_min: 120, ci: 4, tag: "lean", went: 2, pred: 5, rep: 5 },
            BlockSpec { id: "t4", start: "13:52", done: "14:52", actual_min: 60, est_min: 60, ci: 3, tag: "soundcode", went: 1, pred: 4, rep: 3 },
            BlockSpec { id: "p1", start: "15:06", done: "15:26", actual_min: 20, est_min: 20, ci: 2, tag: "admin", went: 1, pred: 3, rep: 2 },
        ],
        breaks: &[
            BreakSpec { start: "08:09", planned_min: 20, actual_min: 24, place: "walk" },
            BreakSpec { start: "09:31", planned_min: 20, actual_min: 31, place: "seat" },
            BreakSpec { start: "13:32", planned_min: 20, actual_min: 20, place: "walk" },
        ],
        energy: &[
            EnergySpec { at: "10:15", pred: 5, rep: 5 },
            EnergySpec { at: "11:15", pred: 4, rep: 4 },
            EnergySpec { at: "12:15", pred: 4, rep: 4 },
            EnergySpec { at: "14:15", pred: 4, rep: 3 },
            EnergySpec { at: "15:40", pred: 3, rep: 2 },
        ],
        idles: &[IdleSpec { at: "15:06", attributed: "leak", min: 14 }],
        interrupts: &[InterruptSpec { at: "12:10", id: "t3", resume_at: "13:05", lost_min: 55, dropped: &["t5"] }],
        routines: &[RoutineSpec { at: "15:56", item: "package", status: "done", actual_min: Some(30) }],
        skips: NO_SKIPS,
        demotes: &[DemoteSpec { at: "21:00", id: "t5", from: "2026-09-07", to: "2026-W37", est_min: 30 }],
        plans: &[
            PlanSpec { at: "07:00", hash: "a91f", replans_today: 1, drift_min: 0 },
            PlanSpec { at: "09:35", hash: "b02c", replans_today: 2, drift_min: 25 },
            PlanSpec { at: "13:06", hash: "c73d", replans_today: 3, drift_min: 30 },
            PlanSpec { at: "15:00", hash: "d41e", replans_today: 4, drift_min: 20 },
        ],
    },
];

// ---------------------------------------------------------------------------
// Building the log
// ---------------------------------------------------------------------------

fn offset() -> FixedOffset {
    FixedOffset::east_opt(OFFSET_SECS).expect("valid offset")
}

fn date_of(spec: &DaySpec) -> NaiveDate {
    NaiveDate::parse_from_str(spec.date, "%Y-%m-%d").expect("valid date")
}

fn at(spec: &DaySpec, hhmm: &str) -> DateTime<FixedOffset> {
    let time = NaiveTime::parse_from_str(hhmm, "%H:%M").expect("valid time");
    offset()
        .from_local_datetime(&date_of(spec).and_time(time))
        .single()
        .expect("unambiguous local time")
}

/// The fixture's events, in timestamp order (ties keep the order below:
/// wake, arrive, plans, demotes, block starts and dones, breaks, energy
/// reports, interruptions, idle prompts, routines, skips).
pub fn entries() -> Vec<LogEntry> {
    let mut out: Vec<LogEntry> = Vec::new();
    for spec in DAYS {
        let wake = at(spec, spec.wake);
        let mut day: Vec<LogEntry> = Vec::new();
        day.push(LogEntry::new(
            wake,
            Event::Wake {
                slept_min: spec.slept_min,
                onset_min: spec.onset_min,
            },
        ));
        if let Some(arrive) = spec.arrive {
            day.push(LogEntry::new(
                at(spec, arrive),
                Event::Arrive {
                    loc: spec.loc.to_string(),
                    window: [spec.window[0].to_string(), spec.window[1].to_string()],
                    budget: spec.budget,
                },
            ));
        }
        for p in spec.plans {
            day.push(LogEntry::new(
                at(spec, p.at),
                Event::Plan {
                    hash: p.hash.to_string(),
                    replans_today: p.replans_today,
                    drift_min: p.drift_min,
                },
            ));
        }
        for d in spec.demotes {
            day.push(LogEntry::new(
                at(spec, d.at),
                Event::Demote {
                    id: d.id.to_string(),
                    from: d.from.to_string(),
                    to: d.to.to_string(),
                    est_min: d.est_min,
                },
            ));
        }
        for (i, b) in spec.blocks.iter().enumerate() {
            let start = at(spec, b.start);
            let since_break = spec
                .breaks
                .iter()
                .map(|br| at(spec, br.start) + chrono::Duration::minutes(br.actual_min as i64))
                .filter(|end| *end <= start)
                .max()
                .map_or(0, |end| {
                    start.signed_duration_since(end).num_minutes().max(0) as u32
                });
            day.push(LogEntry::new(
                start,
                Event::Start {
                    id: b.id.to_string(),
                    pred: b.pred,
                    rep: Some(b.rep),
                    hsw: log::hours_since_wake(&start, &wake),
                    slept_min: spec.slept_min,
                    loc: spec.loc.to_string(),
                    blocks_done: i as u32,
                    since_break_min: since_break,
                },
            ));
            day.push(LogEntry::new(
                at(spec, b.done),
                Event::Done {
                    id: b.id.to_string(),
                    est_min: b.est_min,
                    actual_min: b.actual_min,
                    went: Some(b.went),
                    tags: if b.tag.is_empty() {
                        Vec::new()
                    } else {
                        vec![b.tag.to_string()]
                    },
                    ci: b.ci,
                    partial: false,
                },
            ));
        }
        for br in spec.breaks {
            day.push(LogEntry::new(
                at(spec, br.start),
                Event::Break {
                    planned_min: br.planned_min,
                    actual_min: Some(br.actual_min),
                    r#where: Some(br.place.to_string()),
                },
            ));
        }
        for e in spec.energy {
            let t = at(spec, e.at);
            day.push(LogEntry::new(
                t,
                Event::Energy {
                    pred: e.pred,
                    rep: e.rep,
                    hsw: log::hours_since_wake(&t, &wake),
                    loc: spec.loc.to_string(),
                },
            ));
        }
        for i in spec.interrupts {
            day.push(LogEntry::new(
                at(spec, i.at),
                Event::Interrupt {
                    id: Some(i.id.to_string()),
                },
            ));
            day.push(LogEntry::new(
                at(spec, i.resume_at),
                Event::Resume {
                    lost_min: i.lost_min,
                    dropped: i.dropped.iter().map(|s| s.to_string()).collect(),
                },
            ));
        }
        for i in spec.idles {
            day.push(LogEntry::new(
                at(spec, i.at),
                Event::Idle {
                    attributed: i.attributed.to_string(),
                    min: i.min,
                },
            ));
        }
        for r in spec.routines {
            day.push(LogEntry::new(
                at(spec, r.at),
                Event::Routine {
                    item: r.item.to_string(),
                    inst: spec.date.to_string(),
                    status: r.status.to_string(),
                    actual_min: r.actual_min,
                },
            ));
        }
        for s in spec.skips {
            day.push(LogEntry::new(
                at(spec, s.at),
                Event::Skip {
                    item: s.item.to_string(),
                    inst: spec.date.to_string(),
                },
            ));
        }
        day.sort_by_key(|e| e.t);
        out.extend(day);
    }
    out
}

/// The fixture file's exact contents.
pub fn jsonl() -> String {
    let mut out = String::new();
    for e in entries() {
        out.push_str(&e.to_json().expect("event serializes"));
        out.push('\n');
    }
    out
}

/// `tm-core/tests/fixtures`.
pub fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// The committed fixture file.
pub fn fixture_path() -> PathBuf {
    fixtures().join("logs/review-14d.jsonl")
}

/// The `plan-basic` configuration (`tz = America/Chicago`, §16 defaults).
pub fn config() -> Config {
    Config::load(fixtures().join("plan-basic/config.toml")).expect("config loads")
}

/// The committed fixture's text; it has no malformed line.
pub fn log_text() -> String {
    let text = std::fs::read_to_string(fixture_path()).expect("fixture reads");
    let warnings = chokepoint::warning_lines_of_text(&text);
    assert!(warnings.is_empty(), "{:?}", warnings);
    text
}

/// The committed fixture, replayed over every day.
pub fn replay() -> Replay {
    chokepoint::replay_of_text(&log_text(), TZ)
}

/// The month file the week and month reviews are read against: three
/// outcomes (one finished) and two archived lines carrying enough stamps to
/// reach the cut list.
pub const MONTH_MD: &str = "\
---
month: 2026-09
---
# Outcomes
- [x] 5 !1 Lean: through ch.8 of the tutorial          ^O1
- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2
- [ ] 2 !3 Winter course selection + admin done        ^O3

# Demoted
- [-] 2 2b Re-do the seminar slides @O3 est:2b demoted:W35,W36 ^m8
- [-] 4 1b Rollback smoke test      @O2 est:1b demoted:W34,W35,W36 ^m9
";

/// The week the [`week_review`](tm_core::review::week_review) tests read:
/// one milestone finished, two demoted out of it, one still open, and a task
/// whose id is one of the fixture's logged blocks (so the rollups see logged
/// minutes).
pub const WEEK_MD: &str = "\
---
week: 2026-W36
window: 2026-08-31..2026-09-06
budget: 25
planned: 20
---
# Milestones
- [x] 5 6b Finish ch.5 exercises        @O1 ^m1
- [-] 4 6b Rollback path passes tests   @O2 est:3b demoted:W36 ^m2
- [ ] 5 3b Read ch.6                    @O1 ^m3
- [-] 2 2b Pick winter courses          @O3 est:2b demoted:W35,W36 ^m4

# Tasks
- [x] 5 1b Sunday reading               @m3 ^b12a
";

/// The two files above, ready for [`Tree::from_texts`](tm_core::tree::Tree).
pub fn plan_texts() -> Vec<(&'static str, &'static str)> {
    vec![
        ("month/2026-09.md", MONTH_MD),
        ("week/2026-W36.md", WEEK_MD),
    ]
}

/// The tree those two files make.
pub fn plan_tree(cfg: &Config) -> tm_core::tree::Tree {
    tm_core::tree::Tree::from_texts(&plan_texts(), cfg)
}

/// A date in the fixture's range.
pub fn date(y: i32, m: u32, d: u32) -> NaiveDate {
    NaiveDate::from_ymd_opt(y, m, d).expect("valid date")
}

/// The review day (2026-09-07).
pub fn last_day() -> NaiveDate {
    date(LAST_DAY.0, LAST_DAY.1, LAST_DAY.2)
}
