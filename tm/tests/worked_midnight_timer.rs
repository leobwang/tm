//! **The TUI's timer reads a block worked across local midnight from the
//! log's start** — the owner's D75 (README gaps 3715 and 3625), parity P65,
//! stage 6 W-40 track T.
//!
//! `App::active_elapsed_min` — the Today pane's timer and what §9.1's overtime
//! prompt measures `est × r` against — read `.tm/state.json`'s
//! `active.started`, a bare `HH:MM`, on `state.date`. The first verb after
//! local midnight rolls `state.date` to the new day (`roll_day`), so past
//! midnight a block begun the evening before read as started TONIGHT: `0m`
//! worked, and the overtime prompt never came. It reads the instant of the
//! log's own `start` line now (`Replay::shown_worked_min`), and the pauses of
//! every day since the block began, as `tm now` and `tm done` do
//! (`cli_worked_midnight.rs`).
//!
//! The world: the §4.3 fixture day (`tui_common`), `^t3` done at 22:30, `^t4`
//! started 23:00 and paused 23:30–00:30 by a typed `tm pause` pair, and the
//! runtime state as the first verb after midnight leaves it — `state.date`
//! rolled to Tuesday, `active.started` still `23:00`.

mod tui_common;

use chrono::{DateTime, NaiveTime, TimeZone};
use chrono_tz::Tz;

use tm_core::config::Config;
use tm_core::log::{Event, LogEntry};
use tm_core::model::Id;
use tm_core::store::{ActiveBlock, RuntimeState};

use tui_common::app::App;

/// A local time on the day AFTER the fixture's.
fn tomorrow(cfg: &Config, h: u32, m: u32) -> DateTime<Tz> {
    let date = tui_common::date().succ_opt().expect("tomorrow");
    cfg.tz
        .from_local_datetime(&date.and_hms_opt(h, m, 0).expect("time"))
        .single()
        .expect("unambiguous local time")
}

/// The app at `now`, Tuesday morning: the fixture's log with `^t3` done and
/// `^t4` run into the night, and the state the first verb after midnight
/// leaves.
fn app(now: DateTime<Tz>) -> App {
    let cfg = tui_common::config();
    let mut entries = tui_common::log_entries(&cfg);
    entries.extend([
        tui_common::entry(
            &cfg,
            22,
            30,
            Event::Done {
                id: "t3".into(),
                est_min: 192,
                actual_min: 778,
                went: Some(1),
                tags: Vec::new(),
                ci: 4,
                partial: false,
            },
        ),
        tui_common::entry(
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
        tui_common::entry(&cfg, 23, 30, Event::Pause { id: "t4".into() }),
        LogEntry::new(tomorrow(&cfg, 0, 30).fixed_offset(), Event::Unpause { id: "t4".into() }),
    ]);
    let log = tui_common::chokepoint::text_of(&entries);
    let state = RuntimeState {
        date: Some(now.date_naive()),
        active: Some(ActiveBlock {
            id: Id::new("t4"),
            started: NaiveTime::from_hms_opt(23, 0, 0).expect("time"),
            est_min: 60,
            paused: false,
        }),
        ..tui_common::state()
    };
    tui_common::app_with_log_text(now, state, &log)
}

/// At 00:40 the timer reads the forty minutes worked — 23:00–23:30 and
/// 00:30–00:40 — where `active.started` on the rolled `state.date` read none.
#[test]
fn the_timer_counts_from_the_logs_start_after_midnight() {
    let cfg = tui_common::config();
    let app = app(tomorrow(&cfg, 0, 40));
    assert_eq!(app.today, tui_common::date().succ_opt().expect("tomorrow"));
    assert_eq!(app.active_elapsed_min(), Some(40), "30 before the pause, 10 after it");
    assert!(app.overtime_due().is_none(), "40 of 60 worked");
}

/// §9.1's overtime prompt comes when sixty minutes are WORKED — at 01:00,
/// the minute the owner's drive finishes the block (`cli_worked_midnight.rs`)
/// — and names the minutes the log says.
#[test]
fn the_overtime_prompt_comes_after_midnight() {
    let cfg = tui_common::config();
    assert!(app(tomorrow(&cfg, 0, 59)).overtime_due().is_none(), "59 of 60 worked");
    let over = app(tomorrow(&cfg, 1, 0)).overtime_due().expect("60 worked minutes by 01:00");
    assert_eq!(over.id, Id::new("t4"));
    assert_eq!(over.elapsed_min, 60);
}
