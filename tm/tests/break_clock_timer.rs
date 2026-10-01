//! **The TUI reads a running break's start as the CLI does** — the campaign's
//! D81 call on README gap 3820, parity P73, stage 6 W-41 track T.
//!
//! `App::active_elapsed_min` (the Today pane's timer, and what §9.1's overtime
//! prompt measures) and `App::break_overrun_since` (§9's "Break overran", which
//! raises §9.2's idle prompt) placed `.tm/state.json`'s `break.started` on
//! `state.date`, which the first verb after local midnight rolls to the new day
//! — so a break begun at 23:50 read as begun TONIGHT: the timer counted it as
//! worked and the overrun prompt waited a day. Both read
//! `BreakState::started_at` now, the one reading `tm done` and `tm now` take
//! (`cli_break_clock.rs`).
//!
//! The world: the §4.3 fixture day (`tui_common`), `^t3` done at 22:30, `^t4`
//! started 23:00 and paused by a break begun at 23:50, and the runtime state as
//! the first verb after midnight leaves it — `state.date` rolled to Tuesday.

mod tui_common;

use chrono::{DateTime, NaiveTime, TimeZone};
use chrono_tz::Tz;

use tm_core::config::Config;
use tm_core::log::Event;
use tm_core::model::Id;
use tm_core::store::{ActiveBlock, BreakState, RuntimeState};

use tui_common::app::App;

/// A local time on the day AFTER the fixture's.
fn tomorrow(cfg: &Config, h: u32, m: u32) -> DateTime<Tz> {
    let date = tui_common::date().succ_opt().expect("tomorrow");
    cfg.tz
        .from_local_datetime(&date.and_hms_opt(h, m, 0).expect("time"))
        .single()
        .expect("unambiguous local time")
}

/// The app at `now`, Tuesday just after midnight, with the break running.
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
    ]);
    let log = tui_common::chokepoint::text_of(&entries);
    let hm = |h, m| NaiveTime::from_hms_opt(h, m, 0).expect("time");
    let state = RuntimeState {
        date: Some(now.date_naive()),
        active: Some(ActiveBlock { id: Id::new("t4"), started: hm(23, 0), est_min: 60, paused: true }),
        break_: Some(BreakState { started: Some(hm(23, 50)), planned_min: 20, place: None }),
        ..tui_common::state()
    };
    tui_common::app_with_log_text(now, state, &log)
}

/// At 00:05 the timer reads the fifty minutes worked before the break; the
/// break, begun at 23:50 last night, is not worked.
#[test]
fn the_timer_nets_out_a_break_begun_before_midnight() {
    let cfg = tui_common::config();
    let app = app(tomorrow(&cfg, 0, 5));
    assert_eq!(app.active_elapsed_min(), Some(50), "23:00–23:50; the break since");
}

/// The break was due back at 00:10; at 00:25 it has overrun by fifteen
/// minutes and §9.2's idle prompt is raised — where the break read as begun
/// tonight was never overdue.
#[test]
fn a_break_begun_before_midnight_overruns_after_it() {
    let cfg = tui_common::config();
    assert_eq!(app(tomorrow(&cfg, 0, 9)).break_overrun_since(), None, "still inside its 20m");
    let app = app(tomorrow(&cfg, 0, 25));
    assert_eq!(app.break_overrun_since(), Some(tomorrow(&cfg, 0, 10)));
    let idle = app.idle_due().expect("the overrun is an idle gap");
    assert_eq!(idle.minutes, 15);
}

/// **The break prompt lists the ONE table of places** (the campaign's D81 call
/// on README gap 3903, parity P75): `b` asks `break where?` with each place's
/// key and word as `tm break --where` reads them, in the table's order, and
/// each key picks its place.
#[test]
fn the_break_prompt_lists_the_tables_places() {
    use tm_core::store::BreakPlace;
    let mut app = tui_common::app();
    app.mode = tui_common::app::Mode::BreakWhere;
    let hint = tui_common::lines(&[tui_common::today::hint_line(&app, 120)]);
    assert!(
        hint.contains("break where? w walk · s seat · b bed · p phone"),
        "{hint}"
    );
    for place in BreakPlace::all() {
        assert!(hint.contains(&format!("{} {}", place.key(), place.as_str())), "{hint}");
        assert_eq!(tui_common::app::BreakPlace::from_key(place.key()), Some(place));
    }
}
