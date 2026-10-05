//! `capacity.rs`: §8.1 window and budget, §8.2 step 3 slot cutting and
//! energising, checked against the §4.3 day (`day/2026-09-07.md`: arrival
//! 07:00, meeting 12:50–13:50, window ends 16:00).
//!
//! **Two kinds of test, since R3 leaves fork 4748911's slot cut and energy with no shipped
//! caller** (stage 6 W-46 track C; README gap 4752, the class).  §8.1's window and budget
//! (`window_and_budget`, `budget_blocks`) are the binary's and keep their tests; where one of
//! them also checks the fork's cut or §8.1's equation, it reads fork `cut_slots` and
//! `wall_minutes` BY VALUE (the `tm` tests' `support/forkcap.rs`: this binary's frozen file,
//! `tm-oracle capacity` under `TM_ORACLE`).  Every test of the slot cut and the energy alone is
//! the fork's own behaviour, still calls the in-tree copy, and is deleted with it at R3 (README
//! "W-46 track C", the deletion list) — and with it `remaining_budget`'s two assertions below.

use chrono::{DateTime, TimeZone};
use chrono_tz::Tz;
use tm_core::capacity::{budget_blocks, window_and_budget};
use tm_core::config::Config;

/// Fork 4748911's answers, by value (W-46 track C) — the `tm` tests' module, by path.
#[allow(dead_code)]
#[path = "../../tm/tests/support/forkcap.rs"]
mod forkcap;

const TZ: Tz = Tz::America__Chicago;

fn at(h: u32, m: u32) -> DateTime<Tz> {
    TZ.with_ymd_and_hms(2026, 9, 7, h, m, 0).single().unwrap()
}

fn hm(t: DateTime<Tz>) -> String {
    t.format("%H:%M").to_string()
}

// ---------------------------------------------------------------------------
// §8.1
// ---------------------------------------------------------------------------

/// §8.1: "8h → 6 blocks", and the window extends by the walls inside it.
#[test]
fn window_and_budget_for_the_spec_day() {
    let cfg = Config::default();
    assert_eq!(budget_blocks(&cfg), 6);

    let (end, budget) = window_and_budget(at(7, 0), &[], &cfg);
    assert_eq!(hm(end), "15:00");
    assert_eq!(budget, 6);

    // The §4.3 day: the 1 h meeting pushes the end from 15:00 to 16:00.
    let walls = [(at(12, 50), at(13, 50))];
    let (end, budget) = window_and_budget(at(7, 0), &walls, &cfg);
    assert_eq!(hm(end), "16:00");
    assert_eq!(budget, 6);
}

/// The extension is a fixed point: a wall that only comes inside the window
/// because an earlier wall extended it counts too.
#[test]
fn wall_extension_reaches_a_fixed_point() {
    let cfg = Config::default();
    let walls = [(at(9, 0), at(10, 0)), (at(15, 30), at(16, 0))];
    let (end, _) = window_and_budget(at(7, 0), &walls, &cfg);
    // 15:00 + 1 h (the 09:00 wall) = 16:00, which now contains the 15:30
    // wall's 30 min → 16:30.
    assert_eq!(hm(end), "16:30");
}

/// §8.1 is an equation, not a fixed number of rounds: `end` must satisfy
/// `end = base_end + Σ wall minutes inside [arrival, end]` however long the
/// wall is and however little of it pokes into the base window (a class, an
/// exam, a `travel-day` flight with `buffer:2h`).
#[test]
fn a_long_wall_extends_the_window_by_its_whole_duration() {
    let cfg = Config::default();
    // base_end = min(07:00 + 8h, cap 19:00) = 15:00.
    for (wall, want) in [
        ((at(14, 30), at(19, 30)), "20:00"), // 5 h wall, 30 min of it inside
        ((at(14, 30), at(19, 0)), "19:30"),
        ((at(14, 45), at(20, 0)), "20:15"),
        ((at(14, 59), at(22, 0)), "22:01"), // 1 min inside, 7 h long
    ] {
        let (end, _) = window_and_budget(at(7, 0), &[wall], &cfg);
        assert_eq!(hm(end), want, "wall {}-{}", hm(wall.0), hm(wall.1));
        // The §8.1 equation itself: end = 15:00 + Σ walls inside [07:00, end) — the Σ read by
        // fork 4748911's `wall_minutes`, by value (R3 deleted the in-tree copy).
        assert_eq!(
            end,
            at(15, 0) + chrono::Duration::minutes(forkcap::wall_minutes(forkcap::store(), &cfg, at(7, 0), end, &[wall])),
            "not a fixed point for {}-{}",
            hm(wall.0),
            hm(wall.1)
        );
    }

    // The same wall split into five back-to-back meetings must give the same
    // answer (the walk merges them).
    let split: Vec<_> = (0..5)
        .map(|i| (at(14, 30) + chrono::Duration::hours(i), at(15, 30) + chrono::Duration::hours(i)))
        .collect();
    let (end, _) = window_and_budget(at(7, 0), &split, &cfg);
    assert_eq!(hm(end), "20:00");

    // And the extended window is really usable: 07:00–20:00 minus the 5 h of
    // meetings is 8 h, every minute of it cut into blocks and breaks.
    let cut = forkcap::cut(forkcap::store(), &cfg, at(7, 0), end, &split);
    assert_eq!(cut.slot_minutes + cut.break_minutes, 8 * 60);
    assert_eq!(cut.slot_minutes, 7 * 60);
}

#[test]
fn walls_outside_the_window_do_not_extend_it() {
    let cfg = Config::default();
    let walls = [(at(19, 0), at(20, 0))];
    let (end, _) = window_and_budget(at(7, 0), &walls, &cfg);
    assert_eq!(hm(end), "15:00");
}

/// `window_cap` (19:00) bounds a late arrival; the budget does not shrink
/// (§8.1: "a late start gets a later end and the same budget formula").
#[test]
fn the_window_cap_bounds_a_late_arrival() {
    let cfg = Config::default();
    let (end, budget) = window_and_budget(at(14, 0), &[], &cfg);
    assert_eq!(hm(end), "19:00");
    assert_eq!(budget, 6);
    // Arriving after the cap gives an empty window, never a negative one.
    let (end, _) = window_and_budget(at(20, 0), &[], &cfg);
    assert_eq!(hm(end), "20:00");
    assert!(forkcap::cut(forkcap::store(), &cfg, at(20, 0), end, &[]).slots.is_empty());
}

// ---------------------------------------------------------------------------
// §8.2 step 3
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// energising
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// DST
// ---------------------------------------------------------------------------
