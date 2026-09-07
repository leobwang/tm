//! `capacity.rs`: §8.1 window and budget, §8.2 step 3 slot cutting and
//! energising, checked against the §4.3 day (`day/2026-09-07.md`: arrival
//! 07:00, meeting 12:50–13:50, window ends 16:00).

use chrono::{DateTime, TimeZone};
use chrono_tz::Tz;
use tm_core::capacity::{
    budget_blocks, cut_slots, cut_slots_from, energize, free_intervals, local_dt, remaining_budget,
    window_and_budget, Break, EnergyCtx, Slot, SlotKind, SlotOrBreak,
};
use tm_core::config::Config;
use tm_core::energy::{Model, Posterior};
use tm_core::model::Loc;

const TZ: Tz = Tz::America__Chicago;

fn at(h: u32, m: u32) -> DateTime<Tz> {
    TZ.with_ymd_and_hms(2026, 9, 7, h, m, 0).single().unwrap()
}

fn hm(t: DateTime<Tz>) -> String {
    t.format("%H:%M").to_string()
}

/// `07:00-08:00 B`, `09:00-09:20 break`.
fn layout(parts: &[SlotOrBreak]) -> Vec<String> {
    parts
        .iter()
        .map(|p| match p {
            SlotOrBreak::Slot(s) => format!(
                "{}-{} {}",
                hm(s.start),
                hm(s.end),
                match s.kind {
                    SlotKind::Block => "B",
                    SlotKind::ShortBlock => "b",
                }
            ),
            SlotOrBreak::Break(b) => format!("{}-{} break", hm(b.start), hm(b.end)),
        })
        .collect()
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
    assert_eq!(remaining_budget(budget, 2), 4);
    assert_eq!(remaining_budget(budget, 9), 0);
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
    assert!(cut_slots(at(20, 0), end, &[], &cfg).slots.is_empty());
}

// ---------------------------------------------------------------------------
// §8.2 step 3
// ---------------------------------------------------------------------------

/// The §4.3 day cut with only its wall: two blocks, a break, two blocks, a
/// break, one block, the 10 min before the meeting dropped, then the
/// afternoon. See the module docs for why this is not literally the day file
/// (step 2 has already placed the routines there).
#[test]
fn cut_slots_on_the_spec_day() {
    let cfg = Config::default();
    let walls = [(at(12, 50), at(13, 50))];
    let cut = cut_slots(at(7, 0), at(16, 0), &walls, &cfg);
    assert_eq!(
        layout(&cut.timeline()),
        vec![
            "07:00-08:00 B",
            "08:00-09:00 B",
            "09:00-09:20 break",
            "09:20-10:20 B",
            "10:20-11:20 B",
            "11:20-11:40 break",
            "11:40-12:40 B",
            // 12:40–12:50 is 10 min: shorter than min_last_block_min, dropped.
            "13:50-14:50 B",
            "14:50-15:10 break",
            "15:10-16:00 b",
        ]
    );
    assert_eq!(cut.slots.len(), 7);
    assert_eq!(cut.breaks.len(), 3);
    assert_eq!(cut.slot_minutes(), 6 * 60 + 50);
    assert_eq!(cut.break_minutes(), 60);
    assert_eq!(cut.slots.last().unwrap().kind, SlotKind::ShortBlock);
    assert_eq!(cut.slots.last().unwrap().minutes(), 50);
    // Nothing overlaps the wall.
    assert!(cut
        .slots
        .iter()
        .all(|s| s.end <= at(12, 50) || s.start >= at(13, 50)));
    // cut_slots leaves the energy to `energize`.
    assert!(cut.slots.iter().all(|s| s.energy == 0));
}

/// With the routines of the §4.3 day also occupied (lunch 11:20–11:50), the
/// afternoon lines up with the printed timeline: a block at 11:50 and the
/// wall at 12:50.
#[test]
fn cut_slots_around_a_placed_routine() {
    let cfg = Config::default();
    let walls = [(at(11, 20), at(11, 50)), (at(12, 50), at(13, 50))];
    let cut = cut_slots(at(7, 0), at(16, 0), &walls, &cfg);
    assert_eq!(
        layout(&cut.timeline()),
        vec![
            "07:00-08:00 B",
            "08:00-09:00 B",
            "09:00-09:20 break",
            "09:20-10:20 B",
            "10:20-11:20 B",
            // lunch 11:20–11:50; the break due at 11:20 lands after it.
            "11:50-12:10 break",
            "12:10-12:50 b",
            "13:50-14:50 B",
            "14:50-15:10 break",
            "15:10-16:00 b",
        ]
    );
}

/// A replan in the middle of the day can say how many blocks have already
/// been worked since the last break.
#[test]
fn cut_slots_from_a_pending_break() {
    let cfg = Config::default();
    let cut = cut_slots_from(at(9, 0), at(12, 0), &[], &cfg, 2);
    assert_eq!(
        layout(&cut.timeline()),
        vec![
            "09:00-09:20 break", // due immediately: two blocks are already done
            "09:20-10:20 B",
            "10:20-11:20 B",
            "11:20-11:40 break",
            // 11:40–12:00 is 20 min < min_last_block_min (30) → dropped.
        ]
    );
    // Lower the floor and the 20 min tail survives as a short block.
    let mut cfg2 = cfg.clone();
    cfg2.day.min_last_block_min = 20;
    let cut = cut_slots_from(at(9, 0), at(12, 0), &[], &cfg2, 2);
    assert_eq!(cut.slots.last().unwrap().minutes(), 20);
    assert_eq!(cut.slots.last().unwrap().kind, SlotKind::ShortBlock);
}

#[test]
fn a_tail_shorter_than_the_floor_is_dropped() {
    let cfg = Config::default();
    // 07:00–08:25: one block, then 25 min < min_last_block_min (30).
    let cut = cut_slots(at(7, 0), at(8, 25), &[], &cfg);
    assert_eq!(layout(&cut.timeline()), vec!["07:00-08:00 B"]);
    // 07:00–08:30: the 30 min tail survives as a short block.
    let cut = cut_slots(at(7, 0), at(8, 30), &[], &cfg);
    assert_eq!(
        layout(&cut.timeline()),
        vec!["07:00-08:00 B", "08:00-08:30 b"]
    );
}

#[test]
fn overlapping_walls_are_merged() {
    let cfg = Config::default();
    let walls = [(at(9, 0), at(11, 0)), (at(10, 0), at(10, 30))];
    assert_eq!(
        free_intervals(at(7, 0), at(13, 0), &walls),
        vec![(at(7, 0), at(9, 0)), (at(11, 0), at(13, 0))]
    );
    let cut = cut_slots(at(7, 0), at(13, 0), &walls, &cfg);
    assert_eq!(
        layout(&cut.timeline()),
        vec![
            "07:00-08:00 B",
            "08:00-09:00 B",
            "11:00-11:20 break",
            "11:20-12:20 B",
            "12:20-13:00 b",
        ]
    );
}

// ---------------------------------------------------------------------------
// energising
// ---------------------------------------------------------------------------

fn slots(times: &[(u32, u32, u32, u32)]) -> Vec<Slot> {
    times
        .iter()
        .map(|(h1, m1, h2, m2)| Slot {
            start: at(*h1, *m1),
            end: at(*h2, *m2),
            energy: 0,
            kind: SlotKind::Block,
        })
        .collect()
}

/// §8.2 step 3: `energy::predict` per slot, then the posterior, then the
/// home cap.
#[test]
fn energize_follows_the_prior_curve() {
    let cfg = Config::default();
    let model = Model::default();
    let posterior = Posterior::none(&cfg);
    let wake = at(6, 5);
    let cut = cut_slots(at(7, 0), at(16, 0), &[(at(12, 50), at(13, 50))], &cfg);
    let ctx = EnergyCtx::new(&model, &cfg, &posterior, wake, Loc::Lounge).with_slept(Some(490));
    let energised = energize(&cut.slots, &ctx);
    let levels: Vec<(String, u8)> = energised
        .iter()
        .map(|s| (hm(s.start), s.energy))
        .collect();
    assert_eq!(
        levels,
        vec![
            ("07:00".into(), 4), // hsw 0.92 → the 0–1 h step
            ("08:00".into(), 5),
            ("09:20".into(), 5),
            ("10:20".into(), 5),
            ("11:40".into(), 4), // hsw 5.58 → the 5–8 h step
            ("13:50".into(), 4), // hsw 7.75, still the 5–8 h step
            ("15:10".into(), 3), // hsw 9.08 → the 8–10 h step
        ]
    );
}

#[test]
fn energize_applies_the_home_cap_and_the_posterior() {
    let cfg = Config::default();
    let model = Model::default();
    let none = Posterior::none(&cfg);
    let wake = at(6, 5);
    let s = slots(&[(8, 0, 9, 0), (12, 0, 13, 0)]);

    // Lounge: 5 then 4.
    let ctx = EnergyCtx::new(&model, &cfg, &none, wake, Loc::Lounge);
    assert_eq!(
        energize(&s, &ctx).iter().map(|s| s.energy).collect::<Vec<_>>(),
        vec![5, 4]
    );

    // Home: the prior is 4 then 3, and home_max_ci = 3 caps the first.
    let ctx = EnergyCtx::new(&model, &cfg, &none, wake, Loc::Home);
    assert_eq!(
        energize(&s, &ctx).iter().map(|s| s.energy).collect::<Vec<_>>(),
        vec![3, 3]
    );
    // --allow-home lifts the cap.
    let ctx = ctx.with_allow_home(true);
    assert_eq!(
        energize(&s, &ctx).iter().map(|s| s.energy).collect::<Vec<_>>(),
        vec![4, 3]
    );

    // A report of 3 where 5 was predicted downgrades the later slots.
    let post = Posterior::from_reports(&[(at(9, 30), 5, 3)], &cfg);
    let ctx = EnergyCtx::new(&model, &cfg, &post, wake, Loc::Lounge);
    assert_eq!(
        energize(&s, &ctx).iter().map(|s| s.energy).collect::<Vec<_>>(),
        vec![5, 2] // 08:00 is before the report; 12:00 is 2.5 h after it
    );

    // A short night shifts everything down one level.
    let ctx = EnergyCtx::new(&model, &cfg, &none, wake, Loc::Lounge).with_slept(Some(6 * 60));
    assert_eq!(
        energize(&s, &ctx).iter().map(|s| s.energy).collect::<Vec<_>>(),
        vec![4, 3]
    );
}

#[test]
fn energize_counts_blocks_and_break_gaps() {
    let cfg = Config::default();
    let model = Model::default();
    let none = Posterior::none(&cfg);
    let cut = cut_slots(at(7, 0), at(12, 0), &[], &cfg);
    let ctx =
        EnergyCtx::new(&model, &cfg, &none, at(6, 5), Loc::Lounge).with_blocks_done(2);
    // The features are recomputed per slot; the energies are unaffected in
    // v1 but the call must be stable and keep the slot geometry.
    let energised = energize(&cut.slots, &ctx);
    assert_eq!(energised.len(), cut.slots.len());
    for (a, b) in energised.iter().zip(&cut.slots) {
        assert_eq!(a.start, b.start);
        assert_eq!(a.end, b.end);
        assert_eq!(a.kind, b.kind);
    }
    assert!(energised.iter().all(|s| s.fits(4)));
}

// ---------------------------------------------------------------------------
// DST
// ---------------------------------------------------------------------------

/// The day America/Chicago springs forward (2026-03-08, 02:00 → 03:00): a
/// window of eight wall-clock hours is seven hours of blocks, because the
/// slots are absolute instants.
#[test]
fn slots_cross_a_dst_boundary_correctly() {
    let cfg = Config::default();
    let day = chrono::NaiveDate::from_ymd_opt(2026, 3, 8).unwrap();
    let start = local_dt(TZ, day, chrono::NaiveTime::from_hms_opt(0, 0, 0).unwrap());
    let end = local_dt(TZ, day, chrono::NaiveTime::from_hms_opt(6, 0, 0).unwrap());
    assert_eq!((end - start).num_hours(), 5);
    let cut = cut_slots(start, end, &[], &cfg);
    let labels: Vec<String> = cut
        .timeline()
        .iter()
        .map(|p| match p {
            SlotOrBreak::Slot(s) => format!("{}-{}", hm(s.start), hm(s.end)),
            SlotOrBreak::Break(b) => format!("{}-{} break", hm(b.start), hm(b.end)),
        })
        .collect();
    assert_eq!(
        labels,
        vec![
            "00:00-01:00",
            "01:00-03:00", // the 02:00 hour does not exist
            "03:00-03:20 break",
            "03:20-04:20",
            "04:20-05:20",
            "05:20-05:40 break",
        ]
    );
    assert!(cut.slots.iter().all(|s| s.minutes() == 60));
    // 02:30 does not exist; local_dt returns the first instant after the gap.
    let gap = local_dt(TZ, day, chrono::NaiveTime::from_hms_opt(2, 30, 0).unwrap());
    assert_eq!(hm(gap), "03:00");
}

#[test]
fn breaks_and_slots_are_disjoint_and_ordered() {
    let cfg = Config::default();
    let cut = cut_slots(at(7, 0), at(19, 0), &[(at(10, 0), at(11, 0))], &cfg);
    let parts = cut.timeline();
    for w in parts.windows(2) {
        assert!(w[0].end() <= w[1].start(), "{:?} then {:?}", w[0], w[1]);
    }
    let total: i64 = parts
        .iter()
        .map(|p| (p.end() - p.start()).num_minutes())
        .sum();
    assert!(total <= (at(19, 0) - at(7, 0)).num_minutes() - 60);
    assert_eq!(
        cut.breaks.first(),
        Some(&Break {
            start: at(9, 0),
            end: at(9, 20)
        })
    );
}
