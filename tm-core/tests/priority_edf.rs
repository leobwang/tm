//! §7.3 — the EDF pass, §7.1's bins, and §11's deadline health, on synthetic
//! capacity vectors so every number in the assertions is computed by hand.
//!
//! The capacity model used here: `flat(days, level, minutes)` gives each of
//! `days` consecutive days from Monday 2026-09-07 exactly `minutes` minutes
//! at energy `level` and nothing anywhere else, so
//! `available_until(due, ci ≤ level) = minutes × (days up to and including
//! the due date)`.

use std::collections::BTreeMap;

use chrono::{NaiveDate, NaiveTime};
use chrono_tz::Tz;
use tm_core::capacity::{local_dt, DayCapacity};
use tm_core::config::Config;
use tm_core::model::Id;
use tm_core::priority::{self, Candidate, PrioClass};

const TZ: Tz = Tz::America__Chicago;
const MONDAY: &str = "2026-09-07";

fn date(s: &str) -> NaiveDate {
    NaiveDate::parse_from_str(s, "%Y-%m-%d").expect("date")
}

fn due(s: &str) -> chrono::DateTime<Tz> {
    local_dt(
        TZ,
        date(s),
        NaiveTime::from_hms_opt(23, 59, 0).expect("time"),
    )
}

/// `days` days from Monday 2026-09-07, each with `minutes` at `level`.
fn flat(days: usize, level: usize, minutes: u32) -> Vec<DayCapacity> {
    let start = date(MONDAY);
    (0..days)
        .map(|i| {
            let mut d = DayCapacity::empty(start + chrono::Duration::days(i as i64));
            d.minutes_at_level[level] = minutes;
            d
        })
        .collect()
}

fn cand(id: &str, ci: u8, k: u8, remaining_min: u32, cfg: &Config) -> Candidate {
    Candidate::new(Id::new(id), ci, k, remaining_min, cfg)
}

fn empty() -> BTreeMap<Id, u8> {
    BTreeMap::new()
}

// ---------------------------------------------------------------------------
// (a) two deadlines, each feasible alone, jointly infeasible
// ---------------------------------------------------------------------------

/// Five days of 240 min at energy 5. Two ci-3 items of 8 h remaining each:
/// `need = 480 × 1.3 = 624`.
///
/// * `^e1` due Wed 2026-09-09 sees days Mon–Wed = 720 min → `u = 624/720 =
///   0.8667` → bin +0, and reserves all 624 (Mon 240, Tue 240, Wed 144).
/// * `^e2` due Fri 2026-09-11 then sees only 96 + 240 + 240 = 576 min →
///   `u = 624/576 = 1.0833 ≥ 1` and `need > avail`, so IMPOSSIBLE with a
///   shortfall of 48 min.
///
/// Alone, `^e2` would see all 1200 min (`u = 0.52`), which the second half of
/// the test checks.
#[test]
fn jointly_infeasible_deadlines_flag_the_later_one() {
    let cfg = Config::default();
    let caps = flat(5, 5, 240);
    let mut e1 = cand("e1", 3, 3, 480, &cfg);
    e1.effective_due = Some(due("2026-09-09"));
    e1.own_order = (0, 1);
    let mut e2 = cand("e2", 3, 3, 480, &cfg);
    e2.effective_due = Some(due("2026-09-11"));
    e2.own_order = (0, 2);

    let cands = vec![e1.clone(), e2.clone()];
    assert_eq!(cands[0].need_min, 624);
    assert_eq!(cands[1].need_min, 624);

    let prios = priority::compute(&cands, &caps, &empty(), &cfg, date(MONDAY));

    // The earlier deadline keeps its full reservation.
    assert_eq!(prios[0].class, PrioClass::Dated);
    assert_eq!(prios[0].avail_min, 720);
    assert_eq!(prios[0].allocation_min, 624);
    assert_eq!(prios[0].shortfall_min, 0);
    assert!((prios[0].u.unwrap() - 624.0 / 720.0).abs() < 1e-12);
    assert_eq!(prios[0].bin, Some(0));
    assert_eq!(prios[0].p, 3); // k(3) + 0
    assert_eq!(prios[0].until, Some(date("2026-09-09")));

    // The later one is left with what is not reserved.
    assert_eq!(prios[1].class, PrioClass::Impossible);
    assert_eq!(prios[1].avail_min, 576);
    assert_eq!(prios[1].need_min, 624);
    assert_eq!(prios[1].shortfall_min, 48);
    assert_eq!(prios[1].allocation_min, 576);
    assert!((prios[1].u.unwrap() - 624.0 / 576.0).abs() < 1e-12);
    assert_eq!(prios[1].bin, None);
    assert_eq!(prios[1].p, 0);

    // Alone, the later deadline is comfortable.
    let alone = priority::compute(&[e2], &caps, &empty(), &cfg, date(MONDAY));
    assert_eq!(alone[0].class, PrioClass::Dated);
    assert_eq!(alone[0].avail_min, 1200);
    assert_eq!(alone[0].shortfall_min, 0);
    assert!((alone[0].u.unwrap() - 0.52).abs() < 1e-12);
    assert_eq!(alone[0].bin, Some(0));
}

/// The EDF pass reserves only at levels ≥ `ci`, so a ci-5 item does not eat
/// the capacity a ci-2 item was counting on, and a low-ci item takes the
/// highest matching level first.
#[test]
fn edf_reserves_by_energy_level() {
    let cfg = Config::default();
    let mut caps = flat(2, 5, 120);
    for day in caps.iter_mut() {
        day.minutes_at_level[2] = 120;
    }
    // ci-5 item, due Monday: only the 120 min at level 5 on Monday.
    let mut hard = cand("hard", 5, 3, 60, &cfg); // need 78
    hard.effective_due = Some(due(MONDAY));
    hard.own_order = (0, 1);
    // ci-2 item, due Tuesday: levels 2 and 5 on both days = 480 before
    // reservations, 480 − 78 = 402 after.
    let mut soft = cand("soft", 2, 3, 60, &cfg);
    soft.effective_due = Some(due("2026-09-08"));
    soft.own_order = (0, 2);

    let prios = priority::compute(&[hard, soft], &caps, &empty(), &cfg, date(MONDAY));
    assert_eq!(prios[0].avail_min, 120);
    assert_eq!(prios[0].allocation_min, 78);
    assert_eq!(prios[1].avail_min, 402);
    assert_eq!(prios[1].allocation_min, 78);
}

// ---------------------------------------------------------------------------
// (b) bins at their edges
// ---------------------------------------------------------------------------

/// `bin(u)` at and just below every edge of `config.priority.bins`
/// (`[0.5, 0.25, 0.1]`). `safety` is 1.0 here so `need = remaining` and `u`
/// is exactly `remaining / 1000`.
#[test]
fn bins_at_the_edges() {
    let mut cfg = Config::default();
    cfg.priority.safety = 1.0;
    let caps = flat(1, 5, 1000);
    let today = date(MONDAY);

    let cases: [(u32, Option<u8>, PrioClass, u8); 9] = [
        (1300, None, PrioClass::Impossible, 0), // u = 1.3
        (1000, None, PrioClass::Hot, 0),        // u = 1.0 exactly, need == avail
        (999, Some(0), PrioClass::Dated, 3),    // 0.999
        (500, Some(0), PrioClass::Dated, 3),    // 0.5 exactly
        (499, Some(1), PrioClass::Dated, 4),    // 0.499
        (250, Some(1), PrioClass::Dated, 4),    // 0.25 exactly
        (249, Some(2), PrioClass::Dated, 5),    // 0.249
        (100, Some(2), PrioClass::Dated, 5),    // 0.1 exactly
        (99, Some(3), PrioClass::Dated, 6),     // 0.099
    ];
    for (remaining, bin, class, p) in cases {
        let mut c = cand("x", 0, 3, remaining, &cfg);
        c.effective_due = Some(due(MONDAY));
        let prios = priority::compute(&[c], &caps, &empty(), &cfg, today);
        assert_eq!(prios[0].need_min, remaining, "need for {remaining}");
        assert_eq!(prios[0].bin, bin, "bin for remaining {remaining}");
        assert_eq!(prios[0].class, class, "class for remaining {remaining}");
        assert_eq!(prios[0].p, p, "p for remaining {remaining}");
    }
}

/// `bin_of` is the same function the rule uses, and it is `None` (HOT) for
/// `u ≥ 1` and for a non-finite `u`.
#[test]
fn bin_of_matches_the_spec_table() {
    let bins = [0.5, 0.25, 0.1];
    assert_eq!(priority::bin_of(f64::INFINITY, &bins), None);
    assert_eq!(priority::bin_of(1.0, &bins), None);
    assert_eq!(priority::bin_of(0.9999, &bins), Some(0));
    assert_eq!(priority::bin_of(0.5, &bins), Some(0));
    assert_eq!(priority::bin_of(0.4999, &bins), Some(1));
    assert_eq!(priority::bin_of(0.25, &bins), Some(1));
    assert_eq!(priority::bin_of(0.2499, &bins), Some(2));
    assert_eq!(priority::bin_of(0.1, &bins), Some(2));
    assert_eq!(priority::bin_of(0.0999, &bins), Some(3));
    assert_eq!(priority::bin_of(0.0, &bins), Some(3));
}

/// §7.1: capacity 0 → `u = ∞` → IMPOSSIBLE with the whole need as the
/// shortfall; a need of 0 is not urgent at all.
#[test]
fn zero_capacity_is_infinite_utilization() {
    let cfg = Config::default();
    let caps = flat(3, 5, 0);
    let mut c = cand("x", 3, 3, 120, &cfg);
    c.effective_due = Some(due("2026-09-08"));
    let prios = priority::compute(&[c], &caps, &empty(), &cfg, date(MONDAY));
    assert_eq!(prios[0].u, Some(f64::INFINITY));
    assert_eq!(prios[0].class, PrioClass::Impossible);
    assert_eq!(prios[0].shortfall_min, 156);
    assert_eq!(prios[0].p, 0);

    assert_eq!(priority::utilization(0, 0), 0.0);
    assert_eq!(priority::utilization(10, 0), f64::INFINITY);
    assert_eq!(priority::utilization(60, 120), 0.5);
}

/// A deadline the lookahead does not reach reports a false shortfall, so
/// `lookahead_days` sizes it from the candidates.
#[test]
fn lookahead_days_covers_the_furthest_deadline() {
    let cfg = Config::default();
    let mut near = cand("n", 3, 3, 60, &cfg);
    near.effective_due = Some(due("2026-09-09"));
    let mut far = cand("f", 3, 3, 60, &cfg);
    far.effective_due = Some(due("2026-11-20"));
    let undated = cand("u", 3, 3, 60, &cfg);

    assert_eq!(
        priority::lookahead_days(std::slice::from_ref(&undated), date(MONDAY)),
        7
    );
    assert_eq!(
        priority::lookahead_days(std::slice::from_ref(&near), date(MONDAY)),
        7
    );
    // 2026-09-07 → 2026-11-20 inclusive.
    assert_eq!(
        priority::lookahead_days(&[near, far, undated], date(MONDAY)),
        75
    );
}

// ---------------------------------------------------------------------------
// (j) deadline health (§11)
// ---------------------------------------------------------------------------

/// One HOT, one IMPOSSIBLE, one overdue, one comfortable deadline.
///
/// The comfortable one (`^ok`, 60 min remaining → need 78, due Friday with
/// 5 × 240 = 1200 min available before the others reserve) has
/// `u = 78/1200 = 0.065` and 4 days to go, so its slack is
/// `4 × (1 − 0.065) = 3.74`; the HOT one's slack is negative, so the minimum
/// comes from it.
#[test]
fn deadline_health_counts_and_min_slack() {
    let cfg = Config::default();
    let caps = flat(5, 5, 240);
    let today = date(MONDAY);

    let mut ok = cand("ok", 3, 3, 60, &cfg);
    ok.effective_due = Some(due("2026-09-11"));
    ok.own_order = (0, 1);
    // Needs 1560 min by Tuesday, where 480 exist → IMPOSSIBLE.
    let mut imp = cand("imp", 3, 3, 1200, &cfg);
    imp.effective_due = Some(due("2026-09-08"));
    imp.own_order = (0, 2);
    // Overdue: due last Friday, on-miss persist.
    let mut old = cand("old", 3, 3, 60, &cfg);
    old.effective_due = Some(due("2026-09-04"));
    old.overdue = true;
    old.own_order = (0, 3);

    let cands = vec![ok, imp, old];
    let prios = priority::compute(&cands, &caps, &empty(), &cfg, today);
    assert_eq!(prios[0].class, PrioClass::Dated);
    assert_eq!(prios[1].class, PrioClass::Impossible);
    assert_eq!(prios[2].class, PrioClass::Overdue);

    let health = priority::deadline_health(&prios, &cands, today);
    assert_eq!(health.impossible, 1);
    assert_eq!(health.overdue, 1);
    assert_eq!(health.hot, 0);
    // The IMPOSSIBLE item's slack: 1 day × (1 − 1560/480) = −2.25.
    let slack = health.min_slack_days.expect("a dated candidate");
    assert!(
        (slack - (1.0 * (1.0 - 1560.0 / 480.0))).abs() < 1e-9,
        "{slack}"
    );

    // Without the impossible one, the comfortable deadline sets the minimum.
    let solo = vec![cands[0].clone()];
    let solo_prios = priority::compute(&solo, &caps, &empty(), &cfg, today);
    let health = priority::deadline_health(&solo_prios, &solo, today);
    assert_eq!((health.hot, health.impossible, health.overdue), (0, 0, 0));
    let slack = health.min_slack_days.expect("a dated candidate");
    assert!(
        (slack - 4.0 * (1.0 - 78.0 / 1200.0)).abs() < 1e-9,
        "{slack}"
    );
}

/// A HOT (not impossible) item: `need == avail` exactly.
#[test]
fn hot_when_the_need_exactly_fills_the_window() {
    let cfg = Config::default();
    let caps = flat(1, 4, 130);
    let mut c = cand("h", 4, 2, 100, &cfg); // need = 130
    c.effective_due = Some(due(MONDAY));
    let cands = vec![c];
    let prios = priority::compute(&cands, &caps, &empty(), &cfg, date(MONDAY));
    assert_eq!(prios[0].u, Some(1.0));
    assert_eq!(prios[0].class, PrioClass::Hot);
    assert_eq!(prios[0].shortfall_min, 0);
    assert_eq!(prios[0].p, 0);
    let health = priority::deadline_health(&prios, &cands, date(MONDAY));
    assert_eq!(health.hot, 1);
    assert_eq!(health.impossible, 0);
}
