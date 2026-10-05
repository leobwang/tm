//! §7.3 — the EDF pass, §7.1's bins, and §11's deadline health, on synthetic
//! capacity vectors so every number in the assertions is computed by hand.
//!
//! The capacity model used here: `flat(days, level, minutes)` gives each of
//! `days` consecutive days from Monday 2026-09-07 exactly `minutes` minutes
//! at energy `level` and nothing anywhere else, so
//! `available_until(due, ci ≤ level) = minutes × (days up to and including
//! the due date)`.
//!
//! **Two kinds of test, since R3 leaves fork 4748911's §7 pass with no shipped caller** (stage 6
//! W-46 track C; README gap 4752, the class).  §11's deadline health is the binary's and keeps
//! its tests: they read the fork's grants BY VALUE (`fork_compute`, the `tm` tests' own
//! `support/forkcap.rs`: this binary's frozen file, `tm-oracle capacity` under `TM_ORACLE`), as
//! they read tm-core's in-tree copy of the pass until W-46.  Every other test here is the fork
//! pass's own behaviour — the EDF reservation, the bins, `bin_of`, `utilization` — still calls
//! the in-tree copy, and is deleted with it at R3 (README "W-46 track C", the deletion list).

use std::collections::BTreeMap;

use chrono::{NaiveDate, NaiveTime};
use chrono_tz::Tz;
use tm_core::capacity::{local_dt, DayCapacity};
use tm_core::config::Config;
use tm_core::model::Id;
use tm_core::priority::{self, Candidate, Prio, PrioClass};

/// Fork 4748911's answers, by value (W-46 track C) — the `tm` tests' module, by path.
#[allow(dead_code)]
#[path = "../../tm/tests/support/forkcap.rs"]
mod forkcap;

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
            let mut minutes_at_level = [0; 6];
            minutes_at_level[level] = minutes;
            DayCapacity { date: start + chrono::Duration::days(i as i64), minutes_at_level }
        })
        .collect()
}

/// **Fork 4748911's grants** — fork `priority::compute`, by value (`forkcap::rank`).
fn fork_compute(cands: &[Candidate], caps: &[DayCapacity], yesterday: &BTreeMap<Id, u8>, cfg: &Config, today: NaiveDate) -> Vec<Prio> {
    forkcap::rank(forkcap::store(), cands, caps, yesterday, cfg, today).0
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

// ---------------------------------------------------------------------------
// (b) bins at their edges
// ---------------------------------------------------------------------------

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
    let prios = fork_compute(&cands, &caps, &empty(), &cfg, today);
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
    let solo_prios = fork_compute(&solo, &caps, &empty(), &cfg, today);
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
    let prios = fork_compute(&cands, &caps, &empty(), &cfg, date(MONDAY));
    assert_eq!(prios[0].u, Some(1.0));
    assert_eq!(prios[0].class, PrioClass::Hot);
    assert_eq!(prios[0].shortfall_min, 0);
    assert_eq!(prios[0].p, 0);
    let health = priority::deadline_health(&prios, &cands, date(MONDAY));
    assert_eq!(health.hot, 1);
    assert_eq!(health.impossible, 0);
}
