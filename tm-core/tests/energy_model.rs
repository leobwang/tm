//! `energy.rs`: the §8.5 `model.json` shape, the §16 prior tables, the
//! sleep-debt shift, the posterior weights and the duration multipliers.

use std::path::{Path, PathBuf};

use chrono::{DateTime, TimeZone, Weekday};
use chrono_tz::Tz;
use tm_core::config::Config;
use tm_core::energy::{
    self, duration_multiplier, fmt_planned, planned_minutes, posterior_weight, predict, Features,
    Model, Posterior, DEFAULT_TAG,
};
use tm_core::model::{Dur, Loc};

const TZ: Tz = Tz::America__Chicago;

fn fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/model.json")
}

fn fixture_model() -> Model {
    Model::load(&fixture_path()).unwrap().expect("fixture exists")
}

fn at(h: u32, m: u32) -> DateTime<Tz> {
    TZ.with_ymd_and_hms(2026, 9, 7, h, m, 0).single().unwrap()
}

// ---------------------------------------------------------------------------
// model.json
// ---------------------------------------------------------------------------

#[test]
fn model_json_fixture_parses_to_the_spec_values() {
    let m = fixture_model();
    assert_eq!(m.energy["lounge"], vec![4, 5, 5, 5, 5, 4, 4, 4, 3, 3, 2, 2]);
    assert_eq!(m.energy["home"], vec![3, 4, 4, 4, 3, 3, 3, 2, 2, 2, 2, 2]);
    assert_eq!(m.sleep_debt_shift, Some(0.8));
    assert_eq!(m.duration["lean"], 1.6);
    assert_eq!(m.duration["soundcode"], 1.1);
    assert_eq!(m.duration[DEFAULT_TAG], 1.3);
    assert_eq!(m.p_lounge.get(Weekday::Mon), Some(&0.9));
    assert_eq!(m.p_lounge.get(Weekday::Sun), Some(&0.4));
    assert_eq!(
        m.expected_arrival.get(Weekday::Mon).map(|t| t.to_string()),
        Some("07:10".to_string())
    );
    // A partial weekday table stays partial.
    assert_eq!(m.expected_arrival.len(), 2);
    assert_eq!(m.expected_arrival.get(Weekday::Tue), None);
    assert_eq!(m.fitted.map(|d| d.to_string()), Some("2026-09-14".into()));
    assert_eq!(m.n_obs, 61);
}

/// §17 M8: "model.json round-trips". Byte-for-byte modulo key order and
/// whitespace: the value re-serializes to the snapshot below and parses back
/// to an equal model.
#[test]
fn model_json_round_trips() {
    let m = fixture_model();
    let text = m.to_json();
    assert_eq!(Model::from_json(&text).unwrap(), m);
    insta::assert_snapshot!("model_json_reserialized", text);
}

#[test]
fn empty_model_falls_back_to_the_config_and_round_trips() {
    let m = Model::default();
    assert!(m.is_empty());
    assert!(!m.is_fitted());
    let text = m.to_json();
    assert_eq!(Model::from_json(&text).unwrap(), m);
    // An unknown key (a v2 field, or a hand edit) is ignored, not fatal.
    let m = Model::from_json(r#"{"sleep_debt_shift": 0.5, "future_field": [1,2]}"#).unwrap();
    assert_eq!(m.sleep_debt_shift, Some(0.5));
}

/// §8.5: "hand edits become the new prior". A `model.json` carrying nothing
/// but a `sleep_debt_shift` must be honoured by `predict` — the value is not
/// gated on the file also being a fit — and an absent one falls back to
/// `config.energy.sleep_debt.shift`.
#[test]
fn a_hand_written_sleep_debt_shift_is_honoured_by_predict() {
    let cfg = Config::default(); // sleep_debt.shift = 1, under_hours = 7
    let short = || Features::new(Loc::Lounge, 2.0).with_slept(Some(5 * 60));

    // Absent: the config shift applies (prior 5 − 1).
    let none = Model::from_json(r#"{"energy": {"lounge": [5,5,5,5,5,5,5,5,5,5,5,5]}}"#).unwrap();
    assert_eq!(none.sleep_debt_shift, None);
    assert_eq!(none.sleep_shift(&cfg), 1.0);
    assert_eq!(predict(&none, &cfg, &short()), 4);

    // Hand-written, nothing else in the file: 5 − 3 = 2, with no `fitted`
    // and no `n_obs` to vouch for it.
    let hand = Model::from_json(r#"{"sleep_debt_shift": 3.0}"#).unwrap();
    assert!(!hand.is_fitted());
    assert_eq!(hand.sleep_shift(&cfg), 3.0);
    assert_eq!(predict(&hand, &cfg, &short()), 2);
    // Well-slept nights are untouched by the shift.
    assert_eq!(
        predict(&hand, &cfg, &Features::new(Loc::Lounge, 2.0).with_slept(Some(8 * 60))),
        5
    );

    // A written zero means "short nights cost me nothing", not "unset".
    let zero = Model::from_json(r#"{"sleep_debt_shift": 0.0}"#).unwrap();
    assert_eq!(zero.sleep_shift(&cfg), 0.0);
    assert_eq!(predict(&zero, &cfg, &short()), 5);

    // The distinction survives a round trip: absent stays out of the file.
    assert!(!Model::default().to_json().contains("sleep_debt_shift"));
    assert!(zero.to_json().contains("\"sleep_debt_shift\": 0.0"));
    assert_eq!(Model::from_json(&zero.to_json()).unwrap(), zero);
}

#[test]
fn model_saves_and_loads_through_a_path() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join(".tm/model.json");
    assert_eq!(Model::load(&path).unwrap(), None);
    assert_eq!(Model::load_or_default(&path).unwrap(), Model::default());
    let m = fixture_model();
    m.save(&path).unwrap();
    assert_eq!(Model::load(&path).unwrap(), Some(m.clone()));
    assert_eq!(std::fs::read_to_string(&path).unwrap(), m.to_json());
}

#[test]
fn show_renders_a_table() {
    insta::assert_snapshot!("model_show", energy::show(&fixture_model()));
}

// ---------------------------------------------------------------------------
// predict
// ---------------------------------------------------------------------------

/// §16 `[energy.prior.lounge]` 0-1:4 1-5:5 5-8:4 8-10:3 10+:2 and
/// `[energy.prior.home]` 0-1:3 1-4:4 4-8:3 8+:2, checked at the boundaries.
#[test]
fn predict_matches_the_prior_tables_at_boundaries() {
    let cfg = Config::default();
    let m = Model::default();
    let lounge = |hsw: f64| predict(&m, &cfg, &Features::new(Loc::Lounge, hsw));
    assert_eq!(lounge(0.0), 4);
    assert_eq!(lounge(0.99), 4);
    assert_eq!(lounge(1.0), 5);
    assert_eq!(lounge(4.99), 5);
    assert_eq!(lounge(5.0), 4);
    assert_eq!(lounge(7.99), 4);
    assert_eq!(lounge(8.0), 3);
    assert_eq!(lounge(9.99), 3);
    assert_eq!(lounge(10.0), 2);
    assert_eq!(lounge(23.0), 2);

    let home = |hsw: f64| predict(&m, &cfg, &Features::new(Loc::Home, hsw));
    assert_eq!(home(0.99), 3);
    assert_eq!(home(1.0), 4);
    assert_eq!(home(3.99), 4);
    assert_eq!(home(4.0), 3);
    assert_eq!(home(8.0), 2);
}

/// The learned curve wins where it exists; the bucket is `floor(hsw)`.
#[test]
fn predict_uses_the_learned_curve() {
    let cfg = Config::default();
    let m = fixture_model();
    let lounge = |hsw: f64| predict(&m, &cfg, &Features::new(Loc::Lounge, hsw));
    assert_eq!(lounge(0.99), 4);
    assert_eq!(lounge(1.0), 5);
    assert_eq!(lounge(5.0), 4);
    assert_eq!(lounge(8.0), 3);
    assert_eq!(lounge(10.0), 2);
    // The fixture's learned home curve differs from the prior at hsw 7.
    let home = |hsw: f64| predict(&m, &cfg, &Features::new(Loc::Home, hsw));
    assert_eq!(home(7.0), 2);
    assert_eq!(predict(&Model::default(), &cfg, &Features::new(Loc::Home, 7.0)), 3);
    // Past the last bucket the last learned level holds.
    assert_eq!(lounge(30.0), 2);
}

/// Named, `out` and `any` locations use the home curve unless a curve of
/// their own name exists.
#[test]
fn unknown_locations_use_the_home_curve() {
    let cfg = Config::default();
    let m = Model::default();
    for loc in [Loc::Out, Loc::Any, Loc::Named("zoom".into())] {
        assert_eq!(
            predict(&m, &cfg, &Features::new(loc.clone(), 2.0)),
            4,
            "{loc}"
        );
    }
    // A configured curve for the name is used instead.
    let cfg = Config::parse(
        "[energy.prior.zoom]\n\"0-2\" = 5\n\"2+\" = 1\n[energy.prior.home]\n\"0+\" = 3\n",
    )
    .unwrap();
    assert_eq!(
        predict(&m, &cfg, &Features::new(Loc::Named("zoom".into()), 3.0)),
        1
    );
}

#[test]
fn sleep_debt_shift_is_applied_and_clamped() {
    let cfg = Config::default(); // under 7h → shift 1
    let m = Model::default();
    let f = |slept: u32| Features::new(Loc::Lounge, 2.0).with_slept(Some(slept));
    assert_eq!(predict(&m, &cfg, &f(8 * 60)), 5);
    assert_eq!(predict(&m, &cfg, &f(7 * 60)), 5); // exactly 7h is not debt
    assert_eq!(predict(&m, &cfg, &f(6 * 60 + 59)), 4);
    // Unknown sleep → no shift.
    assert_eq!(predict(&m, &cfg, &Features::new(Loc::Lounge, 2.0)), 5);

    // A fitted model's learned shift is used instead, rounded.
    let fit = fixture_model(); // 0.8 → 1
    assert_eq!(predict(&fit, &cfg, &f(6 * 60)), 4);
    let mut small = fixture_model();
    small.sleep_debt_shift = Some(0.4); // rounds to 0
    assert_eq!(predict(&small, &cfg, &f(6 * 60)), 5);

    // Clamped at 0.
    let mut deep = fixture_model();
    deep.sleep_debt_shift = Some(9.0);
    assert_eq!(predict(&deep, &cfg, &f(6 * 60)), 0);
}

// ---------------------------------------------------------------------------
// posterior
// ---------------------------------------------------------------------------

/// §8.5: `w = 1` for `posterior_full_hours` (3), linearly to 0 at
/// `posterior_zero_hours` (6).
#[test]
fn posterior_weight_is_one_for_three_hours_and_zero_at_six() {
    let cfg = Config::default();
    assert_eq!(cfg.energy.posterior_full_hours, 3.0);
    assert_eq!(cfg.energy.posterior_zero_hours, 6.0);
    for (hours, want) in [
        (0.0, 1.0),
        (2.9, 1.0),
        (3.0, 1.0),
        (4.5, 0.5),
        (5.0, 1.0 / 3.0),
        (6.0, 0.0),
        (7.0, 0.0),
        (-0.5, 0.0),
    ] {
        let got = posterior_weight(hours, 3.0, 6.0);
        assert!((got - want).abs() < 1e-9, "{hours}h → {got}, want {want}");
    }
}

#[test]
fn posterior_corrects_and_decays() {
    let cfg = Config::default();
    // A report of 4 where 5 was predicted: δ = −1.
    let p = Posterior::from_reports(&[(at(9, 0), 5, 4)], &cfg);
    assert_eq!(p.adjustment(at(9, 0)), -1.0);
    assert_eq!(p.correct(at(9, 0), 5), 4);
    assert_eq!(p.correct(at(12, 0), 5), 4); // still full weight at 3h
    assert!((p.adjustment(at(13, 30)) + 0.5).abs() < 1e-9); // 4.5h → −0.5
    assert_eq!(p.correct(at(15, 0), 5), 5); // 6h → no correction
    assert_eq!(p.correct(at(8, 0), 5), 5); // before the report

    // δ = −2 halves to −1 at 4.5h.
    let p = Posterior::from_reports(&[(at(9, 0), 5, 3)], &cfg);
    assert_eq!(p.correct(at(13, 30), 5), 4);

    // Corrections clamp to 0..=5.
    let p = Posterior::from_reports(&[(at(9, 0), 1, 5)], &cfg);
    assert_eq!(p.correct(at(10, 0), 4), 5);

    // The most recent report supersedes the older one.
    let p = Posterior::from_reports(&[(at(11, 0), 4, 4), (at(9, 0), 5, 3)], &cfg);
    assert_eq!(p.reports().len(), 2);
    assert_eq!(p.correct(at(12, 0), 4), 4);
    assert_eq!(p.correct(at(10, 0), 5), 3); // between the two, the 09:00 one applies

    assert!(Posterior::none(&cfg).is_empty());
    assert_eq!(Posterior::none(&cfg).correct(at(10, 0), 3), 3);
}

// ---------------------------------------------------------------------------
// durations
// ---------------------------------------------------------------------------

#[test]
fn duration_multipliers_and_planning() {
    let m = fixture_model();
    let tag = |t: &str| vec![t.to_string()];
    assert_eq!(duration_multiplier(&m, 4, &tag("lean")), 1.6);
    assert_eq!(duration_multiplier(&m, 5, &tag("soundcode")), 1.1);
    assert_eq!(duration_multiplier(&m, 3, &tag("admin")), 1.3); // _default
    assert_eq!(duration_multiplier(&m, 3, &[]), 1.3);
    // First matching tag wins.
    assert_eq!(
        duration_multiplier(&m, 3, &["admin".into(), "lean".into()]),
        1.6
    );
    // A ci-keyed entry wins over the bare tag.
    let mut m2 = m.clone();
    m2.duration.insert("5:lean".into(), 2.0);
    assert_eq!(duration_multiplier(&m2, 5, &tag("lean")), 2.0);
    assert_eq!(duration_multiplier(&m2, 4, &tag("lean")), 1.6);
    // No model at all → 1.0.
    assert_eq!(duration_multiplier(&Model::default(), 3, &tag("lean")), 1.0);

    // §9.1: est 2b ×1.6 = 3h12m.
    assert_eq!(planned_minutes(120, 1.6), 192);
    assert_eq!(planned_minutes(60, 1.0), 60);
    assert_eq!(planned_minutes(45, 1.3), 59); // rounded
    assert_eq!(fmt_planned(&Dur::blocks(2, 60), 1.6), "2b×1.6");
    assert_eq!(fmt_planned(&Dur::blocks(1, 60), 1.0), "1b");
    assert_eq!(fmt_planned(&Dur::canonical(30), 1.25), "30m×1.25");
}
