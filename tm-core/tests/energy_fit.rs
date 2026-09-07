//! `energy::fit` over the synthetic 14-day log
//! (`tests/fixtures/logs/energy-14d.jsonl`, 2026-08-25 .. 2026-09-07): every
//! expected value is recomputed in the test straight from the §8.5 formula
//! `(n0·prior + Σ wᵢ xᵢ) / (n0 + Σ wᵢ)`, `wᵢ = exp(−age/decay) × went`, so
//! the test states the formula rather than the implementation.

use std::path::{Path, PathBuf};

use chrono::{DateTime, Datelike, FixedOffset, NaiveDate, TimeZone, Weekday};
use tm_core::config::Config;
use tm_core::energy::{
    self, arrivals_from_replay, calibration, compare, estimate_calibration, fit, fit_replay,
    ArrivalObs, FitInput, Model, DEFAULT_TAG,
};
use tm_core::log::{DurationObs, EnergyObs, Log, Replay};

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn today() -> NaiveDate {
    NaiveDate::from_ymd_opt(2026, 9, 7).unwrap()
}

fn setup() -> (Config, Replay) {
    let cfg = Config::load(fixtures().join("plan-basic/config.toml")).unwrap();
    let log = Log::read(fixtures().join("logs/energy-14d.jsonl")).unwrap();
    assert!(log.warnings.is_empty(), "{:?}", log.warnings);
    let replay = log.replay(None, cfg.tz);
    (cfg, replay)
}

/// The §8.5 weight of one observation.
fn weight(cfg: &Config, day: NaiveDate, went: Option<u8>) -> f64 {
    let age = (today() - day).num_days() as f64;
    let went = match went {
        Some(3) => 2.0,
        Some(2) => 1.5,
        _ => 1.0,
    };
    (-age / cfg.energy.decay_days).exp() * went
}

/// The §8.5 shrunken mean.
fn shrunken(prior: f64, n0: f64, obs: &[(f64, f64)]) -> f64 {
    let num: f64 = n0 * prior + obs.iter().map(|(w, x)| w * x).sum::<f64>();
    let den: f64 = n0 + obs.iter().map(|(w, _)| w).sum::<f64>();
    num / den
}

#[test]
fn the_fixture_log_replays_cleanly() {
    let (_, r) = setup();
    assert_eq!(r.days.len(), 14);
    assert_eq!(r.unknown, 0);
    assert!(r.warnings.is_empty(), "{:?}", r.warnings);
    // 3 or 4 blocks a day, each with a start report, plus one energy event.
    assert_eq!(r.energy.len(), 61); // 47 block starts + 14 energy events
    assert_eq!(r.durations.len(), 47);
    assert!(r.energy.iter().any(|o| o.loc == "home"));
    assert!(r.energy.iter().any(|o| !o.from_start));
}

/// The hand-computed §8.5 curve for one location:
/// `energy[b] = round((n0·prior[b] + Σ wᵢ repᵢ) / (n0 + Σ wᵢ))` for all 12
/// buckets, plus the observation count per bucket.
fn hand_computed_curve(cfg: &Config, r: &Replay, loc: &str) -> (Vec<u8>, Vec<usize>) {
    let n0 = cfg.energy.prior_weight;
    let mut levels = Vec::with_capacity(12);
    let mut counts = Vec::with_capacity(12);
    for b in 0..12usize {
        let obs: Vec<(f64, f64)> = r
            .energy
            .iter()
            .filter(|o| o.loc == loc && o.hsw.floor() as usize == b)
            .map(|o| (weight(cfg, o.day, o.went), o.rep as f64))
            .collect();
        counts.push(obs.len());
        let prior = cfg.prior_energy(loc, b as f64) as f64;
        levels.push(shrunken(prior, n0, &obs).round() as u8);
    }
    (levels, counts)
}

/// §8.5: `energy[b] = round((n0·prior[b] + Σ wᵢ repᵢ) / (n0 + Σ wᵢ))`, over
/// *every* bucket of both curves — including the ones where the reports pull
/// the level off the prior.
#[test]
fn fit_reproduces_hand_computed_bucket_means() {
    let (cfg, r) = setup();
    let model = fit_replay(&cfg, &r, today());
    let n0 = cfg.energy.prior_weight;
    assert_eq!(n0, 5.0);

    for loc in ["lounge", "home"] {
        let (want, counts) = hand_computed_curve(&cfg, &r, loc);
        assert_eq!(model.energy[loc], want, "{loc} curve (obs per bucket {counts:?})");
        // Buckets with no observations keep the prior exactly.
        for (b, n) in counts.iter().enumerate() {
            if *n == 0 {
                assert_eq!(
                    model.energy[loc][b],
                    cfg.prior_energy(loc, b as f64),
                    "{loc} bucket {b} has no observations"
                );
            }
        }
    }

    // The fit is not a no-op: on this log the reports move `home` at hsw 7
    // off its prior. 7 observations there, hand-computed above, so a fit that
    // silently discarded every energy observation would fail here.
    assert_eq!(cfg.prior_energy("home", 7.0), 3);
    assert_eq!(model.energy["home"][7], 2);
    assert_eq!(
        r.energy
            .iter()
            .filter(|o| o.loc == "home" && o.hsw.floor() as usize == 7)
            .count(),
        7
    );

    // Every curve is a full 12-bucket vector and every level is 0..=5.
    for (loc, curve) in &model.energy {
        assert_eq!(curve.len(), 12, "{loc}");
        assert!(curve.iter().all(|l| *l <= 5), "{loc}");
    }
    assert_eq!(model.fitted, Some(today()));
    assert_eq!(model.n_obs, r.energy.len() as u32);
}

/// The mirror image of the test above: with the energy observations taken
/// away the same fit returns the prior curves unchanged. It pins down that
/// the fitted curves above are actually driven by the reports (and not by
/// the durations, the arrivals or the config alone).
#[test]
fn a_fit_without_energy_observations_is_the_prior_curve() {
    let (cfg, r) = setup();
    let arrivals = arrivals_from_replay(&cfg, &r);
    let blind = fit(&cfg, &FitInput::new(&[], &r.durations, &arrivals), today());
    let real = fit_replay(&cfg, &r, today());

    for loc in ["lounge", "home"] {
        let prior: Vec<u8> = (0..12).map(|b| cfg.prior_energy(loc, b as f64)).collect();
        assert_eq!(blind.energy[loc], prior, "{loc} without observations");
    }
    assert_ne!(blind.energy["home"], real.energy["home"]);
    assert_eq!(blind.n_obs, 0);
    // With no short nights to learn from, the shift stays absent so the
    // config value keeps applying (§8.4/§8.5 config fallback).
    assert_eq!(blind.sleep_debt_shift, None);
    assert!(real.sleep_debt_shift.is_some());
}

/// §8.5: the sleep-debt shift is the shrunken *deficit* `energy[b] − rep`
/// over the short nights (see the module note on the sign).
#[test]
fn fit_learns_the_sleep_debt_shift() {
    let (cfg, r) = setup();
    let model = fit_replay(&cfg, &r, today());
    let under = cfg.energy.sleep_debt.under_hours;
    let obs: Vec<(f64, f64)> = r
        .energy
        .iter()
        .filter(|o| o.slept_min.is_some_and(|m| m as f64 / 60.0 < under))
        .map(|o| {
            let learned = model.energy[&o.loc][o.hsw.floor() as usize] as f64;
            (weight(&cfg, o.day, o.went), learned - o.rep as f64)
        })
        .collect();
    assert!(obs.len() >= 8, "{} short-night observations", obs.len());
    let want = shrunken(cfg.energy.sleep_debt.shift, cfg.energy.prior_weight, &obs);
    let want = (want * 100.0).round() / 100.0;
    assert_eq!(model.sleep_debt_shift, Some(want));
    assert!(want > 0.0, "a deficit is positive");
    assert_eq!(model.sleep_shift(&cfg), want);
}

/// §8.5: `duration[tag] = shrunken mean of actual/est`, prior 1.0,
/// `n0 = duration_prior_weight`.
#[test]
fn fit_learns_duration_multipliers() {
    let (cfg, r) = setup();
    let model = fit_replay(&cfg, &r, today());
    let n0 = cfg.energy.duration_prior_weight;
    assert_eq!(n0, 5.0);

    for tag in ["lean", "soundcode", "admin"] {
        let obs: Vec<(f64, f64)> = r
            .durations
            .iter()
            .filter(|o| o.tags.first().map(|t| t.as_str()) == Some(tag))
            .map(|o| (weight(&cfg, o.day, o.went), o.ratio().unwrap()))
            .collect();
        assert!(obs.len() >= 3, "{tag}: {} observations", obs.len());
        let want = (shrunken(1.0, n0, &obs) * 100.0).round() / 100.0;
        assert_eq!(model.duration[tag], want, "{tag}");
    }

    // `_default` runs over every observation, tagged or not.
    let all: Vec<(f64, f64)> = r
        .durations
        .iter()
        .map(|o| (weight(&cfg, o.day, o.went), o.ratio().unwrap()))
        .collect();
    let want = (shrunken(1.0, n0, &all) * 100.0).round() / 100.0;
    assert_eq!(model.duration[DEFAULT_TAG], want);
    assert!(all.len() > r.durations.iter().filter(|o| !o.tags.is_empty()).count());
}

/// §8.5: `p_lounge[weekday]` and `expected_arrival[weekday]` are shrunken
/// means over the `arrive` events, with the `[expected]` config as prior.
#[test]
fn fit_learns_p_lounge_and_arrival_for_monday() {
    let (cfg, r) = setup();
    let arrivals = arrivals_from_replay(&cfg, &r);
    assert_eq!(arrivals.len(), 14);
    let model = fit_replay(&cfg, &r, today());
    let n0 = cfg.energy.prior_weight;

    let mondays: Vec<&ArrivalObs> = arrivals
        .iter()
        .filter(|a| a.date.weekday() == Weekday::Mon)
        .collect();
    assert_eq!(mondays.len(), 2, "2026-08-31 and 2026-09-07");
    assert!(mondays.iter().all(|a| a.loc == "lounge"));

    // p_lounge: the observations are all 1 (lounge), the prior is 0.9.
    let obs: Vec<(f64, f64)> = mondays
        .iter()
        .map(|a| (weight(&cfg, a.date, None), 1.0))
        .collect();
    let want = shrunken(*cfg.expected.p_lounge.get(Weekday::Mon), n0, &obs);
    let want = (want * 100.0).round() / 100.0;
    assert_eq!(model.p_lounge.get(Weekday::Mon), Some(&want));
    assert!(want > 0.9, "two lounge Mondays pull the prior up");

    // expected_arrival: a mean of minutes-since-midnight, rounded.
    let minutes = |t: chrono::NaiveTime| {
        use chrono::Timelike;
        t.hour() * 60 + t.minute()
    };
    let obs: Vec<(f64, f64)> = mondays
        .iter()
        .map(|a| (weight(&cfg, a.date, None), minutes(a.time) as f64))
        .collect();
    let prior = minutes(*cfg.expected.arrival.get(Weekday::Mon)) as f64;
    let want = shrunken(prior, n0, &obs).round() as u32;
    let got = model.expected_arrival.get(Weekday::Mon).unwrap().time();
    assert_eq!(minutes(got), want);
    // Sunday has no lounge arrivals in the fixture, so it stays near its prior.
    assert!(model.p_lounge.get(Weekday::Sun).unwrap() < &0.4);
}

/// §8.4 falls back to `[expected]` in config.toml for a weekday the model
/// has not learned, and §8.5's own example `model.json` is partial (only
/// `Mon` and `Sat`). So a fit writes a weekday only when it has an `arrive`
/// observation for it — otherwise the first `tm model --fit` would freeze
/// today's config into the file and later config edits would do nothing.
#[test]
fn fit_leaves_unobserved_weekdays_out_of_the_model() {
    let cfg = Config::load(fixtures().join("plan-basic/config.toml")).unwrap();
    let monday = ArrivalObs {
        date: NaiveDate::from_ymd_opt(2026, 9, 7).unwrap(),
        time: chrono::NaiveTime::from_hms_opt(7, 10, 0).unwrap(),
        loc: "lounge".to_string(),
    };
    let model = fit(&cfg, &FitInput::new(&[], &[], &[monday]), today());

    assert_eq!(model.p_lounge.len(), 1);
    assert_eq!(model.expected_arrival.len(), 1);
    assert!(model.p_lounge.get(Weekday::Mon).is_some());
    assert_eq!(model.p_lounge.get(Weekday::Tue), None);
    assert_eq!(model.expected_arrival.get(Weekday::Sat), None);
    assert!(!model.to_json().contains("Tue"), "{}", model.to_json());

    // …so the config still drives the unobserved weekdays after a fit, and a
    // config edit is still visible through the model's accessors.
    assert_eq!(
        model.expected_arrival_on(Weekday::Sat, &cfg),
        *cfg.expected.arrival.get(Weekday::Sat)
    );
    assert_eq!(
        model.p_lounge_on(Weekday::Tue, &cfg),
        *cfg.expected.p_lounge.get(Weekday::Tue)
    );

    // A weekday already in the base model survives a fit that saw nothing
    // new for it (it was learned once; no observation is not evidence
    // against it).
    let refit = fit(
        &cfg,
        &FitInput::new(&[], &[], &[]).with_base(&model),
        today(),
    );
    assert_eq!(refit.p_lounge.get(Weekday::Mon), model.p_lounge.get(Weekday::Mon));
    assert_eq!(refit.p_lounge.get(Weekday::Tue), None);
}

/// §8.5: "hand edits become the new prior" — a refit shrinks towards the
/// model on disk when one is passed as the base.
#[test]
fn fit_shrinks_towards_the_base_model() {
    let (cfg, r) = setup();
    let mut base = Model::from_config(&cfg);
    base.energy.insert("lounge".to_string(), vec![0; 12]);
    let arrivals = arrivals_from_replay(&cfg, &r);
    let input = FitInput::new(&r.energy, &r.durations, &arrivals).with_base(&base);
    let with_base = fit(&cfg, &input, today());
    let without = fit_replay(&cfg, &r, today());
    assert!(
        with_base.energy["lounge"][1] < without.energy["lounge"][1],
        "a zeroed base prior drags the fitted level down"
    );
}

#[test]
fn fitted_model_show_snapshot() {
    let (cfg, r) = setup();
    let model = fit_replay(&cfg, &r, today());
    insta::assert_snapshot!("fitted_14d_show", energy::show(&model));
}

// ---------------------------------------------------------------------------
// compare and the §11 monitors
// ---------------------------------------------------------------------------

fn obs(t: &str, loc: &str, hsw: f64, pred: u8, rep: u8) -> EnergyObs {
    let t: DateTime<FixedOffset> = DateTime::parse_from_rfc3339(t).unwrap();
    EnergyObs {
        t,
        day: t.date_naive(),
        pred,
        rep,
        hsw,
        loc: loc.to_string(),
        slept_min: Some(480),
        went: None,
        id: None,
        from_start: false,
    }
}

/// `tm model --compare`: MAE and bias of two models on the same reports,
/// hand-computed here.
#[test]
fn compare_scores_two_models() {
    let cfg = Config::default();
    let a = Model::default(); // the config prior: 5 at hsw 1, 3 at hsw 9
    let mut b = Model::default();
    b.energy.insert("lounge".to_string(), vec![3; 12]);

    let observations = [
        obs("2026-09-07T08:00:00-05:00", "lounge", 1.0, 5, 5),
        obs("2026-09-07T15:00:00-05:00", "lounge", 9.0, 3, 2),
    ];
    let c = compare(&cfg, &a, &b, &observations);
    assert_eq!(c.n, 2);
    // A predicts 5 and 3 → errors 0 and −1 → MAE 0.5, bias −0.5.
    assert_eq!(c.mae_a, 0.5);
    assert_eq!(c.bias_a, -0.5);
    // B predicts 3 and 3 → errors +2 and −1 → MAE 1.5, bias +0.5.
    assert_eq!(c.mae_b, 1.5);
    assert_eq!(c.bias_b, 0.5);
    assert!(!c.b_is_better());
    assert_eq!(c.by_hour, vec![(8, 0.0, 2.0), (15, 1.0, 1.0)]);
}

/// A model fitted on the log beats the bare prior on that same log — and the
/// margin comes from the buckets the fit actually moved, not from noise: a
/// model that merely *restates* the prior ties with it.
#[test]
fn a_fitted_model_beats_the_prior_on_its_own_observations() {
    let (cfg, r) = setup();
    let fitted = fit_replay(&cfg, &r, today());
    let c = compare(&cfg, &Model::default(), &fitted, &r.energy);
    assert_eq!(c.n, r.energy.len());
    assert!(c.b_is_better(), "prior {} vs fitted {}", c.mae_a, c.mae_b);

    // Both MAEs recomputed here from the curves, so `compare` is checked
    // against the definition and not just against itself.
    let mae = |m: &Model| {
        let sum: f64 = r
            .energy
            .iter()
            .map(|o| {
                let curve = m
                    .energy
                    .get(&o.loc)
                    .map(|c| c[o.hsw.floor() as usize])
                    .unwrap_or_else(|| cfg.prior_energy(&o.loc, o.hsw));
                let shift = if o.slept_min.is_some_and(|s| {
                    s as f64 / 60.0 < cfg.energy.sleep_debt.under_hours
                }) {
                    m.sleep_shift(&cfg).round() as i32
                } else {
                    0
                };
                let pred = (curve as i32 - shift).clamp(0, 5);
                (o.rep as i32 - pred).abs() as f64
            })
            .sum();
        (sum / r.energy.len() as f64 * 100.0).round() / 100.0
    };
    assert_eq!(c.mae_a, mae(&Model::default()));
    assert_eq!(c.mae_b, mae(&fitted));

    // The prior written out as a model scores exactly like the bare prior:
    // `b_is_better` above therefore reports learning, not a change of shape.
    let tie = compare(&cfg, &Model::default(), &Model::from_config(&cfg), &r.energy);
    assert_eq!(tie.mae_a, tie.mae_b);
    assert!(!tie.b_is_better());

    // And the win is the `home` hsw-7 bucket: put the prior level back and
    // the advantage disappears.
    let mut undone = fitted.clone();
    undone.energy.get_mut("home").unwrap()[7] = cfg.prior_energy("home", 7.0);
    let c2 = compare(&cfg, &Model::default(), &undone, &r.energy);
    assert_eq!(c2.mae_a, c2.mae_b);
}

/// §11 energy calibration: MAE and bias of the *logged* predictions.
#[test]
fn calibration_uses_the_logged_predictions() {
    let cfg = Config::default();
    let observations = [
        obs("2026-09-07T08:00:00-05:00", "lounge", 1.0, 5, 5),
        obs("2026-09-07T09:00:00-05:00", "lounge", 2.0, 5, 4),
        obs("2026-09-07T15:00:00-05:00", "lounge", 9.0, 3, 2),
    ];
    let c = calibration(&cfg, &observations);
    assert_eq!(c.n, 3);
    assert_eq!(c.mae, 0.67); // (0 + 1 + 1) / 3
    assert_eq!(c.bias, -0.67); // reports run below the predictions
    assert_eq!(c.by_hour.len(), 3);
    assert_eq!(c.by_hour[0], (8, 1, 0.0, 0.0));

    let (cfg, r) = setup();
    let c = calibration(&cfg, &r.energy);
    assert_eq!(c.n, 61);
    assert!(c.mae > 0.0 && c.mae < 1.5);
}

/// §11 estimate calibration: `actual/est` per tag with the shrunken
/// multiplier (`lean ×1.6 (n=9)`).
#[test]
fn estimate_calibration_reports_per_tag_ratios() {
    let cfg = Config::default();
    let mk = |day: &str, tag: &str, est: u32, actual: u32| DurationObs {
        t: chrono_tz::America::Chicago
            .with_ymd_and_hms(2026, 9, 7, 12, 0, 0)
            .unwrap()
            .fixed_offset(),
        day: NaiveDate::parse_from_str(day, "%Y-%m-%d").unwrap(),
        id: "x".into(),
        ci: 4,
        tags: if tag.is_empty() {
            vec![]
        } else {
            vec![tag.to_string()]
        },
        est_min: est,
        actual_min: actual,
        went: None,
        partial: false,
    };
    let durations = [
        mk("2026-09-07", "lean", 60, 90),  // 1.5
        mk("2026-09-06", "lean", 60, 90),  // 1.5
        mk("2026-09-01", "admin", 60, 30), // 0.5
    ];
    let rows = estimate_calibration(&cfg, &durations, today());
    assert_eq!(rows.len(), 3); // lean, admin, _default
    let lean = rows.iter().find(|r| r.tag == "lean").unwrap();
    assert_eq!(lean.n, 2);
    assert_eq!(lean.mean_ratio, 1.5);
    assert_eq!(lean.recent_ratio, Some(1.5));
    assert!(lean.multiplier > 1.0 && lean.multiplier < 1.5, "shrunk to the 1.0 prior");
    let admin = rows.iter().find(|r| r.tag == "admin").unwrap();
    assert_eq!(admin.mean_ratio, 0.5);
    assert_eq!(admin.recent_ratio, Some(0.5));
    let all = rows.iter().find(|r| r.tag == DEFAULT_TAG).unwrap();
    assert_eq!(all.n, 3);
}
