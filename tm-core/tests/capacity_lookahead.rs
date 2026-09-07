//! `capacity::lookahead` (§8.4) over the week of the `plan-basic` fixture:
//! seven days from Monday 2026-09-07 with the walls of
//! `calendar/2026-W37.md` (meeting Mon 12:50–13:50, CS 234 lecture Wed
//! 15:00–16:20, dinner Thu 19:00–20:00, flight Sat 08:15–10:40).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use chrono::{DateTime, NaiveDate, NaiveTime, Weekday};
use chrono_tz::Tz;
use tm_core::capacity::{
    available_until, cut_slots, energize, local_dt, lookahead, reserve, upto, week_grid,
    window_and_budget, DayCapacity, EnergyCtx, Slot, WallsByDate,
};
use tm_core::config::Config;
use tm_core::energy::{Hhmm, Model, Posterior};
use tm_core::grammar;
use tm_core::model::{Loc, Shape};

const TZ: Tz = Tz::America__Chicago;

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn cfg() -> Config {
    Config::load(fixtures().join("plan-basic/config.toml")).unwrap()
}

fn date(s: &str) -> NaiveDate {
    NaiveDate::parse_from_str(s, "%Y-%m-%d").unwrap()
}

fn at(day: &str, h: u32, m: u32) -> DateTime<Tz> {
    local_dt(TZ, date(day), NaiveTime::from_hms_opt(h, m, 0).unwrap())
}

/// The `calendar/2026-W37.md` intervals, grouped by the day they start on.
fn calendar_walls(cfg: &Config) -> WallsByDate {
    let path = "calendar/2026-W37.md";
    let text = std::fs::read_to_string(fixtures().join("plan-basic").join(path)).unwrap();
    let parsed = grammar::parse_file(path, &text, cfg);
    assert!(parsed.problems.is_empty(), "{:?}", parsed.problems);
    let mut out: WallsByDate = BTreeMap::new();
    for item in parsed.items() {
        if let Shape::Interval { start, end } = item.shape {
            let s = local_dt(cfg.tz, start.date(), start.time());
            let e = local_dt(cfg.tz, end.date(), end.time());
            out.entry(start.date()).or_default().push((s, e));
        }
    }
    out
}

/// Today's remaining slots, energised: the §4.3 day (07:00 → 16:00 around
/// the meeting), lounge, woke 06:05 after 8h10m.
fn today_slots(cfg: &Config, model: &Model) -> Vec<Slot> {
    let posterior = Posterior::none(cfg);
    let walls = [(at("2026-09-07", 12, 50), at("2026-09-07", 13, 50))];
    let cut = cut_slots(
        at("2026-09-07", 7, 0),
        at("2026-09-07", 16, 0),
        &walls,
        cfg,
    );
    let ctx = EnergyCtx::new(model, cfg, &posterior, at("2026-09-07", 6, 5), Loc::Lounge)
        .with_slept(Some(490));
    energize(&cut.slots, &ctx)
}

fn week(cfg: &Config, model: &Model) -> Vec<DayCapacity> {
    lookahead(
        &calendar_walls(cfg),
        cfg,
        model,
        &today_slots(cfg, model),
        date("2026-09-07"),
        7,
        NaiveTime::from_hms_opt(6, 5, 0).unwrap(),
    )
}

#[test]
fn calendar_walls_are_read_from_the_fixture() {
    let cfg = cfg();
    let walls = calendar_walls(&cfg);
    assert_eq!(walls.len(), 4);
    assert_eq!(
        walls[&date("2026-09-07")],
        vec![(at("2026-09-07", 12, 50), at("2026-09-07", 13, 50))]
    );
    assert_eq!(
        walls[&date("2026-09-12")],
        vec![(at("2026-09-12", 8, 15), at("2026-09-12", 10, 40))]
    );
}

#[test]
fn lookahead_week_grid_snapshot() {
    let cfg = cfg();
    let caps = week(&cfg, &Model::default());
    assert_eq!(caps.len(), 7);
    assert_eq!(caps[0].date, date("2026-09-07"));
    assert_eq!(caps[6].date, date("2026-09-13"));
    insta::assert_snapshot!("lookahead_plan_basic_week", week_grid(&caps));
}

/// Today comes from the slots handed in; future days are simulated from the
/// expected arrival, the expected location and the budget.
#[test]
fn lookahead_uses_todays_slots_and_the_budget_for_later_days() {
    let cfg = cfg();
    let model = Model::default();
    let caps = week(&cfg, &model);

    // Today: exactly the slots passed in (6h50m, no budget trimming).
    let mine = today_slots(&cfg, &model);
    assert_eq!(caps[0].total(), mine.iter().map(|s| s.minutes()).sum::<u32>());
    assert_eq!(caps[0].total(), 410);

    // Tuesday: a full day, trimmed to the 6-block budget.
    assert_eq!(caps[1].date, date("2026-09-08"));
    assert_eq!(caps[1].total(), 6 * 60);
    // The highest levels survive the trim: three 5s, then 4s.
    assert_eq!(caps[1].minutes_at_level[5], 180);
    assert_eq!(caps[1].minutes_at_level[4], 180);
    assert_eq!(caps[1].minutes_at_level[3], 0);

    // Sunday is a home day (`p_lounge` 0.4 < 0.5), so the home cap applies:
    // nothing above ci 3.
    let sunday = &caps[6];
    assert_eq!(sunday.date.format("%a").to_string(), "Sun");
    assert_eq!(sunday.minutes_at_level[4], 0);
    assert_eq!(sunday.minutes_at_level[5], 0);
    assert!(sunday.minutes_at_level[3] > 0);

    // Saturday's flight eats the morning but extends the window, so the day
    // still reaches its budget.
    assert_eq!(caps[5].date, date("2026-09-12"));
    assert_eq!(caps[5].total(), 6 * 60);
}

/// §8.4: "expected arrival = `model.expected_arrival(weekday)` (learned;
/// default config), expected location by `P(lounge | weekday)`". Every
/// assertion here is written against the *config* answer as well, so a
/// lookahead that ignored the model and read config.toml would fail.
#[test]
fn lookahead_follows_the_learned_arrival_and_location() {
    let cfg = cfg();
    let mut model = Model::default();
    // Tuesday: learned arrival 12:00 against the config's 07:00.
    model
        .expected_arrival
        .set(Weekday::Tue, Hhmm(NaiveTime::from_hms_opt(12, 0, 0).unwrap()));
    // Wednesday: learned P(lounge) 0.2 against the config's 0.9 → a home day.
    model.p_lounge.set(Weekday::Wed, 0.2);
    // Sunday: learned P(lounge) 0.8 against the config's 0.4 → a lounge day.
    model.p_lounge.set(Weekday::Sun, 0.8);

    let learned = week(&cfg, &model);
    let config = week(&cfg, &Model::default());

    // Tuesday still fills its 6-block budget, but five hours later in the
    // day: the whole distribution slides down the curve (hsw 5.9 → 11.6).
    assert_eq!(learned[1].date, date("2026-09-08"));
    assert_eq!(learned[1].total(), 6 * 60);
    assert_eq!(learned[1].minutes_at_level, [0, 0, 120, 120, 120, 0]);
    assert_eq!(config[1].minutes_at_level, [0, 0, 0, 0, 180, 180]);

    // Wednesday at home: the home cap (`home_max_ci` 3) removes every ci-4
    // and ci-5 minute the config location would have given.
    assert_eq!(learned[2].date, date("2026-09-09"));
    assert_eq!(learned[2].minutes_at_level[4], 0);
    assert_eq!(learned[2].minutes_at_level[5], 0);
    assert!(config[2].minutes_at_level[5] > 0);
    assert_eq!(learned[2].total(), config[2].total());

    // Sunday in the lounge: the cap is gone and ci-5 capacity appears.
    assert!(learned[6].minutes_at_level[5] > 0);
    assert_eq!(config[6].minutes_at_level[5], 0);
    assert_eq!(config[6].minutes_at_level[4], 0);

    // Untouched weekdays keep the config answer.
    assert_eq!(learned[3].minutes_at_level, config[3].minutes_at_level);
}

/// The learned *curve* feeds the lookahead too: the §8.5 example
/// `model.json` reports one level less than the prior at hsw 7 (home 3 → 2),
/// which shows up on Sunday, the fixture week's home day.
#[test]
fn lookahead_uses_the_learned_energy_curve() {
    let cfg = cfg();
    let model = Model::load(&fixtures().join("model.json")).unwrap().unwrap();
    assert_eq!(model.energy["home"][7], 2);
    assert_eq!(cfg.prior_energy("home", 7.0), 3);

    let learned = week(&cfg, &model);
    let config = week(&cfg, &Model::default());
    let sunday = 6;
    assert_eq!(learned[sunday].date, date("2026-09-13"));
    assert_eq!(learned[sunday].total(), config[sunday].total());
    assert_ne!(
        learned[sunday].minutes_at_level,
        config[sunday].minutes_at_level
    );
    // One hour moves from level 3 to level 2 (the hsw-7 block).
    assert_eq!(
        learned[sunday].minutes_at_level[3] + 60,
        config[sunday].minutes_at_level[3]
    );
    assert_eq!(
        learned[sunday].minutes_at_level[2],
        config[sunday].minutes_at_level[2] + 60
    );
    // The fixture's `expected_arrival` is partial (Mon and Sat only), so the
    // other days still come from `[expected]` in config.toml.
    assert_eq!(model.expected_arrival.get(Weekday::Wed), None);
    assert_eq!(
        model.expected_arrival_on(Weekday::Wed, &cfg),
        *cfg.expected.arrival.get(Weekday::Wed)
    );
}

/// §7.1/§7.3: the cumulative helpers the EDF pass uses.
#[test]
fn available_until_and_reserve() {
    let cfg = cfg();
    let mut caps = week(&cfg, &Model::default());

    let by_wed = available_until(&caps, date("2026-09-09"), 0);
    let by_sun = available_until(&caps, date("2026-09-13"), 0);
    assert_eq!(by_wed, caps[..3].iter().map(|d| d.total()).sum::<u32>());
    assert!(by_sun > by_wed);
    // A ci-5 item can only use the lounge mornings.
    let ci5 = available_until(&caps, date("2026-09-13"), 5);
    assert!(ci5 > 0 && ci5 < by_sun);
    assert_eq!(
        ci5,
        caps.iter().map(|d| d.minutes_at_level[5]).sum::<u32>()
    );

    // Reserving takes the earliest days first, highest levels first.
    let n = upto(&caps, date("2026-09-08"));
    assert_eq!(n, 2);
    let before = caps[0].minutes_at_level;
    let got = reserve(&mut caps[..n], 120, 4);
    assert_eq!(got, 120);
    assert_eq!(caps[0].minutes_at_level[5], before[5].saturating_sub(120));
    assert_eq!(caps[0].minutes_at_level[4], before[4]);
    assert_eq!(caps[1].total(), 360, "day 2 untouched while day 1 has room");

    // Asking for more than exists reserves what there is.
    let left: u32 = caps[..n].iter().map(|d| d.at_least(4)).sum();
    let got = reserve(&mut caps[..n], left + 10_000, 4);
    assert_eq!(got, left);
    assert_eq!(available_until(&caps, date("2026-09-08"), 4), 0);
    // Levels below the floor are untouched.
    assert!(caps[0].minutes_at_level[3] > 0 || caps[1].minutes_at_level[3] > 0);
}

#[test]
fn empty_and_degenerate_inputs() {
    let cfg = cfg();
    let caps = lookahead(
        &BTreeMap::new(),
        &cfg,
        &Model::default(),
        &[],
        date("2026-09-07"),
        0,
        NaiveTime::from_hms_opt(6, 5, 0).unwrap(),
    );
    assert!(caps.is_empty());
    assert_eq!(available_until(&caps, date("2026-09-07"), 0), 0);
    assert_eq!(week_grid(&caps).lines().count(), 2); // header + total

    let mut one = vec![DayCapacity::empty(date("2026-09-07"))];
    assert_eq!(reserve(&mut one, 60, 0), 0);
}

/// Today is whatever the planner handed in — empty here — while a later day
/// is simulated end to end from the config's expected arrival: window, cut,
/// energies and the budget trim. The expected value is rebuilt from those
/// pieces rather than copied from a run.
#[test]
fn today_is_taken_as_given_and_later_days_are_simulated() {
    let cfg = cfg();
    let model = Model::default();
    let wake_time = NaiveTime::from_hms_opt(6, 5, 0).unwrap();
    let caps = lookahead(
        &BTreeMap::new(),
        &cfg,
        &model,
        &[],
        date("2026-09-07"),
        3,
        wake_time,
    );
    assert_eq!(caps.len(), 3);
    assert_eq!(caps[0].total(), 0, "today came in empty");

    // Tuesday, rebuilt by hand: arrival from `[expected]`, no walls.
    let tuesday = date("2026-09-08");
    assert_eq!(caps[1].date, tuesday);
    let arrival = local_dt(TZ, tuesday, *cfg.expected.arrival.get(Weekday::Tue));
    assert_eq!(arrival, at("2026-09-08", 7, 0));
    let (end, budget) = window_and_budget(arrival, &[], &cfg);
    assert_eq!(end, at("2026-09-08", 15, 0));
    assert_eq!(budget, 6);
    let cut = cut_slots(arrival, end, &[], &cfg);
    let posterior = Posterior::none(&cfg);
    let ctx = EnergyCtx::new(
        &model,
        &cfg,
        &posterior,
        local_dt(TZ, tuesday, wake_time),
        Loc::Lounge, // config p_lounge Tue = 0.9 ≥ 0.5
    );
    let mut want = DayCapacity::empty(tuesday);
    for s in energize(&cut.slots, &ctx) {
        want.minutes_at_level[s.energy as usize] += s.minutes();
    }
    // The cut is longer than the budget (7 blocks for 6), so §8.4 keeps
    // `budget × block_min` minutes, highest energy first.
    assert!(want.total() > budget * cfg.block_min());
    let mut left = budget * cfg.block_min();
    let mut trimmed = DayCapacity::empty(tuesday);
    for level in (0..6).rev() {
        let take = want.minutes_at_level[level].min(left);
        trimmed.minutes_at_level[level] = take;
        left -= take;
    }
    assert_eq!(caps[1].minutes_at_level, trimmed.minutes_at_level);
    assert_eq!(caps[1].minutes_at_level, [0, 0, 0, 0, 180, 180]);
    assert_eq!(caps[1].total(), 6 * 60);
}
