//! `capacity::lookahead` (§8.4) over the week of the `plan-basic` fixture:
//! seven days from Monday 2026-09-07 with the walls of
//! `calendar/2026-W37.md` (meeting Mon 12:50–13:50, CS 234 lecture Wed
//! 15:00–16:20, dinner Thu 19:00–20:00, flight Sat 08:15–10:40).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use chrono::{DateTime, NaiveDate, NaiveTime, TimeZone};
use chrono_tz::Tz;
use tm_core::capacity::{
    available_until, cut_slots, energize, local_dt, lookahead, reserve, upto, week_grid,
    DayCapacity, EnergyCtx, Slot, WallsByDate,
};
use tm_core::config::Config;
use tm_core::energy::{Model, Posterior};
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

/// A learned model changes the lookahead: the expected arrival and location
/// come from `model.json` when it has them.
#[test]
fn lookahead_follows_the_learned_arrival_and_location() {
    let cfg = cfg();
    let model = Model::load(&fixtures().join("model.json")).unwrap().unwrap();
    let caps = week(&cfg, &model);
    // The fixture model has p_lounge Sat = 0.5 → still lounge, and an
    // expected arrival of 10:30 on Saturday (vs 10:00 in the config), so the
    // flight wall no longer overlaps the window and Saturday keeps its
    // budget.
    assert_eq!(caps[5].total(), 6 * 60);
    // Wednesday's learned p_lounge is 0.8 → lounge, ci 5 slots exist.
    assert!(caps[2].minutes_at_level[5] > 0);
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

#[test]
fn a_day_with_no_arrival_time_still_produces_slots() {
    let cfg = cfg();
    let model = Model::default();
    let caps = lookahead(
        &BTreeMap::new(),
        &cfg,
        &model,
        &[],
        date("2026-09-07"),
        3,
        NaiveTime::from_hms_opt(6, 5, 0).unwrap(),
    );
    assert_eq!(caps[0].total(), 0, "today came in empty");
    assert!(caps[1].total() > 0);
    assert_eq!(
        TZ.timestamp_opt(0, 0).single().map(|_| ()),
        Some(()),
        "timezone sanity"
    );
}
