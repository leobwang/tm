//! **T13: the kernel's lookahead against the fork point's `capacity::lookahead`**
//! (stage 5 D10 step L7; design `kernel/design/stage5/stage5-D9-D10-design.md`
//! §13.7, §14.8 row L7, §17).
//!
//! The fork is the in-tree Rust: `tm_core::capacity::lookahead`, fed the walls
//! `Ctx::walls_on` computes (`tm/src/cli/ctx.rs`; copied below as
//! [`fork_walls_by_date`], because `Ctx` lives in the binary) and the wake
//! `Ctx::wake_time` resolves (`Model::wake_or_expected`). The kernel is reached
//! through `tm_kernel_ffi::call`: the loaded plan's calendar documents, the zone
//! table from `tm/src/cli/tz_table.rs` (the one encoder of zones), and L6's
//! `capacity` section (Boundary.lean's `runCap`).
//!
//! Every generated window is run seven times (and the fork again where P27 or gap 85
//! is measured, below):
//!
//! * the fork with every `P(lounge)` forced to 1, then to 0, then as generated;
//! * the kernel with the model's seven weights forced to `1/1`, then `0/1`, then
//!   to the **threshold twin** of each weekday's weight (`Look.twin`: `1/1` iff
//!   `2w ≥ capDen`, the fork's `p ≥ 0.5`), then as generated.
//!
//! and must satisfy, day by day and level by level:
//!
//! * **the per-location profiles**: the kernel at `1/1` is `capDen ×` the fork at
//!   1, and at `0/1` `capDen ×` the fork at 0
//!   (`lookahead_at_a_certain_weight_is_the_pure_location`);
//! * **T13**: the kernel's twin is `capDen ×` the fork's own run
//!   (`the_twin_forces_the_forks_location`, parity P1 refined);
//! * **the mixture, D10's documented difference**: the kernel's real run is
//!   `w·L + (capDen − w)·H` of the fork's forced minutes `L` and `H`, at the weight
//!   `w` of each date's own weekday, model's else config's
//!   (`lookahead_future_day_is_the_mixture`), and so lies between the locations
//!   (`lookahead_between_the_locations`);
//! * **day 0** is the host's histogram in every run (`lookahead_day_zero_is_the_hosts`).
//!
//! **P27** (site R3 reopened): where `f64` rounds the window's minutes or floors the
//! budget differently from the exact pair, the fork is run again on a config whose
//! doubles give the kernel's two integers, and that run must then agree exactly: the
//! two rounding sites are the whole difference. **Gap 85** (quirk (e), a multi-day wall
//! handed unclipped to each date it covers) is reproduced, not avoided: the generator
//! makes multi-day walls, the kernel must agree with the fork on them, and the test
//! measures what clipping each date's walls to that date would have changed.

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

use std::collections::BTreeMap;

use chrono::{Datelike, Duration, NaiveDate, NaiveTime, TimeZone, Timelike, Weekday};
use chrono_tz::Tz;
use serde_json::{json, Value};
use tm_core::capacity::{self, DayCapacity, Slot, SlotKind, Wall, WallsByDate};
use tm_core::config::{Config, PerWeekday, Step, StepFn};
use tm_core::energy::{weekday_key, Hhmm, Model, WeekdayMap};
use tm_core::model::Shape;
use tm_core::tree::Tree;

/// `Look.capDen` (D17).
const CAP_DEN: u128 = 1_000_000_000_000_000_000;

/// The fixed seed, and the number of windows (each shows day 0 and six future days).
const SEED: u64 = 0x4c37_d10_7_7e57;
const WINDOWS: usize = 64;

const WEEK: [Weekday; 7] = [
    Weekday::Mon,
    Weekday::Tue,
    Weekday::Wed,
    Weekday::Thu,
    Weekday::Fri,
    Weekday::Sat,
    Weekday::Sun,
];

// ---------------------------------------------------------------------------
// The generator
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
}

/// Five zones: design §6.4's, a 30-minute DST (Lord Howe) and a zone without DST.
fn zones() -> [(Tz, &'static [&'static str]); 5] {
    [
        (
            chrono_tz::America::Chicago,
            &["2026-03-08", "2026-11-01", "2027-03-14", "2027-11-07"],
        ),
        (
            chrono_tz::Europe::Berlin,
            &["2026-03-29", "2026-10-25", "2027-03-28", "2027-10-31"],
        ),
        (
            chrono_tz::Australia::Lord_Howe,
            &["2026-04-05", "2026-10-04", "2027-04-04", "2027-10-03"],
        ),
        (
            chrono_tz::Pacific::Chatham,
            &["2026-04-05", "2026-09-27", "2027-04-04", "2027-09-26"],
        ),
        (chrono_tz::Asia::Kolkata, &[]),
    ]
}

fn date(s: &str) -> NaiveDate {
    NaiveDate::parse_from_str(s, "%Y-%m-%d").expect("a date")
}

/// A decimal written as the host's one encoder writes it (design §13.6's
/// `decimal_pair`, L8's, not yet in the binary): the shortest round-trip text of the
/// double, split at the point.
fn decimal_pair(x: f64) -> (u128, u128) {
    let text = format!("{x}");
    let (int, frac) = text.split_once('.').unwrap_or((&text, ""));
    let den = 10u128.pow(frac.len() as u32);
    let num = int.parse::<u128>().expect("digits") * den
        + if frac.is_empty() {
            0
        } else {
            frac.parse::<u128>().expect("digits")
        };
    (num, den)
}

fn places(x: f64) -> usize {
    format!("{x}").split_once('.').map_or(0, |(_, f)| f.len())
}

/// A `P(lounge)`: a round decimal, a value at the threshold, or a raw double.
fn gen_weight(r: &mut Rng) -> f64 {
    match r.below(10) {
        0..=2 => r.below(1001) as f64 / 1000.0,
        3..=4 => *r.pick(&[0.0, 1.0, 0.5, 0.49, 0.51, 0.4999999, 0.5000001]),
        _ => loop {
            let x = (r.next() >> 11) as f64 / (1u64 << 53) as f64;
            if places(x) <= 18 {
                break x;
            }
        },
    }
}

/// A clock: mostly a morning, sometimes inside a DST gap or fold, sometimes late.
fn gen_clock(r: &mut Rng) -> NaiveTime {
    let (h, m) = match r.below(10) {
        0..=5 => (6 + r.below(6) as u32, r.below(60) as u32),
        6..=7 => *r.pick(&[(2, 0), (2, 15), (2, 30), (1, 30), (3, 0), (2, 45)]),
        _ => (r.below(24) as u32, r.below(60) as u32),
    };
    NaiveTime::from_hms_opt(h, m, 0).expect("a clock")
}

fn hhmm(t: NaiveTime) -> String {
    t.format("%H:%M").to_string()
}

/// A decimal with at most `p` places from `lo` to `hi` (inclusive), as text.
fn gen_decimal(r: &mut Rng, lo: u64, hi: u64, p: u32) -> String {
    let den = 10u64.pow(p);
    let n = lo * den + r.below((hi - lo) * den + 1);
    let x = n as f64 / den as f64;
    format!("{x}")
}

/// A prior curve: 0 to 5 ranges, strictly increasing starts, gaps and overlaps, an
/// open last range or not.
fn gen_curve(r: &mut Rng) -> Vec<(String, Option<String>, u8)> {
    let n = r.below(6);
    let mut from = if r.chance(70) { 0 } else { r.below(200) };
    let mut out = Vec::new();
    for i in 0..n {
        let len = 25 + r.below(400);
        let to = if i + 1 == n && r.chance(60) {
            None
        } else {
            Some(from + len)
        };
        if to.is_some_and(|t| t > 4800) {
            break;
        }
        let level = r.below(6) as u8;
        out.push((hundredths(from), to.map(hundredths), level));
        let step = match to {
            Some(t) if r.chance(60) => t - from,
            _ => 10 + r.below(500),
        };
        from += step;
        if from > 4700 {
            break;
        }
    }
    out
}

fn hundredths(h: u64) -> String {
    format!("{}", h as f64 / 100.0)
}

/// One window: config, model, wake, day 0 and the plan's documents.
struct Case {
    tz: Tz,
    today: NaiveDate,
    block_min: u32,
    break_min: u32,
    break_after: u32,
    min_last: u32,
    window_hours: String,
    window_cap: NaiveTime,
    budget_ratio: String,
    home_max: u8,
    prior: BTreeMap<String, Vec<(String, Option<String>, u8)>>,
    energy: BTreeMap<String, Vec<u8>>,
    p_config: [f64; 7],
    p_model: [Option<f64>; 7],
    arr_config: [NaiveTime; 7],
    arr_model: [Option<NaiveTime>; 7],
    wake: Option<(u32, u32)>,
    day0: [u32; 6],
    /// `(path, text)`; a generated window has one calendar file of walls.
    docs: Vec<(String, String)>,
    /// The generated calendar's line count; `None` for a corpus plan.
    wall_lines: Option<usize>,
}

fn gen_case(r: &mut Rng, zone: (Tz, &[&str])) -> Case {
    let (tz, transitions) = zone;
    let transition = (!transitions.is_empty() && r.chance(60))
        .then(|| date(transitions[r.below(transitions.len() as u64) as usize]));
    let today = match transition {
        Some(t) => t - Duration::days(r.below(6) as i64),
        None => date("2026-01-01") + Duration::days(r.below(730) as i64),
    };
    let mut block_min = *r.pick(&[25, 30, 45, 50, 60, 90]);
    let mut window_hours = match r.below(3) {
        0 => r
            .pick(&[
                "8", "7.5", "7.33", "7.325", "6.1", "9.975", "10.15", "12.5", "4.2", "0.5",
            ])
            .to_string(),
        _ => gen_decimal(r, 2, 14, 3),
    };
    let mut budget_ratio = match r.below(3) {
        0 => r
            .pick(&[
                "0.75", "0.7", "0.35", "1", "0.9", "0.55", "0.45", "0.3", "0.123", "0.07",
            ])
            .to_string(),
        _ => gen_decimal(r, 0, 1, 3),
    };
    // P27's two sites, where the doubles and the exact pairs part (found by an exhaustive
    // search over 3-place window hours and 3-place ratios, recorded in the README): the
    // window's minutes at a tie `f64` misses, and the budget's floor just below a whole.
    if r.chance(15) {
        match r.below(3) {
            0 => window_hours = r.pick(&["1.025", "4.225", "8.075", "8.325", "16.025"]).to_string(),
            1 => (window_hours, block_min, budget_ratio) = ("8.75".to_string(), 45, "0.6".to_string()),
            _ => (window_hours, block_min, budget_ratio) = ("13.75".to_string(), 45, "0.6".to_string()),
        }
    }
    let mut prior = BTreeMap::new();
    let keys: &[&str] = match r.below(6) {
        0 => &["lounge"],
        1 => &["home"],
        2 => &["aaa", "zzz"],
        3 => &[],
        _ => &["home", "lounge", "out"],
    };
    for k in keys {
        prior.insert(k.to_string(), gen_curve(r));
    }
    let mut energy = BTreeMap::new();
    for k in ["lounge", "home"] {
        if r.chance(50) {
            let curve = (0..12)
                .map(|_| {
                    if r.chance(10) {
                        *r.pick(&[6, 7, 255])
                    } else {
                        r.below(6) as u8
                    }
                })
                .collect();
            energy.insert(k.to_string(), curve);
        }
    }
    let p_config = std::array::from_fn(|_| gen_weight(r));
    let p_model = std::array::from_fn(|_| r.chance(40).then(|| gen_weight(r)));
    let arr_config = std::array::from_fn(|_| gen_clock(r));
    let arr_model = std::array::from_fn(|_| r.chance(40).then(|| gen_clock(r)));
    let wake = r.chance(70).then(|| match r.below(20) {
        0..=2 => (
            r.below(1440) as u32 * 60 + 59,
            1_000_000_000 + r.below(1_000_000_000) as u32,
        ),
        // Some seconds less than whole hours before an arrival: the first slot's hours since
        // wake then round across a bucket or a range key only in whole seconds (site R11).
        3..=12 => {
            let wd = r.below(7) as usize;
            let arrival = arr_model[wd].unwrap_or(arr_config[wd]);
            let back = 3600 * (1 + r.below(4) as i64) - 1 - r.below(59) as i64;
            let sec = (arrival.num_seconds_from_midnight() as i64 - back).rem_euclid(86_400);
            (sec as u32, r.below(1_000_000_000) as u32)
        }
        _ => (
            r.below(86_400) as u32,
            if r.chance(50) { 0 } else { r.below(1_000_000_000) as u32 },
        ),
    });
    let day0 = std::array::from_fn(|_| if r.chance(50) { 0 } else { r.below(241) as u32 });
    let mut calendar = Vec::new();
    for i in 0..r.below(7) {
        let state = *r.pick(&["[ ]", "[ ]", "[ ]", "[ ]", "[>]", "[?]", "[x]", "[~]"]);
        // The first wall of a window that holds a zone transition lies on it, in the night.
        let (start_day, start) = match transition {
            Some(t) if i == 0 => (
                t,
                NaiveTime::from_hms_opt(r.below(5) as u32, 15 * r.below(4) as u32, 0).unwrap(),
            ),
            _ => (today + Duration::days(r.below(10) as i64 - 2), gen_clock(r)),
        };
        let at = if r.chance(30) {
            let end_day = start_day + Duration::days(1 + r.below(3) as i64);
            format!("{}T{}/{}T{}", start_day, hhmm(start), end_day, hhmm(gen_clock(r)))
        } else {
            let end =
                (start + Duration::minutes(15 + r.below(300) as i64)).min(NaiveTime::from_hms_opt(23, 59, 0).unwrap());
            if end <= start {
                continue;
            }
            format!("{}T{}/{}", start_day, hhmm(start), hhmm(end))
        };
        let buffer = match r.below(8) {
            0 => " buffer:30m",
            1 => " buffer:1b",
            2 => " buffer:2h",
            3 => " buffer:90m",
            _ => "",
        };
        calendar.push(format!("- {state} 3 Wall {i} at:{at}{buffer} ^w{i}"));
    }
    Case {
        tz,
        today,
        block_min,
        break_min: *r.pick(&[0, 10, 20]),
        break_after: r.below(4) as u32,
        min_last: *r.pick(&[1, 10, 30, 45, 100]),
        window_hours,
        window_cap: *r.pick(
            &["19:00", "23:59", "12:00", "16:30", "21:15", "02:45"]
                .map(|s| NaiveTime::parse_from_str(s, "%H:%M").unwrap()),
        ),
        budget_ratio,
        home_max: r.below(6) as u8,
        prior,
        energy,
        p_config,
        p_model,
        arr_config,
        arr_model,
        wake,
        day0,
        docs: vec![(
            format!(
                "calendar/{}-W{:02}.md",
                today.iso_week().year(),
                today.iso_week().week()
            ),
            calendar.iter().map(|l| format!("{l}\n")).collect(),
        )],
        wall_lines: Some(calendar.len()),
    }
}

// ---------------------------------------------------------------------------
// The fork's side
// ---------------------------------------------------------------------------

fn fork_config(c: &Case, window_hours: f64, budget_ratio: f64) -> Config {
    let mut cfg = Config::default();
    cfg.tz = c.tz;
    cfg.day.block_min = c.block_min;
    cfg.day.break_min = c.break_min;
    cfg.day.break_after_blocks = c.break_after;
    cfg.day.min_last_block_min = c.min_last;
    cfg.day.window_hours = window_hours;
    cfg.day.window_cap = c.window_cap;
    cfg.day.budget_ratio = budget_ratio;
    cfg.location.home_max_ci = c.home_max;
    cfg.energy.prior = c
        .prior
        .iter()
        .map(|(k, steps)| {
            let steps = steps
                .iter()
                .map(|(f, t, l)| Step {
                    from: f.parse().unwrap(),
                    to: t.as_ref().map(|t| t.parse().unwrap()),
                    level: *l,
                })
                .collect();
            (k.clone(), StepFn(steps))
        })
        .collect();
    let ix = |wd: Weekday| wd.num_days_from_monday() as usize;
    cfg.expected.arrival = PerWeekday::from_fn(|wd| c.arr_config[ix(wd)]);
    cfg.expected.p_lounge = PerWeekday::from_fn(|wd| c.p_config[ix(wd)]);
    cfg
}

/// The model, with `P(lounge)` as generated, or every weekday forced to `force`.
fn fork_model(c: &Case, force: Option<f64>) -> Model {
    let mut m = Model {
        energy: c.energy.clone(),
        ..Model::default()
    };
    let (mut p, mut a) = (WeekdayMap::new(), WeekdayMap::new());
    for (i, wd) in WEEK.iter().enumerate() {
        if let Some(x) = force.or(c.p_model[i]) {
            p.set(*wd, x);
        }
        if let Some(t) = c.arr_model[i] {
            a.set(*wd, Hhmm(t));
        }
    }
    m.p_lounge = p;
    m.expected_arrival = a;
    m
}

/// **Fork `Ctx::walls_on`, copied** (`tm/src/cli/ctx.rs` at this commit): every item
/// not closed whose effective shape is an interval, the start moved back by
/// `buffer:`, on every date from the shifted start's to the end's, unclipped.
fn fork_walls_on(tree: &Tree, tz: Tz, date: NaiveDate) -> Vec<Wall> {
    let mut out = Vec::new();
    for item in tree.iter() {
        if item.state.is_closed() {
            continue;
        }
        let id = Tree::key_of(item);
        let Shape::Interval { start, end } = tree.effective_shape(&id) else {
            continue;
        };
        let start = match item.buffer {
            Some(b) => start - Duration::minutes(i64::from(b.as_minutes())),
            None => start,
        };
        if start.date() > date || end.date() < date {
            continue;
        }
        out.push((
            capacity::local_dt(tz, start.date(), start.time()),
            capacity::local_dt(tz, end.date(), end.time()),
        ));
    }
    out.sort_by_key(|(a, _)| *a);
    out
}

/// **Fork `Planner::walls_by_date`, copied** (`tm-core/src/planner.rs` at this commit):
/// the planner's own lookahead input when `PlanInput` carries no capacities, which is
/// the TUI's replan.  It differs from `Ctx::walls_on` three ways: only `[ ]` and `[>]`
/// items, the buffer taken off the instant, and each date's walls clipped to it.
/// Measured below for gap 111; the kernel follows `Ctx` (L2).
fn planner_walls_by_date(tree: &Tree, tz: Tz, today: NaiveDate, days: u32) -> WallsByDate {
    let mut out = WallsByDate::new();
    for item in tree.iter() {
        if !item.state.is_open() {
            continue;
        }
        let key = Tree::key_of(item);
        let Shape::Interval { start, end } = tree.effective_shape(&key) else {
            continue;
        };
        let buffer = item.buffer.map_or(0, |d| d.as_minutes());
        let s = capacity::local_dt(tz, start.date(), start.time()) - Duration::minutes(i64::from(buffer));
        let e = capacity::local_dt(tz, end.date(), end.time());
        if e <= s {
            continue;
        }
        for i in 0..i64::from(days) {
            let d = today + Duration::days(i);
            let from = capacity::local_dt(tz, d, NaiveTime::MIN);
            let to = capacity::local_dt(tz, d + Duration::days(1), NaiveTime::MIN);
            let (a, b) = (s.max(from), e.min(to));
            if b > a {
                out.entry(d).or_default().push((a, b));
            }
        }
    }
    out
}

/// Fork `Ctx::walls_by_date`; `clip` bounds each date's walls to that date (what
/// gap 85's fix would do), for the measurement only.
fn fork_walls_by_date(tree: &Tree, tz: Tz, today: NaiveDate, days: u32, clip: bool) -> WallsByDate {
    let mut map = WallsByDate::new();
    for i in 0..i64::from(days) {
        let d = today + Duration::days(i);
        let mut walls = fork_walls_on(tree, tz, d);
        if clip {
            let lo = capacity::local_dt(tz, d, NaiveTime::MIN);
            let hi = capacity::local_dt(tz, d + Duration::days(1), NaiveTime::MIN);
            walls = walls
                .into_iter()
                .map(|(a, b)| (a.max(lo), b.min(hi)))
                .filter(|(a, b)| b > a)
                .collect();
        }
        if !walls.is_empty() {
            map.insert(d, walls);
        }
    }
    map
}

/// Day 0's slots: one slot per level holding the host's minutes.
fn today_slots(c: &Case) -> Vec<Slot> {
    let t0 = c.tz.from_utc_datetime(&c.today.and_hms_opt(12, 0, 0).unwrap());
    (0..6)
        .filter(|l| c.day0[*l] > 0)
        .map(|l| Slot {
            start: t0,
            end: t0 + Duration::minutes(c.day0[l] as i64),
            energy: l as u8,
            kind: SlotKind::Block,
        })
        .collect()
}

fn wake_time(c: &Case) -> Option<NaiveTime> {
    c.wake
        .map(|(s, ns)| NaiveTime::from_num_seconds_from_midnight_opt(s, ns).expect("a wake"))
}

// ---------------------------------------------------------------------------
// The kernel's side
// ---------------------------------------------------------------------------

fn pair_json(x: f64) -> Value {
    let (n, d) = decimal_pair(x);
    json!({"num": n.to_string(), "den": d.to_string()})
}

fn nat_pair(text: &str) -> Value {
    let (n, d) = decimal_pair(text.parse().unwrap());
    json!({"num": n as u64, "den": d as u64})
}

/// The request; `model_weights` replaces the model's `pLounge` table when given.
fn kernel_request(c: &Case, tz_wire: &Value, model_weights: Option<[(u128, u128); 7]>) -> Value {
    let mut p_model = serde_json::Map::new();
    let mut a_model = serde_json::Map::new();
    let mut p_config = serde_json::Map::new();
    let mut a_config = serde_json::Map::new();
    for (i, wd) in WEEK.iter().enumerate() {
        let k = weekday_key(*wd).to_string();
        p_config.insert(k.clone(), pair_json(c.p_config[i]));
        a_config.insert(k.clone(), json!(hhmm(c.arr_config[i])));
        match model_weights {
            Some(ws) => {
                p_model.insert(
                    k.clone(),
                    json!({"num": ws[i].0.to_string(), "den": ws[i].1.to_string()}),
                );
            }
            None => {
                if let Some(x) = c.p_model[i] {
                    p_model.insert(k.clone(), pair_json(x));
                }
            }
        }
        if let Some(t) = c.arr_model[i] {
            a_model.insert(k, json!(hhmm(t)));
        }
    }
    let prior: serde_json::Map<String, Value> = c
        .prior
        .iter()
        .map(|(k, steps)| {
            let steps: Vec<Value> = steps
                .iter()
                .map(|(f, t, l)| json!({"from": nat_pair(f), "to": t.as_ref().map(|t| nat_pair(t)), "level": l}))
                .collect();
            (k.clone(), Value::Array(steps))
        })
        .collect();
    let docs: Vec<Value> = c
        .docs
        .iter()
        .filter(|(_, text)| !text.is_empty())
        .map(|(path, text)| json!({"path": path, "lines": text.lines().collect::<Vec<_>>()}))
        .collect();
    json!({
        "docs": docs,
        "now": c.today.to_string(),
        "blockMin": c.block_min,
        "tz": tz_wire,
        "capacity": {
            "pLounge": {"model": p_model, "config": p_config},
            "arrival": {"model": a_model, "config": a_config},
            "wake": c.wake.map(|(s, ns)| json!({"sec": s, "ns": ns})),
            "energy": c.energy,
            "prior": prior,
            "homeMaxCi": c.home_max,
            "day": {"breakMin": c.break_min, "breakAfterBlocks": c.break_after, "minLastBlockMin": c.min_last,
                    "windowHours": nat_pair(&c.window_hours), "windowCap": hhmm(c.window_cap),
                    "budgetRatio": nat_pair(&c.budget_ratio)},
            "priority": {"bins": [{"num": 5, "den": 10}, {"num": 25, "den": 100}, {"num": 1, "den": 10}],
                         "safety": {"num": 13, "den": 10}, "defaultPriority": 3},
            "days": 7,
            "day0": c.day0,
        }
    })
}

/// The kernel's seven days as `(date, units per level)`.
fn kernel_days(req: &Value) -> Vec<(String, [u128; 6])> {
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    let days = resp["ok"]["lookahead"]["days"]
        .as_array()
        .unwrap_or_else(|| panic!("{raw}\n{req}"));
    assert_eq!(resp["ok"]["lookahead"]["den"], json!(CAP_DEN.to_string()));
    days.iter()
        .map(|d| {
            let units = std::array::from_fn(|l| d["numAt"][l].as_str().expect("digits").parse::<u128>().expect("u128"));
            (d["day"].as_str().expect("a date").to_string(), units)
        })
        .collect()
}

fn units(cap: &DayCapacity) -> [u128; 6] {
    cap.minutes_at_level.map(|m| m as u128 * CAP_DEN)
}

/// The weight the kernel reads for a weekday, in units: the model's pair, else the
/// config's.
fn weight_units(c: &Case, i: usize) -> u128 {
    let (n, d) = decimal_pair(c.p_model[i].unwrap_or(c.p_config[i]));
    n * (CAP_DEN / d)
}

/// Site R3 and site R2 on the exact pairs (`Look.windowMinOf`, `Look.budgetOf`).
fn exact_window_and_budget(c: &Case) -> (i64, u32) {
    let (wn, wd) = decimal_pair(c.window_hours.parse().unwrap());
    let (bn, bd) = decimal_pair(c.budget_ratio.parse().unwrap());
    let window = (120 * wn + wd) / (2 * wd);
    let budget = (60 * wn * bn) / (c.block_min.max(1) as u128 * wd * bd);
    (window as i64, budget as u32)
}

fn fork_window_min(cfg: &Config) -> i64 {
    (cfg.day.window_hours * 60.0).round().max(0.0) as i64
}

// ---------------------------------------------------------------------------
// The run
// ---------------------------------------------------------------------------

#[derive(Default)]
struct Tally {
    windows: usize,
    future_days: usize,
    dst_days: usize,
    dst_wall_days: usize,
    multi_day_wall_days: usize,
    walls: usize,
    wakes_with_seconds: usize,
    seconds_matter_days: usize,
    half_weight_days: usize,
    leap_wakes: usize,
    twin_lounge_days: usize,
    mixed_strictly_between: usize,
    p27_windows: usize,
    p27_days_differing: usize,
    gap85_days_differing: usize,
    gap85_minutes: i64,
    gap85_level_minutes: i64,
    gap111_days_differing: usize,
    whole_cut_visible: usize,
    disagreements: Vec<String>,
}

/// A date on which the zone's offset changes.
fn is_transition_day(tz: Tz, d: NaiveDate) -> bool {
    let off = |t: NaiveTime| {
        use chrono::Offset;
        capacity::local_dt(tz, d, t).offset().fix().local_minus_utc()
    };
    off(NaiveTime::MIN) != off(NaiveTime::from_hms_opt(23, 59, 0).unwrap())
}

fn run_case(c: &Case, tz_wire: &Value, t: &mut Tally) {
    let tag = format!("{} {} ({})", c.tz.name(), c.today, t.windows);
    let wh: f64 = c.window_hours.parse().unwrap();
    let br: f64 = c.budget_ratio.parse().unwrap();
    let cfg = fork_config(c, wh, br);
    let files: Vec<(&str, &str)> = c.docs.iter().map(|(p, s)| (p.as_str(), s.as_str())).collect();
    let tree = Tree::from_texts(&files, &cfg);
    if let Some(n) = c.wall_lines {
        assert!(
            tree.problems().is_empty(),
            "{tag}: {:?}\n{:#?}",
            tree.problems(),
            c.docs
        );
        assert_eq!(tree.len(), n, "{tag}: every wall line is an item");
    }
    let walls = fork_walls_by_date(&tree, c.tz, c.today, 7, false);
    let clipped = fork_walls_by_date(&tree, c.tz, c.today, 7, true);
    let planner_walls = planner_walls_by_date(&tree, c.tz, c.today, 7);
    let slots = today_slots(c);

    // P27: the doubles' window minutes and budget against the exact pairs'.
    let (xw, xb) = exact_window_and_budget(c);
    let p27 = fork_window_min(&cfg) != xw || capacity::budget_blocks(&cfg) != xb;
    let cfg_exact = if p27 {
        t.p27_windows += 1;
        let wh2 = xw as f64 / 60.0;
        let br2 = if xw == 0 {
            assert_eq!(xb, 0);
            0.0
        } else {
            (xb as f64 + 0.5) * c.block_min.max(1) as f64 / xw as f64
        };
        let e = fork_config(c, wh2, br2);
        assert_eq!(
            (fork_window_min(&e), capacity::budget_blocks(&e)),
            (xw, xb),
            "{tag}: the corrected doubles"
        );
        e
    } else {
        cfg.clone()
    };

    let wake_of = |m: &Model| m.wake_or_expected(wake_time(c), c.today.weekday(), &cfg);
    let fork = |cfg: &Config, force: Option<f64>, walls: &WallsByDate| {
        let m = fork_model(c, force);
        capacity::lookahead(walls, cfg, &m, &slots, c.today, 7, wake_of(&m))
    };
    // The same runs with the logged wake cut to its minute: where they differ, the
    // wake's seconds are observable (site R11), and the kernel must still agree.
    let fork_minute_wake = |force: f64| {
        let m = fork_model(c, Some(force));
        let wake = wake_of(&m)
            .with_second(0)
            .and_then(|w| w.with_nanosecond(0))
            .expect("a clock");
        capacity::lookahead(&walls, &cfg_exact, &m, &slots, c.today, 7, wake)
    };
    let (m_lounge, m_home) = (fork_minute_wake(1.0), fork_minute_wake(0.0));
    let (f_lounge, f_home, f_real) = (
        fork(&cfg, Some(1.0), &walls),
        fork(&cfg, Some(0.0), &walls),
        fork(&cfg, None, &walls),
    );
    let (e_lounge, e_home, e_real) = (
        fork(&cfg_exact, Some(1.0), &walls),
        fork(&cfg_exact, Some(0.0), &walls),
        fork(&cfg_exact, None, &walls),
    );

    let effective: [f64; 7] = std::array::from_fn(|i| c.p_model[i].unwrap_or(c.p_config[i]));
    let twin: [(u128, u128); 7] = std::array::from_fn(|i| {
        if 2 * weight_units(c, i) >= CAP_DEN {
            (1, 1)
        } else {
            (0, 1)
        }
    });
    let k_lounge = kernel_days(&kernel_request(c, tz_wire, Some([(1, 1); 7])));
    let k_home = kernel_days(&kernel_request(c, tz_wire, Some([(0, 1); 7])));
    let k_twin = kernel_days(&kernel_request(c, tz_wire, Some(twin)));
    let k_real = kernel_days(&kernel_request(c, tz_wire, None));
    for k in [&k_lounge, &k_home, &k_twin, &k_real] {
        assert_eq!(k.len(), 7, "{tag}");
    }

    let day0: [u128; 6] = c.day0.map(|m| m as u128 * CAP_DEN);
    for i in 0..7 {
        let d = c.today + Duration::days(i as i64);
        let wd = d.weekday().num_days_from_monday() as usize;
        for (name, k) in [
            ("lounge", &k_lounge),
            ("home", &k_home),
            ("twin", &k_twin),
            ("mixed", &k_real),
        ] {
            assert_eq!(k[i].0, d.to_string(), "{tag}: {name} day {i}");
        }
        if i == 0 {
            for (name, k) in [
                ("lounge", &k_lounge),
                ("home", &k_home),
                ("twin", &k_twin),
                ("mixed", &k_real),
            ] {
                assert_eq!(k[0].1, day0, "{tag}: {name} day 0 is the host's");
            }
            assert_eq!(units(&f_real[0]), day0, "{tag}: the fork's day 0 is its slots");
            continue;
        }
        t.future_days += 1;
        t.dst_days += usize::from(is_transition_day(c.tz, d));
        t.dst_wall_days += usize::from(is_transition_day(c.tz, d) && walls.contains_key(&d));
        t.multi_day_wall_days += usize::from(walls.get(&d).is_some_and(|ws| {
            ws.iter()
                .any(|(a, b)| a.date_naive() != b.date_naive() || a.date_naive() != d)
        }));
        t.twin_lounge_days += usize::from(effective[wd] >= 0.5);
        t.half_weight_days += usize::from(effective[wd] == 0.5);
        t.seconds_matter_days += usize::from(m_lounge[i] != e_lounge[i] || m_home[i] != e_home[i]);

        // Against the fork: the exact-rounding run always; the fork's own doubles unless P27.
        let checks = [
            ("lounge", &k_lounge, &e_lounge, &f_lounge),
            ("home", &k_home, &e_home, &f_home),
            ("twin (T13)", &k_twin, &e_real, &f_real),
        ];
        let mut rounded_apart = false;
        for (name, k, exact, own) in checks {
            if k[i].1 != units(&exact[i]) {
                t.disagreements.push(format!(
                    "{tag}: {name} {d}: kernel {:?} fork {:?}",
                    k[i].1, exact[i].minutes_at_level
                ));
            }
            if units(&own[i]) != units(&exact[i]) {
                assert!(p27, "{tag}: the corrected config changed a day outside P27");
                rounded_apart = true;
            }
        }
        t.p27_days_differing += usize::from(rounded_apart);

        // The mixture, from the fork's forced minutes.
        let w = weight_units(c, wd);
        let mixed: [u128; 6] = std::array::from_fn(|l| {
            w * e_lounge[i].minutes_at_level[l] as u128 + (CAP_DEN - w) * e_home[i].minutes_at_level[l] as u128
        });
        if k_real[i].1 != mixed {
            t.disagreements.push(format!(
                "{tag}: mixed {d} at w = {w}: kernel {:?} expected {mixed:?}",
                k_real[i].1
            ));
        }
        for l in 0..6 {
            let (a, b) = (k_lounge[i].1[l], k_home[i].1[l]);
            assert!(
                a.min(b) <= k_real[i].1[l] && k_real[i].1[l] <= a.max(b),
                "{tag}: {d} level {l} between the locations"
            );
        }
        t.mixed_strictly_between += usize::from(k_lounge[i].1 != k_home[i].1 && 0 < w && w < CAP_DEN);

        // Gap 104: on a day the budget does not bind, the profile holds the whole cut.
        for (force, prof) in [(1.0, &e_lounge[i]), (0.0, &e_home[i])] {
            let m = fork_model(c, Some(force));
            let arrival = capacity::local_dt(c.tz, d, m.expected_arrival_on(d.weekday(), &cfg_exact));
            let ws: &[Wall] = walls.get(&d).map_or(&[], |v| v.as_slice());
            let (end, _) = capacity::window_and_budget(arrival, ws, &cfg_exact);
            let cut = capacity::cut_slots(arrival, end, ws, &cfg_exact);
            t.whole_cut_visible += usize::from(cut.slot_minutes() > 0 && prof.total() == cut.slot_minutes());
        }

        // Gap 85: what clipping each date's walls to that date would change.
        let (c_lounge, c_home) = (
            fork(&cfg_exact, Some(1.0), &clipped),
            fork(&cfg_exact, Some(0.0), &clipped),
        );
        let diff = |a: &DayCapacity, b: &DayCapacity| (a.total() as i64 - b.total() as i64).abs();
        let moved = |a: &DayCapacity, b: &DayCapacity| {
            (0..6)
                .map(|l| (a.minutes_at_level[l] as i64 - b.minutes_at_level[l] as i64).abs())
                .sum::<i64>()
        };
        if c_lounge[i] != e_lounge[i] || c_home[i] != e_home[i] {
            t.gap85_days_differing += 1;
        }
        t.gap85_minutes += diff(&e_lounge[i], &c_lounge[i]) + diff(&e_home[i], &c_home[i]);
        t.gap85_level_minutes += moved(&e_lounge[i], &c_lounge[i]) + moved(&e_home[i], &c_home[i]);

        // Gap 111: the TUI's replan reads the walls the planner's way.
        let (p_lounge, p_home) = (
            fork(&cfg_exact, Some(1.0), &planner_walls),
            fork(&cfg_exact, Some(0.0), &planner_walls),
        );
        t.gap111_days_differing += usize::from(p_lounge[i] != e_lounge[i] || p_home[i] != e_home[i]);
    }
    t.walls += tree
        .iter()
        .filter(|it| matches!(tree.effective_shape(&Tree::key_of(it)), Shape::Interval { .. }))
        .count();
    t.wakes_with_seconds += usize::from(c.wake.is_some_and(|(s, ns)| s % 60 != 0 || ns != 0));
    t.leap_wakes += usize::from(c.wake.is_some_and(|(_, ns)| ns >= 1_000_000_000));
    t.windows += 1;
}

/// **T13 and the mixture**, over 64 generated windows (384 future days) with a fixed
/// seed, then over the corpus's four whole plans at seven dates each (168 future days).
/// Every disagreement is listed; none is allowed.
#[test]
fn the_lookahead_is_the_forks_at_each_location_and_mixes_exactly() {
    let tables: Vec<Value> = zones().iter().map(|(tz, _)| tz_table::probe(*tz).to_wire()).collect();
    let mut r = Rng(SEED);
    let mut t = Tally::default();
    for w in 0..WINDOWS {
        let z = w % zones().len();
        let case = gen_case(&mut r, zones()[z]);
        run_case(&case, &tables[z], &mut t);
    }
    report(&t, "T13, generated");
    assert!(t.future_days >= 256);
    assert!(t.dst_wall_days > 0 && t.multi_day_wall_days > 0 && t.leap_wakes > 0 && t.p27_days_differing > 0);
    assert!(t.seconds_matter_days > 0 && t.half_weight_days > 0 && t.gap85_days_differing > 0);
    assert!(t.disagreements.is_empty(), "{} disagreements", t.disagreements.len());

    // The corpus: every whole plan that loads, with `kernel/corpus/model.json`, from the
    // corpus day and the days after it, and one day in the Midterm's week.
    let mut t = Tally::default();
    let mut r = Rng(SEED ^ 0xc0);
    let mut wires: BTreeMap<String, Value> = BTreeMap::new();
    for plan in CORPUS_PLANS {
        for (k, now) in [
            "2026-09-06",
            "2026-09-07",
            "2026-09-08",
            "2026-09-09",
            "2026-09-11",
            "2026-09-12",
            "2026-10-16",
        ]
        .iter()
        .enumerate()
        {
            let case = corpus_case(plan, date(now), k, &mut r);
            let wire = wires
                .entry(case.tz.name().to_string())
                .or_insert_with(|| tz_table::probe(case.tz).to_wire());
            run_case(&case, wire, &mut t);
        }
    }
    report(&t, "T13, corpus");
    assert!(t.future_days >= 168);
    assert!(t.disagreements.is_empty(), "{} disagreements", t.disagreements.len());
}

/// The four whole plans that load (check 6's `4/5`; `plan-conflicts` exists to be refused).
const CORPUS_PLANS: [&str; 4] = ["plan-basic", "plan-home-day", "plan-travel-day", "plan-recur"];

/// A corpus plan as a window: its `config.toml`, the corpus `model.json`, every `.md`
/// file, a wake at 06:05:40 on odd windows (none on even ones), and a generated day 0.
fn corpus_case(plan: &str, today: NaiveDate, k: usize, r: &mut Rng) -> Case {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../kernel/corpus")
        .join(plan);
    let cfg =
        Config::parse(&std::fs::read_to_string(root.join("config.toml")).expect("config.toml")).expect("the config");
    let model =
        Model::from_json(&std::fs::read_to_string(root.join("../model.json")).expect("model.json")).expect("the model");
    let mut docs = Vec::new();
    let mut dirs = vec![root.clone()];
    while let Some(dir) = dirs.pop() {
        for e in std::fs::read_dir(&dir).expect("a plan directory") {
            let path = e.expect("an entry").path();
            if path.is_dir() {
                dirs.push(path);
            } else if path.extension().is_some_and(|x| x == "md") {
                let rel = path.strip_prefix(&root).unwrap().to_string_lossy().replace('\\', "/");
                docs.push((rel, std::fs::read_to_string(&path).expect("a document")));
            }
        }
    }
    docs.sort();
    let text = |x: f64| format!("{x}");
    Case {
        tz: cfg.tz,
        today,
        block_min: cfg.day.block_min,
        break_min: cfg.day.break_min,
        break_after: cfg.day.break_after_blocks,
        min_last: cfg.day.min_last_block_min,
        window_hours: text(cfg.day.window_hours),
        window_cap: cfg.day.window_cap,
        budget_ratio: text(cfg.day.budget_ratio),
        home_max: cfg.location.home_max_ci,
        prior: cfg
            .energy
            .prior
            .iter()
            .map(|(key, f)| {
                (
                    key.clone(),
                    f.0.iter().map(|s| (text(s.from), s.to.map(text), s.level)).collect(),
                )
            })
            .collect(),
        energy: model.energy.clone(),
        p_config: WEEK.map(|wd| *cfg.expected.p_lounge.get(wd)),
        p_model: WEEK.map(|wd| model.p_lounge.get(wd).copied()),
        arr_config: WEEK.map(|wd| *cfg.expected.arrival.get(wd)),
        arr_model: WEEK.map(|wd| model.expected_arrival.get(wd).map(|h| h.0)),
        wake: (k % 2 == 1).then_some((6 * 3600 + 5 * 60 + 40, 0)),
        day0: std::array::from_fn(|_| if r.chance(50) { 0 } else { r.below(181) as u32 }),
        docs,
        wall_lines: None,
    }
}

fn report(t: &Tally, what: &str) {
    println!(
        "{what}: {} windows, {} future days ({} on a zone transition, {} of them with walls; {} with a wall across a date boundary), {} interval items, \
         {} wakes with seconds ({} leap), observable on {} days; twin at the lounge on {} days ({} at exactly 0.5); mixed strictly between on {} days; \
         P27: {} windows, {} fork days differ from the exact rounding; gap 85: {} days would change, {} minutes of daily totals, {} level-minutes; \
         gap 104: the whole cut visible on {} location-days; gap 111: the planner's walls change {} days; disagreements: {}",
        t.windows, t.future_days, t.dst_days, t.dst_wall_days, t.multi_day_wall_days, t.walls, t.wakes_with_seconds, t.leap_wakes,
        t.seconds_matter_days, t.twin_lounge_days, t.half_weight_days, t.mixed_strictly_between, t.p27_windows, t.p27_days_differing, t.gap85_days_differing,
        t.gap85_minutes, t.gap85_level_minutes, t.whole_cut_visible, t.gap111_days_differing, t.disagreements.len()
    );
    for d in &t.disagreements {
        println!("  {d}");
    }
}

/// **P26 and P30, measured where the fork answers.**  Each edit of one generated
/// window is a value the fork point accepts and computes a lookahead from, and the
/// kernel refuses by name (L6's refusals, recorded before this run): a weight above
/// one, a weight of 19 places, a prior key with a denominator of `10^7`, a learned
/// curve of 11 entries, `home_max_ci = 6`, a 25-hour window, and 3,661 days.
#[test]
fn the_recorded_exceptions_are_refused_where_the_fork_answers() {
    let (tz, transitions) = zones()[0];
    let wire = tz_table::probe(tz).to_wire();
    let mut base = gen_case(&mut Rng(SEED), (tz, transitions));
    base.docs.clear();
    type Edit = fn(&mut Case);
    let edits: [(&str, Edit, &str); 6] = [
        (
            "P26 weight above one",
            |c| c.p_config[5] = 1.2,
            "weightAboveOne pLounge.config.Sat",
        ),
        (
            "P26 a weight of 19 places",
            |c| c.p_config[0] = 1e-19,
            "weightPrecision pLounge.config.Mon",
        ),
        (
            "P26 a prior key over 10^6",
            |c| {
                c.prior = BTreeMap::from([(
                    "lounge".to_string(),
                    vec![("0.0000001".to_string(), Some("1".to_string()), 4)],
                )])
            },
            "badStep prior.lounge",
        ),
        (
            "P26 a learned curve of 11",
            |c| c.energy = BTreeMap::from([("lounge".to_string(), vec![4; 11])]),
            "badCurve energy.lounge",
        ),
        ("P26 home_max_ci 6", |c| c.home_max = 6, "badCap homeMaxCi"),
        (
            "P26 a 25-hour window",
            |c| c.window_hours = "25".to_string(),
            "badDay windowHours",
        ),
    ];
    let refusal = |req: &Value| tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    for (what, edit, name) in edits {
        let mut c = Case {
            docs: vec![],
            prior: base.prior.clone(),
            energy: base.energy.clone(),
            window_hours: base.window_hours.clone(),
            budget_ratio: base.budget_ratio.clone(),
            ..base
        };
        edit(&mut c);
        assert_eq!(
            refusal(&kernel_request(&c, &wire, None)),
            format!(r#"{{"err":{{"capacity":"{name}"}}}}"#),
            "{what}"
        );
        let cfg = fork_config(&c, c.window_hours.parse().unwrap(), c.budget_ratio.parse().unwrap());
        let m = fork_model(&c, None);
        let wake = m.wake_or_expected(wake_time(&c), c.today.weekday(), &cfg);
        let caps = capacity::lookahead(&WallsByDate::new(), &cfg, &m, &today_slots(&c), c.today, 7, wake);
        assert_eq!(caps.len(), 7, "{what}: the fork answers");
    }
    // P30: 3,661 days.
    let mut req = kernel_request(&base, &wire, None);
    req["capacity"]["days"] = json!(3661);
    assert_eq!(refusal(&req), r#"{"err":{"capacity":"lookaheadTooLong"}}"#);
    let cfg = fork_config(
        &base,
        base.window_hours.parse().unwrap(),
        base.budget_ratio.parse().unwrap(),
    );
    let m = fork_model(&base, None);
    let wake = m.wake_or_expected(wake_time(&base), base.today.weekday(), &cfg);
    let caps = capacity::lookahead(
        &WallsByDate::new(),
        &cfg,
        &m,
        &today_slots(&base),
        base.today,
        3661,
        wake,
    );
    assert_eq!(caps.len(), 3661, "P30: the fork runs to the due date");
}

/// **P27, measured exhaustively on a grid** (site R3 reopened; site R2 on the exact
/// pairs).  The fork reads `window_hours` and `budget_ratio` as doubles from their
/// decimal text; the kernel reads the same text as exact pairs.  Over every window of
/// 0.000 to 24.000 hours in steps of 0.001, `(wh × 60).round()` differs from the
/// half-up minutes at exactly 9 values, each a tie the double lies below.  Over every
/// window of 2.00 to 14.00 hours in steps of 0.01, six block lengths and every ratio
/// 0.000 to 1.000, `floor(wh × 60 / block_min × ratio)` differs from the exact floor
/// at exactly 2 of 7,213,206 combinations.  The generated run above takes its P27
/// windows from these.
#[test]
fn p27_is_two_integers_at_rare_decimals() {
    let mut windows = Vec::new();
    for n in 0..=24_000u128 {
        let text = format!("{}.{:03}", n / 1000, n % 1000);
        let double = (text.parse::<f64>().unwrap() * 60.0).round().max(0.0) as u128;
        let exact = (120 * n + 1000) / 2000;
        if double != exact {
            windows.push((text, exact, double));
        }
    }
    let texts: Vec<&str> = windows.iter().map(|w| w.0.as_str()).collect();
    assert_eq!(
        texts,
        ["1.025", "4.225", "8.075", "8.325", "16.025", "16.275", "16.525", "16.775", "17.025"],
        "{windows:?}"
    );
    assert!(
        windows.iter().all(|(_, exact, double)| *exact == double + 1),
        "the double rounds a tie down"
    );
    let mut budgets = Vec::new();
    let mut combos = 0u64;
    for wn in 200..=1400u128 {
        let wh: f64 = format!("{}.{:02}", wn / 100, wn % 100).parse().unwrap();
        for bm in [25u128, 30, 45, 50, 60, 90] {
            for rn in 0..=1000u128 {
                combos += 1;
                let ratio: f64 = format!("{}.{:03}", rn / 1000, rn % 1000).parse().unwrap();
                let double = (wh * 60.0 / bm as f64 * ratio).floor().max(0.0) as u128;
                let exact = (wn * 60 * rn) / (bm * 100 * 1000);
                if double != exact {
                    budgets.push((wn, bm, rn, exact, double));
                }
            }
        }
    }
    assert_eq!(combos, 7_213_206);
    assert_eq!(budgets, [(875, 45, 600, 7, 6), (1375, 45, 600, 11, 10)]);
}

// ---------------------------------------------------------------------------
// Stage 5 D10 L8: the priorities on the twin days (design §13.7)
// ---------------------------------------------------------------------------
//
// The kernel's `lookahead.grants` (Boundary.lean's `grantJson` over `Look.priorities`)
// against fork `priority::compute` over the fork's own lookahead, on the threshold
// twin's days (P1 is then no difference), with generated candidates.  The fork's
// candidates carry the kernel's R1 need (`ceil(remaining × 1.3)`, P3 corrected the way
// L7 corrects P27); a second fork run with its own `round` measures P3's reach.  What
// may still differ is recorded: P2 (need 0 against no capacity: HOT in the kernel, the
// lowest bin in the fork) and P7 (the bin's need: the kernel compares the exact
// `remaining × 1.3`, the fork `need_min`).  Each candidate's answer is checked three
// ways: the kernel equals the rule applied at the exact utilisation, the fork equals
// the same rule applied at its own utilisation (so the harness's rule is the fork's),
// and where the two utilisations classify apart the difference is P2 or P7 by name.

use tm_core::model::{Dur, Id, Period, Rate};
use tm_core::priority::{self, Candidate, Prio};

/// One generated candidate: fork `Candidate`'s §7 inputs.
struct GenCand {
    id: String,
    ci: u8,
    root_prio: Option<u8>,
    remaining: u32,
    due: Option<(NaiveDate, NaiveTime)>,
    window: bool,
    wall: bool,
    optional: bool,
    overdue: bool,
    mandatory: bool,
    hot: bool,
    yesterday: Option<u8>,
    /// A `min:` floor (stage 5 D10 L8 host half, gap 79): minutes owed this period, a
    /// multiple of 10 so the fork's `round(left × 1.3)` is the kernel's ceiling (P3
    /// corrected, as for the need), and the period.
    floor: Option<(u32, Period)>,
}

/// Whether a generated candidate enters the EDF pass (gap 80's rule).
fn enters(g: &GenCand) -> bool {
    !g.wall && !g.optional && !g.window && g.due.is_some()
}

/// Four to twelve candidates: walls, optionals, window instances, undated ones and
/// plain dated ones, due from two days before today to the lookahead's last day.  A
/// date's candidates are due at 00:00, 00:01, … in request order, so the fork's
/// `(effective_due, own_order, index)` order is the request order (P12 does not bite).
fn gen_cands(r: &mut Rng, today: NaiveDate) -> Vec<GenCand> {
    let n = 4 + r.below(9) as usize;
    (0..n)
        .map(|i| {
            let kind = r.below(100);
            let dated = kind < 85;
            let due_day = today + Duration::days(r.below(9) as i64 - 2);
            let remaining = match r.below(20) {
                0 => 0,
                1 | 2 => 1 + r.below(3000) as u32,
                _ => 1 + r.below(150) as u32,
            };
            let root_prio = if r.chance(50) { Some(1 + r.below(4) as u8) } else { None };
            let yesterday = if r.chance(30) { Some(r.below(8) as u8) } else { None };
            let floor = r.chance(30).then(|| {
                (10 * (r.below(61) as u32), *r.pick(&[Period::Day, Period::Week, Period::Month]))
            });
            GenCand {
                id: format!("c{i}"),
                ci: r.below(6) as u8,
                root_prio,
                remaining,
                due: dated.then(|| (due_day, NaiveTime::from_hms_opt(0, i as u32, 0).unwrap())),
                window: (20..30).contains(&kind),
                wall: kind < 10,
                optional: (10..20).contains(&kind),
                overdue: r.chance(10),
                mandatory: r.chance(5),
                hot: r.chance(5),
                yesterday,
                floor,
            }
        })
        .collect()
}

/// The fork's candidates; `own_round` keeps `Candidate::new`'s `round(remaining ×
/// safety)`, else the need is the kernel's ceiling.
fn fork_cands(cs: &[GenCand], cfg: &Config, tz: Tz, today: NaiveDate, own_round: bool) -> Vec<Candidate> {
    let t0 = capacity::local_dt(tz, today, NaiveTime::MIN);
    cs.iter()
        .enumerate()
        .map(|(i, g)| {
            let k = g.root_prio.unwrap_or(cfg.priority.default_priority);
            let mut c = Candidate::new(Id::new(g.id.clone()), g.ci, k, g.remaining, cfg);
            if !own_round {
                c.need_min = ((u64::from(g.remaining) * 13 + 9) / 10) as u32;
            }
            c.effective_due = g.due.map(|(d, t)| capacity::local_dt(tz, d, t));
            c.window = g.window.then_some((t0, t0));
            c.is_wall = g.wall;
            c.is_optional = g.optional;
            c.overdue = g.overdue;
            c.mandatory = g.mandatory;
            c.hot = g.hot;
            c.own_order = (0, i);
            c.root_order = (0, i);
            c.floor = g.floor.map(|(l, per)| Rate { amount: Dur::from_minutes(l), per });
            c
        })
        .collect()
}

/// The kernel's `candidates` object; a floor's `until` is fork `period_range`'s last date.
fn cands_json(cs: &[GenCand], hysteresis: bool, today: NaiveDate) -> Value {
    let items: Vec<Value> = cs
        .iter()
        .map(|g| {
            json!({"id": g.id, "ci": g.ci, "rootPrio": g.root_prio, "remaining": g.remaining,
                   "due": g.due.map(|(d, _)| d.to_string()), "window": g.window, "wall": g.wall,
                   "optional": g.optional, "overdue": g.overdue, "mandatory": g.mandatory, "hot": g.hot,
                   "yesterday": g.yesterday,
                   "floor": g.floor.map(|(l, per)| json!({"left": l, "until": priority::period_range(per, today).1.to_string()}))})
        })
        .collect();
    json!({"hysteresis": hysteresis, "items": items})
}

/// §7.2 and §7.4 over a fork `Prio`'s reservation numbers, with the pass's HOT and
/// bin given: the grant the kernel emits for that reading.
fn rule_json(g: &GenCand, fp: &Prio, hysteresis: bool, hot: bool, bin: Option<u8>) -> Value {
    let units = |m: u128| (m * CAP_DEN).to_string();
    if g.wall {
        return json!({"id": g.id, "class": "wall", "k": fp.k, "p": null, "rawP": null, "need": 0, "until": null,
                      "avail": "0", "allocation": "0", "shortfall": "0", "bin": null});
    }
    let entered = fp.until.is_some();
    let (need, avail) = (u128::from(fp.need_min), u128::from(fp.avail_min));
    let shortfall = if entered && hot { need.saturating_sub(avail) } else { 0 };
    let (class, raw) = if g.optional {
        ("optional", 5)
    } else if g.overdue {
        ("overdue", 0)
    } else if g.mandatory {
        ("mandatory", 0)
    } else if g.hot {
        ("hotflag", 0)
    } else if entered && hot {
        (if shortfall > 0 { "impossible" } else { "hot" }, 0)
    } else if entered {
        (if enters(g) { "dated" } else { "floor" }, (fp.k + bin.expect("a bin")).min(7))
    } else {
        ("rank", (fp.k + 2).min(7))
    };
    let p = match (class, g.yesterday) {
        ("optional", _) => raw,
        (_, Some(y)) if hysteresis && raw != 0 && raw + 1 < y => y - 1,
        _ => raw,
    };
    json!({"id": g.id, "class": class, "k": fp.k, "p": p, "rawP": raw, "need": need,
           "until": fp.until.map(|d| d.to_string()), "avail": units(avail),
           "allocation": units(u128::from(fp.allocation_min)), "shortfall": units(shortfall),
           "bin": if entered && !hot { bin } else { None }})
}

/// The fork's reading of the pass: `u = need_min / avail_min` as a double.
fn fork_pass(fp: &Prio, cfg: &Config) -> (bool, Option<u8>) {
    let u = priority::utilization(fp.need_min, fp.avail_min);
    let bin = priority::bin_of(u, &cfg.priority.bins);
    (bin.is_none(), bin.or(Some(0)))
}

/// The kernel's reading (`Look.binAt`, `Look.floorBin`): `remaining × 13/10` (a floor's
/// `left × 13/10`) against `avail`, exactly, no capacity HOT at any need (gap 25).
fn exact_pass(g: &GenCand, fp: &Prio) -> (bool, Option<u8>) {
    let owed = match g.floor {
        Some((left, _)) if !enters(g) => left,
        _ => g.remaining,
    };
    let (rem, a) = (u128::from(owed), u128::from(fp.avail_min));
    if a == 0 || 13 * rem >= 10 * a {
        return (true, Some(0));
    }
    let edges = [(1u128, 2u128), (1, 4), (1, 10)];
    let ix = edges.iter().position(|(p, q)| 13 * rem * q >= 10 * a * p).unwrap_or(3);
    (false, Some(ix as u8))
}

#[derive(Default)]
struct PrioTally {
    windows: usize,
    candidates: usize,
    entered: usize,
    walls: usize,
    optionals: usize,
    windowed: usize,
    undated: usize,
    impossible: usize,
    hot: usize,
    dated: usize,
    floors: usize,
    floor_answers: usize,
    floor_class: usize,
    held: usize,
    p2: usize,
    p7: usize,
    p3_reach: usize,
    p1_changes: usize,
    disagreements: Vec<String>,
}

fn run_priorities(c: &Case, tz_wire: &Value, cs: &[GenCand], hysteresis: bool, t: &mut PrioTally) {
    let tag = format!("{} {} ({})", c.tz.name(), c.today, t.windows);
    let (xw, xb) = exact_window_and_budget(c);
    let wh = xw as f64 / 60.0;
    let br = if xw == 0 { 0.0 } else { (xb as f64 + 0.5) * c.block_min.max(1) as f64 / xw as f64 };
    let mut cfg = fork_config(c, wh, br);
    assert_eq!((fork_window_min(&cfg), capacity::budget_blocks(&cfg)), (xw, xb), "{tag}: the exact doubles");
    cfg.priority.hysteresis = hysteresis;
    let files: Vec<(&str, &str)> = c.docs.iter().map(|(p, s)| (p.as_str(), s.as_str())).collect();
    let tree = Tree::from_texts(&files, &cfg);
    let walls = fork_walls_by_date(&tree, c.tz, c.today, 7, false);
    let m = fork_model(c, None);
    let wake = m.wake_or_expected(wake_time(c), c.today.weekday(), &cfg);
    let caps = capacity::lookahead(&walls, &cfg, &m, &today_slots(c), c.today, 7, wake);

    let yesterday: BTreeMap<Id, u8> =
        cs.iter().filter_map(|g| g.yesterday.map(|y| (Id::new(g.id.clone()), y))).collect();
    let fork = priority::compute(&fork_cands(cs, &cfg, c.tz, c.today, false), &caps, &yesterday, &cfg, c.today);
    let fork_own = priority::compute(&fork_cands(cs, &cfg, c.tz, c.today, true), &caps, &yesterday, &cfg, c.today);

    let twin: [(u128, u128); 7] =
        std::array::from_fn(|i| if 2 * weight_units(c, i) >= CAP_DEN { (1, 1) } else { (0, 1) });
    let grants_of = |weights: Option<[(u128, u128); 7]>| -> Vec<Value> {
        let mut req = kernel_request(c, tz_wire, weights);
        req["capacity"]["candidates"] = cands_json(cs, hysteresis, c.today);
        let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
        let resp: Value = serde_json::from_str(&raw).expect("json");
        resp["ok"]["lookahead"]["grants"].as_array().unwrap_or_else(|| panic!("{tag}: {raw}")).clone()
    };
    let k_twin = grants_of(Some(twin));
    let k_real = grants_of(None);
    assert_eq!(k_twin.len(), cs.len(), "{tag}");

    for (i, g) in cs.iter().enumerate() {
        let fp = &fork[i];
        let (fh, fb) = fork_pass(fp, &cfg);
        let (xh, xb) = exact_pass(g, fp);
        let as_fork = rule_json(g, fp, hysteresis, fh, fb);
        let as_kernel = rule_json(g, fp, hysteresis, xh, xb);
        let fork_seen = json!({"id": g.id, "class": serde_json::to_value(fp.class).unwrap(), "k": fp.k,
            "p": if g.wall { Value::Null } else { json!(fp.p) }, "rawP": if g.wall { Value::Null } else { json!(fp.raw_p) },
            "need": fp.need_min, "until": fp.until.map(|d| d.to_string()),
            "avail": (u128::from(fp.avail_min) * CAP_DEN).to_string(),
            "allocation": (u128::from(fp.allocation_min) * CAP_DEN).to_string(),
            "shortfall": (u128::from(fp.shortfall_min) * CAP_DEN).to_string(), "bin": fp.bin});
        if fork_seen != as_fork {
            t.disagreements.push(format!("{tag}: the harness's rule is not the fork's for {}: {fork_seen} vs {as_fork}", g.id));
        }
        if k_twin[i] != as_kernel {
            t.disagreements.push(format!("{tag}: kernel {} vs the rule at the exact utilisation {as_kernel}", k_twin[i]));
        }
        if as_fork != as_kernel {
            if fp.until.is_some() && fp.need_min == 0 && fp.avail_min == 0 {
                t.p2 += 1;
            } else if fp.until.is_some() && (fh, fb) != (xh, xb) {
                t.p7 += 1;
            } else {
                t.disagreements.push(format!("{tag}: unexplained {} kernel {as_kernel} fork {as_fork}", g.id));
            }
        }
        let fo = &fork_own[i];
        t.p3_reach += usize::from(
            (fo.p, fo.class, fo.avail_min, fo.allocation_min, fo.shortfall_min) != (fp.p, fp.class, fp.avail_min, fp.allocation_min, fp.shortfall_min),
        );
        t.p1_changes += usize::from(k_real[i]["p"] != k_twin[i]["p"]);
        t.candidates += 1;
        t.entered += usize::from(fp.until.is_some());
        t.walls += usize::from(g.wall);
        t.optionals += usize::from(g.optional && !g.wall);
        t.windowed += usize::from(g.window && !g.wall && !g.optional);
        t.undated += usize::from(g.due.is_none());
        t.impossible += usize::from(k_twin[i]["class"] == "impossible");
        t.dated += usize::from(k_twin[i]["class"] == "dated");
        t.floors += usize::from(g.floor.is_some());
        t.floor_answers += usize::from(g.floor.is_some() && !g.wall && !enters(g));
        t.floor_class += usize::from(k_twin[i]["class"] == "floor");
        t.hot += usize::from(k_twin[i]["class"] == "hot");
        t.held += usize::from(k_twin[i]["p"] != k_twin[i]["rawP"]);
    }
    t.windows += 1;
}

/// One plain candidate of 9 minutes at level 0, due today at midnight.
fn one_like(today: NaiveDate) -> GenCand {
    GenCand {
        id: "p7".into(),
        ci: 0,
        root_prio: None,
        remaining: 9,
        due: Some((today, NaiveTime::MIN)),
        window: false,
        wall: false,
        optional: false,
        overdue: false,
        mandatory: false,
        hot: false,
        yesterday: None,
        floor: None,
    }
}

/// **§13.7's second check: the twin's priorities are the fork's** (gaps 80 and 107),
/// over 64 generated windows with four to twelve candidates each, modulo P2 and P7 by
/// name and with P3 corrected; P3's reach and the mixture's effect on `p` (P1) are
/// measured.  Every disagreement is listed; none is allowed.
#[test]
fn the_twin_priorities_are_the_forks_modulo_p2_p3_p7() {
    let tables: Vec<Value> = zones().iter().map(|(tz, _)| tz_table::probe(*tz).to_wire()).collect();
    let mut r = Rng(SEED ^ 0x9e1_0a8);
    let mut t = PrioTally::default();
    for w in 0..WINDOWS {
        let z = w % zones().len();
        let case = gen_case(&mut r, zones()[z]);
        let cs = gen_cands(&mut r, case.today);
        let hysteresis = r.chance(70);
        run_priorities(&case, &tables[z], &cs, hysteresis, &mut t);
    }
    println!(
        "priorities on the twin: {} windows, {} candidates ({} entered the pass; {} walls, {} optionals, {} window instances, {} undated), \
         {} impossible, {} hot, {} dated, {} held by hysteresis; {} floors, {} answered at their floor ({} in the floor class); P2 on {}, P7 on {}; P3 changes {} fork answers; the mixture changes p on {}; disagreements: {}",
        t.windows, t.candidates, t.entered, t.walls, t.optionals, t.windowed, t.undated, t.impossible, t.hot, t.dated, t.held,
        t.floors, t.floor_answers, t.floor_class, t.p2, t.p7,
        t.p3_reach, t.p1_changes, t.disagreements.len()
    );
    for d in &t.disagreements {
        println!("  {d}");
    }
    // P7 targeted, once per zone: day 0 holds 12 minutes at level 0 and one candidate of 9
    // minutes is due today.  The fork's need is `ceil(11.7) = 12` against 12 available, `u = 1`,
    // HOT; the kernel's exact `11.7 / 12` is the `+0` bin, `p = k`.
    for (z, zone) in zones().iter().enumerate() {
        let mut case = gen_case(&mut r, *zone);
        case.day0 = [12, 0, 0, 0, 0, 0];
        let one = one_like(case.today);
        let before = t.p7;
        run_priorities(&case, &tables[z], &[one], true, &mut t);
        assert_eq!(t.p7, before + 1, "P7 is reached in {}", zone.0.name());
        // The tie, where both readings agree: 10 minutes need 13, against 13 available, `u = 1`
        // exactly, HOT in both (the kernel's `u ≥ 1` includes the edge, as the fork's does).
        case.day0 = [13, 0, 0, 0, 0, 0];
        let tie = GenCand { remaining: 10, ..one_like(case.today) };
        let hot_before = t.hot;
        run_priorities(&case, &tables[z], &[tie], true, &mut t);
        assert_eq!((t.p7, t.hot), (before + 1, hot_before + 1), "the tie is HOT in {}", zone.0.name());
    }
    println!("after the targeted P7 windows: P7 on {}, disagreements: {}", t.p7, t.disagreements.len());
    assert!(t.candidates >= 256 && t.entered > 0 && t.impossible > 0 && t.dated > 0 && t.held > 0 && t.walls > 0);
    assert!(t.floor_answers > 0 && t.floor_class > 0, "the floor pass is reached");
    assert!(t.p2 > 0 && t.p3_reach > 0, "the recorded exceptions are reached");
    assert!(t.disagreements.is_empty(), "{} disagreements", t.disagreements.len());
}
