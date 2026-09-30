//! The §12.4 week review over the synthetic 14-day fixture, read for
//! 2026-W36 (2026-08-31 … 2026-09-06) — the one ISO week the fixture covers
//! from Monday to Sunday.
//!
//! From `tests/review_common/mod.rs`'s table, that week is five standard
//! days (four 60-minute blocks at ci 5/4/3/2, two 20-minute breaks and a
//! 30-minute lunch, load `(300+240+180+120)/5 = 168`) plus two weekend days
//! of two blocks each:
//!
//! ```text
//! Mon 08-31  4 blocks · load 168 · interrupted 30m · ^m9 demoted out of W35
//! Tue 09-01  4 blocks · load 168
//! Wed 09-02  4 blocks · load 168 · no lunch, a 45-minute hole
//! Thu 09-03  4 blocks · load 168 · every report one under
//! Fri 09-04  4 blocks · load 168 · groceries skipped
//! Sat 09-05  2 blocks · load  60
//! Sun 09-06  2 blocks · load 108 · ^m2 (180m) and ^m4 (120m) demoted to 2026-09
//! ```

mod review_common;

use review_common as fixture;
use tm_core::energy::Model;
use tm_core::model::{Id, IsoWeek};
use tm_core::review::{render_week, week_review, Style, WeekExtras, HEAT_HOURS, HEAT_STYLES};

fn week() -> IsoWeek {
    IsoWeek::parse("2026-W36").unwrap()
}

fn id(s: &str) -> Id {
    Id::new(s.to_string())
}

fn extras() -> WeekExtras {
    WeekExtras {
        // The week file's `budget: 25` front matter.
        budget_blocks: Some(25),
        planned_blocks: None,
        deadline_health: None,
    }
}

fn review() -> tm_core::review::WeekReview {
    let cfg = fixture::config();
    week_review(
        &fixture::plan_tree(&cfg),
        &fixture::replay(),
        &cfg,
        &Model::default(),
        week(),
        fixture::TZ,
        &extras(),
        // No Pause in the fixture's log: nothing for the kernel's cut to name.
        &tm_core::review::PauseCut::default(),
    )
}

#[test]
fn blocks_per_day_are_the_seven_days_of_the_week() {
    let r = review();
    let days: Vec<(String, u32)> = r
        .blocks_per_day
        .iter()
        .map(|(d, n)| (d.to_string(), *n))
        .collect();
    assert_eq!(
        days,
        vec![
            ("2026-08-31".to_string(), 4),
            ("2026-09-01".to_string(), 4),
            ("2026-09-02".to_string(), 4),
            ("2026-09-03".to_string(), 4),
            ("2026-09-04".to_string(), 4),
            ("2026-09-05".to_string(), 2),
            ("2026-09-06".to_string(), 2),
        ]
    );
    assert_eq!(r.blocks_done, 24); // 4 × 5 + 2 + 2
    assert_eq!(r.block_min, 1440); // 240 × 5 + 120 + 120
    assert_eq!(r.load, 1008.0); // 168 × 5 + 60 + 108
}

#[test]
fn the_heat_grid_is_seven_days_of_twenty_four_hours_by_style() {
    let r = review();
    assert_eq!(r.heat.len(), 7);
    for day in &r.heat {
        assert_eq!(day.hours.len(), HEAT_HOURS);
        for hour in &day.hours {
            assert_eq!(hour.len(), HEAT_STYLES);
            // No hour can hold more than 60 minutes of any one style.
            assert!(hour.iter().all(|m| *m <= 60));
        }
    }
    // The grid accounts for every logged minute of the week.
    let block: u32 = r.heat.iter().map(|d| d.total(Style::Block)).sum();
    let brk: u32 = r.heat.iter().map(|d| d.total(Style::Break)).sum();
    let routine: u32 = r.heat.iter().map(|d| d.total(Style::Routine)).sum();
    let interrupt: u32 = r.heat.iter().map(|d| d.total(Style::Interrupt)).sum();
    let leak: u32 = r.heat.iter().map(|d| d.total(Style::Leak)).sum();
    assert_eq!(block, 1440); // the block minutes above
    assert_eq!(brk, 240); // 40 × 5 + 20 + 20
    assert_eq!(routine, 120); // lunch on Mon, Tue, Thu, Fri
    assert_eq!(interrupt, 30); // Monday's interruption
    assert_eq!(leak, 0); // nothing was attributed to leak this week

    // Monday's first block runs 07:05–08:05 (55 minutes in hour 7, 5 in hour
    // 8), the break 08:05–08:25 and the second block 08:25–09:25 (35 minutes
    // in hour 8, 25 in hour 9).
    let monday = &r.heat[0];
    assert_eq!(monday.hours[7][Style::Block.index()], 55);
    assert_eq!(monday.hours[8][Style::Block.index()], 5 + 35);
    assert_eq!(monday.hours[9][Style::Block.index()], 25 + 15); // + block three
    assert_eq!(monday.hours[8][Style::Break.index()], 20);
    assert_eq!(monday.hours[10][Style::Interrupt.index()], 30);
    assert_eq!(monday.blocks_done, 4);
    assert_eq!(monday.block_min, 240);
}

#[test]
fn milestones_hit_and_demoted_come_from_the_tree_and_the_log() {
    let r = review();
    assert_eq!(r.hit, vec![id("m1")]); // `[x]`
    assert_eq!(r.demoted, vec![id("m2"), id("m4")]); // `[-]`
}

#[test]
fn plan_honesty_is_planned_over_the_realistic_budget() {
    let r = review();
    // Σ remaining over the week's top-level items: ^m1 is done (0), ^m2
    // carries est:3b, ^m3 is 3b and ^m4 est:2b → 480 minutes = 8 blocks.
    // ^b12a is a child of ^m3, so it is a task, not a milestone.
    assert_eq!(r.planned_blocks, 8.0);
    assert_eq!(r.budget_blocks, Some(25));
    // §16's `plan_ratio = 0.8`: 8 / (25 × 0.8) = 0.4.
    assert_eq!(r.plan_honesty, Some(0.4));
}

#[test]
fn carry_over_is_what_the_closes_moved() {
    let r = review();
    // ^m9 left 2026-W35 with 60 minutes on the Monday.
    assert_eq!(r.carry_in_min, 60);
    // ^m2 (180) and ^m4 (120) left 2026-W36 on the Sunday.
    assert_eq!(r.carry_out_min, 300);
}

#[test]
fn demotion_churn_lists_the_repeatedly_demoted() {
    let r = review();
    let rows: Vec<(String, usize)> = r
        .churn
        .iter()
        .map(|c| (c.id.to_string(), c.stamps.len()))
        .collect();
    // ^m9 carries three stamps, ^m4 and ^m8 two each; ^m2's single stamp is
    // below the threshold.
    assert_eq!(
        rows,
        vec![
            ("m9".to_string(), 3),
            ("m4".to_string(), 2),
            ("m8".to_string(), 2),
        ]
    );
}

#[test]
fn the_lounge_rate_is_conditioned_on_the_wake_hour() {
    let r = review();
    // Thirteen days have a location (2026-08-30 has no `arrive`); eleven of
    // them are in the lounge — 2026-08-27 and 2026-08-29 are at home.
    assert_eq!(r.lounge.overall, Some(0.85)); // 11 / 13
    // Ten days wake at 06:05, nine of them in the lounge; three wake at
    // 08:00–08:30, two of them in the lounge.
    assert_eq!(
        r.lounge.by_wake_hour,
        vec![(6, 10, 0.9), (8, 3, 0.67)]
    );
    // 2026-08-31 … 2026-09-06 are all lounge days: a streak of seven.
    assert_eq!(r.lounge.streak, 7);
}

#[test]
fn the_calibration_trend_is_one_row_per_day() {
    let r = review();
    let rows: Vec<(String, usize, f64)> = r
        .mae_per_day
        .iter()
        .map(|(d, n, mae)| (d.to_string(), *n, *mae))
        .collect();
    // Errors per day, from the table's pred/rep columns:
    //   Mon 5/5 5/5 4/3 4/4 → 1 wrong of 4      Tue all right
    //   Wed 5/5 5/5 4/4 4/3 → 1 of 4            Thu 5/4 5/4 4/4 4/3 → 3 of 4
    //   Fri all right       Sat all right       Sun 5/5 5/4 → 1 of 2
    assert_eq!(
        rows,
        vec![
            ("2026-08-31".to_string(), 4, 0.25),
            ("2026-09-01".to_string(), 4, 0.0),
            ("2026-09-02".to_string(), 4, 0.25),
            ("2026-09-03".to_string(), 4, 0.75),
            ("2026-09-04".to_string(), 4, 0.0),
            ("2026-09-05".to_string(), 2, 0.0),
            ("2026-09-06".to_string(), 2, 0.5),
        ]
    );
}

#[test]
fn the_curve_overlay_carries_the_prior_and_the_learned_curve() {
    let cfg = fixture::config();
    let replay = fixture::replay();
    // A fitted model, so the overlay has both halves.
    let model = tm_core::energy::fit_observations(
        &cfg,
        &replay.energy,
        &replay.durations,
        &tm_core::energy::arrivals_from_replay(&cfg, &replay),
        fixture::last_day(),
    );
    let r = week_review(
        &fixture::plan_tree(&cfg),
        &replay,
        &cfg,
        &model,
        week(),
        fixture::TZ,
        &extras(),
        &tm_core::review::PauseCut::default(),
    );
    let names: Vec<&str> = r.curves.iter().map(|c| c.curve.as_str()).collect();
    assert_eq!(names, vec!["home", "lounge"]);
    let lounge = r.curves.iter().find(|c| c.curve == "lounge").unwrap();
    // §16's lounge prior: 0–1h → 4, 1–5h → 5, 5–8h → 4, 8–10h → 3, 10h+ → 2.
    assert_eq!(lounge.prior, vec![4, 5, 5, 5, 5, 4, 4, 4, 3, 3, 2, 2]);
    let learned = lounge.learned.as_ref().expect("the model was fitted");
    assert_eq!(learned.len(), 12);
    // Every report in the fixture is at or below the prior, so no learned
    // level can be above it.
    assert!(learned.iter().zip(&lounge.prior).all(|(l, p)| l <= p));

    // Estimate multipliers are the running ones, so the counts are the whole
    // log's: 13 #admin blocks, 12 #lean, 11 #soundcode, 45 in total.
    let counts: Vec<(&str, usize)> =
        r.estimates.iter().map(|t| (t.tag.as_str(), t.n)).collect();
    assert_eq!(
        counts,
        vec![("admin", 13), ("lean", 12), ("soundcode", 11), ("_default", 45)]
    );
}

#[test]
fn the_week_carries_the_day_monitors_that_have_a_week_trend() {
    let r = review();
    // Energy mix: five standard days give 60 minutes at each of ci 5/4/3/2,
    // Saturday adds ci 3 and 2, Sunday ci 5 and 4 → 360 minutes each.
    assert_eq!(r.mix.minutes_by_ci, [0, 0, 360, 360, 360, 360]);
    assert_eq!(r.mix.total_min, 1440);
    // §11's share is of the *budget*: every one of the seven days arrived
    // with a budget of six blocks, so 7 × 6 × 60 = 2520 minutes.
    assert_eq!(r.mix.budget_min, 2520);
    assert_eq!(r.mix.high_share, Some(29)); // 720 of 2520 = 28.6%

    // Break histogram: five days of walk + seat, then one each.
    assert_eq!(r.breaks.planned_min, 240); // 40 × 5 + 20 + 20
    assert_eq!(r.breaks.actual_min, 240);
    assert_eq!(r.breaks.over_count, 0);
    assert_eq!(r.breaks.by_where["walk"], (6, 120));
    assert_eq!(r.breaks.by_where["seat"], (6, 120));

    // Start latency: weekdays wake 06:05 and arrive 07:00 (55m) then start
    // five minutes later; the weekend wakes late and arrives 90 minutes on.
    let latency: Vec<(Option<i64>, Option<i64>)> =
        r.latency.iter().map(|(_, w, s)| (*w, *s)).collect();
    assert_eq!(
        latency,
        vec![
            (Some(55), Some(5)),
            (Some(55), Some(5)),
            (Some(55), Some(5)),
            (Some(55), Some(5)),
            (Some(55), Some(5)),
            (Some(90), Some(5)),
            (Some(90), Some(5)),
        ]
    );

    // Sleep panel: the table's `slept_min`, with the blocks that followed.
    let sleep: Vec<(Option<u32>, u32)> =
        r.sleep.iter().map(|s| (s.slept_min, s.blocks_done)).collect();
    assert_eq!(
        sleep,
        vec![
            (Some(480), 4),
            (Some(480), 4),
            (Some(480), 4),
            (Some(400), 4),
            (Some(480), 4),
            (Some(520), 2),
            (Some(500), 2),
        ]
    );
    assert!(r.sleep.iter().all(|s| s.onset_min.is_none()));
}

#[test]
fn the_week_screen_renders() {
    insta::assert_snapshot!("render_week", render_week(&review()));
}

#[test]
fn the_json_shape_is_stable() {
    let r = review();
    // The heat grid is 7 × 24 × 7 numbers; the snapshot keeps everything else.
    insta::assert_json_snapshot!("week_review_json", {
        let mut r = r;
        r.heat.clear();
        r
    });
}
