//! The §12.4 month review over the synthetic 14-day fixture, read for
//! 2026-09: outcomes done and not, demotion churn, carry-over week over week
//! and the proposed cut list (§6.3 "≥ 2 stamps ⇒ cut or re-scope").
//!
//! The tree is `tests/review_common/mod.rs`'s two files: three outcomes (^O1
//! finished) with two archived lines under `# Demoted` (^m8 with two stamps,
//! ^m9 with three), and a week whose ^m4 also carries two. The only
//! September demotions in the log are the Sunday close of 2026-W36, which
//! moved ^m2 (180m) and ^m4 (120m) into the month.

mod review_common;

use review_common as fixture;
use tm_core::model::{Id, YearMonth};
use tm_core::review::{month_review, render_month, MonthExtras, MonthReview};

fn id(s: &str) -> Id {
    Id::new(s.to_string())
}

fn month() -> YearMonth {
    YearMonth::parse("2026-09").unwrap()
}

fn review() -> MonthReview {
    let cfg = fixture::config();
    month_review(
        &fixture::plan_tree(&cfg),
        &fixture::replay(),
        &cfg,
        month(),
        fixture::TZ,
        &MonthExtras::default(),
    )
}

#[test]
fn outcomes_are_the_month_file_outside_the_demoted_section() {
    let r = review();
    let rows: Vec<(String, u8, bool)> = r
        .outcomes
        .iter()
        .map(|o| (o.id.to_string(), o.k, o.done))
        .collect();
    assert_eq!(
        rows,
        vec![
            ("O1".to_string(), 1, true),
            ("O2".to_string(), 1, false),
            ("O3".to_string(), 3, false),
        ]
    );
    assert_eq!(r.done_count, 1);
    // The `# Demoted` lines are listed apart.
    assert_eq!(r.demoted, vec![id("m8"), id("m9")]);
}

#[test]
fn progress_rolls_the_logged_minutes_up_the_tree() {
    let r = review();
    // ^O1's children are ^m1 (6b) and ^m3 (3b) → 540 planned minutes. The
    // only logged item under it is ^b12a, the Sunday block, worth 60 →
    // 60 / 540 = 0.111.
    assert_eq!(r.outcomes[0].progress, Some(0.11));
    // Nothing under ^O2 (^m2, 6b) or ^O3 (^m4 2b + ^m8 2b) was logged.
    assert_eq!(r.outcomes[1].progress, Some(0.0));
    assert_eq!(r.outcomes[2].progress, Some(0.0));
}

#[test]
fn carry_over_is_grouped_by_the_week_that_shed_it() {
    let r = review();
    // The 2026-W36 close on Sunday 2026-09-06 demoted ^m2 (180m) and ^m4
    // (120m). The 2026-W35 close happened on 2026-08-31, which is August, and
    // ^t5's day close carries a day stamp, not a week one.
    assert_eq!(r.carry_over, vec![("2026-W36".to_string(), 300)]);
}

#[test]
fn august_sees_only_its_own_close() {
    let cfg = fixture::config();
    let r = month_review(
        &fixture::plan_tree(&cfg),
        &fixture::replay(),
        &cfg,
        YearMonth::parse("2026-08").unwrap(),
        fixture::TZ,
        &MonthExtras::default(),
    );
    // ^m9 left 2026-W35 with 60 minutes on 2026-08-31.
    assert_eq!(r.carry_over, vec![("2026-W35".to_string(), 60)]);
    // There is no August file in the tree, so there are no outcomes.
    assert!(r.outcomes.is_empty());
    // The cut list is a property of the tree, not of the month.
    assert_eq!(r.cuts, vec![id("m9"), id("m4"), id("m8")]);
}

#[test]
fn the_cut_list_is_everything_with_two_stamps_or_more() {
    let r = review();
    let rows: Vec<(String, usize)> = r
        .churn
        .iter()
        .map(|c| (c.id.to_string(), c.stamps.len()))
        .collect();
    assert_eq!(
        rows,
        vec![
            ("m9".to_string(), 3),
            ("m4".to_string(), 2),
            ("m8".to_string(), 2),
        ]
    );
    assert_eq!(r.cuts, vec![id("m9"), id("m4"), id("m8")]);

    // Raising the threshold drops the two-stamp lines.
    let cfg = fixture::config();
    let strict = month_review(
        &fixture::plan_tree(&cfg),
        &fixture::replay(),
        &cfg,
        month(),
        fixture::TZ,
        &MonthExtras { cut_stamps: 3 },
    );
    assert_eq!(strict.cuts, vec![id("m9")]);
}

#[test]
fn the_month_screen_renders() {
    insta::assert_snapshot!("render_month", render_month(&review()));
}

#[test]
fn the_json_shape_is_stable() {
    insta::assert_json_snapshot!("month_review_json", review());
}
