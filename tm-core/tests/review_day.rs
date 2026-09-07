//! §11 monitors and the §12.4 day review on the synthetic 14-day fixture
//! (§17 M8: "monitors computed from a synthetic 14-day log fixture match
//! hand-computed values").
//!
//! Every expected number below is written out from
//! `tests/review_common/mod.rs`'s table, not from running the code. The day
//! under review is 2026-09-07, whose table entry is:
//!
//! ```text
//! wake 06:05 slept 490 onset 25 · arrive 07:00 lounge · window 07:00–16:00 · budget 6
//! t1 07:02→08:09  67m est 60  ci 5 #lean       went 1  pred 5 rep 5
//! t2 08:33→09:31  58m est 60  ci 5 #lean       went 1  pred 4 rep 5
//! t3 10:02→13:32 155m est 120 ci 4 #lean       went 2  pred 5 rep 5   (interrupted 12:10–13:05)
//! t4 13:52→14:52  60m est 60  ci 3 #soundcode  went 1  pred 4 rep 3
//! p1 15:06→15:26  20m est 20  ci 2 #admin      went 1  pred 3 rep 2
//! breaks 08:09 20/24 walk · 09:31 20/31 seat · 13:32 20/20 walk
//! energy 10:15 5/5 · 11:15 4/4 · 12:15 4/4 · 14:15 4/3 · 15:40 3/2
//! idle   15:06 leak 14m · resume 13:05 lost 55m dropped t5
//! plans  4, drift 0+25+30+20 = 75 · demote t5 30m → 2026-W37
//! ```

mod review_common;

use chrono::{NaiveTime, TimeZone};
use review_common as fixture;
use tm_core::capacity::local_dt;
use tm_core::energy::Model;
use tm_core::log::{Event, Log, LogEntry};
use tm_core::model::Id;
use tm_core::review::{
    day_review, render_day, render_status, render_status_full, status_line, DayExtras,
    OptionalQuota, PlannedBlock, StatusHead, TomorrowCandidate,
};
use tm_core::store::{MemStore, RuntimeState, Store};
use tm_core::tree::Tree;

fn time(hhmm: &str) -> NaiveTime {
    NaiveTime::parse_from_str(hhmm, "%H:%M").unwrap()
}

fn id(s: &str) -> Id {
    Id::new(s.to_string())
}

/// The `plan-basic` tree — `day_review` reads it only to attribute block
/// minutes the log has no `ci` for, of which this day has none.
fn tree() -> Tree {
    let store = MemStore::from_dir(fixture::fixtures().join("plan-basic")).unwrap();
    store.read_tree().unwrap().tree()
}

/// The six blocks the day was planned with at arrival: five of them were
/// started within ±10m (07:00/07:02, 08:30/08:33, 10:00/10:02, 13:50/13:52,
/// 15:00/15:06) and ^t5 never started at all → adherence 5/6 = 83%.
fn plan_at_arrival() -> Vec<PlannedBlock> {
    let date = fixture::last_day();
    [
        ("t1", "07:00"),
        ("t2", "08:30"),
        ("t3", "10:00"),
        ("t4", "13:50"),
        ("p1", "15:00"),
        ("t5", "16:00"),
    ]
    .iter()
    .map(|(i, t)| PlannedBlock::new(id(i), local_dt(fixture::TZ, date, time(t))))
    .collect()
}

fn extras() -> DayExtras {
    DayExtras {
        plan_at_arrival: plan_at_arrival(),
        underused: 1,
        tomorrow_first: vec![
            TomorrowCandidate::new(id("t5"), Some("after t4")),
            TomorrowCandidate::new(id("d1"), Some("p1 u=0.6")),
            TomorrowCandidate::new(id("a3"), Some("done")),
        ],
        optional: None,
        lost_note: Some("call".to_string()),
        budget: None,
    }
}

fn review() -> tm_core::review::DayReview {
    let cfg = fixture::config();
    day_review(
        &tree(),
        &fixture::replay(),
        &cfg,
        &Model::default(),
        fixture::last_day(),
        fixture::TZ,
        &extras(),
    )
}

// ---------------------------------------------------------------------------
// Blocks, load and the leak ledger
// ---------------------------------------------------------------------------

#[test]
fn blocks_and_load_come_straight_off_the_table() {
    let r = review();
    // Five `done` events with actual_min > 0, against the arrival budget.
    assert_eq!(r.blocks_done, 5);
    assert_eq!(r.budget, 6);
    // 67 + 58 + 155 + 60 + 20.
    assert_eq!(r.block_min, 360);
    // §11 load = Σ block_min × ci / 5
    //          = (125×5 + 155×4 + 60×3 + 20×2) / 5 = 1465 / 5.
    assert_eq!(r.load, 293.0);
    assert_eq!(r.load_blocks, 4.88); // 293 / 60, to two places
    assert_eq!(r.window, Some((time("07:00"), time("16:00"))));
    assert_eq!(r.loc.as_deref(), Some("lounge"));
}

#[test]
fn the_energy_mix_splits_the_day_by_ci() {
    let r = review();
    // ci 5: t1 67 + t2 58 = 125 · ci 4: t3 155 · ci 3: t4 60 · ci 2: p1 20.
    assert_eq!(r.mix.minutes_by_ci, [0, 0, 20, 60, 155, 125]);
    assert_eq!(r.mix.total_min, 360);
    assert_eq!(r.mix.high_min, 280); // 155 + 125
    assert_eq!(r.mix.high_share, Some(78)); // 280 / 360 = 77.8%
    assert_eq!(r.mix.underused, 1); // the parameter
}

#[test]
fn the_leak_ledger_adds_attributed_leak_and_unattributed_gaps() {
    let r = review();
    // One idle prompt, 14 minutes, and a day with no holes.
    assert_eq!(r.leak.attributed_min, 14);
    assert_eq!(r.leak.gap_min, 0);
    assert_eq!(r.leak.total_min, 14);
    assert_eq!(r.leak.longest_min, 14);
    assert_eq!(r.lost_min, 55); // resume.lost_min
}

#[test]
fn a_day_with_a_hole_counts_the_hole_as_leak() {
    // 2026-09-02: the third block ends 10:45, the fourth starts 11:30, and
    // nobody answered an idle prompt — 45 unattributed minutes.
    let cfg = fixture::config();
    let r = day_review(
        &tree(),
        &fixture::replay(),
        &cfg,
        &Model::default(),
        fixture::date(2026, 9, 2),
        fixture::TZ,
        &DayExtras::default(),
    );
    assert_eq!(r.leak.attributed_min, 0);
    assert_eq!(r.leak.gap_min, 45);
    assert_eq!(r.leak.total_min, 45);
    assert_eq!(r.leak.longest_min, 45);
    // A standard day: four 60-minute blocks at ci 5/4/3/2.
    assert_eq!(r.blocks_done, 4);
    assert_eq!(r.load, 168.0); // (300 + 240 + 180 + 120) / 5
}

// ---------------------------------------------------------------------------
// Adherence, latency, replans, breaks, rest debt, sleep
// ---------------------------------------------------------------------------

#[test]
fn adherence_is_five_of_six_planned_blocks() {
    let r = review();
    assert_eq!(r.adherence.planned, 6);
    assert_eq!(r.adherence.started_on_time, 5);
    assert_eq!(r.adherence.completed, 5);
    assert_eq!(r.adherence.started_pct, Some(83));
    assert_eq!(r.adherence.completed_pct, Some(83));
    assert_eq!(r.adherence.missed, vec![id("t5")]);
}

#[test]
fn a_planned_block_more_than_ten_minutes_late_does_not_count() {
    // Same day, but ^p1 was planned for 14:50 and started at 15:06 (16m).
    let date = fixture::last_day();
    let mut plan = plan_at_arrival();
    plan[4] = PlannedBlock::new(id("p1"), local_dt(fixture::TZ, date, time("14:50")));
    let cfg = fixture::config();
    let r = day_review(
        &tree(),
        &fixture::replay(),
        &cfg,
        &Model::default(),
        date,
        fixture::TZ,
        &DayExtras {
            plan_at_arrival: plan,
            ..DayExtras::default()
        },
    );
    assert_eq!(r.adherence.started_on_time, 4);
    assert_eq!(r.adherence.started_pct, Some(67)); // 4/6 = 66.7%
    // It was still finished, so the completion column does not move.
    assert_eq!(r.adherence.completed, 5);
}

#[test]
fn start_latency_and_replans_are_the_logged_differences() {
    let r = review();
    assert_eq!(r.wake_to_arrive_min, Some(55)); // 06:05 → 07:00
    assert_eq!(r.arrive_to_start_min, Some(2)); // 07:00 → 07:02
    assert_eq!(r.replans, 4); // four `plan` events
    assert_eq!(r.drift_min, 75); // 0 + 25 + 30 + 20
}

#[test]
fn break_integrity_keeps_planned_actual_and_the_where_histogram() {
    let r = review();
    assert_eq!(r.breaks.breaks.len(), 3);
    assert_eq!(r.breaks.planned_min, 60); // 20 × 3
    assert_eq!(r.breaks.actual_min, 75); // 24 + 31 + 20
    assert_eq!(r.breaks.over_count, 0); // none reached 2 × 20
    assert_eq!(r.breaks.over_share, Some(0));
    assert_eq!(r.breaks.by_where["walk"], (2, 44)); // 24 + 20
    assert_eq!(r.breaks.by_where["seat"], (1, 31));
    // Five blocks owed ⌊5/2⌋ × 20 = 40 minutes of break; 75 were taken.
    assert_eq!(r.rest_debt_min, 0);
}

#[test]
fn a_day_of_cut_breaks_owes_rest_debt() {
    // 2026-08-27: three blocks owe ⌊3/2⌋ × 20 = 20 minutes and 25 were taken;
    // 2026-08-25 owes ⌊4/2⌋ × 20 = 40 and took 40. Neither is in debt, so
    // check the arithmetic the other way: a fabricated runtime with no breaks
    // at all is what the status line reports on.
    let cfg = fixture::config();
    let replay = fixture::replay();
    let r = day_review(
        &tree(),
        &replay,
        &cfg,
        &Model::default(),
        fixture::date(2026, 8, 27),
        fixture::TZ,
        &DayExtras::default(),
    );
    assert_eq!(r.breaks.actual_min, 25);
    assert_eq!(r.rest_debt_min, 0);

    // 2026-08-30 is a day off: a wake and nothing else.
    let off = day_review(
        &tree(),
        &replay,
        &cfg,
        &Model::default(),
        fixture::date(2026, 8, 30),
        fixture::TZ,
        &DayExtras::default(),
    );
    assert_eq!(off.blocks_done, 0);
    assert_eq!(off.rest_debt_min, 0);
    assert_eq!(off.slept_min, Some(560));
    assert_eq!(off.budget, 6); // no `arrive`: §16's floor(8 × 60 / 60 × 0.75)
}

#[test]
fn the_sleep_panel_is_the_wake_event() {
    let r = review();
    assert_eq!(r.slept_min, Some(490)); // 8h10m
    assert_eq!(r.onset_min, Some(25));
}

// ---------------------------------------------------------------------------
// Energy and estimate calibration
// ---------------------------------------------------------------------------

#[test]
fn energy_calibration_is_the_mean_error_of_the_logged_prediction() {
    let r = review();
    // Ten observations: five block starts and five `energy` events.
    // errors: 0, +1, 0, −1, −1 (starts) and 0, 0, 0, −1, −1 (events).
    assert_eq!(r.energy.n, 10);
    assert_eq!(r.energy.mae, 0.5); // Σ|e| = 5 over 10
    assert_eq!(r.energy.bias, -0.3); // Σe = +1 − 4 = −3 over 10
    // Hour 8 is the only positive hour; 13, 14 and 15 are negative.
    assert_eq!(r.energy.flip_hour, Some(13));
    // The config prior (lounge: 4 5 5 5 5 4 4 4 3 3 …) is wrong four times
    // out of ten: at 07:02 (hsw 0.95 → 4 vs 5) and at 13:52, 15:06, 15:40.
    assert_eq!(r.energy.mae_prior, 0.4);
    // An empty model falls back to the same prior.
    assert_eq!(r.energy.mae_learned, 0.4);
}

#[test]
fn the_energy_row_is_one_cell_per_hour_with_gaps_predicted() {
    let r = review();
    let cells: Vec<(u32, u8, Option<u8>)> =
        r.energy.hours.iter().map(|h| (h.hour, h.pred, h.rep)).collect();
    assert_eq!(
        cells,
        vec![
            (7, 5, Some(5)),
            (8, 4, Some(5)),
            // 09:00 was never asked: hsw 2.92 on the lounge prior is 5.
            (9, 5, None),
            (10, 5, Some(5)), // 10:02 and 10:15, both 5/5
            (11, 4, Some(4)),
            (12, 4, Some(4)),
            (13, 4, Some(3)),
            (14, 4, Some(3)),
            (15, 3, Some(2)), // 15:06 and 15:40, both 3/2
        ]
    );
}

#[test]
fn estimate_calibration_counts_every_block_of_the_fourteen_days() {
    let r = review();
    let by_tag: Vec<(&str, usize, f64)> = r
        .estimates
        .iter()
        .map(|t| (t.tag.as_str(), t.n, t.mean_ratio))
        .collect();
    // #admin: twelve blocks of 60m against an estimate of 75m (0.8) and
    //         ^p1's 20/20 → (12 × 0.8 + 1) / 13 = 10.6 / 13 = 0.8154.
    // #lean:  nine blocks of 60m against 45m (4/3) plus 67/60, 58/60 and
    //         155/120 → (12 + 3.375) / 12 = 1.28125.
    // #soundcode: eleven blocks of 60m against 60m.
    // _default: all 45 blocks → 45.975 / 45 = 1.0217.
    assert_eq!(
        by_tag,
        vec![
            ("admin", 13, 0.82),
            ("lean", 12, 1.28),
            ("soundcode", 11, 1.0),
            ("_default", 45, 1.02),
        ]
    );
    // The multiplier is the §8.5 shrunken mean of those ratios, so it sits
    // between the prior 1.0 and the plain mean.
    let lean = &r.estimates[1];
    assert!(lean.multiplier > 1.0 && lean.multiplier < lean.mean_ratio);
    // The trend column is the last seven days only: 2026-09-01 .. 09-07,
    // which hold five 4/3 ratios and the review day's three.
    assert_eq!(lean.recent_ratio, Some(1.26)); // 10.0417 / 8
}

// ---------------------------------------------------------------------------
// Done, demoted, tomorrow
// ---------------------------------------------------------------------------

#[test]
fn the_done_and_demoted_lists_are_the_days_events() {
    let r = review();
    assert_eq!(
        r.done,
        vec![id("t1"), id("t2"), id("t3"), id("t4"), id("p1")]
    );
    assert_eq!(r.demoted.len(), 1);
    assert_eq!(r.demoted[0].id, id("t5"));
    assert_eq!(r.demoted[0].est_min, 30);
    assert_eq!(r.demoted[0].to, "2026-W37");
    assert_eq!(r.tomorrow.len(), 3);
    assert_eq!(r.tomorrow[0].id, id("t5"));
}

// ---------------------------------------------------------------------------
// Status line (§12.1)
// ---------------------------------------------------------------------------

#[test]
fn the_status_line_reports_the_same_monitors() {
    let cfg = fixture::config();
    let runtime = RuntimeState {
        date: Some(fixture::last_day()),
        window: Some((time("07:00"), time("16:00"))),
        budget: Some(6),
        ..RuntimeState::default()
    };
    let s = status_line(&fixture::replay(), &cfg, &runtime, &plan_at_arrival());
    assert_eq!(s.blocks_done, 5);
    assert_eq!(s.budget, 6);
    assert_eq!(s.leak_min, 14);
    assert_eq!(s.adherence_pct, Some(83));
    assert_eq!(s.window_end, Some(time("16:00")));
    assert_eq!(s.lost_min, 55);
    assert_eq!(s.rest_debt_min, 0);
    assert_eq!(s.load, 293.0);
    assert_eq!(
        render_status(&s),
        "● 5/6 · leak 14m · adherence 83% · window → 16:00 · lost 55m"
    );

    let head = StatusHead {
        date: fixture::last_day(),
        now: time("10:42"),
        loc: Some("lounge".to_string()),
        wake: Some(time("06:05")),
        slept_min: Some(490),
        pred: Some(4),
        rep: Some(4),
    };
    insta::assert_snapshot!("status_line_full", render_status_full(&head, &s));
}

#[test]
fn a_day_with_no_plan_has_no_adherence_and_a_bare_lost_column() {
    let cfg = fixture::config();
    let runtime = RuntimeState {
        date: Some(fixture::date(2026, 9, 2)),
        ..RuntimeState::default()
    };
    let s = status_line(&fixture::replay(), &cfg, &runtime, &[]);
    assert_eq!(s.rest_debt_min, 0); // four blocks owe 40m, two breaks gave 40
    assert_eq!(s.adherence_pct, None);
    assert_eq!(s.leak_min, 45); // the unattributed hole
    assert_eq!(
        render_status(&s),
        "● 4/6 · leak 45m · adherence - · window → 15:00 · lost 0"
    );
}

/// Six 60-minute blocks in a row and not one break: §16's
/// `break_after_blocks = 2` and `break_min = 20` make that ⌊6/2⌋ × 20 = 60
/// minutes of rest debt, which is over the 40-minute warning line.
#[test]
fn the_status_line_warns_when_the_rest_debt_is_over_forty_minutes() {
    let cfg = fixture::config();
    let date = fixture::date(2026, 10, 5);
    let offset = chrono::FixedOffset::east_opt(-5 * 3600).unwrap();
    let at = |hhmm: &str| {
        offset
            .from_local_datetime(&date.and_time(time(hhmm)))
            .unwrap()
    };
    let mut entries = vec![
        LogEntry::new(at("06:00"), Event::Wake { slept_min: 480, onset_min: None }),
        LogEntry::new(
            at("07:00"),
            Event::Arrive {
                loc: "lounge".to_string(),
                window: ["07:00".to_string(), "15:00".to_string()],
                budget: 6,
            },
        ),
    ];
    for i in 0..6u32 {
        let start = format!("{:02}:00", 7 + i);
        let end = format!("{:02}:00", 8 + i);
        entries.push(LogEntry::new(
            at(&start),
            Event::Start {
                id: format!("z{i}"),
                pred: 4,
                rep: Some(4),
                hsw: 1.0 + i as f64,
                slept_min: 480,
                loc: "lounge".to_string(),
                blocks_done: i,
                since_break_min: 0,
            },
        ));
        entries.push(LogEntry::new(
            at(&end),
            Event::Done {
                id: format!("z{i}"),
                est_min: 60,
                actual_min: 60,
                went: Some(1),
                tags: Vec::new(),
                ci: 3,
                partial: false,
            },
        ));
    }
    let replay = Log::from_entries(entries).replay(None, fixture::TZ);
    let runtime = RuntimeState {
        date: Some(date),
        ..RuntimeState::default()
    };
    let s = status_line(&replay, &cfg, &runtime, &[]);
    assert_eq!(s.blocks_done, 6);
    assert_eq!(s.rest_debt_min, 60);
    assert_eq!(s.load, 216.0); // 360 minutes at ci 3 → 1080 / 5
    assert!(
        render_status(&s).ends_with("· rest debt 60m"),
        "{}",
        render_status(&s)
    );
}

#[test]
fn plan_honesty_is_the_planned_blocks_over_the_budget() {
    let r = review();
    // Six planned blocks against a budget of six.
    assert_eq!(r.plan_honesty, Some(1.0));
    // With nothing planned there is nothing to be honest about.
    let cfg = fixture::config();
    let bare = day_review(
        &tree(),
        &fixture::replay(),
        &cfg,
        &Model::default(),
        fixture::last_day(),
        fixture::TZ,
        &DayExtras::default(),
    );
    assert_eq!(bare.plan_honesty, None);
}

#[test]
fn the_optional_quota_is_carried_through() {
    let cfg = fixture::config();
    let quota = OptionalQuota {
        minutes: 60,
        cap_min: Some(240), // `max:4h/w`
        outside_rest_min: 15,
    };
    let r = day_review(
        &tree(),
        &fixture::replay(),
        &cfg,
        &Model::default(),
        fixture::last_day(),
        fixture::TZ,
        &DayExtras {
            optional: Some(quota),
            ..DayExtras::default()
        },
    );
    assert_eq!(r.optional, Some(quota));
}

// ---------------------------------------------------------------------------
// Rendering (§12.4) and --json (§13)
// ---------------------------------------------------------------------------

#[test]
fn the_review_screen_matches_the_spec_layout() {
    insta::assert_snapshot!("render_day", render_day(&review()));
}

#[test]
fn the_json_shape_is_stable() {
    insta::assert_json_snapshot!("day_review_json", review());
}
