//! Boundary and wake-to-wake cases the fourteen-day fixture does not reach:
//! the §11 energy-mix denominator, the strict `> 2×` of break integrity and
//! the strict `> idle_min` of the leak ledger, a day whose energy
//! observations cross midnight (§10.1: a day runs wake to wake), block
//! minutes whose item has left the tree, the heat grid across a DST
//! fall-back, and the §11 "Waiting" row.
//!
//! Every expected number is hand-computed from the log each test writes.

mod review_common;

use chrono::{DateTime, FixedOffset};
use review_common as fixture;
use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::{Event, Log, LogEntry, Replay};
use tm_core::model::{Id, IsoWeek};
use tm_core::review::{day_review, waiting, week_review, DayExtras, DayReview, Style, WeekExtras};
use tm_core::tree::Tree;

fn t(s: &str) -> DateTime<FixedOffset> {
    DateTime::parse_from_rfc3339(s).expect("timestamp")
}

fn entry(at: &str, ev: Event) -> LogEntry {
    LogEntry::new(t(at), ev)
}

fn wake(at: &str, slept_min: u32) -> LogEntry {
    entry(
        at,
        Event::Wake {
            slept_min,
            onset_min: None,
        },
    )
}

fn start(at: &str, id: &str, pred: u8, rep: u8) -> LogEntry {
    entry(
        at,
        Event::Start {
            id: id.to_string(),
            pred,
            rep: Some(rep),
            hsw: 1.0,
            slept_min: 480,
            loc: "lounge".to_string(),
            blocks_done: 0,
            since_break_min: 0,
        },
    )
}

fn done(at: &str, id: &str, actual_min: u32, ci: u8) -> LogEntry {
    entry(
        at,
        Event::Done {
            id: id.to_string(),
            est_min: 60,
            actual_min,
            went: Some(1),
            tags: Vec::new(),
            ci,
            partial: false,
        },
    )
}

fn replay_of(entries: Vec<LogEntry>) -> Replay {
    Log::from_entries(entries).replay(None, fixture::TZ)
}

fn empty_tree(cfg: &Config) -> Tree {
    Tree::from_texts(&[], cfg)
}

fn review_of(replay: &Replay, cfg: &Config, y: i32, m: u32, d: u32) -> DayReview {
    day_review(
        &empty_tree(cfg),
        replay,
        cfg,
        &Model::default(),
        fixture::date(y, m, d),
        fixture::TZ,
        &DayExtras::default(),
    )
}

// ---------------------------------------------------------------------------
// §11 energy mix: "share of budget with ci ≥ 4"
// ---------------------------------------------------------------------------

#[test]
fn the_energy_mix_share_is_measured_against_the_budget() {
    let cfg = fixture::config();
    // 2026-09-02 is a standard day: four 60-minute blocks at ci 5/4/3/2
    // against the arrival budget of six blocks.
    let r = day_review(
        &fixture::plan_tree(&cfg),
        &fixture::replay(),
        &cfg,
        &Model::default(),
        fixture::date(2026, 9, 2),
        fixture::TZ,
        &DayExtras::default(),
    );
    assert_eq!(r.budget, 6);
    assert_eq!(r.mix.total_min, 240); // worked
    assert_eq!(r.mix.high_min, 120); // 60 at ci 5 + 60 at ci 4
    assert_eq!(r.mix.budget_min, 360); // 6 blocks × 60 minutes
    // 120 / 360 = 33.3%, not 120 / 240 = 50%.
    assert_eq!(r.mix.high_share, Some(33));
}

// ---------------------------------------------------------------------------
// §11 break integrity: "share > 2×"
// ---------------------------------------------------------------------------

fn day_with_break(actual_min: u32) -> DayReview {
    let cfg = fixture::config();
    let replay = replay_of(vec![
        wake("2026-06-01T06:00:00-05:00", 480),
        start("2026-06-01T07:00:00-05:00", "z1", 4, 4),
        done("2026-06-01T08:00:00-05:00", "z1", 60, 4),
        entry(
            "2026-06-01T08:00:00-05:00",
            Event::Break {
                planned_min: 20,
                actual_min: Some(actual_min),
                r#where: Some("walk".to_string()),
            },
        ),
    ]);
    review_of(&replay, &cfg, 2026, 6, 1)
}

#[test]
fn a_break_of_exactly_twice_its_plan_is_not_over_run() {
    let r = day_with_break(40);
    assert_eq!(r.breaks.breaks.len(), 1);
    assert_eq!(r.breaks.breaks[0].planned_min, 20);
    assert_eq!(r.breaks.breaks[0].actual_min, 40);
    assert!(!r.breaks.breaks[0].over, "40m is 2 × 20m, not more than it");
    assert_eq!(r.breaks.over_count, 0);
    assert_eq!(r.breaks.over_share, Some(0));
}

#[test]
fn a_break_over_twice_its_plan_is_counted() {
    let r = day_with_break(41);
    assert!(r.breaks.breaks[0].over);
    assert_eq!(r.breaks.over_count, 1);
    assert_eq!(r.breaks.over_share, Some(100));
}

// ---------------------------------------------------------------------------
// §11 leak ledger: "unattributed gaps > idle_min"
// ---------------------------------------------------------------------------

fn day_with_gap(second_start: &str, second_done: &str) -> DayReview {
    let cfg = fixture::config();
    let replay = replay_of(vec![
        wake("2026-06-01T06:00:00-05:00", 480),
        start("2026-06-01T07:00:00-05:00", "z1", 4, 4),
        done("2026-06-01T08:00:00-05:00", "z1", 60, 4),
        start(second_start, "z2", 4, 4),
        done(second_done, "z2", 60, 4),
    ]);
    review_of(&replay, &cfg, 2026, 6, 1)
}

#[test]
fn an_unattributed_gap_of_exactly_idle_min_is_not_a_leak() {
    let cfg = fixture::config();
    assert_eq!(cfg.day.idle_min, 12);
    let r = day_with_gap("2026-06-01T08:12:00-05:00", "2026-06-01T09:12:00-05:00");
    assert_eq!(r.leak.gap_min, 0);
    assert_eq!(r.leak.total_min, 0);
    assert_eq!(r.leak.longest_min, 0);
}

#[test]
fn an_unattributed_gap_over_idle_min_is_a_leak() {
    let r = day_with_gap("2026-06-01T08:13:00-05:00", "2026-06-01T09:13:00-05:00");
    assert_eq!(r.leak.gap_min, 13);
    assert_eq!(r.leak.total_min, 13);
    assert_eq!(r.leak.longest_min, 13);
}

// ---------------------------------------------------------------------------
// Block minutes whose item is no longer in the tree
// ---------------------------------------------------------------------------

#[test]
fn block_minutes_of_an_item_outside_the_tree_are_still_counted() {
    let cfg = fixture::config();
    // A block cut by `stop` carries no `ci`, and `^ghost` is in no tree, so
    // the minutes can only be attributed at ci 0 — but they must be counted.
    let replay = replay_of(vec![
        wake("2026-06-01T06:00:00-05:00", 480),
        start("2026-06-01T07:00:00-05:00", "ghost", 4, 4),
        entry(
            "2026-06-01T08:00:00-05:00",
            Event::Stop {
                id: "ghost".to_string(),
                remaining_min: 60,
            },
        ),
    ]);
    let r = review_of(&replay, &cfg, 2026, 6, 1);
    assert_eq!(r.block_min, 60);
    assert_eq!(r.mix.minutes_by_ci, [60, 0, 0, 0, 0, 0]);
    assert_eq!(r.mix.total_min, r.block_min);
    assert_eq!(r.load, 0.0); // 60 minutes × ci 0 / 5
}

// ---------------------------------------------------------------------------
// A wake-to-wake day whose energy observations cross midnight
// ---------------------------------------------------------------------------

#[test]
fn the_energy_row_runs_forwards_across_midnight() {
    let cfg = fixture::config();
    let replay = replay_of(vec![
        wake("2026-10-05T08:00:00-05:00", 480),
        start("2026-10-05T22:00:00-05:00", "z1", 3, 3),
        done("2026-10-05T23:00:00-05:00", "z1", 60, 3),
        entry(
            "2026-10-06T00:30:00-05:00",
            Event::Energy {
                pred: 2,
                rep: 1,
                hsw: 16.5,
                loc: "lounge".to_string(),
            },
        ),
    ]);
    let r = review_of(&replay, &cfg, 2026, 10, 5);
    // Both observations belong to the 2026-10-05 wake-to-wake day.
    assert_eq!(r.energy.n, 2);
    // Three cells, in the order they happened: 22:00, 23:00 (never asked),
    // 00:30 — not 23 cells starting at hour 0.
    let hours: Vec<u32> = r.energy.hours.iter().map(|h| h.hour).collect();
    assert_eq!(hours, vec![22, 23, 0]);
    let reps: Vec<Option<u8>> = r.energy.hours.iter().map(|h| h.rep).collect();
    assert_eq!(reps, vec![Some(3), None, Some(1)]);
    assert_eq!(r.energy.hours[0].pred, 3);
    assert_eq!(r.energy.hours[2].pred, 2);
    // The calibration rows are in the same order.
    let by_hour: Vec<u32> = r.energy.by_hour.iter().map(|(h, _, _, _)| *h).collect();
    assert_eq!(by_hour, vec![22, 0]);
}

#[test]
fn the_bias_flips_at_the_hour_it_actually_flips_after_midnight() {
    let cfg = fixture::config();
    let replay = replay_of(vec![
        wake("2026-06-01T14:00:00-05:00", 480),
        entry(
            "2026-06-01T20:00:00-05:00",
            Event::Energy {
                pred: 3,
                rep: 4,
                hsw: 6.0,
                loc: "lounge".to_string(),
            },
        ),
        entry(
            "2026-06-02T02:00:00-05:00",
            Event::Energy {
                pred: 3,
                rep: 2,
                hsw: 12.0,
                loc: "lounge".to_string(),
            },
        ),
    ]);
    let r = review_of(&replay, &cfg, 2026, 6, 1);
    assert_eq!(r.energy.n, 2);
    // +1 at 20:00 then −1 at 02:00: the sign flips after 02:00.
    assert_eq!(r.energy.flip_hour, Some(2));
}

// ---------------------------------------------------------------------------
// The heat grid across a DST fall-back
// ---------------------------------------------------------------------------

#[test]
fn the_heat_grid_splits_a_segment_across_the_ambiguous_hour() {
    let cfg = fixture::config();
    // 2026-11-01, America/Chicago: 02:00 CDT falls back to 01:00 CST, so a
    // block from 00:30 CDT to 02:30 CST is three hours long and lives in
    // hour 0 (30m), hour 1 (60m CDT + 60m CST) and hour 2 (30m).
    let replay = replay_of(vec![
        wake("2026-11-01T00:00:00-05:00", 480),
        start("2026-11-01T00:30:00-05:00", "z1", 4, 4),
        done("2026-11-01T02:30:00-06:00", "z1", 180, 4),
    ]);
    let r = week_review(
        &empty_tree(&cfg),
        &replay,
        &cfg,
        &Model::default(),
        IsoWeek::parse("2026-W44").unwrap(),
        fixture::TZ,
        &WeekExtras::default(),
    );
    let sunday = r.heat.last().expect("seven days");
    assert_eq!(sunday.date, fixture::date(2026, 11, 1));
    let blocks: Vec<(usize, u32)> = sunday
        .hours
        .iter()
        .enumerate()
        .filter(|(_, h)| h[Style::Block.index()] > 0)
        .map(|(i, h)| (i, h[Style::Block.index()]))
        .collect();
    assert_eq!(blocks, vec![(0, 30), (1, 120), (2, 30)]);
    assert_eq!(sunday.total(Style::Block), 180);
}

// ---------------------------------------------------------------------------
// §11 "Waiting": items in `[?]` with days waiting and timeout
// ---------------------------------------------------------------------------

#[test]
fn the_waiting_monitor_lists_days_waited_and_the_timeout() {
    let cfg = fixture::config();
    let backlog = "\
- [?] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4
- [?] 2 15m Chase the landlord  ^a5
- [ ] 2 15m Not waiting at all  ^a6
";
    let tree = Tree::from_texts(&[("backlog.md", backlog)], &cfg);
    let replay = replay_of(Vec::new());
    let rows = waiting(&tree, &replay, fixture::date(2026, 9, 7), &cfg);
    let ids: Vec<Id> = rows.iter().map(|r| r.id.clone()).collect();
    assert_eq!(ids, vec![Id::new("a4".to_string()), Id::new("a5".to_string())]);
    // waiting:2026-09-05 + 7d → the timeout falls on 2026-09-12, and on
    // 2026-09-07 the item has waited two days.
    assert_eq!(rows[0].days_waiting, 2);
    assert_eq!(rows[0].since, Some(fixture::date(2026, 9, 5)));
    assert_eq!(rows[0].timeout_at, Some(fixture::date(2026, 9, 12)));
    assert!(!rows[0].expired);
    assert_eq!(rows[0].event.as_deref(), Some("reply"));
    // No `waiting:` stamp and no `on-event:`: nothing to count down.
    assert_eq!(rows[1].days_waiting, 0);
    assert_eq!(rows[1].timeout_at, None);
    assert_eq!(rows[1].event, None);
}

#[test]
fn a_wait_past_its_timeout_is_expired() {
    let cfg = fixture::config();
    let backlog =
        "- [?] 2 15m Ask Prof. Lee  on-event:reply/7d waiting:2026-09-05 ^a4\n";
    let tree = Tree::from_texts(&[("backlog.md", backlog)], &cfg);
    let replay = replay_of(Vec::new());
    // §5.1: expired the day *after* the timeout date.
    let rows = waiting(&tree, &replay, fixture::date(2026, 9, 12), &cfg);
    assert!(!rows[0].expired);
    let rows = waiting(&tree, &replay, fixture::date(2026, 9, 13), &cfg);
    assert!(rows[0].expired);
    assert_eq!(rows[0].days_waiting, 8);
}
