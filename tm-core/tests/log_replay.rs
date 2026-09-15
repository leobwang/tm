//! Replay of the synthetic three-day fixture (`tests/fixtures/logs/
//! three-days.jsonl`): every value below is computed by hand from the
//! fixture. Day 1 mirrors the §10.1 examples; day 2 exercises undo of
//! `done`, `skip`, `stop`, `drop` and `event`, an unknown event, and the
//! wake-to-wake day boundary (its `close` is logged after midnight); day 3
//! has no `wake`, an interruption without an id, and an open paused block.

//!
//! Every replay here is read through the test chokepoint
//! (`tm/tests/support/replay.rs`, step R12). The tests of the reader's own
//! internals (the undo mask, the day index, a ranged replay) live beside it,
//! in `log.rs`'s `reader_tests`, and go with it at the switch.

#[path = "../../tm/tests/support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

use std::path::{Path, PathBuf};

use chrono::{DateTime, FixedOffset, NaiveDate};
use chrono_tz::Tz;
use tm_core::log::{Replay, SegmentKind};
use tm_core::model::{Id, InstanceStatus, Stamp};

const TZ: Tz = Tz::America__Chicago;

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/logs/three-days.jsonl")
}

/// The fixture, replayed over every day through the chokepoint; it has no
/// malformed line.
fn load() -> Replay {
    let text = std::fs::read_to_string(fixture()).unwrap();
    assert!(chokepoint::warning_lines_of_text(&text).is_empty());
    chokepoint::replay_of_text(&text, TZ)
}

fn at(s: &str) -> DateTime<FixedOffset> {
    DateTime::parse_from_rfc3339(s).unwrap()
}

fn d(s: &str) -> NaiveDate {
    NaiveDate::parse_from_str(s, "%Y-%m-%d").unwrap()
}

fn seg_lines(r: &Replay, date: NaiveDate) -> Vec<String> {
    r.day(date)
        .unwrap()
        .segments
        .iter()
        .map(|s| {
            let kind = match &s.kind {
                SegmentKind::Block { id } => format!("block {id}"),
                SegmentKind::Pause { id } => format!("pause {id}"),
                SegmentKind::Interrupt { id } => format!("interrupt {}", id.as_deref().unwrap_or("-")),
                SegmentKind::Break { r#where } => format!("break {}", r#where.as_deref().unwrap_or("-")),
                SegmentKind::Routine { item, inst } => format!("routine {item} {inst}"),
                SegmentKind::Idle { attributed } => format!("idle {attributed}"),
            };
            format!(
                "{}-{} {} {}m",
                s.start.with_timezone(&TZ).format("%H:%M"),
                s.end.with_timezone(&TZ).format("%H:%M"),
                kind,
                s.minutes()
            )
        })
        .collect()
}

#[test]
fn day_one_matches_hand_computed_values() {
    let r = load();
    let d7 = d("2026-09-07");
    let day = r.day(d7).unwrap();
    assert_eq!(day.wake, Some(at("2026-09-07T06:05:00-05:00")));
    assert_eq!((day.slept_min, day.onset_min), (Some(490), None));
    assert_eq!(day.arrival, Some(at("2026-09-07T07:00:00-05:00")));
    assert_eq!(day.loc.as_deref(), Some("lounge"));
    assert_eq!(day.window, Some(["07:00".to_string(), "15:00".to_string()]));
    assert_eq!(day.budget, Some(6));
    assert_eq!(day.wake_to_arrive_min(), Some(55));
    assert_eq!(day.arrive_to_start_min(), Some(2));
    assert_eq!(day.loc_changes.len(), 2);
    assert_eq!(day.loc_changes[1].1, "home");
    // t1 67 + t2 58 + t3 138 (partial) + t4 45 (12:00–12:10, 13:05–13:20,
    // 13:30–13:50, cut by stop) + t5 60 + a3 0 (retro).
    assert_eq!(day.block_min, 368);
    assert_eq!(r.block_minutes_on_day(d7), 368);
    assert_eq!(day.blocks_done, 4, "t1 t2 t3 t5; the retro done is not a block");
    assert_eq!(r.blocks_done(d7), 4);
    assert_eq!(day.done, vec!["t1", "t2", "t5", "a3"]);
    assert_eq!(day.starts.len(), 5);
    assert_eq!(day.starts[3].rep, None);
    assert_eq!(day.minutes_by_ci, [0, 0, 0, 60, 138, 125]);
    assert_eq!(day.high_ci_min(), 263);
    assert!((day.load() - 271.4).abs() < 1e-9, "{}", day.load());
    assert_eq!((day.lost_min, day.leak_min, day.longest_leak), (55, 14, 14));
    assert_eq!(day.dropped, vec!["t5"]);
    assert_eq!(day.idle.len(), 1);
    assert_eq!(day.breaks.len(), 1);
    assert_eq!(day.breaks[0].actual_or_planned(), 24);
    assert_eq!(day.breaks[0].r#where.as_deref(), Some("walk"));
    assert_eq!(day.break_min(), 24);
    assert_eq!(day.routine_min, 48);
    assert_eq!((day.plans, day.replans_today, day.drift_min), (3, 4, 75));
    assert_eq!(day.last_plan_hash.as_deref(), Some("c3d5"));
    assert_eq!(
        seg_lines(&r, d7),
        vec![
            "07:02-08:09 block t1 67m",
            "08:10-09:08 block t2 58m",
            "09:08-09:32 break walk 24m",
            "09:32-11:50 block t3 138m",
            "11:20-11:50 routine lunch 2026-09-07 30m",
            "12:00-12:10 block t4 10m",
            "12:10-13:05 interrupt t4 55m",
            "13:05-13:20 block t4 15m",
            "13:20-13:30 pause t4 10m",
            "13:30-13:50 block t4 20m",
            "14:05-15:05 block t5 60m",
            "15:26-15:40 idle leak 14m",
            "15:52-16:10 routine package 2026-09-07 18m",
        ]
    );
    // Unattributed gaps ≥ 12m (`config.day.idle_min`) between the first and
    // last logged segment: 13:50→14:05, 15:05→15:26, 15:40→15:52. The
    // 08:09→08:10 and 11:50→12:00 holes are shorter; the 15:26→15:40 leak is
    // attributed, so it is not a gap; the lunch routine inside the t3 block
    // makes no hole.
    let gaps: Vec<String> = day
        .gaps(12)
        .iter()
        .map(|(s, e)| {
            format!(
                "{}-{}",
                s.with_timezone(&TZ).format("%H:%M"),
                e.with_timezone(&TZ).format("%H:%M")
            )
        })
        .collect();
    assert_eq!(gaps, vec!["13:50-14:05", "15:05-15:26", "15:40-15:52"]);
    assert_eq!(day.gap_min(12), 48);
    assert_eq!(day.gap_min(60), 0);
    // Energy: t1, t2 (starts), the 09:32 report, t3, t5; t4 had no report.
    let obs: Vec<_> = r.energy_on(d7).collect();
    assert_eq!(obs.len(), 5);
    assert_eq!(obs[0].id.as_deref(), Some("t1"));
    assert_eq!((obs[0].pred, obs[0].rep, obs[0].went), (5, 5, Some(1)));
    assert_eq!(obs[0].slept_min, Some(490));
    assert!(!obs[2].from_start);
    assert_eq!((obs[2].pred, obs[2].rep, obs[2].delta()), (5, 4, -1));
    assert_eq!(obs[2].slept_min, Some(490), "from the day's wake");
    assert_eq!((obs[3].id.as_deref(), obs[3].went, obs[3].weight()), (Some("t3"), Some(2), 1.5));
    assert_eq!(obs[4].loc, "home");
    // Durations: one per timed block; the stop and the retro done give none.
    let dur: Vec<_> = r.durations_on(d7).collect();
    assert_eq!(dur.len(), 4);
    assert_eq!(dur[0].ratio(), Some(67.0 / 60.0));
    assert_eq!(dur[0].tags, vec!["lean"]);
    assert_eq!((dur[2].id.as_str(), dur[2].est_min, dur[2].actual_min, dur[2].partial), ("t3", 120, 138, true));
    assert_eq!(dur[3].ci, 3);
    // Items.
    assert_eq!(r.block_minutes("t1"), 67);
    assert_eq!(r.block_minutes("t4"), 45);
    assert_eq!(r.block_minutes("a3"), 0);
    assert_eq!(r.items["t3"].extended_min, 60);
    assert_eq!(r.items["t4"].stops, 1);
    assert_eq!(r.items["t3"].partial_done_at.len(), 1);
    assert_eq!(r.items["a3"].done_at, vec![at("2026-09-07T18:00:00-05:00")]);
    assert!(r.is_done("a3") && r.is_done("t1") && !r.is_done("t4"));
    // Instances and events.
    assert_eq!(r.instance_status("lunch", "2026-09-07"), InstanceStatus::Done);
    assert_eq!(r.instance("lunch", "2026-09-07").unwrap().actual_min, Some(30));
    assert_eq!(r.instance_status("workout", "2026-09-07"), InstanceStatus::Skipped);
    assert_eq!(r.instance_status("package", "2026-09-07"), InstanceStatus::Done);
    assert_eq!(r.instance_status("package", "2026-09-08"), InstanceStatus::Pending);
    assert_eq!(r.last_done("lunch"), Some(at("2026-09-07T11:50:00-05:00")));
    assert_eq!(r.done_dates("package"), vec![d7]);
    assert_eq!(r.events_named("reply").len(), 1);
    assert_eq!(r.events_named("reply")[0].id.as_deref(), Some("a4"));
    assert_eq!(r.events_for("a4").len(), 1);
    assert!(r.event_occurred("reply", None, Some("a4")));
    assert!(!r.event_occurred("reply", Some(at("2026-09-07T17:01:00-05:00")), None));
    assert_eq!(r.interrupts_on(d7).count(), 1);
    assert_eq!(r.interrupts[0].id.as_deref(), Some("t4"));
    assert_eq!(r.interrupts[0].lost_min, 55);
    assert_eq!(r.interrupts[0].start, Some(at("2026-09-07T12:10:00-05:00")));
}

#[test]
fn day_two_applies_undo_and_the_midnight_close() {
    let r = load();
    let d8 = d("2026-09-08");
    let day = r.day(d8).unwrap();
    assert_eq!((day.slept_min, day.onset_min), (Some(400), Some(35)));
    assert_eq!(day.loc.as_deref(), Some("home"));
    // t3 65 + t6 62 (the undone 60 does not count) + t7 45 (the undone stop
    // would have credited 30 more).
    assert_eq!(day.block_min, 172);
    assert_eq!(day.blocks_done, 3);
    assert_eq!(day.done, vec!["t3", "t6", "t7"]);
    assert_eq!(r.block_minutes("t6"), 62);
    assert_eq!(r.block_minutes("t7"), 45);
    assert_eq!(r.items["t7"].stops, 0, "the stop was undone");
    assert_eq!(r.items["t6"].done_at.len(), 1);
    assert!((day.load() - 116.2).abs() < 1e-9, "{}", day.load());
    assert_eq!((day.lost_min, day.leak_min, day.longest_leak), (0, 37, 25));
    assert_eq!(day.idle.len(), 3, "work 3, leak 25, leak 12");
    assert_eq!(day.idle[0].attributed, "work");
    assert_eq!(day.breaks[0].actual_min, None);
    assert_eq!(day.break_min(), 20, "planned when no actual");
    assert_eq!(day.routine_min, 15);
    assert_eq!((day.plans, day.replans_today, day.drift_min), (2, 2, 30));
    assert_eq!(
        seg_lines(&r, d8),
        vec![
            "07:35-08:40 block t3 65m",
            "08:45-09:05 break - 20m",
            "09:05-10:07 block t6 62m",
            "10:07-10:10 idle work 3m",
            "10:15-11:00 block t7 45m",
            "10:45-11:00 routine shower #3 15m",
            "11:35-12:00 idle leak 25m",
            "12:18-12:30 idle leak 12m",
        ]
    );
    // Energy: t3 (went 3 → double weight), t6 (went from the redone done),
    // the 14:10 report; t7 had no report.
    let obs: Vec<_> = r.energy_on(d8).collect();
    assert_eq!(obs.len(), 3);
    assert_eq!((obs[0].went, obs[0].weight()), (Some(3), 2.0));
    assert_eq!((obs[1].id.as_deref(), obs[1].went), (Some("t6"), Some(1)));
    assert_eq!((obs[2].rep, obs[2].slept_min), (2, Some(400)));
    assert_eq!(r.durations_on(d8).count(), 3);
    // Undo results.
    assert_eq!(r.instance_status("laundry", "2026-09-08"), InstanceStatus::Pending, "skip undone");
    assert_eq!(r.instance_status("laundry", "2026-09-07"), InstanceStatus::Missed);
    assert_eq!(r.instance_status("breakfast", "2026-09-08"), InstanceStatus::Expired);
    assert_eq!(r.instance_status("shower", "#3"), InstanceStatus::Done);
    assert_eq!(r.instances_of("laundry").map(|(k, _)| k).collect::<Vec<_>>(), vec!["2026-09-07"]);
    assert!(r.dropped_items.is_empty(), "drop undone");
    assert!(r.events_named("visa").is_empty(), "event undone");
    assert_eq!(r.events.len(), 1);
    // Completion bookkeeping across days.
    assert!(r.is_done("t3"));
    assert_eq!(r.last_done("t3"), Some(at("2026-09-08T08:40:00-05:00")));
    assert_eq!(r.done_dates("t3"), vec![d8], "the day-1 done was partial");
    assert_eq!(r.done_dates("shower"), vec![d8], "ordinal instance → the day");
    assert_eq!(r.last_done("shower"), Some(at("2026-09-08T11:00:00-05:00")));
    assert_eq!(r.block_minutes("t3"), 203);
    assert_eq!(r.block_minutes_on("t3", d8), 65);
    // Demotion, drop-less, unknown, closes.
    assert_eq!(r.stamps("m2"), vec![Stamp::Week(37)]);
    assert_eq!(r.demotions["m2"][0].est_min, 180);
    assert_eq!(r.stamps("m9"), vec![]);
    assert_eq!(r.unknown, 1);
    assert_eq!(r.closes.len(), 2);
    assert_eq!(r.closes[1].key, "2026-09-08");
    assert_eq!(r.longest_leak.as_ref().map(|l| (l.day, l.min)), Some((d8, 25)));
    assert!(r.warnings.is_empty(), "{:?}", r.warnings);
}

#[test]
fn day_three_has_no_wake_and_an_open_block() {
    let r = load();
    let d9 = d("2026-09-09");
    let day = r.day(d9).unwrap();
    assert_eq!(day.wake, None);
    assert_eq!(day.arrival, Some(at("2026-09-09T09:00:00-05:00")));
    assert_eq!(day.block_min, 60, "the open block earns nothing yet");
    assert_eq!(day.blocks_done, 1);
    assert!(day.done.is_empty(), "only a partial done");
    assert_eq!(day.lost_min, 15);
    assert_eq!(
        seg_lines(&r, d9),
        vec![
            "09:05-10:05 block t8 60m",
            "10:05-10:20 block t8 15m",
            "10:20-10:35 interrupt t8 15m",
            "10:35-10:50 block t8 15m",
        ]
    );
    assert_eq!(r.interrupts.len(), 2);
    assert_eq!(r.interrupts[1].id.as_deref(), Some("t8"), "taken from the running block");
    let obs: Vec<_> = r.energy_on(d9).collect();
    assert_eq!(obs.len(), 2);
    assert_eq!(obs[0].went, Some(1));
    assert_eq!(obs[1].went, None, "the second block is still open");
    assert_eq!(obs[0].slept_min, Some(0));
    let open = r.open_block.as_ref().unwrap();
    assert_eq!((open.id.as_str(), open.worked_min, open.paused, open.since), ("t8", 30, true, None));
    assert_eq!(open.started, at("2026-09-09T10:05:00-05:00"));
    assert!(r.open_interrupt.is_none());
    assert!(!r.is_done("t8"));
    assert_eq!(r.block_minutes("t8"), 60);
    // Whole-log totals.
    assert_eq!(r.total_block_min(), 600);
    assert_eq!(r.energy.len(), 10);
    assert_eq!(r.durations.len(), 8);
    assert_eq!(r.done_items.len(), 10);
    assert_eq!(r.days.len(), 3);
    assert_eq!(r.breaks().count(), 2);
    assert_eq!(r.items.len(), 9);
    // The map `tree::done_minutes` (§6.4) consumes.
    let minutes = r.done_minutes_map();
    assert_eq!(minutes.len(), 9);
    assert_eq!(minutes[&Id::new("t3")], 203);
    assert_eq!(minutes[&Id::new("a3")], 0, "retro done, no block");
}

#[test]
fn replay_is_json_safe_and_snapshotted() {
    let r = load();
    let json = serde_json::to_string(&r).unwrap();
    let back: Replay = serde_json::from_str(&json).unwrap();
    assert_eq!(back, r);
    insta::assert_yaml_snapshot!("three_days_replay", r);
}

/// Design §11.2, step R13: every observation carries the physical line of the
/// entry it came from (a `start`'s observation the start's line, a duration
/// its `done`'s), and `energy` and `durations` are in that order, which is
/// file order.
#[test]
fn observations_carry_their_source_line() {
    let r = load();
    let row = |line: u64| {
        r.view()
            .iter()
            .find(|row| row.line == line)
            .unwrap_or_else(|| panic!("no entry on line {line}"))
    };
    assert_eq!(r.energy.len(), 10);
    for o in &r.energy {
        let row = row(o.line);
        assert!(!row.cancelled, "line {}", o.line);
        assert_eq!(row.entry.t, o.t, "line {}", o.line);
        match &row.entry.ev {
            tm_core::log::Event::Start { id, .. } => {
                assert!(o.from_start);
                assert_eq!(o.id.as_deref(), Some(id.as_str()));
            }
            tm_core::log::Event::Energy { .. } => assert!(!o.from_start),
            other => panic!("line {}: {other:?} is not an observation", o.line),
        }
    }
    assert_eq!(r.durations.len(), 8);
    for o in &r.durations {
        let row = row(o.line);
        assert!(!row.cancelled, "line {}", o.line);
        assert_eq!(row.entry.t, o.t, "line {}", o.line);
        assert!(
            matches!(&row.entry.ev, tm_core::log::Event::Done { id, .. } if *id == o.id),
            "line {}",
            o.line
        );
    }
    assert!(r.energy.windows(2).all(|w| w[0].line < w[1].line));
    assert!(r.durations.windows(2).all(|w| w[0].line < w[1].line));
    // Line 5 is day 1's first `done` (t1), line 4 its `start`.
    assert_eq!((r.energy[0].line, r.durations[0].line), (4, 5));
}
