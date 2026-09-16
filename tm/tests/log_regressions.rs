//! Regression tests for the review findings on `log.rs`: the ci accounting of
//! block minutes (§11 blocks/load and energy mix), pause segments (§11 leak
//! ledger, §12.1 day bar), `done` after `stop` (§6.4 `done_minutes`), reading
//! a log with a corrupt line (§10.1 "never fail on content"), appending after
//! a torn write, a stray `unpause`, arithmetic that must not panic, the day a
//! `wake` logged out of order belongs to, and two `wake`s on one date.

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

use std::path::{Path, PathBuf};

use chrono::{DateTime, FixedOffset, NaiveDate};
use chrono_tz::Tz;
use tm_core::log::{Event, LogEntry, Replay};

const TZ: Tz = Tz::America__Chicago;

fn at(s: &str) -> DateTime<FixedOffset> {
    DateTime::parse_from_rfc3339(s).unwrap()
}

fn d(s: &str) -> NaiveDate {
    NaiveDate::parse_from_str(s, "%Y-%m-%d").unwrap()
}

fn e(t: &str, ev: Event) -> LogEntry {
    LogEntry::new(at(t), ev)
}

fn wake(t: &str, slept_min: u32) -> LogEntry {
    e(t, Event::Wake { slept_min, onset_min: None })
}

fn start(t: &str, id: &str) -> LogEntry {
    e(
        t,
        Event::Start {
            id: id.into(),
            pred: 4,
            rep: Some(4),
            hsw: 3.0,
            slept_min: 480,
            loc: "lounge".into(),
            blocks_done: 0,
            since_break_min: 0,
        },
    )
}

fn done(t: &str, id: &str, actual_min: u32, ci: u8) -> LogEntry {
    e(
        t,
        Event::Done {
            id: id.into(),
            est_min: 60,
            actual_min,
            went: Some(1),
            tags: vec![],
            ci,
            partial: false,
        },
    )
}

fn stop(t: &str, id: &str, remaining_min: u32) -> LogEntry {
    e(t, Event::Stop { id: id.into(), remaining_min })
}

fn replay_of(entries: Vec<LogEntry>) -> Replay {
    chokepoint::replay_of_entries(&entries, TZ)
}

/// [`replay_of`] keeping the kernel's named refusal (design §17's P17).
fn try_replay_of(entries: Vec<LogEntry>) -> Result<Replay, String> {
    chokepoint::try_replay_of_text(&chokepoint::text_of(&entries), TZ)
}

fn seg_lines(r: &Replay, date: NaiveDate) -> Vec<String> {
    r.day(date)
        .unwrap()
        .segments
        .iter()
        .map(|s| {
            format!(
                "{}-{} {:?}",
                s.start.with_timezone(&TZ).format("%H:%M"),
                s.end.with_timezone(&TZ).format("%H:%M"),
                s.kind
            )
        })
        .collect()
}

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-core/tests/fixtures/logs/three-days.jsonl")
}

/// §11: `load = Σ block_min × ci / 5` and the energy mix need a ci for every
/// logged block minute, but `stop` carries none. The minutes of a cut block
/// must therefore be visible as *ci-unknown* rather than silently missing, so
/// `Σ minutes_by_ci + ci_unknown_min == block_min` always holds and `review.rs`
/// knows exactly which items it has to look up in the tree.
#[test]
fn cut_block_minutes_are_accounted_as_ci_unknown() {
    let r = replay_of(vec![
        wake("2026-09-07T06:00:00-05:00", 480),
        start("2026-09-07T09:00:00-05:00", "a"),
        stop("2026-09-07T10:00:00-05:00", "a", 30),
        start("2026-09-07T10:00:00-05:00", "b"),
        done("2026-09-07T11:00:00-05:00", "b", 60, 4),
    ]);
    let day = r.day(d("2026-09-07")).unwrap();
    assert_eq!(day.block_min, 120);
    assert_eq!(day.minutes_by_ci.iter().sum::<u32>(), 60, "only b's ci is logged");
    assert_eq!(day.ci_unknown_min(), 60, "a was cut by `stop`, which has no ci");
    assert_eq!(day.ci_unknown.get("a").copied(), Some(60));
    assert_eq!(
        day.minutes_by_ci.iter().sum::<u32>() + day.ci_unknown_min(),
        day.block_min,
        "every block minute is either attributed to a ci or listed as unknown"
    );
    assert_eq!(day.load(), 48.0, "load covers the minutes whose ci is known");

    // The same identity on every day of the three-day fixture (day 1 has the
    // 45 minutes of `t4`, cut by `stop`, with no ci in the log).
    let r = chokepoint::replay_of_text(&std::fs::read_to_string(fixture()).unwrap(), TZ);
    assert_eq!(r.day(d("2026-09-07")).unwrap().ci_unknown_min(), 45);
    assert_eq!(r.day(d("2026-09-08")).unwrap().ci_unknown_min(), 0);
    for day in r.days.values() {
        assert_eq!(
            day.minutes_by_ci.iter().sum::<u32>() + day.ci_unknown_min(),
            day.block_min,
            "{}",
            day.date
        );
    }
}

/// §13 has `tm pause` but no `tm unpause`, so a block closed while still
/// paused is the ordinary path. The paused stretch must still become a
/// `Pause` segment (§12.1 day bar) instead of an unattributed gap that the
/// §11 leak ledger would charge as leak.
#[test]
fn a_pause_closed_by_done_still_becomes_a_segment() {
    let r = replay_of(vec![
        wake("2026-09-07T06:00:00-05:00", 480),
        start("2026-09-07T09:00:00-05:00", "a"),
        e("2026-09-07T09:30:00-05:00", Event::Pause { id: "a".into() }),
        done("2026-09-07T10:30:00-05:00", "a", 30, 3),
        start("2026-09-07T10:35:00-05:00", "b"),
        done("2026-09-07T11:35:00-05:00", "b", 60, 3),
    ]);
    let d7 = d("2026-09-07");
    assert_eq!(
        seg_lines(&r, d7),
        vec![
            "09:00-09:30 Block { id: \"a\" }",
            "09:30-10:30 Pause { id: \"a\" }",
            "10:35-11:35 Block { id: \"b\" }",
        ]
    );
    let day = r.day(d7).unwrap();
    assert_eq!(day.gaps(12), vec![], "the pause is not an unattributed gap");
    assert_eq!(day.gap_min(12), 0);

    // A `stop` while paused closes the pause the same way, and so does the
    // start of the next block.
    let r = replay_of(vec![
        wake("2026-09-07T06:00:00-05:00", 480),
        start("2026-09-07T09:00:00-05:00", "a"),
        e("2026-09-07T09:30:00-05:00", Event::Pause { id: "a".into() }),
        stop("2026-09-07T10:00:00-05:00", "a", 30),
        start("2026-09-07T10:00:00-05:00", "b"),
        e("2026-09-07T10:20:00-05:00", Event::Pause { id: "b".into() }),
        start("2026-09-07T10:40:00-05:00", "c"),
    ]);
    assert_eq!(
        seg_lines(&r, d7),
        vec![
            "09:00-09:30 Block { id: \"a\" }",
            "09:30-10:00 Pause { id: \"a\" }",
            "10:00-10:20 Block { id: \"b\" }",
            "10:20-10:40 Pause { id: \"b\" }",
        ]
    );
    assert_eq!(r.block_minutes("a"), 30, "paused minutes are not worked minutes");
    assert_eq!(r.block_minutes("b"), 20);

    // An interruption inside a pause splits the two without overlapping, and
    // the block stays paused after the resume.
    let r = replay_of(vec![
        wake("2026-09-07T06:00:00-05:00", 480),
        start("2026-09-07T09:00:00-05:00", "a"),
        e("2026-09-07T09:30:00-05:00", Event::Pause { id: "a".into() }),
        e("2026-09-07T09:40:00-05:00", Event::Interrupt { id: None }),
        e("2026-09-07T09:50:00-05:00", Event::Resume { lost_min: 10, dropped: vec![] }),
        e("2026-09-07T10:00:00-05:00", Event::Unpause { id: "a".into() }),
        stop("2026-09-07T10:30:00-05:00", "a", 0),
    ]);
    assert_eq!(
        seg_lines(&r, d7),
        vec![
            "09:00-09:30 Block { id: \"a\" }",
            "09:30-09:40 Pause { id: \"a\" }",
            "09:40-09:50 Interrupt { id: Some(\"a\") }",
            "09:50-10:00 Pause { id: \"a\" }",
            "10:00-10:30 Block { id: \"a\" }",
        ]
    );
    assert_eq!(r.block_minutes("a"), 60, "30 before the pause + 30 after the unpause");
}

/// §10.1: `done.actual_min` is authoritative for the block's minutes. A
/// `done` that closes a block already cut by `stop` must replace the partial
/// credit, not add to it — `done_minutes` (§6.4) and `progress` read this.
#[test]
fn done_after_stop_replaces_the_partial_credit() {
    let d7 = d("2026-09-07");
    let r = replay_of(vec![
        wake("2026-09-07T06:00:00-05:00", 480),
        start("2026-09-07T09:00:00-05:00", "a"),
        stop("2026-09-07T10:00:00-05:00", "a", 30),
        done("2026-09-07T10:01:00-05:00", "a", 60, 4),
    ]);
    assert_eq!(r.block_minutes("a"), 60, "60 worked minutes, logged twice");
    assert_eq!(r.block_minutes_on("a", d7), 60);
    assert_eq!(r.day(d7).unwrap().block_min, 60);
    assert_eq!(r.day(d7).unwrap().minutes_by_ci[4], 60);
    assert_eq!(r.day(d7).unwrap().ci_unknown_min(), 0, "the ci is known after all");
    assert_eq!(r.done_minutes_map()[&tm_core::model::Id::new("a")], 60);

    // A retro `tm done ^id` (actual_min 0) after a stop keeps the worked
    // minutes: there is nothing authoritative to replace them with.
    let r = replay_of(vec![
        wake("2026-09-07T06:00:00-05:00", 480),
        start("2026-09-07T09:00:00-05:00", "a"),
        stop("2026-09-07T10:00:00-05:00", "a", 30),
        done("2026-09-07T10:01:00-05:00", "a", 0, 4),
    ]);
    assert_eq!(r.block_minutes("a"), 60);
    assert!(r.is_done("a"));

    // A `done` for an item cut long ago, with another block in between, is a
    // separate block and still adds.
    let r = replay_of(vec![
        wake("2026-09-07T06:00:00-05:00", 480),
        start("2026-09-07T09:00:00-05:00", "a"),
        stop("2026-09-07T10:00:00-05:00", "a", 30),
        start("2026-09-07T10:00:00-05:00", "b"),
        done("2026-09-07T11:00:00-05:00", "b", 60, 3),
        done("2026-09-07T11:01:00-05:00", "a", 30, 3),
    ]);
    assert_eq!(r.block_minutes("a"), 90);
    assert_eq!(r.block_minutes("b"), 60);
}



/// An `unpause` with no matching `pause` (a duplicate keypress, or a `pause`
/// removed by `tm undo`) must be a no-op, not a reset of the block's clock.
#[test]
fn a_stray_unpause_keeps_the_worked_minutes() {
    let r = replay_of(vec![
        wake("2026-09-07T06:00:00-05:00", 480),
        start("2026-09-07T09:00:00-05:00", "a"),
        e("2026-09-07T09:40:00-05:00", Event::Unpause { id: "a".into() }),
        stop("2026-09-07T10:00:00-05:00", "a", 0),
    ]);
    assert_eq!(r.block_minutes("a"), 60);
    assert_eq!(
        seg_lines(&r, d("2026-09-07")),
        vec!["09:00-10:00 Block { id: \"a\" }"]
    );

    // A second `unpause` after a real one is a no-op too.
    let r = replay_of(vec![
        wake("2026-09-07T06:00:00-05:00", 480),
        start("2026-09-07T09:00:00-05:00", "a"),
        e("2026-09-07T09:30:00-05:00", Event::Pause { id: "a".into() }),
        e("2026-09-07T09:40:00-05:00", Event::Unpause { id: "a".into() }),
        e("2026-09-07T09:50:00-05:00", Event::Unpause { id: "a".into() }),
        stop("2026-09-07T10:00:00-05:00", "a", 0),
    ]);
    assert_eq!(r.block_minutes("a"), 50);
}

/// Nothing in a syntactically valid log line may make a read **panic** (§10.1:
/// log content is never fatal) — and since S, a minute sum past `u32::MAX` is
/// **refused by name** rather than saturated.
///
/// This is design §17's parity **P17**, which reads: "minute and count sums
/// above `2^32 − 1` | `Nat`; the Rust decoder refuses `minutesOverflow` by name
/// | `saturating_add`". Before the switch the in-tree reader took the fork's
/// column and pinned every field at `u32::MAX`; the kernel takes the other one.
/// The test is retargeted at the row, not weakened: what it asserts is still
/// "this input does not panic", plus the stronger half — that the refusal
/// **names** what overflowed, which a saturating sum could never tell you.
#[test]
fn absurd_minute_counts_are_refused_by_name_not_saturated() {
    let huge = 3_000_000_000u32;
    let r = try_replay_of(vec![
        wake("2026-09-07T06:00:00-05:00", 480),
        done("2026-09-07T09:00:00-05:00", "a", huge, 5),
        done("2026-09-07T10:00:00-05:00", "a", huge, 5),
        e("2026-09-07T11:00:00-05:00", Event::Extend { id: "a".into(), by_min: huge }),
        e("2026-09-07T11:01:00-05:00", Event::Extend { id: "a".into(), by_min: huge }),
        e("2026-09-07T12:00:00-05:00", Event::Idle { attributed: "leak".into(), min: huge }),
        e("2026-09-07T12:01:00-05:00", Event::Idle { attributed: "leak".into(), min: huge }),
        e("2026-09-07T13:00:00-05:00", Event::Resume { lost_min: huge, dropped: vec![] }),
        e("2026-09-07T13:01:00-05:00", Event::Resume { lost_min: huge, dropped: vec![] }),
        e(
            "2026-09-07T14:00:00-05:00",
            Event::Break { planned_min: huge, actual_min: None, r#where: None },
        ),
        e(
            "2026-09-07T14:01:00-05:00",
            Event::Break { planned_min: huge, actual_min: None, r#where: None },
        ),
        e(
            "2026-09-07T15:00:00-05:00",
            Event::Plan { hash: "x".into(), replans_today: 1, drift_min: huge },
        ),
        e(
            "2026-09-07T15:01:00-05:00",
            Event::Plan { hash: "x".into(), replans_today: 2, drift_min: huge },
        ),
    ]);
    let why = r.expect_err("the kernel saturated a minute sum instead of refusing it");
    assert!(
        why.contains("minutesOverflow"),
        "the refusal does not name P17's overflow: {why}"
    );
    // Named, not merely refused: the field that overflowed is in the message,
    // which is the whole of §17's P15 ("named constructors where the fork had
    // serde's free text") applied to this row.
    assert!(
        why.contains("leakMin") || why.contains("Min") || why.contains("min"),
        "the refusal names no field: {why}"
    );
    eprintln!("P17: a minute sum past u32::MAX is refused by name — {why}");
}

/// `tm wake 06:05` typed at 09:40, after `tm energy 4` was already logged,
/// appends the `wake` line *after* the `energy` line. The energy observation
/// must still carry the day's `slept_min`, which §8.5 fits the sleep term on.
#[test]
fn an_energy_report_logged_before_its_wake_still_gets_slept_min() {
    let r = replay_of(vec![
        e(
            "2026-09-07T09:32:00-05:00",
            Event::Energy { pred: 5, rep: 4, hsw: 3.45, loc: "lounge".into() },
        ),
        wake("2026-09-07T06:05:00-05:00", 480),
    ]);
    let day = r.day(d("2026-09-07")).unwrap();
    assert_eq!(day.slept_min, Some(480));
    assert_eq!(r.energy.len(), 1);
    assert_eq!(r.energy[0].slept_min, Some(480), "taken from the day, not the file order");
}

/// §12.1: one row per 24 h from wake to wake. A second `tm wake` on the same
/// date (a nap, or a re-run of the verb) must not stretch that day to 38 h and
/// swallow the next morning.
#[test]
fn two_wakes_on_one_date_do_not_stretch_the_day() {
    let d7 = d("2026-09-07");
    let d8 = d("2026-09-08");
    // `DayIndex` went at S with the rest of the reader (design §12). The claim
    // it carried is unchanged and is made here where a verb can still see it:
    // the wake-attributed day of each entry, in the replay's own view rows.
    // Only the **first** `wake` of a date counts, so an afternoon nap must not
    // stretch the 7th to 38 h and swallow the next morning.
    let attributed = replay_of(vec![
        wake("2026-09-07T06:05:00-05:00", 480),
        wake("2026-09-07T14:00:00-05:00", 60),
        e("2026-09-07T15:00:00-05:00", Event::Note { text: "afternoon".into() }),
        e("2026-09-08T10:00:00-05:00", Event::Note { text: "next morning".into() }),
    ]);
    let day_of_line = |line: u64| attributed.view().iter().find(|r| r.line == line).map(|r| r.day);
    assert_eq!(day_of_line(1), Some(d7), "the first wake");
    assert_eq!(day_of_line(2), Some(d7), "the nap belongs to the day it falls in");
    assert_eq!(day_of_line(3), Some(d7), "the afternoon");
    assert_eq!(day_of_line(4), Some(d8), "the next morning, not the 7th");
    assert_eq!(
        attributed.day(d7).and_then(|x| x.wake),
        Some(at("2026-09-07T06:05:00-05:00")),
        "one wake per date: the first one"
    );
    // (Deliberately not asserted: `days` gains a key only for a day with a
    // *record*, and the next morning here holds nothing but a note. The claim
    // is the attribution, and the view rows above are where it is visible.)

    // Replay attributes the next morning's work to the next day.
    let r = replay_of(vec![
        wake("2026-09-07T06:05:00-05:00", 480),
        wake("2026-09-07T14:00:00-05:00", 60),
        start("2026-09-08T10:00:00-05:00", "a"),
        done("2026-09-08T11:00:00-05:00", "a", 60, 3),
    ]);
    assert_eq!(r.block_minutes_on("a", d8), 60);
    assert_eq!(r.blocks_done(d8), 1);
    assert_eq!(r.blocks_done(d7), 0);
    assert_eq!(r.day(d7).unwrap().slept_min, Some(480), "the first wake of the day");
}
