//! The synthetic 14-day log fixture (§17 M8) is generated, not hand-written:
//! `tests/review_common/mod.rs` holds the day-by-day table and turns it into
//! `log::Event`s. This test pins `tm-core/tests/fixtures/logs/review-14d.jsonl` to
//! that table (run with `TM_WRITE_FIXTURES=1` to regenerate the file) and
//! checks that the log the fixture describes replays exactly as the table
//! says it should.

mod review_common;

use std::fs;

use review_common as fixture;
use tm_core::log::SegmentKind;

#[test]
fn the_committed_fixture_is_what_the_generator_produces() {
    let expected = fixture::jsonl();
    if std::env::var("TM_WRITE_FIXTURES").is_ok() {
        fs::create_dir_all(fixture::fixture_path().parent().unwrap()).unwrap();
        fs::write(fixture::fixture_path(), &expected).unwrap();
    }
    let found = fs::read_to_string(fixture::fixture_path()).expect("fixture is committed");
    assert_eq!(
        found, expected,
        "tm-core/tests/fixtures/logs/review-14d.jsonl is out of date; \
         re-run with TM_WRITE_FIXTURES=1"
    );
}

#[test]
fn the_fixture_replays_cleanly_over_fourteen_days() {
    let r = fixture::replay();
    assert_eq!(r.days.len(), 14);
    assert_eq!(r.unknown, 0);
    assert!(r.warnings.is_empty(), "{:?}", r.warnings);

    // 45 timed blocks: 4 on each of the eight standard days (d0, d1, d6, d7,
    // d8, d9, d10 = 7 × 4 = 28), 3 on d2 and d3, 2 on d4, d11 and d12,
    // none on d5 and 5 on d13 → 28 + 6 + 6 + 5 = 45.
    assert_eq!(r.durations.len(), 45);
    // 51 energy observations: one per block start (45) plus the six standalone
    // `energy` events (one on d3, five on d13).
    assert_eq!(r.energy.len(), 45 + 6);
    // Two interruptions: 30 minutes on d6, 55 on d13.
    assert_eq!(r.interrupts.len(), 2);
    // Five demotions: ^m9 on d6, ^m2 and ^m4 on d12, ^t5 on d13.
    assert_eq!(r.demotions.values().flatten().count(), 4);
}

#[test]
fn every_day_but_the_two_with_holes_is_contiguous() {
    let r = fixture::replay();
    // The fixture is laid out so that the only unattributed gaps are the ones
    // the monitors are meant to see: 45 minutes on 2026-09-02.
    for (date, day) in &r.days {
        let expected = if *date == fixture::date(2026, 9, 2) { 45 } else { 0 };
        assert_eq!(day.gap_min(12), expected, "gaps on {date}");
    }
}

#[test]
fn the_review_day_has_the_segments_the_table_describes() {
    let r = fixture::replay();
    let day = r.day(fixture::last_day()).expect("2026-09-07");
    let kinds: Vec<String> = day
        .segments
        .iter()
        .map(|s| match &s.kind {
            SegmentKind::Block { id } => format!("block {id}"),
            SegmentKind::Break { .. } => "break".to_string(),
            SegmentKind::Interrupt { .. } => "interrupt".to_string(),
            SegmentKind::Idle { attributed } => format!("idle {attributed}"),
            SegmentKind::Routine { item, .. } => format!("routine {item}"),
            SegmentKind::Pause { .. } => "pause".to_string(),
        })
        .collect();
    assert_eq!(
        kinds,
        vec![
            "block t1",
            "break",
            "block t2",
            "break",
            "block t3",
            "interrupt",
            "block t3",
            "break",
            "block t4",
            "idle leak",
            "block p1",
            "routine package",
        ]
    );
}
