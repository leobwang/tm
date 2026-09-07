//! `tm review day --write` (§13): the rendered review goes into the day
//! file's `<!-- tm:review start --> … <!-- tm:review end -->` block — the one
//! `horizon::close_day` leaves behind with a `review pending` body (§6.3
//! "the day file gets its review section") — and nothing outside the markers
//! moves (§1.3).

use tm_core::horizon::{REVIEW_BLOCK, REVIEW_PLACEHOLDER};
use tm_core::model::Horizon;
use tm_core::review::write_day_review;
use tm_core::store::{MemStore, Store};

const DAY: &str = "day/2026-09-07.md";

/// A day file as `close_day` leaves it: the generated plan, the human
/// sections, and the review placeholder at the end.
const CLOSED_DAY: &str = "\
---
date: 2026-09-07
---
![day](2026-09-07.svg)
<!-- tm:plan start 10:42 -->
07:00  5 p1 ✓ Read ch.6 §1–2               @m3  1b  (67m)
<!-- tm:plan end -->

# Pinned
- [ ] 2 20m Call the bank about the card  ^p1

## Log
06:05 wake slept=8h10m

## Notes
the afternoon went sideways

<!-- tm:review start -->
review pending
<!-- tm:review end -->
";

fn date() -> chrono::NaiveDate {
    chrono::NaiveDate::from_ymd_opt(2026, 9, 7).unwrap()
}

#[test]
fn the_review_replaces_the_placeholder_and_nothing_else() {
    let store = MemStore::new().with_file(DAY, CLOSED_DAY);
    write_day_review(&store, date(), " Day 2026-09-07 · 5/6 blocks\n done t1 t2").unwrap();
    let text = store.text(DAY).unwrap();
    assert!(
        text.contains("<!-- tm:review start -->\n Day 2026-09-07 · 5/6 blocks\n done t1 t2\n<!-- tm:review end -->"),
        "{text}"
    );
    assert!(!text.contains(REVIEW_PLACEHOLDER));
    // Everything outside the markers is byte-identical.
    let before = CLOSED_DAY.split("<!-- tm:review start -->").next().unwrap();
    assert!(text.starts_with(before), "{text}");
    insta::assert_snapshot!("day_file_with_review", text);
}

#[test]
fn writing_twice_replaces_rather_than_appends() {
    let store = MemStore::new().with_file(DAY, CLOSED_DAY);
    write_day_review(&store, date(), "first").unwrap();
    write_day_review(&store, date(), "second").unwrap();
    let text = store.text(DAY).unwrap();
    assert_eq!(text.matches("<!-- tm:review start -->").count(), 1);
    assert!(text.contains("second"));
    assert!(!text.contains("first"));
}

#[test]
fn a_day_file_without_the_block_gets_one_at_the_end() {
    let plain = "---\ndate: 2026-09-07\n---\n\n## Notes\nnothing yet\n";
    let store = MemStore::new().with_file(DAY, plain);
    write_day_review(&store, date(), "one line").unwrap();
    let text = store.text(DAY).unwrap();
    assert!(text.starts_with(plain), "{text}");
    assert!(
        text.ends_with("<!-- tm:review start -->\none line\n<!-- tm:review end -->\n"),
        "{text}"
    );
}

#[test]
fn a_missing_day_file_is_created_with_its_front_matter() {
    let store = MemStore::new();
    write_day_review(&store, date(), "a review").unwrap();
    let text = store.text(DAY).unwrap();
    assert!(text.starts_with("---\ndate: 2026-09-07\n"), "{text}");
    assert!(text.contains("<!-- tm:review start -->\na review\n<!-- tm:review end -->"));
    // The path is the one §2 gives the day horizon.
    assert_eq!(Horizon::Day(date()).path(), DAY);
    let parsed = store.read_file(DAY).unwrap();
    assert!(parsed.generated(REVIEW_BLOCK).is_some());
}

#[test]
fn a_rendered_review_round_trips_through_the_day_file() {
    let store = MemStore::new().with_file(DAY, CLOSED_DAY);
    let body = " Day 2026-09-07 · lounge · 5/6 blocks\n done      t1 t2 t3\n sleep     8h10m\n";
    write_day_review(&store, date(), body).unwrap();
    let parsed = store.read_file(DAY).unwrap();
    let range = parsed.generated(REVIEW_BLOCK).unwrap();
    let start = range.start_line;
    let end = range.end_line.unwrap();
    let inner: Vec<String> = parsed.lines[start..end - 1]
        .iter()
        .map(|l| l.text().to_string())
        .collect();
    assert_eq!(
        inner,
        vec![
            " Day 2026-09-07 · lounge · 5/6 blocks",
            " done      t1 t2 t3",
            " sleep     8h10m",
        ]
    );
}
