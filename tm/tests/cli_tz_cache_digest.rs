//! **`.tm/cache/replay/tz.json` carries a digest of its own text, and a zone table whose digest does
//! not match is probed afresh, never served** — D93's rule for the replay cache's month files and
//! D98's for its checkpoint, reached at the third file of that directory (the W-44 repair, README
//! gap 4613), driven through the binary.
//!
//! **The defect, as the critic drove it.**  The zone table is the one fact of the cache that decides
//! which local DATE an instant falls on.  One offset of a cached table changed by hand or by a disk
//! fault, its `key` kept, was served as written: at 23:58 every verb was refused `nowDisagrees` (the
//! request's `now` and the table disagree about the date), and at 00:10 the evening's twenty
//! minutes were credited to the NEXT day — a day's minutes moved to another date with nothing said,
//! the silent wrong answer D93 names.
//!
//! **The bite is shown first**: the same edit with the digest recomputed — a table a binary could
//! have WRITTEN — is served (D13 trusts what the cache's writer wrote); with the digest as it was,
//! it is not. So it is the digest, and nothing else, that refuses it.

mod cli_common;

use std::fs;

use cli_common::{ckpt_redigested, Tm};

/// The evening the critic drove: a wake at 23:30 on Sunday 2026-09-06, `^m1` 23:35-23:55.
fn evening() -> Tm {
    let tm = Tm::empty();
    tm.ok_at("2026-09-06T23:00:00-05:00", &["init", "--example"]);
    tm.ok_at("2026-09-06T23:30:00-05:00", &["wake", "23:30"]);
    tm.ok_at("2026-09-06T23:35:00-05:00", &["start", "^m1", "--energy", "3"]);
    tm.ok_at("2026-09-06T23:55:00-05:00", &["stop"]);
    tm
}

fn zone_file(tm: &Tm) -> std::path::PathBuf {
    tm.plan.join(".tm/cache/replay/tz.json")
}

/// `tm review day`'s date and block minutes at `now`.
fn reviewed(tm: &Tm, now: &str) -> (String, u64) {
    let v = tm.json_at(now, &["review", "day"]);
    (v["review"]["date"].as_str().expect("a date").to_string(), v["review"]["block_min"].as_u64().expect("block_min"))
}

/// The table with the offset in force from 2026-03-08 (Chicago's spring change) moved from
/// `-05:00:00` to `-03:00:00`, every other byte kept — the digest as it was.
fn planted(tm: &Tm) -> String {
    let text = fs::read_to_string(zone_file(tm)).expect("tz.json");
    let from = "[\"2026-03-08T08:00:00Z\",\"-05:00:00\"]";
    assert_eq!(text.matches(from).count(), 1, "the 2026 spring change, once");
    text.replace(from, "[\"2026-03-08T08:00:00Z\",\"-03:00:00\"]")
}

#[test]
fn the_zone_table_opens_with_the_digest_of_the_rest_of_its_text() {
    let tm = evening();
    let text = fs::read_to_string(zone_file(&tm)).expect("tz.json written by the first capacity verb");
    assert!(text.starts_with("{\"digest\":\""), "{}", &text[..text.len().min(80)]);
    assert_eq!(ckpt_redigested(&text), text, "the digest is the harness's FNV-1a-64 of the rest of the text");
}

/// **The bite**: the planted offset with the digest recomputed is served — the evening's minutes move
/// to Monday; with the digest left as it was, the table is probed afresh and the evening stays
/// Sunday's, at both instants the critic drove, and the file is rewritten with the probe.
#[test]
fn only_the_digest_stands_between_a_changed_offset_and_the_days_minutes() {
    let tm = evening();
    let sunday = ("2026-09-06".to_string(), 20);
    assert_eq!(reviewed(&tm, "2026-09-06T23:58:00-05:00"), sunday);
    assert_eq!(reviewed(&tm, "2026-09-07T00:10:00-05:00"), ("2026-09-07".to_string(), 0));
    let truth = fs::read_to_string(zone_file(&tm)).expect("tz.json");

    let consistent = ckpt_redigested(&planted(&tm));
    fs::write(zone_file(&tm), &consistent).expect("a table a binary could have written");
    assert_eq!(
        reviewed(&tm, "2026-09-07T00:10:00-05:00"),
        ("2026-09-07".to_string(), 20),
        "a table whose digest matches is trusted as written (D13)"
    );

    fs::write(zone_file(&tm), &truth).expect("the table as the binary wrote it");
    fs::write(zone_file(&tm), planted(&tm)).expect("the planted table, its digest as it was");
    assert_ne!(fs::read_to_string(zone_file(&tm)).expect("tz.json"), truth);
    assert_eq!(reviewed(&tm, "2026-09-06T23:58:00-05:00"), sunday, "a table that does not match its digest was served");
    assert_eq!(fs::read_to_string(zone_file(&tm)).expect("rewritten"), truth, "the probe is written back");
    fs::write(zone_file(&tm), planted(&tm)).expect("planted again");
    assert_eq!(reviewed(&tm, "2026-09-07T00:10:00-05:00"), ("2026-09-07".to_string(), 0));
}
