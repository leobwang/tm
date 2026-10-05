//! The walls of the `plan-basic` fixture's week, read as a `WallsByDate`:
//! `calendar/2026-W37.md`'s intervals grouped by the day they start on
//! (meeting Mon 12:50–13:50, CS 234 lecture Wed 15:00–16:20, dinner Thu
//! 19:00–20:00, flight Sat 08:15–10:40).
//!
//! This file held the tests of fork 4748911's own lookahead over that week.
//! R3 deleted the fork's lookahead with the rest of the class it orphans
//! (README gap 4752, W-46 track C §5), and with it every test of that
//! function's own behaviour; the lookahead the binary runs is the kernel's,
//! held to fork 4748911's answers by value in `tm/tests/kernel_lookahead_parity.rs`.
//! What stays is the one test of what the fixture's walls are (README gap 4816).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use chrono::{DateTime, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use tm_core::capacity::{local_dt, WallsByDate};
use tm_core::config::Config;
use tm_core::grammar;
use tm_core::model::Shape;

const TZ: Tz = Tz::America__Chicago;

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn cfg() -> Config {
    Config::load(fixtures().join("plan-basic/config.toml")).unwrap()
}

fn date(s: &str) -> NaiveDate {
    NaiveDate::parse_from_str(s, "%Y-%m-%d").unwrap()
}

fn at(day: &str, h: u32, m: u32) -> DateTime<Tz> {
    local_dt(TZ, date(day), NaiveTime::from_hms_opt(h, m, 0).unwrap())
}

/// The `calendar/2026-W37.md` intervals, grouped by the day they start on.
fn calendar_walls(cfg: &Config) -> WallsByDate {
    let path = "calendar/2026-W37.md";
    let text = std::fs::read_to_string(fixtures().join("plan-basic").join(path)).unwrap();
    let parsed = grammar::parse_file(path, &text, cfg);
    assert!(parsed.problems.is_empty(), "{:?}", parsed.problems);
    let mut out: WallsByDate = BTreeMap::new();
    for item in parsed.items() {
        if let Shape::Interval { start, end } = item.shape {
            let s = local_dt(cfg.tz, start.date(), start.time());
            let e = local_dt(cfg.tz, end.date(), end.time());
            out.entry(start.date()).or_default().push((s, e));
        }
    }
    out
}

#[test]
fn calendar_walls_are_read_from_the_fixture() {
    let cfg = cfg();
    let walls = calendar_walls(&cfg);
    assert_eq!(walls.len(), 4);
    assert_eq!(
        walls[&date("2026-09-07")],
        vec![(at("2026-09-07", 12, 50), at("2026-09-07", 13, 50))]
    );
    assert_eq!(
        walls[&date("2026-09-12")],
        vec![(at("2026-09-12", 8, 15), at("2026-09-12", 10, 40))]
    );
}
