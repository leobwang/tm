//! `ics.rs` against the `sample.ics` fixture — tm-spec-v1.md §15 and the M9
//! definition of done: "sync against a fixture `.ics` preserves manual lines
//! and stable ids".
//!
//! The fixture holds a one-off meeting with a `TZID`, a UTC event, an all-day
//! event, a weekly lecture (`BYDAY` + `EXDATE`), a flight, a multi-day event
//! with a folded `SUMMARY`, a multi-day event that is already under way when
//! the window opens, another that spans two written weeks, a `DURATION`-only
//! daily series, a monthly series that starts before the window, a cancelled
//! event, a floating event and two summaries that would break the line
//! grammar if written verbatim.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use chrono::NaiveDate;
use tm_core::config::Config;
use tm_core::grammar::{parse_line, ParseCtx};
use tm_core::ics::{
    events_in_window, merge_calendar_file, parse_ics_report, render_calendar_lines,
    render_calendar_weeks, sync, sync_report, window_for_week, CalEvent, IcsError, ParseOptions,
    StaticFetcher,
};
use tm_core::model::{Id, IsoWeek, Shape};

const URL: &str = "https://calendar.example.test/private/basic.ics";

/// The Monday of the week the fixture is written around.
fn today() -> NaiveDate {
    NaiveDate::from_ymd_opt(2026, 9, 7).unwrap()
}

fn week() -> IsoWeek {
    IsoWeek::from_date(today())
}

fn fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/sample.ics")
}

fn sample() -> String {
    std::fs::read_to_string(fixture_path()).unwrap()
}

/// The §16 config with the fixture feed and `tz = America/Chicago`.
fn config() -> Config {
    let mut cfg = Config::default();
    cfg.calendar.ics_urls = vec![URL.to_string()];
    cfg
}

fn fetcher() -> StaticFetcher {
    StaticFetcher::new().with(URL, sample())
}

fn parse_window() -> Vec<CalEvent> {
    let cfg = config();
    let (from, to) = window_for_week(week());
    let feed = parse_ics_report(&sample(), &ParseOptions::new(cfg.tz).window(from, to)).unwrap();
    assert!(feed.warnings.is_empty(), "{:?}", feed.warnings);
    events_in_window(feed.events, from, to)
}

/// `start end summary` per occurrence, for readable assertions.
fn digest(events: &[CalEvent]) -> Vec<String> {
    events
        .iter()
        .map(|e| {
            format!(
                "{} {} {}",
                e.start.format("%Y-%m-%dT%H:%M"),
                e.end.format("%Y-%m-%dT%H:%M"),
                e.summary
            )
        })
        .collect()
}

#[test]
fn the_three_week_window_holds_the_expected_occurrences() {
    let events = parse_window();
    assert_eq!(
        digest(&events),
        vec![
            // Already under way when the window opens (it starts in W35).
            "2026-08-28T09:00 2026-09-02T17:00 Systems conference",
            // W36: the lecture already runs, twice a week.
            "2026-09-02T15:00 2026-09-02T16:20 CS 234 lecture",
            "2026-09-04T15:00 2026-09-04T16:20 CS 234 lecture",
            // W37.
            "2026-09-07T06:30 2026-09-07T06:50 Morning pages",
            "2026-09-07T12:50 2026-09-07T13:50 Meeting w/ host",
            "2026-09-08T09:00 2026-09-08T09:30 Standup with the Berlin team",
            "2026-09-08T13:00 2026-09-08T14:00 Focus block",
            "2026-09-09T06:30 2026-09-09T06:50 Morning pages",
            "2026-09-09T15:00 2026-09-09T16:20 CS 234 lecture",
            "2026-09-10T16:00 2026-09-10T16:45 review: draft @lab #ops",
            "2026-09-10T19:00 2026-09-10T20:00 Dinner w/ Kun, then drinks",
            "2026-09-11T06:30 2026-09-11T06:50 Morning pages",
            "2026-09-12T08:15 2026-09-12T10:40 UA 1234 ORD→SFO",
            "2026-09-13T06:30 2026-09-13T06:50 Morning pages",
            // Starts on the Sunday of W37 and runs into W38.
            "2026-09-13T18:00 2026-09-15T12:00 Bike tour to Wisconsin",
            // W38.
            "2026-09-15T06:30 2026-09-15T06:50 Morning pages",
            "2026-09-15T10:00 2026-09-15T10:30 Monthly 1:1 w/ advisor",
            "2026-09-16T00:00 2026-09-17T00:00 Conference day",
            "2026-09-16T15:00 2026-09-16T16:20 CS 234 lecture",
            "2026-09-18T09:00 2026-09-20T17:00 Team retreat at the lake house",
            "2026-09-18T15:00 2026-09-18T16:20 CS 234 lecture",
        ]
    );

    // The cancelled event never appears, and the lecture's EXDATE (Fri 09-11)
    // is gone while the other Fridays stay.
    assert!(!events.iter().any(|e| e.summary == "Team offsite"));
    assert!(!events
        .iter()
        .any(|e| e.summary == "CS 234 lecture" && e.start.format("%m-%d").to_string() == "09-11"));

    // All-day, recurring and one-off flags.
    let by = |uid: &str| events.iter().filter(|e| e.uid == uid).collect::<Vec<_>>();
    assert!(by("allday-conf-0006")[0].all_day);
    assert!(!by("allday-conf-0006")[0].recurring);
    assert_eq!(by("morning-pages-0007").len(), 5);
    assert!(by("morning-pages-0007").iter().all(|e| e.recurring));
    assert!(!by("meeting-host-0001")[0].recurring);
    assert_eq!(
        by("retreat-0005")[0].location.as_deref(),
        Some("Lake House, Wisconsin")
    );
}

#[test]
fn parsing_without_a_window_finds_the_same_occurrences_after_filtering() {
    let cfg = config();
    let (from, to) = window_for_week(week());
    let all = parse_ics_report(&sample(), &ParseOptions::new(cfg.tz))
        .unwrap()
        .events;
    // The unbounded read walks the lecture and the monthly series further out.
    assert!(all.len() > parse_window().len());
    assert_eq!(
        digest(&events_in_window(all, from, to)),
        digest(&parse_window())
    );
}

/// The three weeks a sync of `today` writes.
fn weeks() -> [IsoWeek; 3] {
    [week().prev(), week(), week().next()]
}

#[test]
fn rendered_lines_snapshot() {
    let cfg = config();
    let events = parse_window();
    let mut out = String::new();
    for (w, lines) in render_calendar_weeks(&events, &cfg, &weeks()) {
        out.push_str(&format!("=== calendar/{w}.md\n"));
        for line in lines {
            out.push_str(&line);
            out.push('\n');
        }
    }
    insta::assert_snapshot!(out);
}

#[test]
fn every_event_in_the_window_is_written_exactly_once() {
    let cfg = config();
    let events = parse_window();
    let rendered = render_calendar_weeks(&events, &cfg, &weeks());
    // Every occurrence lands in exactly one file, ids included: an event that
    // is already under way when the window opens (the conference starting in
    // W35) is written into the first week that is being written, and one that
    // spans two written weeks (the bike tour) stays in the week it starts in.
    let total: usize = rendered.iter().map(|(_, l)| l.len()).sum();
    assert_eq!(total, events.len());

    let mut ids: Vec<String> = Vec::new();
    for (w, lines) in &rendered {
        let path = format!("calendar/{w}.md");
        let ctx = ParseCtx::new(&path, cfg.block_min());
        for line in lines {
            let item = parse_line(line, &ctx).unwrap();
            assert!(item.problems.is_empty(), "{line}: {:?}", item.problems);
            assert_eq!(item.line_text(), *line);
            let Shape::Interval { start, end } = item.shape else {
                panic!("{line}: not an interval");
            };
            let ev = events
                .iter()
                .find(|e| e.start == start && e.end == end)
                .unwrap_or_else(|| panic!("{line}: no event at {start}"));
            assert_eq!(item.id, ev.id(), "{line}");
            // Only an all-day event carries a tag, and nothing else from the
            // summary leaked into a field.
            let expected_tags: Vec<String> = if ev.all_day {
                vec!["all-day".to_string()]
            } else {
                Vec::new()
            };
            assert_eq!(item.tags, expected_tags, "{line}");
            assert!(item.parent.is_none() && item.priority.is_none());
            ids.push(item.id.to_string());
        }
    }
    let unique: std::collections::HashSet<&String> = ids.iter().collect();
    assert_eq!(unique.len(), ids.len(), "an id was written twice: {ids:?}");
}

#[test]
fn the_conference_already_under_way_lands_in_the_first_written_week() {
    let cfg = config();
    let events = parse_window();
    let rendered = render_calendar_weeks(&events, &cfg, &weeks());
    let holding: Vec<String> = rendered
        .iter()
        .filter(|(_, lines)| lines.iter().any(|l| l.contains("Systems conference")))
        .map(|(w, _)| w.to_string())
        .collect();
    assert_eq!(holding, vec!["2026-W36"]);
    assert!(rendered[0]
        .1
        .iter()
        .any(|l| l.contains("at:2026-08-28T09:00/2026-09-02T17:00 loc:Hyde-Park")));
}

#[test]
fn the_flight_gets_ci_1_and_the_travel_day_buffer() {
    let cfg = config();
    let events = parse_window();
    let lines = render_calendar_lines(&events, &cfg, week());
    let flight: Vec<&String> = lines.iter().filter(|l| l.contains("UA 1234")).collect();
    assert_eq!(flight.len(), 1);
    let ctx = ParseCtx::new("calendar/2026-W37.md", cfg.block_min());
    let item = parse_line(flight[0], &ctx).unwrap();
    assert_eq!(item.ci, 1);
    assert_eq!(item.buffer.map(|d| d.to_string()).as_deref(), Some("2h"));
    // fork `Item::is_travel_day`'s reading of the flag (R3 deleted that method, README gap 4752)
    assert!(item.has_flag("travel-day"));
    assert!(item.title.starts_with('✈'), "{}", item.title);

    // The lecture shares the shape of the default flight regex (`CS 234`) but
    // is not a flight: ci 2, no buffer.
    let lecture = lines.iter().find(|l| l.contains("CS 234")).unwrap();
    let item = parse_line(lecture, &ctx).unwrap();
    assert_eq!(item.ci, 2);
    assert!(item.buffer.is_none() && !item.has_flag("travel-day"));

    // A plain meeting is ci 3.
    let meeting = lines
        .iter()
        .find(|l| l.contains("Meeting w/ host"))
        .unwrap();
    assert_eq!(parse_line(meeting, &ctx).unwrap().ci, 3);
}

#[test]
fn sync_writes_one_file_per_week_in_the_window() {
    let files = sync(&fetcher(), &config(), today(), &[]).unwrap();
    let weeks: Vec<String> = files.iter().map(|(w, _)| w.to_string()).collect();
    assert_eq!(weeks, vec!["2026-W36", "2026-W37", "2026-W38"]);
    for (w, text) in &files {
        assert!(text.ends_with('\n'), "{w}");
        for line in text.lines() {
            assert!(line.starts_with("- [ ] "), "{w}: {line}");
        }
    }
    insta::assert_snapshot!(files[1].1);
}

/// A hand-written calendar file: prose, a `manual` line with unusual spacing,
/// and a stale generated line that the sync must replace.
const EXISTING_W37: &str = "\
---
week: 2026-W37
---
# Synced

- [ ] 3 Stale meeting  at:2026-09-07T09:00/10:00 loc:zoom ^zzzzzz
- [ ] 1  Dinner w/ Kun   at:2026-09-10T19:00/20:00  manual   ^g4
- [ ] 3 Another stale one  at:2026-09-08T09:00/10:00 ^yyyyyy

Anything outside the item lines is mine.
";

#[test]
fn sync_preserves_manual_lines_byte_for_byte() {
    let manual = "- [ ] 1  Dinner w/ Kun   at:2026-09-10T19:00/20:00  manual   ^g4";
    let existing = vec![(week(), EXISTING_W37.to_string())];
    let files = sync(&fetcher(), &config(), today(), &existing).unwrap();
    let w37 = &files.iter().find(|(w, _)| *w == week()).unwrap().1;

    // The manual line survives exactly once, unchanged, including its spacing.
    assert_eq!(w37.lines().filter(|l| *l == manual).count(), 1);
    // Prose and front matter survive; the stale generated lines are gone.
    assert!(w37.starts_with("---\nweek: 2026-W37\n---\n# Synced\n\n"));
    assert!(w37.ends_with("\nAnything outside the item lines is mine.\n"));
    assert!(!w37.contains("Stale meeting") && !w37.contains("Another stale one"));
    // The generated block landed where the first generated line was.
    let lines: Vec<&str> = w37.lines().collect();
    let first_gen = lines.iter().position(|l| l.contains("at:")).unwrap();
    assert_eq!(first_gen, 5);
    assert!(lines[first_gen].starts_with("- [ ] 3 Morning pages  at:2026-09-07T06:30/06:50 ^"));

    insta::assert_snapshot!(w37);

    // Merging again over the produced file is a no-op.
    let again = sync(&fetcher(), &config(), today(), &files).unwrap();
    assert_eq!(&again, &files);
}

#[test]
fn a_manual_line_is_kept_even_when_nothing_is_generated() {
    let manual = "- [ ] 1 Dinner w/ Kun  at:2026-09-10T19:00/20:00 manual ^g4\n";
    assert_eq!(merge_calendar_file(Some(manual), &[]), manual);
}

#[test]
fn re_syncing_never_changes_an_id() {
    let cfg = config();
    // Two independent syncs, one of them starting from the written files.
    let first = sync(&fetcher(), &cfg, today(), &[]).unwrap();
    let second = sync(&fetcher(), &cfg, today(), &first).unwrap();
    assert_eq!(first, second);

    // And the ids do not depend on which weeks are written together: syncing
    // from the previous and the next Monday gives the same line for the same
    // occurrence.
    let ids = |files: &[(IsoWeek, String)]| -> HashMap<String, String> {
        let ctx_cfg = cfg.block_min();
        files
            .iter()
            .flat_map(|(w, text)| {
                let path = format!("calendar/{w}.md");
                text.lines()
                    .map(|l| {
                        let item = parse_line(l, &ParseCtx::new(&path, ctx_cfg)).unwrap();
                        (format!("{:?}", item.shape), item.id.to_string())
                    })
                    .collect::<Vec<_>>()
            })
            .collect()
    };
    let a = ids(&first);
    for day in [
        NaiveDate::from_ymd_opt(2026, 8, 31).unwrap(),
        NaiveDate::from_ymd_opt(2026, 9, 14).unwrap(),
    ] {
        let other = sync(&fetcher(), &cfg, day, &[]).unwrap();
        let b = ids(&other);
        for (shape, id) in &a {
            if let Some(other_id) = b.get(shape) {
                assert_eq!(id, other_id, "{shape}");
            }
        }
    }

    // Ids are unique inside every file and 6 chars from the id alphabet.
    for (w, text) in &first {
        let mut seen: Vec<Id> = Vec::new();
        for line in text.lines() {
            let item = parse_line(line, &ParseCtx::new("calendar/2026-W37.md", 60)).unwrap();
            assert_eq!(item.id.as_str().len(), 6, "{w}: {line}");
            assert!(
                item.id
                    .as_str()
                    .bytes()
                    .all(|b| b"abcdefghijkmnpqrstuvwxyz23456789".contains(&b)),
                "{w}: {line}"
            );
            assert!(!seen.contains(&item.id), "{w}: duplicate id in {line}");
            seen.push(item.id);
        }
    }
}

#[test]
fn sync_reports_the_events_it_wrote_and_no_warnings() {
    let report = sync_report(&fetcher(), &config(), today(), &[]).unwrap();
    assert!(report.warnings.is_empty(), "{:?}", report.warnings);
    assert_eq!(report.events.len(), 21);
    // Every reported occurrence really was written — including the conference
    // that starts in W35 and the bike tour that spans W37 and W38.
    let written: usize = report.files.iter().map(|(_, t)| t.lines().count()).sum();
    assert_eq!(written, report.events.len());
}

#[test]
fn pinning_a_generated_line_does_not_duplicate_it_on_the_next_sync() {
    let cfg = config();
    let first = sync(&fetcher(), &cfg, today(), &[]).unwrap();
    let w37 = first.iter().find(|(w, _)| *w == week()).unwrap().1.clone();

    // The user keeps the meeting by adding the `manual` flag to the line the
    // sync generated (§4.3: only `manual` lines survive a sync).
    let line = w37
        .lines()
        .find(|l| l.contains("Meeting w/ host"))
        .unwrap()
        .to_string();
    let (head, id) = line.rsplit_once(" ^").unwrap();
    let pinned = format!("{head} manual ^{id}");
    let edited: Vec<(IsoWeek, String)> = first
        .iter()
        .map(|(w, t)| (*w, t.replace(&line, &pinned)))
        .collect();

    let again = sync(&fetcher(), &cfg, today(), &edited).unwrap();
    let text = &again.iter().find(|(w, _)| *w == week()).unwrap().1;
    assert_eq!(text.lines().filter(|l| **l == pinned).count(), 1);
    assert_eq!(
        text.lines()
            .filter(|l| l.contains("Meeting w/ host"))
            .count(),
        1,
        "{text}"
    );
    assert_eq!(text.matches(&format!(" ^{id}")).count(), 1, "{text}");
    // And it stays put: a further sync changes nothing.
    assert_eq!(sync(&fetcher(), &cfg, today(), &again).unwrap(), again);
}

#[test]
fn a_missing_feed_is_an_error() {
    let err = sync(&StaticFetcher::new(), &config(), today(), &[]).unwrap_err();
    assert!(matches!(err, IcsError::NotFound(url) if url == URL));
}
