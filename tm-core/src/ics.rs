//! Calendar sync — tm-spec-v1.md §15, with the file format of §4.3
//! (`calendar/YYYY-Www.md`) and the `[calendar]` config of §16.
//!
//! # API overview
//!
//! * [`parse_ics`]`(text)` / [`parse_ics_with`]`(text, &`[`ParseOptions`]`)` /
//!   [`parse_ics_report`] — an ICS feed becomes a flat list of [`CalEvent`]
//!   occurrences. `ParseOptions` carries the target timezone (`config.tz`) and
//!   the window recurrences are expanded into; [`parse_ics_report`] also
//!   returns the warnings (unsupported rules, unknown `TZID`s, skipped
//!   events) so `tm sync-cal` can print them.
//! * [`events_in_window`]`(events, from, to)` — keep the occurrences that
//!   overlap `[from, to)`; [`window_for_week`] and [`sync_weeks`] give the
//!   §15 window `[this week − 1, this week + 1]`.
//! * [`stable_id`]`(uid, occurrence_start)` — the id written on a generated
//!   line: a 6-char FNV-1a hash over the `UID` (plus the occurrence start for
//!   a recurring event), so re-syncs never renumber lines.
//! * [`render_calendar_lines`]`(events, cfg, week)` — the §4.3 lines for one
//!   ISO week; [`classify_event`] is the documented ci / flight rule.
//! * [`merge_calendar_file`]`(existing, new_lines)` — replace the generated
//!   lines, keep `manual` lines and prose verbatim.
//! * [`Fetcher`] (+ [`HttpFetcher`], [`StaticFetcher`], the free [`fetch`])
//!   and [`sync`] / [`sync_report`] — fetch every `config.calendar.ics_urls`
//!   feed and produce one calendar file text per week in the window.
//! * Errors: [`IcsError`].
//!
//! # Time
//!
//! ICS times are converted at this edge and stored as naive local time in
//! `config.tz`, which is what the `at:` token holds (§17.2 "Time"):
//!
//! * `…T…Z` — UTC, converted to `opts.tz`.
//! * `;TZID=<zone>` — read in that zone (IANA names; a leading
//!   `/prefix/…/Area/City` is trimmed), converted to `opts.tz`. An unknown
//!   zone (e.g. the Windows `Central Standard Time`) is a warning and the
//!   time is taken as written.
//! * no suffix and no `TZID` — floating; taken as written.
//! * `;VALUE=DATE` — an all-day event: `all_day` is set and the ICS half-open
//!   convention is kept, so a one-day event is `at:<date>T00:00/<next>T00:00`.
//!   All-day events are floating by definition and are never converted.
//!
//! A recurring event is expanded in the wall clock of its own zone (so a
//! weekly 15:00 lecture stays at 15:00 across a DST change) and each
//! occurrence is then converted. The occurrence length is the length of the
//! first occurrence after conversion.
//!
//! # Recurrence support
//!
//! `RRULE` is expanded for `FREQ=DAILY`, `FREQ=WEEKLY` (with `BYDAY`) and
//! `FREQ=MONTHLY` (with `BYMONTHDAY`), honouring `INTERVAL`, `COUNT`,
//! `UNTIL` and `EXDATE` (`COUNT` counts rule occurrences before `EXDATE`
//! removal, per RFC 5545). `DTSTART` always counts as the first occurrence.
//!
//! Not supported (each is a warning; the event still appears as its single
//! `DTSTART` occurrence): `FREQ=YEARLY|HOURLY|MINUTELY|SECONDLY`, ordinal
//! `BYDAY` values (`2MO`), negative `BYMONTHDAY` (`-1`), `BYSETPOS`,
//! `BYMONTH`, `BYWEEKNO`, `BYYEARDAY`, `BYHOUR`/`BYMINUTE`/`BYSECOND`, a
//! `WKST` other than Monday, and `RDATE`. Events with `RECURRENCE-ID` (a
//! single edited occurrence of a series) are skipped with a warning, and
//! `STATUS:CANCELLED` events are dropped silently. `VTIMEZONE` components are
//! ignored — zones are resolved through `chrono-tz`.

use std::collections::{BTreeMap, HashSet};
use std::io::BufReader;
use std::time::Duration as StdDuration;

use chrono::{Datelike, Duration, NaiveDate, NaiveDateTime, NaiveTime, TimeZone, Utc, Weekday};
use chrono_tz::Tz;
use ical::parser::ical::component::IcalEvent;
use ical::property::Property;
use regex::Regex;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::config::Config;
use crate::grammar::{ItemLine, ID_ALPHABET};
use crate::model::{fmt_interval, Id, IsoWeek};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from fetching, parsing or syncing a calendar feed.
#[derive(Debug, Error)]
pub enum IcsError {
    /// The HTTP request failed.
    #[error("cannot fetch {url}: {source}")]
    Fetch {
        /// The URL attempted.
        url: String,
        /// Underlying error.
        #[source]
        source: Box<ureq::Error>,
    },
    /// The response could not be read as text.
    #[error("cannot read the body of {url}: {source}")]
    Body {
        /// The URL attempted.
        url: String,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// The feed is not a readable `VCALENDAR`.
    #[error("cannot parse the ICS feed: {0}")]
    Parse(String),
    /// A [`StaticFetcher`] was asked for a URL it does not hold.
    #[error("no fixture calendar for {0}")]
    NotFound(String),
}

// ---------------------------------------------------------------------------
// Events
// ---------------------------------------------------------------------------

/// One occurrence of a calendar event, in `config.tz` wall-clock time.
///
/// A recurring event yields one `CalEvent` per occurrence; they share `uid`
/// and differ in `start`, which is why [`stable_id`] mixes the start in for
/// them (see [`CalEvent::id`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CalEvent {
    /// The ICS `UID`.
    pub uid: String,
    /// `SUMMARY`, unescaped and whitespace-collapsed (may be empty).
    pub summary: String,
    /// Start, naive local time in the target zone.
    pub start: NaiveDateTime,
    /// End, naive local time in the target zone (`>= start`).
    pub end: NaiveDateTime,
    /// `LOCATION`, unescaped and whitespace-collapsed, when non-empty.
    pub location: Option<String>,
    /// True for a `VALUE=DATE` event; `end` is then the exclusive end date at
    /// `00:00`.
    pub all_day: bool,
    /// True when this occurrence came from an `RRULE`.
    pub recurring: bool,
}

impl CalEvent {
    /// The id written on the generated line (see [`stable_id`]).
    pub fn id(&self) -> Id {
        stable_id(&self.uid, self.recurring.then_some(self.start))
    }
    /// Length in minutes.
    pub fn minutes(&self) -> i64 {
        (self.end - self.start).num_minutes().max(0)
    }
    /// True when the occupied time overlaps `[from, to)`. A zero-length event
    /// overlaps when it starts inside the range.
    pub fn overlaps(&self, from: NaiveDateTime, to: NaiveDateTime) -> bool {
        if self.end == self.start {
            self.start >= from && self.start < to
        } else {
            self.start < to && self.end > from
        }
    }
    /// The ISO week the occurrence starts in — the calendar file it is
    /// written to.
    pub fn week(&self) -> IsoWeek {
        IsoWeek::from_date(self.start.date())
    }
}

/// Everything one feed produced: the occurrences and the things that could
/// not be represented.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct IcsFeed {
    /// Occurrences, sorted by `(start, summary, uid)`.
    pub events: Vec<CalEvent>,
    /// Human-readable warnings (unsupported rules, unknown zones, skipped
    /// events).
    pub warnings: Vec<String>,
}

/// How an ICS feed is read: the target zone and the expansion window.
#[derive(Clone, Debug, PartialEq)]
pub struct ParseOptions {
    /// Zone all times are converted into (`config.tz`).
    pub tz: Tz,
    /// Half-open window `[from, to)` recurrences are expanded into. `None`
    /// expands at most [`MAX_UNWINDOWED_OCCURRENCES`] occurrences per rule,
    /// which is only useful for feeds of bounded rules — pass a window
    /// whenever one is known.
    pub window: Option<(NaiveDateTime, NaiveDateTime)>,
}

impl Default for ParseOptions {
    fn default() -> ParseOptions {
        ParseOptions {
            tz: Tz::UTC,
            window: None,
        }
    }
}

impl ParseOptions {
    /// Options with a target zone and no window.
    pub fn new(tz: Tz) -> ParseOptions {
        ParseOptions { tz, window: None }
    }
    /// Add the expansion window `[from, to)`.
    pub fn window(mut self, from: NaiveDateTime, to: NaiveDateTime) -> ParseOptions {
        self.window = Some((from, to));
        self
    }
    /// Options for the §15 sync window around `week` in `tz`.
    pub fn for_week(tz: Tz, week: IsoWeek) -> ParseOptions {
        let (from, to) = window_for_week(week);
        ParseOptions::new(tz).window(from, to)
    }
}

/// Cap on occurrences expanded from one rule when no window is given.
pub const MAX_UNWINDOWED_OCCURRENCES: u32 = 1000;

/// Cap on rule periods walked while looking for occurrences in the window
/// (100 000 daily periods is 274 years).
const MAX_PERIODS: u32 = 100_000;

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

/// Parse an ICS feed with the default options (UTC, no window).
///
/// Prefer [`parse_ics_with`] with the configured zone and the sync window;
/// this signature exists for callers that only want to read a bounded feed.
pub fn parse_ics(text: &str) -> Result<Vec<CalEvent>, IcsError> {
    parse_ics_with(text, &ParseOptions::default())
}

/// Parse an ICS feed, expanding recurrences into `opts.window`.
pub fn parse_ics_with(text: &str, opts: &ParseOptions) -> Result<Vec<CalEvent>, IcsError> {
    parse_ics_report(text, opts).map(|f| f.events)
}

/// Parse an ICS feed and keep the warnings.
pub fn parse_ics_report(text: &str, opts: &ParseOptions) -> Result<IcsFeed, IcsError> {
    let mut events: Vec<CalEvent> = Vec::new();
    let mut warnings: Vec<String> = Vec::new();
    let mut seen: HashSet<(String, NaiveDateTime)> = HashSet::new();
    let mut any_calendar = false;

    for cal in ical::IcalParser::new(BufReader::new(text.as_bytes())) {
        let cal = cal.map_err(|e| IcsError::Parse(e.to_string()))?;
        any_calendar = true;
        for ev in &cal.events {
            for e in convert_event(ev, opts, &mut warnings) {
                if seen.insert((e.uid.clone(), e.start)) {
                    events.push(e);
                }
            }
        }
    }
    if !any_calendar && !text.trim().is_empty() {
        return Err(IcsError::Parse("no VCALENDAR component".to_string()));
    }
    events.sort_by(|a, b| {
        a.start
            .cmp(&b.start)
            .then_with(|| a.summary.cmp(&b.summary))
            .then_with(|| a.uid.cmp(&b.uid))
    });
    Ok(IcsFeed { events, warnings })
}

/// The zone an ICS time is written in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Zone {
    /// `…Z`.
    Utc,
    /// `TZID=…`.
    Named(Tz),
    /// No zone information (also every `VALUE=DATE`).
    Floating,
}

/// One time value as written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RawTime {
    naive: NaiveDateTime,
    zone: Zone,
    is_date: bool,
}

fn convert_event(ev: &IcalEvent, opts: &ParseOptions, warnings: &mut Vec<String>) -> Vec<CalEvent> {
    let uid = text_value(ev, "UID").unwrap_or_default();
    let label = if uid.is_empty() {
        "<event without UID>".to_string()
    } else {
        uid.clone()
    };
    if let Some(status) = text_value(ev, "STATUS") {
        if status.eq_ignore_ascii_case("CANCELLED") {
            return Vec::new();
        }
    }
    if prop(ev, "RECURRENCE-ID").is_some() {
        warnings.push(format!(
            "{label}: RECURRENCE-ID (an edited single occurrence) is not supported; skipped"
        ));
        return Vec::new();
    }
    let Some(dtstart_prop) = prop(ev, "DTSTART") else {
        warnings.push(format!("{label}: no DTSTART; skipped"));
        return Vec::new();
    };
    let Some(dtstart) = parse_prop_time(dtstart_prop, &label, warnings) else {
        warnings.push(format!("{label}: unreadable DTSTART; skipped"));
        return Vec::new();
    };

    // End: DTEND, else DTSTART + DURATION, else one day (all-day) or zero.
    let base_start = to_zone(dtstart.naive, dtstart.zone, opts.tz);
    let base_end = match prop(ev, "DTEND").and_then(|p| parse_prop_time(p, &label, warnings)) {
        Some(t) => to_zone(t.naive, t.zone, opts.tz),
        None => match prop(ev, "DURATION").and_then(|p| p.value.as_deref()) {
            Some(v) => match parse_ics_duration(v) {
                Some(d) => base_start + d,
                None => {
                    warnings.push(format!("{label}: unreadable DURATION {v:?}; treated as 0"));
                    base_start
                }
            },
            None if dtstart.is_date => base_start + Duration::days(1),
            None => base_start,
        },
    };
    let length = if base_end >= base_start {
        base_end - base_start
    } else {
        warnings.push(format!("{label}: end before start; treated as 0"));
        Duration::zero()
    };

    let summary = text_value(ev, "SUMMARY").unwrap_or_default();
    let location = text_value(ev, "LOCATION").filter(|s| !s.is_empty());
    let exdates: Vec<RawTime> = props(ev, "EXDATE")
        .flat_map(|p| split_values(p).into_iter().map(move |v| (p, v)))
        .filter_map(|(p, v)| parse_time_value(&v, p, &label, warnings))
        .collect();
    let excluded: Vec<NaiveDateTime> = exdates
        .iter()
        .map(|t| to_zone(t.naive, t.zone, opts.tz))
        .collect();
    let excluded_dates: Vec<NaiveDate> = exdates
        .iter()
        .filter(|t| t.is_date)
        .map(|t| t.naive.date())
        .collect();

    let rrule = prop(ev, "RRULE").and_then(|p| p.value.as_deref());
    let starts: Vec<NaiveDateTime> = match rrule {
        None => vec![dtstart.naive],
        Some(v) => {
            let rule = Rrule::parse(v);
            for u in &rule.unsupported {
                warnings.push(format!(
                    "{label}: RRULE {u} is not supported; only the first occurrence is used"
                ));
            }
            if prop(ev, "RDATE").is_some() {
                warnings.push(format!("{label}: RDATE is not supported; ignored"));
            }
            rule.expand(dtstart.naive, source_window(opts.window, dtstart.zone))
        }
    };

    // Every occurrence of a rule is identified by its start, whether or not
    // this window happens to hold more than one of them — otherwise the id of
    // a series would change as the window moves over it.
    let recurring = rrule.is_some();
    starts
        .into_iter()
        .map(|s| {
            let start = to_zone(s, dtstart.zone, opts.tz);
            CalEvent {
                uid: uid.clone(),
                summary: summary.clone(),
                start,
                end: start + length,
                location: location.clone(),
                all_day: dtstart.is_date,
                recurring,
            }
        })
        .filter(|e| !excluded.contains(&e.start) && !excluded_dates.contains(&e.start.date()))
        .filter(|e| match opts.window {
            Some((from, to)) => e.overlaps(from, to),
            None => true,
        })
        .collect()
}

/// The expansion window in the *source* zone: widened by two days on each
/// side so no zone offset (at most 26h apart) can drop an occurrence that
/// lands inside the window after conversion — the exact filter runs on the
/// converted times.
fn source_window(
    window: Option<(NaiveDateTime, NaiveDateTime)>,
    zone: Zone,
) -> Option<(NaiveDateTime, NaiveDateTime)> {
    let (from, to) = window?;
    match zone {
        Zone::Floating => Some((from, to)),
        _ => Some((from - Duration::days(2), to + Duration::days(2))),
    }
}

fn prop<'a>(ev: &'a IcalEvent, name: &str) -> Option<&'a Property> {
    ev.properties
        .iter()
        .find(|p| p.name.eq_ignore_ascii_case(name))
}

fn props<'a>(ev: &'a IcalEvent, name: &'a str) -> impl Iterator<Item = &'a Property> {
    ev.properties
        .iter()
        .filter(move |p| p.name.eq_ignore_ascii_case(name))
}

fn param<'a>(p: &'a Property, key: &str) -> Option<&'a str> {
    p.params
        .as_ref()?
        .iter()
        .find(|(k, _)| k.eq_ignore_ascii_case(key))
        .and_then(|(_, v)| v.first())
        .map(|s| s.as_str())
}

/// A `TEXT` property, unescaped and whitespace-collapsed.
fn text_value(ev: &IcalEvent, name: &str) -> Option<String> {
    prop(ev, name)
        .and_then(|p| p.value.as_deref())
        .map(unescape_text)
}

/// RFC 5545 `TEXT` unescaping, then whitespace collapsing (a line has no
/// room for newlines or runs of spaces).
fn unescape_text(v: &str) -> String {
    let mut out = String::with_capacity(v.len());
    let mut chars = v.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') | Some('N') => out.push(' '),
            Some(other) => out.push(other),
            None => out.push('\\'),
        }
    }
    collapse_ws(&out)
}

fn collapse_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The comma-separated values of a multi-valued property (`EXDATE`).
fn split_values(p: &Property) -> Vec<String> {
    p.value
        .as_deref()
        .unwrap_or("")
        .split(',')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect()
}

fn parse_prop_time(p: &Property, label: &str, warnings: &mut Vec<String>) -> Option<RawTime> {
    let value = p.value.as_deref()?.trim().to_string();
    parse_time_value(&value, p, label, warnings)
}

fn parse_time_value(
    value: &str,
    p: &Property,
    label: &str,
    warnings: &mut Vec<String>,
) -> Option<RawTime> {
    let is_date = param(p, "VALUE").is_some_and(|v| v.eq_ignore_ascii_case("DATE"))
        || (value.len() == 8 && !value.contains('T'));
    if is_date {
        let d = NaiveDate::parse_from_str(value, "%Y%m%d").ok()?;
        return Some(RawTime {
            naive: d.and_time(NaiveTime::MIN),
            zone: Zone::Floating,
            is_date: true,
        });
    }
    let (naive, utc) = parse_ics_datetime(value)?;
    let zone = if utc {
        Zone::Utc
    } else {
        match param(p, "TZID") {
            Some(t) => match zone_from_tzid(t) {
                Some(tz) => Zone::Named(tz),
                None => {
                    warnings.push(format!(
                        "{label}: unknown TZID {t:?}; the time is taken as written"
                    ));
                    Zone::Floating
                }
            },
            None => Zone::Floating,
        }
    };
    Some(RawTime {
        naive,
        zone,
        is_date: false,
    })
}

/// `YYYYMMDDTHHMMSS[Z]` (seconds optional).
fn parse_ics_datetime(v: &str) -> Option<(NaiveDateTime, bool)> {
    let (body, utc) = match v.strip_suffix('Z').or_else(|| v.strip_suffix('z')) {
        Some(b) => (b, true),
        None => (v, false),
    };
    NaiveDateTime::parse_from_str(body, "%Y%m%dT%H%M%S")
        .or_else(|_| NaiveDateTime::parse_from_str(body, "%Y%m%dT%H%M"))
        .ok()
        .map(|d| (d, utc))
}

/// Resolve a `TZID` to an IANA zone, trimming quotes and a leading
/// `/prefix/…` path (Apple and some Exchange exporters write those).
fn zone_from_tzid(tzid: &str) -> Option<Tz> {
    let cleaned = tzid.trim().trim_matches('"');
    if let Ok(tz) = cleaned.parse::<Tz>() {
        return Some(tz);
    }
    let parts: Vec<&str> = cleaned.split('/').filter(|s| !s.is_empty()).collect();
    for start in 1..parts.len() {
        if let Ok(tz) = parts[start..].join("/").parse::<Tz>() {
            return Some(tz);
        }
    }
    None
}

/// `P[n]W` / `P[n]D[T[n]H[n]M[n]S]` (a leading `-` inverts).
fn parse_ics_duration(v: &str) -> Option<Duration> {
    let v = v.trim();
    let (sign, rest) = match v.strip_prefix('-') {
        Some(r) => (-1i64, r),
        None => (1i64, v.strip_prefix('+').unwrap_or(v)),
    };
    let rest = rest.strip_prefix('P').or_else(|| rest.strip_prefix('p'))?;
    let mut minutes = 0i64;
    let mut num = String::new();
    let mut in_time = false;
    let mut any = false;
    for c in rest.chars() {
        match c {
            '0'..='9' => num.push(c),
            'T' | 't' => in_time = true,
            _ => {
                let n: i64 = num.parse().ok()?;
                num.clear();
                any = true;
                minutes += match (c, in_time) {
                    ('W', _) | ('w', _) => n * 7 * 24 * 60,
                    ('D', _) | ('d', _) => n * 24 * 60,
                    ('H', true) | ('h', true) => n * 60,
                    ('M', true) | ('m', true) => n,
                    ('S', true) | ('s', true) => 0, // sub-minute precision is dropped
                    _ => return None,
                };
            }
        }
    }
    if !num.is_empty() || !any {
        return None;
    }
    Some(Duration::minutes(sign * minutes))
}

/// Convert a wall-clock time in `zone` to naive local time in `target`.
fn to_zone(naive: NaiveDateTime, zone: Zone, target: Tz) -> NaiveDateTime {
    match zone {
        Zone::Floating => naive,
        Zone::Utc => Utc
            .from_utc_datetime(&naive)
            .with_timezone(&target)
            .naive_local(),
        Zone::Named(tz) => {
            // A DST gap has no such local time; step forward an hour.
            let dt = tz
                .from_local_datetime(&naive)
                .earliest()
                .or_else(|| {
                    tz.from_local_datetime(&(naive + Duration::hours(1)))
                        .earliest()
                })
                .unwrap_or_else(|| Utc.from_utc_datetime(&naive).with_timezone(&tz));
            dt.with_timezone(&target).naive_local()
        }
    }
}

// ---------------------------------------------------------------------------
// Recurrence
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Freq {
    Daily,
    Weekly,
    Monthly,
    Unsupported,
}

/// The subset of `RRULE` this module expands (see the module docs).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Rrule {
    freq: Freq,
    interval: u32,
    count: Option<u32>,
    until: Option<NaiveDateTime>,
    until_utc: bool,
    byday: Vec<Weekday>,
    bymonthday: Vec<u32>,
    unsupported: Vec<String>,
}

impl Rrule {
    fn parse(value: &str) -> Rrule {
        let mut r = Rrule {
            freq: Freq::Unsupported,
            interval: 1,
            count: None,
            until: None,
            until_utc: false,
            byday: Vec::new(),
            bymonthday: Vec::new(),
            unsupported: Vec::new(),
        };
        for part in value.split(';') {
            let Some((k, v)) = part.split_once('=') else {
                continue;
            };
            let key = k.trim().to_ascii_uppercase();
            let val = v.trim();
            match key.as_str() {
                "FREQ" => {
                    r.freq = match val.to_ascii_uppercase().as_str() {
                        "DAILY" => Freq::Daily,
                        "WEEKLY" => Freq::Weekly,
                        "MONTHLY" => Freq::Monthly,
                        other => {
                            r.unsupported.push(format!("FREQ={other}"));
                            Freq::Unsupported
                        }
                    }
                }
                "INTERVAL" => r.interval = val.parse().unwrap_or(1).max(1),
                "COUNT" => r.count = val.parse().ok(),
                "UNTIL" => match parse_ics_datetime(val) {
                    Some((dt, utc)) => {
                        r.until = Some(dt);
                        r.until_utc = utc;
                    }
                    None => match NaiveDate::parse_from_str(val, "%Y%m%d") {
                        Ok(d) => {
                            r.until = Some(
                                d.and_hms_opt(23, 59, 59)
                                    .unwrap_or(d.and_time(NaiveTime::MIN)),
                            )
                        }
                        Err(_) => r.unsupported.push(format!("UNTIL={val}")),
                    },
                },
                "BYDAY" => {
                    for d in val.split(',') {
                        match weekday_from_ics(d.trim()) {
                            Some(wd) => r.byday.push(wd),
                            None => r.unsupported.push(format!("BYDAY={d}")),
                        }
                    }
                }
                "BYMONTHDAY" => {
                    for d in val.split(',') {
                        match d.trim().parse::<i32>() {
                            Ok(n) if (1..=31).contains(&n) => r.bymonthday.push(n as u32),
                            _ => r.unsupported.push(format!("BYMONTHDAY={d}")),
                        }
                    }
                }
                "WKST" => {
                    if !val.eq_ignore_ascii_case("MO") {
                        r.unsupported.push(format!("WKST={val}"));
                    }
                }
                "BYSETPOS" | "BYMONTH" | "BYWEEKNO" | "BYYEARDAY" | "BYHOUR" | "BYMINUTE"
                | "BYSECOND" => r.unsupported.push(format!("{key}={val}")),
                _ => {}
            }
        }
        r.byday.sort_by_key(|w| w.num_days_from_monday());
        r.byday.dedup();
        r.bymonthday.sort_unstable();
        r.bymonthday.dedup();
        r
    }

    /// Occurrence starts in the event's own wall clock, `DTSTART` first.
    ///
    /// `window` is `[from, to)` in the same wall clock; without one the walk
    /// stops after [`MAX_UNWINDOWED_OCCURRENCES`].
    fn expand(
        &self,
        start: NaiveDateTime,
        window: Option<(NaiveDateTime, NaiveDateTime)>,
    ) -> Vec<NaiveDateTime> {
        if !self.unsupported.is_empty() || self.freq == Freq::Unsupported {
            return vec![start];
        }
        let until = self.until;
        let time = start.time();
        let mut out: Vec<NaiveDateTime> = Vec::new();
        let mut generated: u32 = 0;
        let mut period: u32 = 0;
        loop {
            if period > MAX_PERIODS {
                break;
            }
            let dates = self.dates_in_period(start.date(), period);
            for d in dates {
                let occ = d.and_time(time);
                if occ < start {
                    continue;
                }
                if until.is_some_and(|u| occ > u) {
                    return out;
                }
                if self.count.is_some_and(|c| generated >= c) {
                    return out;
                }
                generated += 1;
                match window {
                    Some((from, to)) => {
                        if occ >= to {
                            return out;
                        }
                        if occ >= from {
                            out.push(occ);
                        }
                    }
                    None => out.push(occ),
                }
            }
            if window.is_none() && generated >= MAX_UNWINDOWED_OCCURRENCES {
                break;
            }
            period += 1;
        }
        out
    }

    /// The candidate dates of period `n`, ascending.
    fn dates_in_period(&self, start: NaiveDate, n: u32) -> Vec<NaiveDate> {
        let step = (n as i64) * (self.interval as i64);
        match self.freq {
            Freq::Daily => vec![start + Duration::days(step)],
            Freq::Weekly => {
                let monday = start - Duration::days(start.weekday().num_days_from_monday() as i64);
                let week = monday + Duration::days(step * 7);
                let days = if self.byday.is_empty() {
                    vec![start.weekday()]
                } else {
                    self.byday.clone()
                };
                days.iter()
                    .map(|w| week + Duration::days(w.num_days_from_monday() as i64))
                    .collect()
            }
            Freq::Monthly => {
                let months = start.year() as i64 * 12 + (start.month() as i64 - 1) + step;
                let (y, m) = (
                    (months.div_euclid(12)) as i32,
                    (months.rem_euclid(12)) as u32 + 1,
                );
                let days = if self.bymonthday.is_empty() {
                    vec![start.day()]
                } else {
                    self.bymonthday.clone()
                };
                days.iter()
                    .filter_map(|d| NaiveDate::from_ymd_opt(y, m, *d))
                    .collect()
            }
            Freq::Unsupported => Vec::new(),
        }
    }
}

fn weekday_from_ics(s: &str) -> Option<Weekday> {
    match s.to_ascii_uppercase().as_str() {
        "MO" => Some(Weekday::Mon),
        "TU" => Some(Weekday::Tue),
        "WE" => Some(Weekday::Wed),
        "TH" => Some(Weekday::Thu),
        "FR" => Some(Weekday::Fri),
        "SA" => Some(Weekday::Sat),
        "SU" => Some(Weekday::Sun),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Window
// ---------------------------------------------------------------------------

/// The §15 sync window around `week`: `[Monday of week − 1, Monday of
/// week + 2)`, i.e. three whole ISO weeks.
pub fn window_for_week(week: IsoWeek) -> (NaiveDateTime, NaiveDateTime) {
    let from = week.prev().monday().and_time(NaiveTime::MIN);
    let to = week.next().next().monday().and_time(NaiveTime::MIN);
    (from, to)
}

/// The three ISO weeks a sync writes: `[week − 1, week, week + 1]`.
pub fn sync_weeks(week: IsoWeek) -> [IsoWeek; 3] {
    [week.prev(), week, week.next()]
}

/// Keep the occurrences overlapping `[from, to)`, order preserved.
pub fn events_in_window(
    events: Vec<CalEvent>,
    from: NaiveDateTime,
    to: NaiveDateTime,
) -> Vec<CalEvent> {
    let mut events = events;
    events.retain(|e| e.overlaps(from, to));
    events
}

// ---------------------------------------------------------------------------
// Stable ids
// ---------------------------------------------------------------------------

/// Length of a generated calendar id.
pub const CAL_ID_LEN: usize = 6;

/// The id for a calendar line: 6 characters from the tm id alphabet
/// (`[a-z0-9]` minus `l o 0 1`), derived from a 64-bit FNV-1a hash of the
/// ICS `UID` — plus the occurrence start for a recurring event, so every
/// occurrence gets its own id.
///
/// The hash is a pure function of its inputs, so a re-sync of an unchanged
/// feed rewrites exactly the same ids. Moving a one-off event keeps its id
/// (same event, new time); re-timing a series does renumber its occurrences,
/// because an occurrence *is* its start.
pub fn stable_id(uid: &str, occurrence_start: Option<NaiveDateTime>) -> Id {
    let key = match occurrence_start {
        Some(s) => format!("{uid}@{}", s.format("%Y-%m-%dT%H:%M")),
        None => uid.to_string(),
    };
    Id::new(encode_id(fnv1a64(key.as_bytes())))
}

/// FNV-1a, 64-bit.
fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        hash ^= *b as u64;
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

/// Render the low 5 bits of `hash`, [`CAL_ID_LEN`] times, through
/// [`ID_ALPHABET`] (32 symbols).
fn encode_id(hash: u64) -> String {
    let mut h = hash;
    let mut s = String::with_capacity(CAL_ID_LEN);
    for _ in 0..CAL_ID_LEN {
        s.push(ID_ALPHABET[(h & 0x1f) as usize] as char);
        h >>= 5;
    }
    s
}

// ---------------------------------------------------------------------------
// Rendering (§4.3)
// ---------------------------------------------------------------------------

/// The buffer written before a flight (§15).
pub const FLIGHT_BUFFER: &str = "2h";

/// Words that mark an event as attendance rather than work.
const LECTURE_WORDS: &[&str] = &[
    "lecture",
    "lectures",
    "class",
    "seminar",
    "recitation",
    "colloquium",
    "tutorial",
    "webinar",
];

/// What a calendar event is, which fixes its `ci` and its buffer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EventKind {
    /// A flight: `ci` 1 and `buffer:2h travel-day`.
    Flight,
    /// A lecture, class or seminar — attendance, not work: `ci` 2.
    Lecture,
    /// Anything else — a meeting takes part in the conversation: `ci` 3.
    Other,
}

impl EventKind {
    /// The `ci` written on the line.
    pub fn ci(&self) -> u8 {
        match self {
            EventKind::Flight => 1,
            EventKind::Lecture => 2,
            EventKind::Other => 3,
        }
    }
}

/// The documented ci rule (§4.3 shows 1 / 2 / 3 for a flight, a lecture and a
/// meeting):
///
/// 1. a summary naming a lecture, class, seminar, recitation, colloquium,
///    tutorial or webinar is a [`EventKind::Lecture`] — checked *first*
///    because a course code (`CS 234`) matches the default flight regex;
/// 2. otherwise a `✈` in the summary or a match of `flight_re`
///    (`config.calendar.flight_regex`) makes it a [`EventKind::Flight`];
/// 3. otherwise [`EventKind::Other`].
pub fn classify_event(summary: &str, flight_re: Option<&Regex>) -> EventKind {
    if LECTURE_WORDS.iter().any(|w| contains_word(summary, w)) {
        return EventKind::Lecture;
    }
    if summary.contains('✈') || flight_re.is_some_and(|re| re.is_match(summary)) {
        return EventKind::Flight;
    }
    EventKind::Other
}

/// Case-insensitive whole-word containment (word = run of alphanumerics).
fn contains_word(haystack: &str, word: &str) -> bool {
    haystack
        .split(|c: char| !c.is_alphanumeric())
        .any(|w| w.eq_ignore_ascii_case(word))
}

/// The §4.3 lines for the events starting in `week`, in start order.
///
/// Each line is
/// `- [ ] <ci> <Title>  at:<start>/<end> [loc:<x>] [buffer:2h travel-day] ^<id>`
/// with the short `at:` end form when the event ends on the day it starts and
/// the full `YYYY-MM-DDTHH:MM` end otherwise. Ids come from [`stable_id`]; on
/// the (astronomically unlikely) collision inside one week the id is re-hashed
/// with a counter so a file never has two lines with the same id.
///
/// `ci` and the flight buffer follow [`classify_event`]. A
/// `config.calendar.flight_regex` that is not a valid regex is ignored — only
/// `✈` then marks a flight — rather than failing the sync.
pub fn render_calendar_lines(events: &[CalEvent], cfg: &Config, week: IsoWeek) -> Vec<String> {
    let re = Regex::new(&cfg.calendar.flight_regex).ok();
    let mut list: Vec<&CalEvent> = events.iter().filter(|e| e.week() == week).collect();
    list.sort_by(|a, b| {
        a.start
            .cmp(&b.start)
            .then_with(|| a.end.cmp(&b.end))
            .then_with(|| a.summary.cmp(&b.summary))
            .then_with(|| a.uid.cmp(&b.uid))
    });
    let mut taken: HashSet<String> = HashSet::new();
    list.into_iter()
        .map(|e| {
            let kind = classify_event(&e.summary, re.as_ref());
            let id = unique_id(e, &mut taken);
            render_line(e, kind, &id)
        })
        .collect()
}

/// [`stable_id`], disambiguated against the ids already used in this file.
fn unique_id(ev: &CalEvent, taken: &mut HashSet<String>) -> Id {
    let base = ev.id();
    if taken.insert(base.as_str().to_string()) {
        return base;
    }
    for n in 1..1000u32 {
        let key = format!("{}#{n}", ev.uid);
        let id = stable_id(&key, ev.recurring.then_some(ev.start));
        if taken.insert(id.as_str().to_string()) {
            return id;
        }
    }
    base
}

/// One §4.3 calendar line.
fn render_line(ev: &CalEvent, kind: EventKind, id: &Id) -> String {
    let mut s = format!(
        "- [ ] {} {}  at:{}",
        kind.ci(),
        event_title(&ev.summary, kind),
        fmt_interval(ev.start, ev.end)
    );
    if let Some(loc) = ev.location.as_deref().and_then(loc_token) {
        s.push_str(&format!(" loc:{loc}"));
    }
    if kind == EventKind::Flight {
        s.push_str(&format!(" buffer:{FLIGHT_BUFFER} travel-day"));
    }
    s.push(' ');
    s.push_str(&id.token());
    s
}

/// The title as written on the line: the summary, made safe for the §4.1
/// title rule, with the `✈` of §4.3 in front of a flight that has none.
fn event_title(summary: &str, kind: EventKind) -> String {
    let safe = safe_title(summary);
    if kind == EventKind::Flight && !safe.contains('✈') {
        format!("✈ {safe}")
    } else {
        safe
    }
}

/// Make a summary safe to write as a title: a word that the parser would read
/// as a token (`@x`, `#x`, `!2`, `^x`, `key:value`) — or, in first position, as
/// the leading estimate (`2h`) — is wrapped in parentheses, which no token
/// starts with. An empty summary becomes `untitled`.
fn safe_title(summary: &str) -> String {
    let words: Vec<&str> = summary.split_whitespace().collect();
    if words.is_empty() {
        return "untitled".to_string();
    }
    words
        .iter()
        .enumerate()
        .map(|(i, w)| {
            if unsafe_title_word(i, w) {
                format!("({w})")
            } else {
                (*w).to_string()
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// True when the word would not survive a re-parse as title text.
fn unsafe_title_word(index: usize, word: &str) -> bool {
    // The ci slot is always written, so the first title word lands in the
    // (empty) leading-estimate slot.
    if index == 0 && crate::model::Dur::parse_no_days(word, 1).is_ok() {
        return true;
    }
    let mut chars = word.chars();
    match chars.next() {
        Some('@') | Some('#') | Some('!') | Some('^') => chars.next().is_some(),
        _ => match word.split_once(':') {
            Some((k, _)) => !k.is_empty() && k.bytes().all(|b| b.is_ascii_lowercase() || b == b'-'),
            None => false,
        },
    }
}

/// The `loc:` value: the first comma-separated part of `LOCATION`, with
/// internal whitespace turned into `-` (a `loc:` value is one token).
fn loc_token(location: &str) -> Option<String> {
    let first = location.split(',').next().unwrap_or(location).trim();
    let token = first.split_whitespace().collect::<Vec<_>>().join("-");
    (!token.is_empty()).then_some(token)
}

// ---------------------------------------------------------------------------
// Merging
// ---------------------------------------------------------------------------

/// Rewrite a calendar file: `new_lines` replace the generated item lines,
/// while every item line carrying the `manual` flag and every non-item line
/// (headings, prose, blank lines, front matter) is kept byte for byte.
///
/// The generated block goes where the file's first generated line was, so the
/// result is stable under repeated syncs; in a file that has none it goes
/// after everything kept. The text always ends with a newline (an empty file
/// stays empty).
pub fn merge_calendar_file(existing_text: Option<&str>, new_lines: &[String]) -> String {
    let Some(existing) = existing_text else {
        return join_lines(new_lines.iter().map(|s| s.as_str()));
    };
    let mut kept: Vec<&str> = Vec::new();
    let mut insert_at: Option<usize> = None;
    for line in split_lines(existing) {
        match ItemLine::parse(line) {
            // A generated line: dropped, and it marks where the new block goes.
            Ok(l) if !l.has_flag("manual") => {
                if insert_at.is_none() {
                    insert_at = Some(kept.len());
                }
            }
            // `manual` lines and everything that is not an item line.
            _ => kept.push(line),
        }
    }
    let at = insert_at.unwrap_or(kept.len());
    let out: Vec<&str> = kept[..at]
        .iter()
        .copied()
        .chain(new_lines.iter().map(|s| s.as_str()))
        .chain(kept[at..].iter().copied())
        .collect();
    join_lines(out)
}

/// Lines without their endings; a trailing newline does not add an empty line
/// (a `\r` stays on the line, so CRLF files round-trip).
fn split_lines(text: &str) -> Vec<&str> {
    let mut lines: Vec<&str> = text.split('\n').collect();
    if lines.last() == Some(&"") {
        lines.pop();
    }
    lines
}

fn join_lines<'a>(lines: impl IntoIterator<Item = &'a str>) -> String {
    let v: Vec<&str> = lines.into_iter().collect();
    if v.is_empty() {
        return String::new();
    }
    let mut s = v.join("\n");
    s.push('\n');
    s
}

// ---------------------------------------------------------------------------
// Fetching
// ---------------------------------------------------------------------------

/// How [`sync`] gets a feed. Production uses [`HttpFetcher`]; tests use
/// [`StaticFetcher`] or their own implementation.
pub trait Fetcher {
    /// Return the ICS text at `url`.
    fn fetch(&self, url: &str) -> Result<String, IcsError>;
}

/// Timeout for [`fetch`].
pub const FETCH_TIMEOUT_SECS: u64 = 20;

/// Fetch an ICS feed over HTTP (blocking, `ureq`).
pub fn fetch(url: &str) -> Result<String, IcsError> {
    let agent = ureq::builder()
        .timeout(StdDuration::from_secs(FETCH_TIMEOUT_SECS))
        .build();
    agent
        .get(url)
        .call()
        .map_err(|e| IcsError::Fetch {
            url: url.to_string(),
            source: Box::new(e),
        })?
        .into_string()
        .map_err(|e| IcsError::Body {
            url: url.to_string(),
            source: e,
        })
}

/// The [`Fetcher`] that talks to the network.
#[derive(Clone, Copy, Debug, Default)]
pub struct HttpFetcher;

impl Fetcher for HttpFetcher {
    fn fetch(&self, url: &str) -> Result<String, IcsError> {
        fetch(url)
    }
}

/// A [`Fetcher`] over texts held in memory (fixtures, `--from-file`).
#[derive(Clone, Debug, Default)]
pub struct StaticFetcher {
    feeds: BTreeMap<String, String>,
}

impl StaticFetcher {
    /// Empty.
    pub fn new() -> StaticFetcher {
        StaticFetcher::default()
    }
    /// Add one feed.
    pub fn with(mut self, url: impl Into<String>, text: impl Into<String>) -> StaticFetcher {
        self.feeds.insert(url.into(), text.into());
        self
    }
}

impl Fetcher for StaticFetcher {
    fn fetch(&self, url: &str) -> Result<String, IcsError> {
        self.feeds
            .get(url)
            .cloned()
            .ok_or_else(|| IcsError::NotFound(url.to_string()))
    }
}

// ---------------------------------------------------------------------------
// Sync
// ---------------------------------------------------------------------------

/// Everything one [`sync_report`] produced.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SyncResult {
    /// One `(week, text)` per week in the window, oldest first.
    pub files: Vec<(IsoWeek, String)>,
    /// The occurrences that were written, in start order.
    pub events: Vec<CalEvent>,
    /// Warnings from every feed, prefixed with the URL.
    pub warnings: Vec<String>,
}

/// Fetch every configured feed and produce the calendar file text for each of
/// the three weeks in the §15 window.
///
/// `today` is the current date in `cfg.tz`. `existing` holds the current text
/// of the calendar files that exist, keyed by week; a week that is absent is
/// written from scratch. Fetching or parsing failure of any feed fails the
/// whole sync — no file is half-written.
pub fn sync<F: Fetcher + ?Sized>(
    fetcher: &F,
    cfg: &Config,
    today: NaiveDate,
    existing: &[(IsoWeek, String)],
) -> Result<Vec<(IsoWeek, String)>, IcsError> {
    sync_report(fetcher, cfg, today, existing).map(|r| r.files)
}

/// [`sync`], keeping the events and the warnings.
pub fn sync_report<F: Fetcher + ?Sized>(
    fetcher: &F,
    cfg: &Config,
    today: NaiveDate,
    existing: &[(IsoWeek, String)],
) -> Result<SyncResult, IcsError> {
    let week = IsoWeek::from_date(today);
    let (from, to) = window_for_week(week);
    let opts = ParseOptions::new(cfg.tz).window(from, to);

    let mut events: Vec<CalEvent> = Vec::new();
    let mut warnings: Vec<String> = Vec::new();
    let mut seen: HashSet<(String, NaiveDateTime)> = HashSet::new();
    for url in &cfg.calendar.ics_urls {
        let text = fetcher.fetch(url)?;
        let feed = parse_ics_report(&text, &opts)?;
        warnings.extend(feed.warnings.into_iter().map(|w| format!("{url}: {w}")));
        for e in feed.events {
            if seen.insert((e.uid.clone(), e.start)) {
                events.push(e);
            }
        }
    }
    let mut events = events_in_window(events, from, to);
    events.sort_by(|a, b| {
        a.start
            .cmp(&b.start)
            .then_with(|| a.summary.cmp(&b.summary))
            .then_with(|| a.uid.cmp(&b.uid))
    });

    let files = sync_weeks(week)
        .into_iter()
        .map(|w| {
            let lines = render_calendar_lines(&events, cfg, w);
            let old = existing
                .iter()
                .find(|(k, _)| *k == w)
                .map(|(_, t)| t.as_str());
            (w, merge_calendar_file(old, &lines))
        })
        .collect();
    Ok(SyncResult {
        files,
        events,
        warnings,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::{parse_line, ParseCtx};
    use crate::model::Shape;

    fn dt(s: &str) -> NaiveDateTime {
        NaiveDateTime::parse_from_str(s, "%Y-%m-%dT%H:%M").unwrap()
    }

    fn ics(body: &str) -> String {
        format!(
            "BEGIN:VCALENDAR\r\nVERSION:2.0\r\nPRODID:-//tm//test//EN\r\n{body}END:VCALENDAR\r\n"
        )
    }

    fn chicago() -> ParseOptions {
        ParseOptions::new(chrono_tz::America::Chicago)
    }

    #[test]
    fn utc_times_convert_to_the_target_zone() {
        let text = ics("BEGIN:VEVENT\r\nUID:u1\r\nSUMMARY:Standup\r\nDTSTART:20260908T140000Z\r\nDTEND:20260908T143000Z\r\nEND:VEVENT\r\n");
        let evs = parse_ics_with(&text, &chicago()).unwrap();
        assert_eq!(evs.len(), 1);
        assert_eq!(evs[0].start, dt("2026-09-08T09:00"));
        assert_eq!(evs[0].end, dt("2026-09-08T09:30"));
        assert!(!evs[0].all_day);
        // The same feed read in UTC keeps the UTC wall clock.
        let utc = parse_ics(&text).unwrap();
        assert_eq!(utc[0].start, dt("2026-09-08T14:00"));
    }

    #[test]
    fn tzid_and_floating_times() {
        let text = ics(concat!(
            "BEGIN:VEVENT\r\nUID:tz\r\nSUMMARY:Meeting\r\n",
            "DTSTART;TZID=America/New_York:20260908T090000\r\n",
            "DTEND;TZID=America/New_York:20260908T100000\r\nEND:VEVENT\r\n",
            "BEGIN:VEVENT\r\nUID:float\r\nSUMMARY:Focus\r\n",
            "DTSTART:20260908T130000\r\nDTEND:20260908T140000\r\nEND:VEVENT\r\n",
        ));
        let evs = parse_ics_with(&text, &chicago()).unwrap();
        let by = |uid: &str| evs.iter().find(|e| e.uid == uid).unwrap().clone();
        assert_eq!(by("tz").start, dt("2026-09-08T08:00"));
        assert_eq!(by("float").start, dt("2026-09-08T13:00"));
    }

    #[test]
    fn unknown_tzid_is_a_warning_and_stays_as_written() {
        let text = ics(concat!(
            "BEGIN:VEVENT\r\nUID:win\r\nSUMMARY:Sync\r\n",
            "DTSTART;TZID=Central Standard Time:20260911T090000\r\n",
            "DTEND;TZID=Central Standard Time:20260911T093000\r\nEND:VEVENT\r\n",
        ));
        let feed = parse_ics_report(&text, &chicago()).unwrap();
        assert_eq!(feed.events[0].start, dt("2026-09-11T09:00"));
        assert!(feed.warnings.iter().any(|w| w.contains("unknown TZID")));
    }

    #[test]
    fn prefixed_tzid_resolves() {
        assert_eq!(
            zone_from_tzid("/freeassociation.sourceforge.net/Europe/Berlin"),
            Some(chrono_tz::Europe::Berlin)
        );
        assert_eq!(
            zone_from_tzid("\"America/Chicago\""),
            Some(chrono_tz::America::Chicago)
        );
        assert_eq!(zone_from_tzid("Middle Earth"), None);
    }

    #[test]
    fn all_day_events_keep_the_half_open_ics_convention() {
        let text = ics("BEGIN:VEVENT\r\nUID:ad\r\nSUMMARY:Conference\r\nDTSTART;VALUE=DATE:20260916\r\nDTEND;VALUE=DATE:20260917\r\nEND:VEVENT\r\n");
        let evs = parse_ics_with(&text, &chicago()).unwrap();
        assert!(evs[0].all_day);
        assert_eq!(evs[0].start, dt("2026-09-16T00:00"));
        assert_eq!(evs[0].end, dt("2026-09-17T00:00"));
    }

    #[test]
    fn all_day_without_dtend_is_one_day() {
        let text = ics("BEGIN:VEVENT\r\nUID:ad\r\nSUMMARY:Holiday\r\nDTSTART;VALUE=DATE:20260916\r\nEND:VEVENT\r\n");
        let evs = parse_ics_with(&text, &chicago()).unwrap();
        assert_eq!(evs[0].end, dt("2026-09-17T00:00"));
    }

    #[test]
    fn duration_replaces_dtend() {
        let text = ics("BEGIN:VEVENT\r\nUID:d\r\nSUMMARY:Pages\r\nDTSTART:20260907T063000\r\nDURATION:PT20M\r\nEND:VEVENT\r\n");
        let evs = parse_ics_with(&text, &chicago()).unwrap();
        assert_eq!(evs[0].end, dt("2026-09-07T06:50"));
        assert_eq!(
            parse_ics_duration("P1DT2H30M"),
            Some(Duration::minutes(1590))
        );
        assert_eq!(parse_ics_duration("P2W"), Some(Duration::days(14)));
        assert_eq!(parse_ics_duration("PT45S"), Some(Duration::zero()));
        assert_eq!(parse_ics_duration("nonsense"), None);
    }

    #[test]
    fn cancelled_and_recurrence_id_events_are_dropped() {
        let text = ics(concat!(
            "BEGIN:VEVENT\r\nUID:c\r\nSUMMARY:Gone\r\nSTATUS:CANCELLED\r\n",
            "DTSTART:20260909T110000\r\nDTEND:20260909T120000\r\nEND:VEVENT\r\n",
            "BEGIN:VEVENT\r\nUID:r\r\nSUMMARY:Moved\r\nRECURRENCE-ID:20260909T110000\r\n",
            "DTSTART:20260909T140000\r\nDTEND:20260909T150000\r\nEND:VEVENT\r\n",
        ));
        let feed = parse_ics_report(&text, &chicago()).unwrap();
        assert!(feed.events.is_empty());
        assert_eq!(feed.warnings.len(), 1);
        assert!(feed.warnings[0].contains("RECURRENCE-ID"));
    }

    #[test]
    fn weekly_byday_with_exdate_expands_into_the_window() {
        let text = ics(concat!(
            "BEGIN:VEVENT\r\nUID:lec\r\nSUMMARY:CS 234 lecture\r\n",
            "DTSTART;TZID=America/Chicago:20260902T150000\r\n",
            "DTEND;TZID=America/Chicago:20260902T162000\r\n",
            "RRULE:FREQ=WEEKLY;BYDAY=WE,FR;UNTIL=20260930T045959Z\r\n",
            "EXDATE;TZID=America/Chicago:20260911T150000\r\nEND:VEVENT\r\n",
        ));
        let opts = ParseOptions::for_week(chrono_tz::America::Chicago, IsoWeek::new(2026, 37));
        let evs = parse_ics_with(&text, &opts).unwrap();
        let starts: Vec<String> = evs.iter().map(|e| e.start.to_string()).collect();
        assert_eq!(
            starts,
            vec![
                "2026-09-02 15:00:00",
                "2026-09-04 15:00:00",
                "2026-09-09 15:00:00",
                "2026-09-16 15:00:00",
                "2026-09-18 15:00:00",
            ]
        );
        assert!(evs.iter().all(|e| e.recurring));
        assert_eq!(evs[0].end, dt("2026-09-02T16:20"));
    }

    #[test]
    fn daily_interval_and_count() {
        let text = ics(concat!(
            "BEGIN:VEVENT\r\nUID:mp\r\nSUMMARY:Morning pages\r\n",
            "DTSTART;TZID=America/Chicago:20260907T063000\r\nDURATION:PT20M\r\n",
            "RRULE:FREQ=DAILY;INTERVAL=2;COUNT=5\r\nEND:VEVENT\r\n",
        ));
        let evs = parse_ics_with(&text, &chicago()).unwrap();
        let days: Vec<u32> = evs.iter().map(|e| e.start.day()).collect();
        assert_eq!(days, vec![7, 9, 11, 13, 15]);
    }

    #[test]
    fn monthly_bymonthday_starts_before_the_window() {
        let text = ics(concat!(
            "BEGIN:VEVENT\r\nUID:m11\r\nSUMMARY:Monthly 1:1\r\n",
            "DTSTART;TZID=America/Chicago:20260815T100000\r\n",
            "DTEND;TZID=America/Chicago:20260815T103000\r\n",
            "RRULE:FREQ=MONTHLY;BYMONTHDAY=15\r\nEND:VEVENT\r\n",
        ));
        let opts = ParseOptions::for_week(chrono_tz::America::Chicago, IsoWeek::new(2026, 37));
        let evs = parse_ics_with(&text, &opts).unwrap();
        assert_eq!(evs.len(), 1);
        assert_eq!(evs[0].start, dt("2026-09-15T10:00"));
    }

    #[test]
    fn unsupported_rules_warn_and_keep_the_first_occurrence() {
        let text = ics(concat!(
            "BEGIN:VEVENT\r\nUID:y\r\nSUMMARY:Birthday\r\n",
            "DTSTART;VALUE=DATE:20260913\r\nDTEND;VALUE=DATE:20260914\r\n",
            "RRULE:FREQ=YEARLY\r\nEND:VEVENT\r\n",
        ));
        let feed = parse_ics_report(&text, &chicago()).unwrap();
        assert_eq!(feed.events.len(), 1);
        assert_eq!(feed.events[0].start, dt("2026-09-13T00:00"));
        // Still "from a rule", so its id is occurrence-keyed and would not
        // move if a later version learned to expand the rule.
        assert!(feed.events[0].recurring);
        assert!(feed.warnings[0].contains("FREQ=YEARLY"));
    }

    #[test]
    fn a_recurring_event_keeps_its_wall_clock_across_dst() {
        let text = ics(concat!(
            "BEGIN:VEVENT\r\nUID:dst\r\nSUMMARY:Standing sync\r\n",
            "DTSTART;TZID=America/Chicago:20261028T090000\r\n",
            "DTEND;TZID=America/Chicago:20261028T093000\r\n",
            "RRULE:FREQ=WEEKLY;BYDAY=WE;COUNT=3\r\nEND:VEVENT\r\n",
        ));
        // Chicago leaves DST on 2026-11-01; the wall clock stays 09:00.
        let evs = parse_ics_with(&text, &chicago()).unwrap();
        let starts: Vec<NaiveTime> = evs.iter().map(|e| e.start.time()).collect();
        assert_eq!(starts, vec![NaiveTime::from_hms_opt(9, 0, 0).unwrap(); 3]);
        // Read from another zone the offset change does show.
        let berlin = ParseOptions::new(chrono_tz::Europe::Berlin);
        let evs = parse_ics_with(&text, &berlin).unwrap();
        assert_eq!(evs[0].start, dt("2026-10-28T15:00"));
        assert_eq!(evs[2].start, dt("2026-11-11T16:00"));
    }

    #[test]
    fn window_and_weeks_cover_three_iso_weeks() {
        let w = IsoWeek::new(2026, 37);
        assert_eq!(
            window_for_week(w),
            (dt("2026-08-31T00:00"), dt("2026-09-21T00:00"))
        );
        assert_eq!(
            sync_weeks(w).map(|x| x.to_string()),
            ["2026-W36", "2026-W37", "2026-W38"].map(|s| s.to_string())
        );
    }

    #[test]
    fn events_in_window_keeps_overlaps() {
        let ev = |s: &str, e: &str| CalEvent {
            uid: s.to_string(),
            summary: "x".into(),
            start: dt(s),
            end: dt(e),
            location: None,
            all_day: false,
            recurring: false,
        };
        let (from, to) = (dt("2026-09-07T00:00"), dt("2026-09-14T00:00"));
        let all = vec![
            ev("2026-09-06T09:00", "2026-09-06T10:00"), // before
            ev("2026-09-06T23:00", "2026-09-07T01:00"), // straddles the start
            ev("2026-09-10T09:00", "2026-09-10T10:00"), // inside
            ev("2026-09-13T23:00", "2026-09-14T02:00"), // straddles the end
            ev("2026-09-14T09:00", "2026-09-14T10:00"), // after
        ];
        let kept: Vec<String> = events_in_window(all, from, to)
            .iter()
            .map(|e| e.uid.clone())
            .collect();
        assert_eq!(
            kept,
            vec!["2026-09-06T23:00", "2026-09-10T09:00", "2026-09-13T23:00"]
        );
    }

    #[test]
    fn stable_ids_are_deterministic_and_occurrence_specific() {
        let a = stable_id("uid-1", None);
        assert_eq!(a, stable_id("uid-1", None));
        assert_ne!(a, stable_id("uid-2", None));
        let o1 = stable_id("uid-1", Some(dt("2026-09-09T15:00")));
        let o2 = stable_id("uid-1", Some(dt("2026-09-16T15:00")));
        assert_ne!(o1, o2);
        assert_ne!(o1, a);
        for id in [&a, &o1, &o2] {
            assert_eq!(id.as_str().len(), CAL_ID_LEN);
            assert!(id.as_str().bytes().all(|b| ID_ALPHABET.contains(&b)));
        }
    }

    #[test]
    fn an_occurrence_keeps_its_id_when_the_window_moves() {
        let text = ics(concat!(
            "BEGIN:VEVENT\r\nUID:series\r\nSUMMARY:Standing sync\r\n",
            "DTSTART;TZID=America/Chicago:20260909T090000\r\n",
            "DTEND;TZID=America/Chicago:20260909T093000\r\n",
            "RRULE:FREQ=WEEKLY;BYDAY=WE;COUNT=2\r\nEND:VEVENT\r\n",
        ));
        let read = |from: &str, to: &str| -> Vec<(NaiveDateTime, Id)> {
            let opts = chicago().window(dt(from), dt(to));
            parse_ics_with(&text, &opts)
                .unwrap()
                .iter()
                .map(|e| (e.start, e.id()))
                .collect()
        };
        // One occurrence in the narrow window, two in the wide one; the
        // occurrence they share keeps its id.
        let narrow = read("2026-09-07T00:00", "2026-09-14T00:00");
        let wide = read("2026-09-07T00:00", "2026-09-21T00:00");
        assert_eq!(narrow.len(), 1);
        assert_eq!(wide.len(), 2);
        assert_eq!(narrow[0], wide[0]);
        assert_ne!(wide[0].1, wide[1].1);
    }

    #[test]
    fn classify_uses_the_documented_rule() {
        let re = Regex::new(&Config::default().calendar.flight_regex).unwrap();
        assert_eq!(
            classify_event("UA 1234 ORD→SFO", Some(&re)),
            EventKind::Flight
        );
        assert_eq!(classify_event("✈ to Boston", Some(&re)), EventKind::Flight);
        // A course code matches the default flight regex; the lecture rule wins.
        assert_eq!(
            classify_event("CS 234 lecture", Some(&re)),
            EventKind::Lecture
        );
        assert_eq!(
            classify_event("Meeting w/ host", Some(&re)),
            EventKind::Other
        );
        assert_eq!(EventKind::Flight.ci(), 1);
        assert_eq!(EventKind::Lecture.ci(), 2);
        assert_eq!(EventKind::Other.ci(), 3);
    }

    fn event(summary: &str, start: &str, end: &str, loc: Option<&str>) -> CalEvent {
        CalEvent {
            uid: format!("uid-{summary}"),
            summary: summary.to_string(),
            start: dt(start),
            end: dt(end),
            location: loc.map(|s| s.to_string()),
            all_day: false,
            recurring: false,
        }
    }

    #[test]
    fn rendered_lines_reparse_to_the_same_fields() {
        let cfg = Config::default();
        // In start order, which is the order the lines come out in.
        let evs = vec![
            event(
                "Meeting w/ host",
                "2026-09-07T12:50",
                "2026-09-07T13:50",
                Some("zoom"),
            ),
            event(
                "Retreat",
                "2026-09-11T17:00",
                "2026-09-13T12:00",
                Some("Lake House, WI"),
            ),
            event(
                "UA 1234 ORD→SFO",
                "2026-09-12T08:15",
                "2026-09-12T10:40",
                None,
            ),
        ];
        let lines = render_calendar_lines(&evs, &cfg, IsoWeek::new(2026, 37));
        assert_eq!(lines.len(), 3);
        assert!(
            lines[0].starts_with("- [ ] 3 Meeting w/ host  at:2026-09-07T12:50/13:50 loc:zoom ^")
        );
        assert!(lines[1].contains("at:2026-09-11T17:00/2026-09-13T12:00 loc:Lake-House"));
        assert!(lines[2].starts_with(
            "- [ ] 1 ✈ UA 1234 ORD→SFO  at:2026-09-12T08:15/10:40 buffer:2h travel-day ^"
        ));

        let ctx = ParseCtx::new("calendar/2026-W37.md", cfg.block_min());
        for (line, ev) in lines.iter().zip(&evs) {
            let item = parse_line(line, &ctx).unwrap();
            assert!(item.problems.is_empty(), "{line}: {:?}", item.problems);
            assert_eq!(
                item.shape,
                Shape::Interval {
                    start: ev.start,
                    end: ev.end
                }
            );
            assert_eq!(item.id, ev.id());
            assert!(item.title.contains(ev.summary.split(' ').next().unwrap()));
        }
        let flight = parse_line(&lines[2], &ctx).unwrap();
        assert!(flight.is_travel_day());
        assert_eq!(flight.buffer.map(|d| d.as_minutes()), Some(120));
        assert_eq!(flight.ci, 1);
    }

    #[test]
    fn hostile_summaries_stay_titles() {
        let cfg = Config::default();
        let evs = vec![
            event(
                "review: draft @lab #ops !2 ^x",
                "2026-09-10T16:00",
                "2026-09-10T16:45",
                None,
            ),
            event(
                "2h of deep work",
                "2026-09-10T09:00",
                "2026-09-10T11:00",
                None,
            ),
            event("", "2026-09-10T08:00", "2026-09-10T08:15", None),
        ];
        let lines = render_calendar_lines(&evs, &cfg, IsoWeek::new(2026, 37));
        let ctx = ParseCtx::new("calendar/2026-W37.md", cfg.block_min());
        let titles: Vec<String> = lines
            .iter()
            .map(|l| parse_line(l, &ctx).unwrap().title)
            .collect();
        assert_eq!(
            titles,
            vec![
                "untitled",
                "(2h) of deep work",
                "(review:) draft (@lab) (#ops) (!2) (^x)",
            ]
        );
        for line in &lines {
            let item = parse_line(line, &ctx).unwrap();
            assert!(item.problems.is_empty(), "{line}: {:?}", item.problems);
            assert!(item.parent.is_none() && item.tags.is_empty() && item.priority.is_none());
            assert_eq!(item.ci, 3);
        }
    }

    #[test]
    fn merge_keeps_manual_lines_and_prose() {
        let existing = "\
---
week: 2026-W37
---
# Calendar
- [ ] 3 Old meeting  at:2026-09-07T09:00/10:00 ^aaaaaa
- [ ] 1 Dinner w/ Kun  at:2026-09-10T19:00/20:00 manual ^g4

Notes below the block.
";
        let new = vec!["- [ ] 3 New meeting  at:2026-09-07T12:50/13:50 ^bbbbbb".to_string()];
        let out = merge_calendar_file(Some(existing), &new);
        assert_eq!(
            out,
            "\
---
week: 2026-W37
---
# Calendar
- [ ] 3 New meeting  at:2026-09-07T12:50/13:50 ^bbbbbb
- [ ] 1 Dinner w/ Kun  at:2026-09-10T19:00/20:00 manual ^g4

Notes below the block.
"
        );
        // Idempotent: merging the result again changes nothing.
        assert_eq!(merge_calendar_file(Some(&out), &new), out);
    }

    #[test]
    fn merge_without_an_existing_file_or_generated_lines() {
        let new = vec!["- [ ] 3 A  at:2026-09-07T09:00/10:00 ^aaaaaa".to_string()];
        assert_eq!(
            merge_calendar_file(None, &new),
            "- [ ] 3 A  at:2026-09-07T09:00/10:00 ^aaaaaa\n"
        );
        assert_eq!(merge_calendar_file(None, &[]), "");
        // Only a manual line: the block is appended after it, and stays there.
        let manual = "- [ ] 1 Dinner  at:2026-09-10T19:00/20:00 manual ^g4\n";
        let once = merge_calendar_file(Some(manual), &new);
        assert_eq!(once, format!("{manual}{}\n", new[0]));
        assert_eq!(merge_calendar_file(Some(&once), &new), once);
        // Everything generated is dropped when there is nothing to write.
        assert_eq!(merge_calendar_file(Some(&once), &[]), manual);
    }

    #[test]
    fn merge_preserves_crlf_manual_lines_byte_for_byte() {
        let manual = "- [ ] 1  Dinner   w/ Kun  at:2026-09-10T19:00/20:00  manual  ^g4  \r";
        let existing = format!("- [ ] 3 Old  at:2026-09-07T09:00/10:00 ^aaaaaa\r\n{manual}\n");
        let out = merge_calendar_file(Some(&existing), &[]);
        assert_eq!(out, format!("{manual}\n"));
    }

    #[test]
    fn sync_writes_three_weeks_and_repeats_identically() {
        let text = ics(concat!(
            "BEGIN:VEVENT\r\nUID:lec\r\nSUMMARY:CS 234 lecture\r\n",
            "DTSTART;TZID=America/Chicago:20260902T150000\r\n",
            "DTEND;TZID=America/Chicago:20260902T162000\r\n",
            "RRULE:FREQ=WEEKLY;BYDAY=WE;COUNT=6\r\nLOCATION:JCL\r\nEND:VEVENT\r\n",
        ));
        let mut cfg = Config::default();
        cfg.calendar.ics_urls = vec!["https://example.test/basic.ics".to_string()];
        let fetcher = StaticFetcher::new().with("https://example.test/basic.ics", text);
        let today = NaiveDate::from_ymd_opt(2026, 9, 7).unwrap();
        let files = sync(&fetcher, &cfg, today, &[]).unwrap();
        assert_eq!(files.len(), 3);
        assert_eq!(files[0].0, IsoWeek::new(2026, 36));
        assert!(files[0].1.contains("at:2026-09-02T15:00/16:20 loc:JCL"));
        assert!(files[1].1.contains("at:2026-09-09T15:00/16:20"));
        assert!(files[2].1.contains("at:2026-09-16T15:00/16:20"));
        // Re-running against the written files reproduces them byte for byte.
        let again = sync(&fetcher, &cfg, today, &files).unwrap();
        assert_eq!(again, files);
    }

    #[test]
    fn a_failing_feed_fails_the_sync() {
        let mut cfg = Config::default();
        cfg.calendar.ics_urls = vec!["https://example.test/missing.ics".to_string()];
        let err = sync(
            &StaticFetcher::new(),
            &cfg,
            NaiveDate::from_ymd_opt(2026, 9, 7).unwrap(),
            &[],
        )
        .unwrap_err();
        assert!(matches!(err, IcsError::NotFound(_)));
    }

    #[test]
    fn a_body_that_is_not_a_calendar_is_an_error() {
        assert!(parse_ics("<html>nope</html>").is_err());
        assert!(parse_ics("").unwrap().is_empty());
    }

    #[test]
    fn text_values_are_unescaped_and_collapsed() {
        let text = ics("BEGIN:VEVENT\r\nUID:e\r\nSUMMARY:Dinner w/ Kun\\, then drinks\r\nDTSTART:20260910T190000\r\nDTEND:20260910T200000\r\nEND:VEVENT\r\n");
        let evs = parse_ics_with(&text, &chicago()).unwrap();
        assert_eq!(evs[0].summary, "Dinner w/ Kun, then drinks");
    }
}
