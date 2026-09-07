//! Data model — tm-spec-v1.md §3 (plus `Instance` from §5.1).
//!
//! # API overview
//!
//! * [`Item`] — the one entity. Every field is exactly what the line says;
//!   nothing here is resolved against the tree (parents, ci-from-parent,
//!   effective shape) — that is `tree.rs`. `src` carries the byte-faithful
//!   token list for rewriting (see `grammar.rs`).
//! * Small enums with the spec's names: [`State`], [`Scope`], [`Shape`],
//!   [`WindowRange`], [`Recur`], [`Rule`], [`OnMiss`], [`Budget`], [`Rate`],
//!   [`Period`], [`Dep`], [`Loc`], [`Horizon`], [`Pref`], [`Stamp`].
//! * [`Id`] (bare id; `token()` gives `^id`), [`Ref`] (target written after `@`).
//! * [`Dur`] — minutes plus the unit as written; `Display` formats it back in
//!   that unit; `Dur::blocks(n, block_min)` for tool-written estimates.
//! * [`Moment`] — a date or a date-time exactly as written (`due:` accepts both).
//! * [`YearMonth`] / [`IsoWeek`] — parse/format `2026-09` and `2026-W37`,
//!   with date ranges. [`Horizon::from_path`] derives a horizon from a file path.
//! * [`Instance`], [`InstanceKey`], [`InstanceStatus`] — §5.1 occurrence types.
//!
//! All types derive `Clone, Debug, PartialEq, Serialize, Deserialize`.
//! Equality on [`Dur`] is structural (`2h` ≠ `120m`); compare `.minutes` for
//! semantic equality.

use std::fmt;
use std::str::FromStr;

use chrono::{Datelike, Duration, NaiveDate, NaiveDateTime, NaiveTime, Weekday};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::grammar::ItemLine;

/// Error for the small value parsers in this module.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ModelError {
    /// A value did not match the expected format.
    #[error("invalid {what}: {value:?}")]
    Invalid {
        /// What was being parsed (e.g. `duration`, `year-month`).
        what: &'static str,
        /// The offending text.
        value: String,
    },
}

fn invalid(what: &'static str, value: &str) -> ModelError {
    ModelError::Invalid {
        what,
        value: value.to_string(),
    }
}

// ---------------------------------------------------------------------------
// Ids and refs
// ---------------------------------------------------------------------------

/// A stable item id as written after `^` (any `[A-Za-z0-9_-]+`; the generator
/// produces 4 chars from `[a-z0-9]` minus `l o 0 1`). Empty when the line has
/// no `^id` yet (see [`Item::has_id`]).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize, Default)]
#[serde(transparent)]
pub struct Id(pub String);

impl Id {
    /// Build an id from a bare string (without `^`).
    pub fn new(s: impl Into<String>) -> Id {
        Id(s.into())
    }
    /// The bare id.
    pub fn as_str(&self) -> &str {
        &self.0
    }
    /// The id as a line token: `^id`.
    pub fn token(&self) -> String {
        format!("^{}", self.0)
    }
    /// True when no id has been assigned.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// True when `s` is an acceptable id: non-empty `[A-Za-z0-9_-]+`.
    pub fn is_valid(s: &str) -> bool {
        !s.is_empty()
            && s.chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
    }
}

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<&str> for Id {
    fn from(s: &str) -> Id {
        Id(s.to_string())
    }
}

/// A parent reference as written after `@` (an id in the examples; resolution
/// against the tree happens in `tree.rs`).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Ref(pub String);

impl Ref {
    /// Build a ref from the bare target (without `@`).
    pub fn new(s: impl Into<String>) -> Ref {
        Ref(s.into())
    }
    /// The bare target.
    pub fn as_str(&self) -> &str {
        &self.0
    }
    /// The ref as a line token: `@target`.
    pub fn token(&self) -> String {
        format!("@{}", self.0)
    }
    /// The target interpreted as an [`Id`].
    pub fn to_id(&self) -> Id {
        Id(self.0.clone())
    }
}

impl fmt::Display for Ref {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

// ---------------------------------------------------------------------------
// Durations
// ---------------------------------------------------------------------------

/// The unit a duration was written in. `Blocks(n)` remembers the block count
/// so `Display` can print `nb` again regardless of `block_min`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DurUnit {
    /// `Nb` — N blocks of `config.day.block_min` minutes.
    Blocks(u32),
    /// `Nm`.
    Minutes,
    /// `Nh`.
    Hours,
    /// `NhMm`, e.g. `8h30m`.
    HoursMinutes,
    /// `Nd` (24h days; used by `after-done:`, `on-event:` timeouts).
    Days,
}

/// A duration: total minutes plus the unit it was written in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Dur {
    /// Total minutes.
    pub minutes: u32,
    /// Unit as written; drives `Display`.
    pub unit: DurUnit,
}

impl Dur {
    /// `n` minutes, formatted as `Nm`.
    pub fn from_minutes(n: u32) -> Dur {
        Dur {
            minutes: n,
            unit: DurUnit::Minutes,
        }
    }
    /// `n` hours, formatted as `Nh`.
    pub fn hours(n: u32) -> Dur {
        Dur {
            minutes: n * 60,
            unit: DurUnit::Hours,
        }
    }
    /// `h` hours and `m` minutes, formatted as `NhMm`.
    pub fn hours_minutes(h: u32, m: u32) -> Dur {
        Dur {
            minutes: h * 60 + m,
            unit: DurUnit::HoursMinutes,
        }
    }
    /// `n` days, formatted as `Nd`.
    pub fn days(n: u32) -> Dur {
        Dur {
            minutes: n * 24 * 60,
            unit: DurUnit::Days,
        }
    }
    /// `n` blocks of `block_min` minutes, formatted as `Nb`. Used by
    /// tool-written `est:` edits.
    pub fn blocks(n: u32, block_min: u32) -> Dur {
        Dur {
            minutes: n * block_min,
            unit: DurUnit::Blocks(n),
        }
    }
    /// Minutes formatted in the most compact of `Nm`, `Nh`, `NhMm`.
    pub fn canonical(minutes: u32) -> Dur {
        let unit = if minutes.is_multiple_of(60) && minutes > 0 {
            DurUnit::Hours
        } else if minutes > 60 {
            DurUnit::HoursMinutes
        } else {
            DurUnit::Minutes
        };
        Dur { minutes, unit }
    }
    /// Total minutes.
    pub fn as_minutes(&self) -> u32 {
        self.minutes
    }
    /// Duration as a fractional number of blocks.
    pub fn as_blocks(&self, block_min: u32) -> f64 {
        self.minutes as f64 / block_min.max(1) as f64
    }
    /// Convert to a `chrono::Duration`.
    pub fn to_chrono(&self) -> Duration {
        Duration::minutes(self.minutes as i64)
    }

    /// Parse `Nb | Nm | Nh | NhMm | Nd` (`b` converts via `block_min`).
    pub fn parse(s: &str, block_min: u32) -> Result<Dur, ModelError> {
        let err = || invalid("duration", s);
        let bytes = s.as_bytes();
        if bytes.is_empty() || !bytes[0].is_ascii_digit() {
            return Err(err());
        }
        let digits_end = bytes.iter().position(|b| !b.is_ascii_digit()).ok_or_else(err)?;
        let n: u32 = s[..digits_end].parse().map_err(|_| err())?;
        let rest = &s[digits_end..];
        let mul = |a: u32, b: u32| a.checked_mul(b).ok_or_else(err);
        match rest {
            "b" => Ok(Dur {
                minutes: mul(n, block_min)?,
                unit: DurUnit::Blocks(n),
            }),
            "m" => Ok(Dur::from_minutes(n)),
            "h" => Ok(Dur {
                minutes: mul(n, 60)?,
                unit: DurUnit::Hours,
            }),
            "d" => Ok(Dur {
                minutes: mul(n, 24 * 60)?,
                unit: DurUnit::Days,
            }),
            _ => {
                // NhMm
                let r = rest.strip_prefix('h').ok_or_else(err)?;
                let m_str = r.strip_suffix('m').ok_or_else(err)?;
                if m_str.is_empty() || !m_str.bytes().all(|b| b.is_ascii_digit()) {
                    return Err(err());
                }
                let m: u32 = m_str.parse().map_err(|_| err())?;
                Ok(Dur {
                    minutes: mul(n, 60)?.checked_add(m).ok_or_else(err)?,
                    unit: DurUnit::HoursMinutes,
                })
            }
        }
    }

    /// Parse without the `d` unit (leading estimates and `est:`/`dur:` values).
    pub fn parse_no_days(s: &str, block_min: u32) -> Result<Dur, ModelError> {
        let d = Dur::parse(s, block_min)?;
        if d.unit == DurUnit::Days {
            return Err(invalid("duration", s));
        }
        Ok(d)
    }
}

impl fmt::Display for Dur {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.unit {
            DurUnit::Blocks(n) => write!(f, "{n}b"),
            DurUnit::Minutes => write!(f, "{}m", self.minutes),
            DurUnit::Hours if self.minutes.is_multiple_of(60) => write!(f, "{}h", self.minutes / 60),
            DurUnit::Hours | DurUnit::HoursMinutes => {
                write!(f, "{}h{}m", self.minutes / 60, self.minutes % 60)
            }
            DurUnit::Days if self.minutes.is_multiple_of(1440) => write!(f, "{}d", self.minutes / 1440),
            DurUnit::Days => write!(f, "{}m", self.minutes),
        }
    }
}

// ---------------------------------------------------------------------------
// Time helpers
// ---------------------------------------------------------------------------

/// A date or a date-time, exactly as written (`due:2026-09-11` vs
/// `due:2026-09-11T23:59`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Moment {
    /// `YYYY-MM-DD`.
    Date(NaiveDate),
    /// `YYYY-MM-DDTHH:MM`.
    DateTime(NaiveDateTime),
}

impl Moment {
    /// The calendar date.
    pub fn date(&self) -> NaiveDate {
        match self {
            Moment::Date(d) => *d,
            Moment::DateTime(dt) => dt.date(),
        }
    }
    /// The date-time, using `default_time` for a bare date.
    pub fn to_datetime(&self, default_time: NaiveTime) -> NaiveDateTime {
        match self {
            Moment::Date(d) => d.and_time(default_time),
            Moment::DateTime(dt) => *dt,
        }
    }
    /// The date-time, treating a bare date as `23:59` that day.
    pub fn end_of_day(&self) -> NaiveDateTime {
        self.to_datetime(NaiveTime::from_hms_opt(23, 59, 0).expect("valid time"))
    }
    /// Parse `YYYY-MM-DD` or `YYYY-MM-DDTHH:MM`.
    pub fn parse(s: &str) -> Result<Moment, ModelError> {
        if let Ok(d) = parse_date(s) {
            return Ok(Moment::Date(d));
        }
        parse_datetime(s)
            .map(Moment::DateTime)
            .map_err(|_| invalid("date or date-time", s))
    }
}

impl fmt::Display for Moment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Moment::Date(d) => write!(f, "{}", d.format("%Y-%m-%d")),
            Moment::DateTime(dt) => write!(f, "{}", dt.format("%Y-%m-%dT%H:%M")),
        }
    }
}

/// Parse `YYYY-MM-DD` (zero-padded).
pub fn parse_date(s: &str) -> Result<NaiveDate, ModelError> {
    if s.len() != 10 {
        return Err(invalid("date", s));
    }
    NaiveDate::parse_from_str(s, "%Y-%m-%d").map_err(|_| invalid("date", s))
}

/// Parse `HH:MM` (seconds not accepted).
pub fn parse_time(s: &str) -> Result<NaiveTime, ModelError> {
    if s.len() != 5 {
        return Err(invalid("time", s));
    }
    NaiveTime::parse_from_str(s, "%H:%M").map_err(|_| invalid("time", s))
}

/// Parse `YYYY-MM-DDTHH:MM` (zero-padded).
pub fn parse_datetime(s: &str) -> Result<NaiveDateTime, ModelError> {
    if s.len() != 16 {
        return Err(invalid("date-time", s));
    }
    NaiveDateTime::parse_from_str(s, "%Y-%m-%dT%H:%M").map_err(|_| invalid("date-time", s))
}

/// Format `HH:MM`.
pub fn fmt_time(t: NaiveTime) -> String {
    t.format("%H:%M").to_string()
}

/// Format `YYYY-MM-DDTHH:MM`.
pub fn fmt_datetime(dt: NaiveDateTime) -> String {
    dt.format("%Y-%m-%dT%H:%M").to_string()
}

/// Parse a weekday name (`Mon`, `monday`, …).
pub fn parse_weekday(s: &str) -> Result<Weekday, ModelError> {
    s.parse::<Weekday>().map_err(|_| invalid("weekday", s))
}

/// A calendar month, e.g. `2026-09`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct YearMonth {
    /// Four-digit year.
    pub year: i32,
    /// Month 1..=12.
    pub month: u32,
}

impl YearMonth {
    /// Build from year and month (1..=12).
    pub fn new(year: i32, month: u32) -> YearMonth {
        YearMonth { year, month }
    }
    /// Parse `YYYY-MM`.
    pub fn parse(s: &str) -> Result<YearMonth, ModelError> {
        let err = || invalid("year-month", s);
        let (y, m) = s.split_once('-').ok_or_else(err)?;
        if y.len() != 4 || m.len() != 2 {
            return Err(err());
        }
        let year: i32 = y.parse().map_err(|_| err())?;
        let month: u32 = m.parse().map_err(|_| err())?;
        if !(1..=12).contains(&month) {
            return Err(err());
        }
        Ok(YearMonth { year, month })
    }
    /// The month containing `date`.
    pub fn from_date(date: NaiveDate) -> YearMonth {
        YearMonth {
            year: date.year(),
            month: date.month(),
        }
    }
    /// First day of the month.
    pub fn first_day(&self) -> NaiveDate {
        NaiveDate::from_ymd_opt(self.year, self.month, 1).expect("valid year-month")
    }
    /// Last day of the month.
    pub fn last_day(&self) -> NaiveDate {
        self.next().first_day().pred_opt().expect("valid date")
    }
    /// Inclusive date range of the month.
    pub fn range(&self) -> (NaiveDate, NaiveDate) {
        (self.first_day(), self.last_day())
    }
    /// True when `date` falls in this month.
    pub fn contains(&self, date: NaiveDate) -> bool {
        YearMonth::from_date(date) == *self
    }
    /// The following month.
    pub fn next(&self) -> YearMonth {
        if self.month == 12 {
            YearMonth::new(self.year + 1, 1)
        } else {
            YearMonth::new(self.year, self.month + 1)
        }
    }
    /// The preceding month.
    pub fn prev(&self) -> YearMonth {
        if self.month == 1 {
            YearMonth::new(self.year - 1, 12)
        } else {
            YearMonth::new(self.year, self.month - 1)
        }
    }
}

impl fmt::Display for YearMonth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:04}-{:02}", self.year, self.month)
    }
}

impl FromStr for YearMonth {
    type Err = ModelError;
    fn from_str(s: &str) -> Result<YearMonth, ModelError> {
        YearMonth::parse(s)
    }
}

/// An ISO week, e.g. `2026-W37` (Monday..Sunday).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct IsoWeek {
    /// ISO week-based year.
    pub year: i32,
    /// ISO week number 1..=53.
    pub week: u32,
}

impl IsoWeek {
    /// Build from ISO year and week number.
    pub fn new(year: i32, week: u32) -> IsoWeek {
        IsoWeek { year, week }
    }
    /// Parse `YYYY-Www`.
    pub fn parse(s: &str) -> Result<IsoWeek, ModelError> {
        let err = || invalid("iso-week", s);
        let (y, w) = s.split_once("-W").ok_or_else(err)?;
        if y.len() != 4 || w.len() != 2 {
            return Err(err());
        }
        let year: i32 = y.parse().map_err(|_| err())?;
        let week: u32 = w.parse().map_err(|_| err())?;
        if !(1..=53).contains(&week) {
            return Err(err());
        }
        // Validate that the week exists in that ISO year.
        NaiveDate::from_isoywd_opt(year, week, Weekday::Mon).ok_or_else(err)?;
        Ok(IsoWeek { year, week })
    }
    /// The ISO week containing `date`.
    pub fn from_date(date: NaiveDate) -> IsoWeek {
        let iw = date.iso_week();
        IsoWeek {
            year: iw.year(),
            week: iw.week(),
        }
    }
    /// Monday of the week.
    pub fn monday(&self) -> NaiveDate {
        NaiveDate::from_isoywd_opt(self.year, self.week, Weekday::Mon).expect("valid iso week")
    }
    /// Sunday of the week.
    pub fn sunday(&self) -> NaiveDate {
        NaiveDate::from_isoywd_opt(self.year, self.week, Weekday::Sun).expect("valid iso week")
    }
    /// Inclusive date range Monday..Sunday.
    pub fn range(&self) -> (NaiveDate, NaiveDate) {
        (self.monday(), self.sunday())
    }
    /// All seven dates of the week, Monday first.
    pub fn dates(&self) -> Vec<NaiveDate> {
        let m = self.monday();
        (0..7).map(|i| m + Duration::days(i)).collect()
    }
    /// True when `date` falls in this week.
    pub fn contains(&self, date: NaiveDate) -> bool {
        IsoWeek::from_date(date) == *self
    }
    /// The following week.
    pub fn next(&self) -> IsoWeek {
        IsoWeek::from_date(self.monday() + Duration::days(7))
    }
    /// The preceding week.
    pub fn prev(&self) -> IsoWeek {
        IsoWeek::from_date(self.monday() - Duration::days(7))
    }
    /// Short label without the year: `W37`.
    pub fn short(&self) -> String {
        format!("W{:02}", self.week)
    }
}

impl fmt::Display for IsoWeek {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:04}-W{:02}", self.year, self.week)
    }
}

impl FromStr for IsoWeek {
    type Err = ModelError;
    fn from_str(s: &str) -> Result<IsoWeek, ModelError> {
        IsoWeek::parse(s)
    }
}

// ---------------------------------------------------------------------------
// Enums
// ---------------------------------------------------------------------------

/// Checkbox state: `[ ] [>] [x] [-] [~] [?]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum State {
    /// `[ ]`
    #[default]
    Todo,
    /// `[>]`
    Active,
    /// `[x]`
    Done,
    /// `[-]`
    Demoted,
    /// `[~]`
    Dropped,
    /// `[?]`
    Waiting,
}

impl State {
    /// The bracket form, e.g. `[ ]`.
    pub fn as_str(&self) -> &'static str {
        match self {
            State::Todo => "[ ]",
            State::Active => "[>]",
            State::Done => "[x]",
            State::Demoted => "[-]",
            State::Dropped => "[~]",
            State::Waiting => "[?]",
        }
    }
    /// The character inside the brackets.
    pub fn glyph(&self) -> char {
        self.as_str().chars().nth(1).expect("three chars")
    }
    /// Parse the bracket form or the bare inner character.
    pub fn parse(s: &str) -> Result<State, ModelError> {
        let inner = s.strip_prefix('[').and_then(|r| r.strip_suffix(']')).unwrap_or(s);
        match inner {
            " " => Ok(State::Todo),
            ">" => Ok(State::Active),
            "x" | "X" => Ok(State::Done),
            "-" => Ok(State::Demoted),
            "~" => Ok(State::Dropped),
            "?" => Ok(State::Waiting),
            _ => Err(invalid("state", s)),
        }
    }
    /// Parse from the glyph character.
    pub fn from_glyph(c: char) -> Option<State> {
        match c {
            ' ' => Some(State::Todo),
            '>' => Some(State::Active),
            'x' | 'X' => Some(State::Done),
            '-' => Some(State::Demoted),
            '~' => Some(State::Dropped),
            '?' => Some(State::Waiting),
            _ => None,
        }
    }
    /// True for `Todo` and `Active` — the states the planner considers.
    pub fn is_open(&self) -> bool {
        matches!(self, State::Todo | State::Active)
    }
    /// True for `Done` and `Dropped` — the states that end a series item.
    pub fn is_closed(&self) -> bool {
        matches!(self, State::Done | State::Dropped)
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Finite (default) or open-ended (`open` flag, routines, optional).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum Scope {
    /// Work that finishes.
    #[default]
    Finite,
    /// Recurring/ongoing; never "done" as a whole.
    Open,
}

/// Where in time an item lives, from `due:` / `at:` / `win:`+`dur:`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum Shape {
    /// No temporal shape.
    #[default]
    None,
    /// `due:` — a deadline.
    Point {
        /// The deadline as written (date or date-time).
        due: Moment,
    },
    /// `at:` — a fixed wall.
    Interval {
        /// Start.
        start: NaiveDateTime,
        /// End.
        end: NaiveDateTime,
    },
    /// `win:` + `dur:` — a duration to place somewhere inside a range.
    Window {
        /// The range.
        range: WindowRange,
        /// The duration to place.
        dur: Dur,
    },
}

impl Shape {
    /// Default `on_miss` for this shape (§5.3): Window → Expire, else Persist.
    pub fn default_on_miss(&self) -> OnMiss {
        match self {
            Shape::Window { .. } => OnMiss::Expire,
            _ => OnMiss::Persist,
        }
    }
}

/// The range of a window: a daily time-of-day range (overnight allowed) or an
/// absolute date-time range.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WindowRange {
    /// `win:11:30-13:30` (or overnight `win:22:00-08:00`).
    Daily {
        /// Opening time.
        from: NaiveTime,
        /// Closing time; `to <= from` means the window crosses midnight.
        to: NaiveTime,
    },
    /// `win:2026-09-07T14:00/17:00`.
    Absolute {
        /// Opening date-time.
        from: NaiveDateTime,
        /// Closing date-time.
        to: NaiveDateTime,
    },
}

impl WindowRange {
    /// True for a daily window whose end is at or before its start.
    pub fn is_overnight(&self) -> bool {
        matches!(self, WindowRange::Daily { from, to } if to <= from)
    }
    /// Parse the `win:` value.
    pub fn parse(s: &str) -> Result<WindowRange, ModelError> {
        let err = || invalid("window", s);
        if s.contains('T') {
            let (from, to) = parse_interval(s)?;
            Ok(WindowRange::Absolute { from, to })
        } else {
            let (a, b) = s.split_once('-').ok_or_else(err)?;
            Ok(WindowRange::Daily {
                from: parse_time(a).map_err(|_| err())?,
                to: parse_time(b).map_err(|_| err())?,
            })
        }
    }
}

impl fmt::Display for WindowRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WindowRange::Daily { from, to } => write!(f, "{}-{}", fmt_time(*from), fmt_time(*to)),
            WindowRange::Absolute { from, to } => f.write_str(&fmt_interval(*from, *to)),
        }
    }
}

/// Parse `YYYY-MM-DDTHH:MM/HH:MM` (end on the same day; an end before the
/// start rolls to the next day) or `YYYY-MM-DDTHH:MM/YYYY-MM-DDTHH:MM`.
pub fn parse_interval(s: &str) -> Result<(NaiveDateTime, NaiveDateTime), ModelError> {
    let err = || invalid("interval", s);
    let (a, b) = s.split_once('/').ok_or_else(err)?;
    let start = parse_datetime(a).map_err(|_| err())?;
    let end = if b.contains('T') {
        parse_datetime(b).map_err(|_| err())?
    } else {
        let t = parse_time(b).map_err(|_| err())?;
        let mut end = start.date().and_time(t);
        if end < start {
            end += Duration::days(1);
        }
        end
    };
    Ok((start, end))
}

/// Format an interval the way the grammar writes it: same-day ends as `HH:MM`,
/// otherwise a full date-time.
pub fn fmt_interval(start: NaiveDateTime, end: NaiveDateTime) -> String {
    if end.date() == start.date() && end >= start {
        format!("{}/{}", fmt_datetime(start), fmt_time(end.time()))
    } else {
        format!("{}/{}", fmt_datetime(start), fmt_datetime(end))
    }
}

/// Preferred anchor inside a window (`pref:`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pref {
    /// `pref:wake+10m`.
    WakePlus(Dur),
    /// `pref:12:00`.
    At(NaiveTime),
}

impl Pref {
    /// Parse the `pref:` value.
    pub fn parse(s: &str, block_min: u32) -> Result<Pref, ModelError> {
        if let Some(rest) = s.strip_prefix("wake+") {
            return Dur::parse(rest, block_min)
                .map(Pref::WakePlus)
                .map_err(|_| invalid("pref", s));
        }
        if s == "wake" {
            return Ok(Pref::WakePlus(Dur::from_minutes(0)));
        }
        parse_time(s).map(Pref::At).map_err(|_| invalid("pref", s))
    }
}

impl fmt::Display for Pref {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pref::WakePlus(d) => write!(f, "wake+{d}"),
            Pref::At(t) => f.write_str(&fmt_time(*t)),
        }
    }
}

/// Recurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum Recur {
    /// Not recurring.
    #[default]
    None,
    /// `every:` — calendar rule.
    Calendar(Rule),
    /// `after-done:2d~1d` — next instance `offset` after the last completion,
    /// valid for `window` after that.
    AfterDone {
        /// Offset from the last completion.
        offset: Dur,
        /// Validity window after the due point.
        window: Option<Dur>,
    },
    /// `on-event:reply/7d` — next instance when the named event arrives or the
    /// timeout elapses.
    OnEvent {
        /// Event name.
        name: String,
        /// Timeout after which the wait ends anyway.
        timeout: Option<Dur>,
    },
}

impl Recur {
    /// Parse an `after-done:` value (`2d` or `2d~1d`).
    pub fn parse_after_done(s: &str, block_min: u32) -> Result<Recur, ModelError> {
        let err = || invalid("after-done", s);
        let (a, b) = match s.split_once('~') {
            Some((a, b)) => (a, Some(b)),
            None => (s, None),
        };
        Ok(Recur::AfterDone {
            offset: Dur::parse(a, block_min).map_err(|_| err())?,
            window: b.map(|w| Dur::parse(w, block_min).map_err(|_| err())).transpose()?,
        })
    }
    /// Parse an `on-event:` value (`reply` or `reply/7d`).
    pub fn parse_on_event(s: &str, block_min: u32) -> Result<Recur, ModelError> {
        let err = || invalid("on-event", s);
        let (name, t) = match s.split_once('/') {
            Some((a, b)) => (a, Some(b)),
            None => (s, None),
        };
        if !Id::is_valid(name) {
            return Err(err());
        }
        Ok(Recur::OnEvent {
            name: name.to_string(),
            timeout: t.map(|w| Dur::parse(w, block_min).map_err(|_| err())).transpose()?,
        })
    }
    /// The `key:value` token for this recurrence, if any.
    pub fn token(&self) -> Option<String> {
        match self {
            Recur::None => None,
            Recur::Calendar(r) => Some(format!("every:{r}")),
            Recur::AfterDone { offset, window } => Some(match window {
                Some(w) => format!("after-done:{offset}~{w}"),
                None => format!("after-done:{offset}"),
            }),
            Recur::OnEvent { name, timeout } => Some(match timeout {
                Some(t) => format!("on-event:{name}/{t}"),
                None => format!("on-event:{name}"),
            }),
        }
    }
}

/// Calendar recurrence rule (`every:`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Rule {
    /// `every:day`.
    Daily,
    /// `every:weekday` — Monday to Friday.
    Weekdays,
    /// `every:Mon,Wed,Fri`.
    Weekly(Vec<Weekday>),
    /// `every:3d`.
    EveryNDays(u32),
    /// `every:2w:Sun`.
    EveryNWeeks(u32, Weekday),
    /// `every:month:15` — day of month.
    Monthly(u8),
    /// `every:week` / `every:2w` — once every N weeks, any day
    /// (not in the spec's enum; needed by the `every:week` routines example).
    Weeks(u32),
}

impl Rule {
    /// Parse the `every:` value.
    pub fn parse(s: &str) -> Result<Rule, ModelError> {
        let err = || invalid("every", s);
        if s.is_empty() {
            return Err(err());
        }
        match s {
            "day" | "daily" => return Ok(Rule::Daily),
            "weekday" | "weekdays" => return Ok(Rule::Weekdays),
            "week" | "weekly" => return Ok(Rule::Weeks(1)),
            _ => {}
        }
        if let Some(day) = s.strip_prefix("month:") {
            let d: u8 = day.parse().map_err(|_| err())?;
            if !(1..=31).contains(&d) {
                return Err(err());
            }
            return Ok(Rule::Monthly(d));
        }
        if s.as_bytes()[0].is_ascii_digit() {
            let digits_end = s
                .bytes()
                .position(|b| !b.is_ascii_digit())
                .ok_or_else(err)?;
            let n: u32 = s[..digits_end].parse().map_err(|_| err())?;
            if n == 0 {
                return Err(err());
            }
            let rest = &s[digits_end..];
            return match rest {
                "d" => Ok(Rule::EveryNDays(n)),
                "w" => Ok(Rule::Weeks(n)),
                _ => {
                    let wd = rest.strip_prefix("w:").ok_or_else(err)?;
                    Ok(Rule::EveryNWeeks(n, parse_weekday(wd).map_err(|_| err())?))
                }
            };
        }
        let days = s
            .split(',')
            .map(|d| parse_weekday(d.trim()).map_err(|_| err()))
            .collect::<Result<Vec<_>, _>>()?;
        if days.is_empty() {
            return Err(err());
        }
        Ok(Rule::Weekly(days))
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rule::Daily => f.write_str("day"),
            Rule::Weekdays => f.write_str("weekday"),
            Rule::Weekly(days) => {
                let names: Vec<String> = days.iter().map(|d| d.to_string()).collect();
                f.write_str(&names.join(","))
            }
            Rule::EveryNDays(n) => write!(f, "{n}d"),
            Rule::EveryNWeeks(n, wd) => write!(f, "{n}w:{wd}"),
            Rule::Monthly(d) => write!(f, "month:{d}"),
            Rule::Weeks(1) => f.write_str("week"),
            Rule::Weeks(n) => write!(f, "{n}w"),
        }
    }
}

/// What happens to a missed instance (§5.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum OnMiss {
    /// Instance expires; nothing carried.
    Expire,
    /// Stays pending, overdue.
    Persist,
    /// Skipped; next occurrence unchanged.
    Next,
}

impl OnMiss {
    /// Parse `expire | persist | next`.
    pub fn parse(s: &str) -> Result<OnMiss, ModelError> {
        match s {
            "expire" => Ok(OnMiss::Expire),
            "persist" => Ok(OnMiss::Persist),
            "next" => Ok(OnMiss::Next),
            _ => Err(invalid("on-miss", s)),
        }
    }
    /// The value as written.
    pub fn as_str(&self) -> &'static str {
        match self {
            OnMiss::Expire => "expire",
            OnMiss::Persist => "persist",
            OnMiss::Next => "next",
        }
    }
}

impl fmt::Display for OnMiss {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Budget period.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Period {
    /// `/d`
    Day,
    /// `/w`
    Week,
    /// `/m`
    Month,
}

impl Period {
    /// Parse `d | w | m` (also `day | week | month`).
    pub fn parse(s: &str) -> Result<Period, ModelError> {
        match s {
            "d" | "day" => Ok(Period::Day),
            "w" | "week" => Ok(Period::Week),
            "m" | "month" => Ok(Period::Month),
            _ => Err(invalid("period", s)),
        }
    }
    /// The one-letter form.
    pub fn as_str(&self) -> &'static str {
        match self {
            Period::Day => "d",
            Period::Week => "w",
            Period::Month => "m",
        }
    }
}

impl fmt::Display for Period {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// An amount per period, e.g. `6b/w`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Rate {
    /// The amount.
    pub amount: Dur,
    /// Per day, week, or month.
    pub per: Period,
}

impl Rate {
    /// Parse `<dur>/<d|w|m>`.
    pub fn parse(s: &str, block_min: u32) -> Result<Rate, ModelError> {
        let err = || invalid("rate", s);
        let (a, p) = s.split_once('/').ok_or_else(err)?;
        Ok(Rate {
            amount: Dur::parse(a, block_min).map_err(|_| err())?,
            per: Period::parse(p).map_err(|_| err())?,
        })
    }
}

impl fmt::Display for Rate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.amount, self.per)
    }
}

/// Budget floor (`min:`) and cap (`max:`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct Budget {
    /// `min:` — at least this much per period.
    pub floor: Option<Rate>,
    /// `max:` / `cap:` — at most this much per period.
    pub cap: Option<Rate>,
}

/// A dependency (`after:`).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Dep {
    /// `^id` — wait for that item to be Done.
    Item(Id),
    /// `event:name` — wait for `tm event name`.
    Event(String),
}

impl Dep {
    /// Parse one `after:` element: `^id`, bare `id`, or `event:name`.
    pub fn parse(s: &str) -> Result<Dep, ModelError> {
        if let Some(name) = s.strip_prefix("event:") {
            if Id::is_valid(name) {
                return Ok(Dep::Event(name.to_string()));
            }
            return Err(invalid("dependency", s));
        }
        let id = s.strip_prefix('^').unwrap_or(s);
        if Id::is_valid(id) {
            Ok(Dep::Item(Id::new(id)))
        } else {
            Err(invalid("dependency", s))
        }
    }
    /// Parse a comma-separated `after:` list.
    pub fn parse_list(s: &str) -> Result<Vec<Dep>, ModelError> {
        s.split(',')
            .map(|d| Dep::parse(d.trim()))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| invalid("after", s))
    }
}

impl fmt::Display for Dep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Dep::Item(id) => f.write_str(&id.token()),
            Dep::Event(n) => write!(f, "event:{n}"),
        }
    }
}

/// Location constraint (`loc:`).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum Loc {
    /// No constraint.
    #[default]
    Any,
    /// `loc:lounge`
    Lounge,
    /// `loc:home`
    Home,
    /// `loc:out`
    Out,
    /// Any other name, e.g. `loc:zoom`, `loc:JCL`.
    Named(String),
}

impl Loc {
    /// Parse the `loc:` value (case-sensitive for named locations).
    pub fn parse(s: &str) -> Result<Loc, ModelError> {
        match s {
            "" => Err(invalid("loc", s)),
            "any" => Ok(Loc::Any),
            "lounge" => Ok(Loc::Lounge),
            "home" => Ok(Loc::Home),
            "out" => Ok(Loc::Out),
            other => Ok(Loc::Named(other.to_string())),
        }
    }
    /// The value as written.
    pub fn as_str(&self) -> &str {
        match self {
            Loc::Any => "any",
            Loc::Lounge => "lounge",
            Loc::Home => "home",
            Loc::Out => "out",
            Loc::Named(n) => n,
        }
    }
}

impl fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Which planning conversation a line belongs to — derived from its file path.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum Horizon {
    /// `backlog.md` (horizon none).
    #[default]
    Backlog,
    /// `month/YYYY-MM.md`.
    Month(YearMonth),
    /// `week/YYYY-Www.md`.
    Week(IsoWeek),
    /// `day/YYYY-MM-DD.md`.
    Day(NaiveDate),
    /// `routines.md`.
    Routine,
    /// `optional.md`.
    Optional,
    /// `calendar/YYYY-Www.md`.
    Calendar(IsoWeek),
    /// `inbox.md`.
    Inbox,
}

impl Horizon {
    /// Derive the horizon from a file path such as `plan/week/2026-W37.md`.
    /// Returns `None` for paths that are not one of the eight file kinds.
    pub fn from_path(path: &str) -> Option<Horizon> {
        let norm = path.replace('\\', "/");
        let mut parts = norm.rsplit('/');
        let file = parts.next()?;
        let dir = parts.next().unwrap_or("");
        let stem = file.strip_suffix(".md")?;
        match dir {
            "month" => YearMonth::parse(stem).ok().map(Horizon::Month),
            "week" => IsoWeek::parse(stem).ok().map(Horizon::Week),
            "day" => parse_date(stem).ok().map(Horizon::Day),
            "calendar" => IsoWeek::parse(stem).ok().map(Horizon::Calendar),
            _ => match stem {
                "backlog" => Some(Horizon::Backlog),
                "routines" => Some(Horizon::Routine),
                "optional" => Some(Horizon::Optional),
                "inbox" => Some(Horizon::Inbox),
                _ => None,
            },
        }
    }
    /// The relative file path for this horizon, e.g. `week/2026-W37.md`.
    pub fn path(&self) -> String {
        match self {
            Horizon::Backlog => "backlog.md".to_string(),
            Horizon::Month(m) => format!("month/{m}.md"),
            Horizon::Week(w) => format!("week/{w}.md"),
            Horizon::Day(d) => format!("day/{}.md", d.format("%Y-%m-%d")),
            Horizon::Routine => "routines.md".to_string(),
            Horizon::Optional => "optional.md".to_string(),
            Horizon::Calendar(w) => format!("calendar/{w}.md"),
            Horizon::Inbox => "inbox.md".to_string(),
        }
    }
    /// Default `ci` for lines in this file kind without an explicit ci:
    /// routines 1, optional 0, otherwise 3.
    pub fn default_ci(&self) -> u8 {
        match self {
            Horizon::Routine => 1,
            Horizon::Optional => 0,
            _ => 3,
        }
    }
    /// True for files whose lines are implicitly `open` and may omit the state.
    pub fn is_open_file(&self) -> bool {
        matches!(self, Horizon::Routine | Horizon::Optional)
    }
    /// True for files where a missing state is not a problem
    /// (routines, optional, inbox).
    pub fn allows_missing_state(&self) -> bool {
        matches!(self, Horizon::Routine | Horizon::Optional | Horizon::Inbox)
    }
}

impl fmt::Display for Horizon {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Horizon::Backlog => f.write_str("backlog"),
            Horizon::Month(m) => write!(f, "month {m}"),
            Horizon::Week(w) => write!(f, "week {w}"),
            Horizon::Day(d) => write!(f, "day {}", d.format("%Y-%m-%d")),
            Horizon::Routine => f.write_str("routines"),
            Horizon::Optional => f.write_str("optional"),
            Horizon::Calendar(w) => write!(f, "calendar {w}"),
            Horizon::Inbox => f.write_str("inbox"),
        }
    }
}

/// A demotion stamp: `W37` (week) or `D07` (day of month).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Stamp {
    /// `W37` — demoted at the close of ISO week 37.
    Week(u32),
    /// `D07` — demoted at the close of day 7.
    Day(u32),
}

impl Stamp {
    /// Parse `W\d+` or `D\d+`.
    pub fn parse(s: &str) -> Result<Stamp, ModelError> {
        let err = || invalid("stamp", s);
        let (kind, n) = s.split_at(if s.is_empty() { 0 } else { 1 });
        if n.is_empty() || !n.bytes().all(|b| b.is_ascii_digit()) {
            return Err(err());
        }
        let n: u32 = n.parse().map_err(|_| err())?;
        match kind {
            "W" => Ok(Stamp::Week(n)),
            "D" => Ok(Stamp::Day(n)),
            _ => Err(err()),
        }
    }
    /// Parse a comma-separated `demoted:` list.
    pub fn parse_list(s: &str) -> Result<Vec<Stamp>, ModelError> {
        s.split(',')
            .map(|p| Stamp::parse(p.trim()))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| invalid("demoted", s))
    }
}

impl fmt::Display for Stamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stamp::Week(n) => write!(f, "W{n:02}"),
            Stamp::Day(n) => write!(f, "D{n:02}"),
        }
    }
}

/// Tool-written stamps.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct Stamps {
    /// `demoted:W36,W37` / `demoted:D07`.
    pub demoted: Vec<Stamp>,
    /// `waiting:2026-09-05` — set together with state `[?]`.
    pub waiting_since: Option<NaiveDate>,
}

impl Stamps {
    /// `demoted:` value as written (`W36,W37`).
    pub fn demoted_value(&self) -> String {
        self.demoted
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join(",")
    }
}

/// Where a line came from, with the byte-faithful token list.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, Default)]
pub struct SourceLoc {
    /// File path as given to the parser.
    pub file: String,
    /// 1-based line number.
    pub line: usize,
    /// Text of the enclosing heading (without `#`s), if any.
    pub section: Option<String>,
    /// The line's tokens; `tokens.to_string()` is the original line.
    pub tokens: ItemLine,
}

// ---------------------------------------------------------------------------
// The entity
// ---------------------------------------------------------------------------

/// The one entity (§3.1). Fields are exactly what the line says; see the
/// module docs for what is *not* resolved here.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Item {
    /// `^id`; empty when missing (see [`Item::has_id`]).
    pub id: Id,
    /// Title text (plus any unclassifiable bare words found after the tokens).
    pub title: String,
    /// `[ ]` … ; `Todo` when omitted (routines, optional, inbox).
    pub state: State,
    /// Min-energy 0..=5; the file default (routines 1, optional 0, else 3)
    /// when absent — `tree.rs` applies the parent's ci when `!ci_explicit`.
    pub ci: u8,
    /// True when the line carries a ci (positional or `ci:`).
    pub ci_explicit: bool,
    /// `est:` — remaining estimate (tool-written after partial work).
    pub est: Option<Dur>,
    /// The leading estimate as written.
    pub est_original: Option<Dur>,
    /// `dur:` as written (also inside `Shape::Window` when `win:` is present;
    /// optional items carry a bare `dur:`).
    pub dur: Option<Dur>,
    /// `!k`, 1..=4.
    pub priority: Option<u8>,
    /// `@parent`.
    pub parent: Option<Ref>,
    /// From the file path.
    pub horizon: Horizon,
    /// `open` flag, or a routines/optional file.
    pub scope: Scope,
    /// From `due:` / `at:` / `win:`+`dur:`.
    pub shape: Shape,
    /// `pref:` anchor inside a window.
    pub pref: Option<Pref>,
    /// From `every:` / `after-done:` / `on-event:`.
    pub recur: Recur,
    /// `on-miss:` or the shape default (§5.3).
    pub on_miss: OnMiss,
    /// `min:` / `max:`.
    pub budget: Budget,
    /// `!atomic`.
    pub splittable: bool,
    /// `after:`.
    pub after: Vec<Dep>,
    /// `loc:`.
    pub loc: Loc,
    /// `buffer:` — blocked time before an interval's start.
    pub buffer: Option<Dur>,
    /// `#tags`, in line order.
    pub tags: Vec<String>,
    /// Flags seen (`open atomic manual travel-day hot`), in line order.
    pub flags: Vec<String>,
    /// `(name, 0-based index)` inside a `## series:<name>` section.
    pub series: Option<(String, u32)>,
    /// Tool-written stamps.
    pub stamps: Stamps,
    /// Unknown `key:value` tokens and known keys whose value did not parse,
    /// verbatim `(key, value)`.
    pub extra: Vec<(String, String)>,
    /// Human-readable parse problems (bad values, duplicate ids, …); reported
    /// by `tm check`.
    pub problems: Vec<String>,
    /// File, line, section, tokens.
    pub src: SourceLoc,
}

impl Item {
    /// True when the line carries a `^id`.
    pub fn has_id(&self) -> bool {
        !self.id.is_empty()
    }
    /// True when the line carries the named flag.
    pub fn has_flag(&self, flag: &str) -> bool {
        self.flags.iter().any(|f| f == flag)
    }
    /// `manual` — a calendar line that survives a sync.
    pub fn is_manual(&self) -> bool {
        self.has_flag("manual")
    }
    /// `travel-day`.
    pub fn is_travel_day(&self) -> bool {
        self.has_flag("travel-day")
    }
    /// `hot` — forced p = 0.
    pub fn is_hot(&self) -> bool {
        self.has_flag("hot")
    }
    /// `est` if set, else `est_original` (the line's own remaining estimate;
    /// `tree.rs` adds the children rollup).
    pub fn own_remaining(&self) -> Option<Dur> {
        self.est.or(self.est_original)
    }
    /// The byte-faithful line.
    pub fn line(&self) -> &ItemLine {
        &self.src.tokens
    }
    /// The original line text.
    pub fn line_text(&self) -> String {
        self.src.tokens.to_string()
    }
}

// ---------------------------------------------------------------------------
// Instances (§5.1)
// ---------------------------------------------------------------------------

/// One occurrence of a recurring item.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Instance {
    /// The recurring item.
    pub item: Id,
    /// Date (calendar) or ordinal (after-done / on-event).
    pub key: InstanceKey,
    /// When it is due, if dated.
    pub due: Option<NaiveDateTime>,
    /// The window it must be placed in, if any.
    pub window: Option<(NaiveDateTime, NaiveDateTime)>,
    /// Status from the log.
    pub status: InstanceStatus,
}

/// Identifies an instance: calendar recurrences by date, completion/event
/// recurrences by ordinal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum InstanceKey {
    /// Calendar occurrence on a date.
    Date(NaiveDate),
    /// N-th occurrence (after-done / on-event).
    Nth(u32),
}

impl fmt::Display for InstanceKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InstanceKey::Date(d) => write!(f, "{}", d.format("%Y-%m-%d")),
            InstanceKey::Nth(n) => write!(f, "#{n}"),
        }
    }
}

/// Status of an instance, derived from the log.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum InstanceStatus {
    /// Not yet done.
    #[default]
    Pending,
    /// Logged done.
    Done,
    /// Missed with `on_miss = persist`.
    Missed,
    /// Missed with `on_miss = expire`.
    Expired,
    /// Skipped (`tm skip`, or `on-miss:next`).
    Skipped,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dur_parse_and_format() {
        let cases = [
            ("2b", 120, "2b"),
            ("30m", 30, "30m"),
            ("2h", 120, "2h"),
            ("8h30m", 510, "8h30m"),
            ("2d", 2880, "2d"),
            ("0m", 0, "0m"),
        ];
        for (s, min, back) in cases {
            let d = Dur::parse(s, 60).unwrap();
            assert_eq!(d.minutes, min, "{s}");
            assert_eq!(d.to_string(), back, "{s}");
        }
        assert_eq!(Dur::parse("3b", 45).unwrap().minutes, 135);
        assert_eq!(Dur::blocks(3, 45).to_string(), "3b");
        for bad in ["", "b", "2", "2x", "h30m", "2h30", "2hm", "-2m", "2h-1m"] {
            assert!(Dur::parse(bad, 60).is_err(), "{bad:?} should fail");
        }
        assert!(Dur::parse_no_days("2d", 60).is_err());
        assert_eq!(Dur::canonical(90).to_string(), "1h30m");
        assert_eq!(Dur::canonical(120).to_string(), "2h");
        assert_eq!(Dur::canonical(45).to_string(), "45m");
    }

    #[test]
    fn year_month_and_week() {
        let ym = YearMonth::parse("2026-09").unwrap();
        assert_eq!(ym.to_string(), "2026-09");
        assert_eq!(ym.first_day(), NaiveDate::from_ymd_opt(2026, 9, 1).unwrap());
        assert_eq!(ym.last_day(), NaiveDate::from_ymd_opt(2026, 9, 30).unwrap());
        assert_eq!(ym.next(), YearMonth::new(2026, 10));
        assert_eq!(YearMonth::new(2026, 12).next(), YearMonth::new(2027, 1));
        assert_eq!(YearMonth::new(2026, 1).prev(), YearMonth::new(2025, 12));
        assert!(YearMonth::parse("2026-13").is_err());
        assert!(YearMonth::parse("2026-9").is_err());

        let w = IsoWeek::parse("2026-W37").unwrap();
        assert_eq!(w.to_string(), "2026-W37");
        assert_eq!(w.short(), "W37");
        assert_eq!(w.monday(), NaiveDate::from_ymd_opt(2026, 9, 7).unwrap());
        assert_eq!(w.sunday(), NaiveDate::from_ymd_opt(2026, 9, 13).unwrap());
        assert_eq!(w.next().to_string(), "2026-W38");
        assert_eq!(w.prev().to_string(), "2026-W36");
        assert!(w.contains(NaiveDate::from_ymd_opt(2026, 9, 10).unwrap()));
        assert_eq!(IsoWeek::from_date(NaiveDate::from_ymd_opt(2026, 9, 10).unwrap()), w);
        assert!(IsoWeek::parse("2026-W54").is_err());
        assert!(IsoWeek::parse("2026-37").is_err());
        assert_eq!(w.dates().len(), 7);
    }

    #[test]
    fn horizon_from_path() {
        assert_eq!(
            Horizon::from_path("plan/month/2026-09.md"),
            Some(Horizon::Month(YearMonth::new(2026, 9)))
        );
        assert_eq!(
            Horizon::from_path("week/2026-W37.md"),
            Some(Horizon::Week(IsoWeek::new(2026, 37)))
        );
        assert_eq!(
            Horizon::from_path("/abs/plan/day/2026-09-07.md"),
            Some(Horizon::Day(NaiveDate::from_ymd_opt(2026, 9, 7).unwrap()))
        );
        assert_eq!(
            Horizon::from_path("calendar/2026-W37.md"),
            Some(Horizon::Calendar(IsoWeek::new(2026, 37)))
        );
        assert_eq!(Horizon::from_path("backlog.md"), Some(Horizon::Backlog));
        assert_eq!(Horizon::from_path("plan/routines.md"), Some(Horizon::Routine));
        assert_eq!(Horizon::from_path("optional.md"), Some(Horizon::Optional));
        assert_eq!(Horizon::from_path("inbox.md"), Some(Horizon::Inbox));
        assert_eq!(Horizon::from_path("notes.md"), None);
        assert_eq!(Horizon::from_path("week/foo.md"), None);
        assert_eq!(Horizon::from_path("week/2026-W37.txt"), None);
        assert_eq!(Horizon::Week(IsoWeek::new(2026, 37)).path(), "week/2026-W37.md");
    }

    #[test]
    fn moment_interval_window() {
        assert_eq!(
            Moment::parse("2026-09-11").unwrap(),
            Moment::Date(NaiveDate::from_ymd_opt(2026, 9, 11).unwrap())
        );
        let m = Moment::parse("2026-09-11T23:59").unwrap();
        assert_eq!(m.to_string(), "2026-09-11T23:59");
        assert_eq!(Moment::parse("2026-09-11").unwrap().end_of_day(), m.end_of_day());
        assert!(Moment::parse("2026-9-11").is_err());

        let (s, e) = parse_interval("2026-09-07T12:50/13:50").unwrap();
        assert_eq!(fmt_interval(s, e), "2026-09-07T12:50/13:50");
        let (s, e) = parse_interval("2026-09-12T08:15/2026-09-12T10:40").unwrap();
        assert_eq!(fmt_interval(s, e), "2026-09-12T08:15/10:40");
        let (s, e) = parse_interval("2026-09-12T23:30/05:45").unwrap();
        assert_eq!(e.date(), s.date().succ_opt().unwrap());
        assert_eq!(fmt_interval(s, e), "2026-09-12T23:30/2026-09-13T05:45");
        assert!(parse_interval("2026-09-12T23:30").is_err());

        let w = WindowRange::parse("22:00-08:00").unwrap();
        assert!(w.is_overnight());
        assert_eq!(w.to_string(), "22:00-08:00");
        let w = WindowRange::parse("2026-09-07T14:00/17:00").unwrap();
        assert!(!w.is_overnight());
        assert_eq!(w.to_string(), "2026-09-07T14:00/17:00");
        assert!(WindowRange::parse("11:30").is_err());
    }

    #[test]
    fn rules() {
        let cases = [
            ("day", Rule::Daily),
            ("weekday", Rule::Weekdays),
            ("week", Rule::Weeks(1)),
            ("Mon,Wed,Fri", Rule::Weekly(vec![Weekday::Mon, Weekday::Wed, Weekday::Fri])),
            ("2w:Sun", Rule::EveryNWeeks(2, Weekday::Sun)),
            ("3d", Rule::EveryNDays(3)),
            ("2w", Rule::Weeks(2)),
            ("month:15", Rule::Monthly(15)),
        ];
        for (s, r) in cases {
            assert_eq!(Rule::parse(s).unwrap(), r, "{s}");
            assert_eq!(r.to_string(), s, "{s}");
        }
        for bad in ["", "0d", "month:32", "2w:Funday", "Mon,", "3x"] {
            assert!(Rule::parse(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn rates_deps_stamps_locs() {
        let r = Rate::parse("6b/w", 60).unwrap();
        assert_eq!(r.amount.minutes, 360);
        assert_eq!(r.per, Period::Week);
        assert_eq!(r.to_string(), "6b/w");
        assert_eq!(Rate::parse("4h/w", 60).unwrap().to_string(), "4h/w");
        assert_eq!(Rate::parse("30m/d", 60).unwrap().per, Period::Day);
        assert!(Rate::parse("6b", 60).is_err());
        assert!(Rate::parse("6b/y", 60).is_err());

        assert_eq!(
            Dep::parse_list("^k7q2,^m2").unwrap(),
            vec![Dep::Item(Id::new("k7q2")), Dep::Item(Id::new("m2"))]
        );
        assert_eq!(
            Dep::parse_list("event:visa,^t4").unwrap(),
            vec![Dep::Event("visa".into()), Dep::Item(Id::new("t4"))]
        );
        assert_eq!(Dep::Event("visa".into()).to_string(), "event:visa");
        assert!(Dep::parse_list("^,^t4").is_err());

        assert_eq!(
            Stamp::parse_list("W36,W37").unwrap(),
            vec![Stamp::Week(36), Stamp::Week(37)]
        );
        assert_eq!(Stamp::parse("D07").unwrap(), Stamp::Day(7));
        assert_eq!(Stamp::Day(7).to_string(), "D07");
        assert!(Stamp::parse("X1").is_err());

        assert_eq!(Loc::parse("zoom").unwrap(), Loc::Named("zoom".into()));
        assert_eq!(Loc::parse("out").unwrap(), Loc::Out);
        assert!(Loc::parse("").is_err());

        assert_eq!(
            Pref::parse("wake+10m", 60).unwrap(),
            Pref::WakePlus(Dur::from_minutes(10))
        );
        assert_eq!(Pref::parse("12:00", 60).unwrap().to_string(), "12:00");
        assert_eq!(Pref::parse("wake+10m", 60).unwrap().to_string(), "wake+10m");
    }

    #[test]
    fn states() {
        for s in [
            State::Todo,
            State::Active,
            State::Done,
            State::Demoted,
            State::Dropped,
            State::Waiting,
        ] {
            assert_eq!(State::parse(s.as_str()).unwrap(), s);
            assert_eq!(State::from_glyph(s.glyph()), Some(s));
        }
        assert!(State::parse("[!]").is_err());
    }
}
