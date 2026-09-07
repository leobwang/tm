//! Configuration — tm-spec-v1.md §16, plus top-level `tz`.
//!
//! # API overview
//!
//! * [`Config`] mirrors `config.toml` section by section: `tz`, [`DayConfig`],
//!   [`WeekConfig`], [`PriorityConfig`], [`LocationConfig`], [`EnergyConfig`]
//!   (with `prior.<loc>` step functions and [`SleepDebt`]), [`ExpectedConfig`],
//!   [`CalendarConfig`], [`TuiConfig`]. Every field has the §16 default, so a
//!   partial or missing file works; an unknown key anywhere is a parse error.
//! * `Config::default()`, [`Config::parse`]`(&str)`, [`Config::load`]`(path)`,
//!   [`Config::load_or_default`]`(path)`, [`Config::to_toml`]`()`,
//!   [`Config::default_toml`]`()` (the §16 text, used by `tm init`).
//! * [`Config::prior_energy`]`(loc, hours_since_wake) -> u8` — the step
//!   function lookup; [`StepFn`] holds one curve.
//! * [`PerWeekday`]`<T>` — a value per weekday (`get(Weekday)`).
//! * Times such as `"19:00"` are `NaiveTime` (serialized back as `HH:MM`).

use std::collections::BTreeMap;
use std::fmt;
use std::path::Path;

use chrono::{NaiveTime, Weekday};
use chrono_tz::Tz;
use serde::de::{self, Deserializer, MapAccess, Visitor};
use serde::ser::{SerializeMap, Serializer};
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Errors from loading a config file.
#[derive(Debug, Error)]
pub enum ConfigError {
    /// The file could not be read.
    #[error("cannot read {path}: {source}")]
    Io {
        /// Path attempted.
        path: String,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// The TOML did not parse or did not match the schema.
    #[error("invalid config {path}: {source}")]
    Parse {
        /// Path attempted (`<string>` for [`Config::parse`]).
        path: String,
        /// Underlying error.
        #[source]
        source: toml::de::Error,
    },
    /// The TOML could not be produced.
    #[error("cannot serialize config: {0}")]
    Serialize(#[from] toml::ser::Error),
}

/// `HH:MM` serde for `NaiveTime` fields.
pub mod hhmm {
    use chrono::NaiveTime;
    use serde::{de, Deserialize, Deserializer, Serializer};

    /// Parse `HH:MM` (or `HH:MM:SS`).
    pub fn parse(s: &str) -> Result<NaiveTime, String> {
        NaiveTime::parse_from_str(s, "%H:%M")
            .or_else(|_| NaiveTime::parse_from_str(s, "%H:%M:%S"))
            .map_err(|_| format!("invalid time {s:?}, expected HH:MM"))
    }

    /// Format `HH:MM`.
    pub fn format(t: &NaiveTime) -> String {
        t.format("%H:%M").to_string()
    }

    /// Serialize as `HH:MM`.
    pub fn serialize<S: Serializer>(t: &NaiveTime, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&format(t))
    }

    /// Deserialize from `HH:MM`.
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<NaiveTime, D::Error> {
        let s = String::deserialize(d)?;
        parse(&s).map_err(de::Error::custom)
    }
}

/// A value per weekday, serialized with `Mon`..`Sun` keys.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PerWeekday<T> {
    /// Monday.
    #[serde(rename = "Mon")]
    pub mon: T,
    /// Tuesday.
    #[serde(rename = "Tue")]
    pub tue: T,
    /// Wednesday.
    #[serde(rename = "Wed")]
    pub wed: T,
    /// Thursday.
    #[serde(rename = "Thu")]
    pub thu: T,
    /// Friday.
    #[serde(rename = "Fri")]
    pub fri: T,
    /// Saturday.
    #[serde(rename = "Sat")]
    pub sat: T,
    /// Sunday.
    #[serde(rename = "Sun")]
    pub sun: T,
}

impl<T> PerWeekday<T> {
    /// Build from a function of the weekday.
    pub fn from_fn(mut f: impl FnMut(Weekday) -> T) -> PerWeekday<T> {
        PerWeekday {
            mon: f(Weekday::Mon),
            tue: f(Weekday::Tue),
            wed: f(Weekday::Wed),
            thu: f(Weekday::Thu),
            fri: f(Weekday::Fri),
            sat: f(Weekday::Sat),
            sun: f(Weekday::Sun),
        }
    }
    /// The value for a weekday.
    pub fn get(&self, wd: Weekday) -> &T {
        match wd {
            Weekday::Mon => &self.mon,
            Weekday::Tue => &self.tue,
            Weekday::Wed => &self.wed,
            Weekday::Thu => &self.thu,
            Weekday::Fri => &self.fri,
            Weekday::Sat => &self.sat,
            Weekday::Sun => &self.sun,
        }
    }
    /// Apply `f` to every value.
    pub fn map<U>(&self, mut f: impl FnMut(&T) -> U) -> PerWeekday<U> {
        PerWeekday::from_fn(|wd| f(self.get(wd)))
    }
    /// Apply a fallible `f` to every value.
    pub fn try_map<U, E>(&self, mut f: impl FnMut(&T) -> Result<U, E>) -> Result<PerWeekday<U>, E> {
        Ok(PerWeekday {
            mon: f(&self.mon)?,
            tue: f(&self.tue)?,
            wed: f(&self.wed)?,
            thu: f(&self.thu)?,
            fri: f(&self.fri)?,
            sat: f(&self.sat)?,
            sun: f(&self.sun)?,
        })
    }
}

mod hhmm_per_weekday {
    use super::{hhmm, PerWeekday};
    use chrono::NaiveTime;
    use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(t: &PerWeekday<NaiveTime>, s: S) -> Result<S::Ok, S::Error> {
        t.map(hhmm::format).serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<PerWeekday<NaiveTime>, D::Error> {
        let raw = PerWeekday::<String>::deserialize(d)?;
        raw.try_map(|s| hhmm::parse(s)).map_err(de::Error::custom)
    }
}

/// One step of an energy prior: `from ≤ hours < to` → `level`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Step {
    /// Start (hours since wake, inclusive).
    pub from: f64,
    /// End (exclusive); `None` for an open `N+` range.
    pub to: Option<f64>,
    /// Energy level 0..=5.
    pub level: u8,
}

/// A step function of hours-since-wake, from keys like `"0-1"`, `"10+"`.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct StepFn(pub Vec<Step>);

fn fmt_num(x: f64) -> String {
    if x.fract() == 0.0 {
        format!("{}", x as i64)
    } else {
        x.to_string()
    }
}

impl StepFn {
    /// Build from `(range key, level)` pairs; sorted by range start.
    pub fn from_pairs<'a>(pairs: impl IntoIterator<Item = (&'a str, u8)>) -> Result<StepFn, String> {
        let mut steps = Vec::new();
        for (k, level) in pairs {
            let (from, to) = StepFn::parse_key(k)?;
            steps.push(Step { from, to, level });
        }
        steps.sort_by(|a, b| a.from.partial_cmp(&b.from).unwrap_or(std::cmp::Ordering::Equal));
        Ok(StepFn(steps))
    }

    /// Parse `"0-1"` → `(0, Some(1))`, `"10+"` → `(10, None)`.
    pub fn parse_key(k: &str) -> Result<(f64, Option<f64>), String> {
        let bad = || format!("invalid energy range {k:?}, expected \"a-b\" or \"a+\"");
        if let Some(a) = k.strip_suffix('+') {
            return Ok((a.trim().parse().map_err(|_| bad())?, None));
        }
        let (a, b) = k.split_once('-').ok_or_else(bad)?;
        Ok((
            a.trim().parse().map_err(|_| bad())?,
            Some(b.trim().parse().map_err(|_| bad())?),
        ))
    }

    /// The range key for a step (`"0-1"`, `"10+"`).
    pub fn key(step: &Step) -> String {
        match step.to {
            Some(to) => format!("{}-{}", fmt_num(step.from), fmt_num(to)),
            None => format!("{}+", fmt_num(step.from)),
        }
    }

    /// Level at `hours` since wake: the step whose range contains it; before
    /// the first step → the first level; after the last → the last level.
    /// Returns 3 for an empty function.
    pub fn at(&self, hours: f64) -> u8 {
        let Some(first) = self.0.first() else {
            return 3;
        };
        if hours < first.from {
            return first.level;
        }
        for s in &self.0 {
            let inside = hours >= s.from && s.to.is_none_or(|to| hours < to);
            if inside {
                return s.level;
            }
        }
        // Gaps between ranges: use the last step that starts at or before `hours`.
        self.0
            .iter()
            .rev()
            .find(|s| hours >= s.from)
            .map(|s| s.level)
            .unwrap_or(first.level)
    }
}

impl Serialize for StepFn {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let mut m = s.serialize_map(Some(self.0.len()))?;
        for step in &self.0 {
            m.serialize_entry(&StepFn::key(step), &step.level)?;
        }
        m.end()
    }
}

impl<'de> Deserialize<'de> for StepFn {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<StepFn, D::Error> {
        struct V;
        impl<'de> Visitor<'de> for V {
            type Value = StepFn;
            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("a table of \"a-b\" / \"a+\" range keys to energy levels")
            }
            fn visit_map<A: MapAccess<'de>>(self, mut m: A) -> Result<StepFn, A::Error> {
                let mut pairs: Vec<(String, u8)> = Vec::new();
                while let Some((k, v)) = m.next_entry::<String, u8>()? {
                    if v > 5 {
                        return Err(de::Error::custom(format!("energy level {v} out of 0..=5")));
                    }
                    pairs.push((k, v));
                }
                StepFn::from_pairs(pairs.iter().map(|(k, v)| (k.as_str(), *v)))
                    .map_err(de::Error::custom)
            }
        }
        d.deserialize_map(V)
    }
}

/// `[day]`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct DayConfig {
    /// Minutes per block.
    pub block_min: u32,
    /// Blocks between breaks.
    pub break_after_blocks: u32,
    /// Break length in minutes.
    pub break_min: u32,
    /// Working window length from arrival.
    pub window_hours: f64,
    /// Latest window end.
    #[serde(with = "hhmm")]
    pub window_cap: NaiveTime,
    /// Share of the window that becomes the block budget.
    pub budget_ratio: f64,
    /// Wind-down time (no ci ≥ 4 blocks after).
    #[serde(with = "hhmm")]
    pub wind_down: NaiveTime,
    /// Bed time.
    #[serde(with = "hhmm")]
    pub bed: NaiveTime,
    /// Minutes between overtime prompts.
    pub overtime_reprompt_min: u32,
    /// Minutes idle before the idle prompt.
    pub idle_min: u32,
    /// Shortest last block of the day.
    pub min_last_block_min: u32,
}

impl Default for DayConfig {
    fn default() -> Self {
        DayConfig {
            block_min: 60,
            break_after_blocks: 2,
            break_min: 20,
            window_hours: 8.0,
            window_cap: hm(19, 0),
            budget_ratio: 0.75,
            wind_down: hm(21, 30),
            bed: hm(22, 0),
            overtime_reprompt_min: 15,
            idle_min: 12,
            min_last_block_min: 30,
        }
    }
}

/// `[week]`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct WeekConfig {
    /// Warn if planned > plan_ratio × budget.
    pub plan_ratio: f64,
}

impl Default for WeekConfig {
    fn default() -> Self {
        WeekConfig { plan_ratio: 0.8 }
    }
}

/// `[priority]`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct PriorityConfig {
    /// `k` for roots without `!k` and for untied items.
    pub default_priority: u8,
    /// Utilization bin edges, descending: `u ≥ bins[0]` → +0, …, below the last → +3.
    pub bins: Vec<f64>,
    /// Multiplier on remaining estimate for `need`.
    pub safety: f64,
    /// Limit priority improvement to one bin per day.
    pub hysteresis: bool,
    /// Items with remaining ≤ this many minutes are batched.
    pub batch_max_min: u32,
}

impl Default for PriorityConfig {
    fn default() -> Self {
        PriorityConfig {
            default_priority: 3,
            bins: vec![0.5, 0.25, 0.1],
            safety: 1.3,
            hysteresis: true,
            batch_max_min: 20,
        }
    }
}

/// `[location]`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct LocationConfig {
    /// Highest ci schedulable at home (unless `--allow-home`).
    pub home_max_ci: u8,
}

impl Default for LocationConfig {
    fn default() -> Self {
        LocationConfig { home_max_ci: 3 }
    }
}

/// `[energy.sleep_debt]`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct SleepDebt {
    /// Sleep shorter than this many hours counts as debt.
    pub under_hours: f64,
    /// Levels subtracted from the prior under debt.
    pub shift: f64,
}

impl Default for SleepDebt {
    fn default() -> Self {
        SleepDebt {
            under_hours: 7.0,
            shift: 1.0,
        }
    }
}

/// `[energy]`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct EnergyConfig {
    /// Shrinkage weight of the prior (`n0`).
    pub prior_weight: f64,
    /// Observation decay in days.
    pub decay_days: f64,
    /// Shrinkage weight for duration multipliers.
    pub duration_prior_weight: f64,
    /// Posterior correction is full for this many hours after a report…
    pub posterior_full_hours: f64,
    /// …and fades to zero at this many hours.
    pub posterior_zero_hours: f64,
    /// Prior curves by location name (`lounge`, `home`, …).
    pub prior: BTreeMap<String, StepFn>,
    /// Sleep-debt correction.
    pub sleep_debt: SleepDebt,
}

impl Default for EnergyConfig {
    fn default() -> Self {
        let lounge = StepFn::from_pairs([("0-1", 4), ("1-5", 5), ("5-8", 4), ("8-10", 3), ("10+", 2)])
            .expect("valid default");
        let home = StepFn::from_pairs([("0-1", 3), ("1-4", 4), ("4-8", 3), ("8+", 2)])
            .expect("valid default");
        let mut prior = BTreeMap::new();
        prior.insert("lounge".to_string(), lounge);
        prior.insert("home".to_string(), home);
        EnergyConfig {
            prior_weight: 5.0,
            decay_days: 30.0,
            duration_prior_weight: 5.0,
            posterior_full_hours: 3.0,
            posterior_zero_hours: 6.0,
            prior,
            sleep_debt: SleepDebt::default(),
        }
    }
}

/// `[expected]` — used by the lookahead until learned.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct ExpectedConfig {
    /// Expected arrival time per weekday.
    #[serde(with = "hhmm_per_weekday")]
    pub arrival: PerWeekday<NaiveTime>,
    /// Probability of being at the lounge per weekday.
    pub p_lounge: PerWeekday<f64>,
}

impl Default for ExpectedConfig {
    fn default() -> Self {
        ExpectedConfig {
            arrival: PerWeekday::from_fn(|wd| match wd {
                Weekday::Sat | Weekday::Sun => hm(10, 0),
                _ => hm(7, 0),
            }),
            p_lounge: PerWeekday::from_fn(|wd| match wd {
                Weekday::Fri => 0.8,
                Weekday::Sat => 0.5,
                Weekday::Sun => 0.4,
                _ => 0.9,
            }),
        }
    }
}

/// `[calendar]`. The default has no ICS addresses, so a missing config
/// never triggers a fetch; `tm init` writes an example URL in a comment.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct CalendarConfig {
    /// Private ICS addresses (empty = no calendar sync).
    pub ics_urls: Vec<String>,
    /// Sync on `tm arrive`.
    pub sync_on_arrive: bool,
    /// Events matching this get `buffer:2h travel-day`.
    pub flight_regex: String,
}

impl Default for CalendarConfig {
    fn default() -> Self {
        CalendarConfig {
            ics_urls: Vec::new(),
            sync_on_arrive: true,
            flight_regex: r"\b[A-Z]{2} ?\d{2,4}\b".to_string(),
        }
    }
}

/// `[tui]`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct TuiConfig {
    /// Project hues.
    pub palette: Vec<String>,
    /// Columns below which panes stack.
    pub min_width: u32,
    /// Editor command; `{file}` and `{line}` are substituted.
    pub editor: String,
}

impl Default for TuiConfig {
    fn default() -> Self {
        TuiConfig {
            palette: [
                "#e6194b", "#3cb44b", "#4363d8", "#f58231", "#911eb4", "#42d4f4", "#f032e6",
                "#bfef45", "#fabed4", "#469990", "#dcbeff", "#9A6324",
            ]
            .iter()
            .map(|s| s.to_string())
            .collect(),
            min_width: 110,
            editor: "code -g {file}:{line}".to_string(),
        }
    }
}

/// The whole `config.toml`. Every section rejects unknown keys
/// (`deny_unknown_fields`), so a misspelled key is a parse error instead of
/// a silent fallback to the default.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct Config {
    /// Local timezone applied at the planner edges.
    pub tz: Tz,
    /// `[day]`
    pub day: DayConfig,
    /// `[week]`
    pub week: WeekConfig,
    /// `[priority]`
    pub priority: PriorityConfig,
    /// `[location]`
    pub location: LocationConfig,
    /// `[energy]`
    pub energy: EnergyConfig,
    /// `[expected]`
    pub expected: ExpectedConfig,
    /// `[calendar]`
    pub calendar: CalendarConfig,
    /// `[tui]`
    pub tui: TuiConfig,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            tz: Tz::America__Chicago,
            day: DayConfig::default(),
            week: WeekConfig::default(),
            priority: PriorityConfig::default(),
            location: LocationConfig::default(),
            energy: EnergyConfig::default(),
            expected: ExpectedConfig::default(),
            calendar: CalendarConfig::default(),
            tui: TuiConfig::default(),
        }
    }
}

fn hm(h: u32, m: u32) -> NaiveTime {
    NaiveTime::from_hms_opt(h, m, 0).expect("valid time")
}

/// The complete §16 `config.toml` text (with `tz`), as written by `tm init`.
pub const DEFAULT_TOML: &str = r##"tz = "America/Chicago"

[day]
block_min             = 60
break_after_blocks    = 2
break_min             = 20
window_hours          = 8
window_cap            = "19:00"
budget_ratio          = 0.75
wind_down             = "21:30"
bed                   = "22:00"
overtime_reprompt_min = 15
idle_min              = 12
min_last_block_min    = 30

[week]
plan_ratio = 0.8                 # warn if planned > 0.8 × budget

[priority]
default_priority = 3             # k for roots without !k and for untied items
bins             = [0.5, 0.25, 0.1]
safety           = 1.3
hysteresis       = true
batch_max_min    = 20

[location]
home_max_ci = 3

[energy]
prior_weight          = 5
decay_days            = 30
duration_prior_weight = 5
posterior_full_hours  = 3
posterior_zero_hours  = 6
[energy.prior.lounge]            # by hours since wake
"0-1" = 4
"1-5" = 5
"5-8" = 4
"8-10" = 3
"10+" = 2
[energy.prior.home]
"0-1" = 3
"1-4" = 4
"4-8" = 3
"8+" = 2
[energy.sleep_debt]
under_hours = 7.0
shift       = 1

[expected]                       # used by the lookahead until learned
arrival = { Mon = "07:00", Tue = "07:00", Wed = "07:00", Thu = "07:00", Fri = "07:00", Sat = "10:00", Sun = "10:00" }
p_lounge = { Mon = 0.9, Tue = 0.9, Wed = 0.9, Thu = 0.9, Fri = 0.8, Sat = 0.5, Sun = 0.4 }

[calendar]
ics_urls       = []              # e.g. ["https://calendar.google.com/calendar/ical/<id>/private-<key>/basic.ics"]
sync_on_arrive = true
flight_regex   = "\\b[A-Z]{2} ?\\d{2,4}\\b"

[tui]
palette   = ["#e6194b","#3cb44b","#4363d8","#f58231","#911eb4","#42d4f4","#f032e6","#bfef45","#fabed4","#469990","#dcbeff","#9A6324"]
min_width = 110
editor    = "code -g {file}:{line}"
"##;

impl Config {
    /// Parse TOML text; missing fields take their defaults.
    pub fn parse(text: &str) -> Result<Config, ConfigError> {
        toml::from_str(text).map_err(|source| ConfigError::Parse {
            path: "<string>".to_string(),
            source,
        })
    }

    /// Read and parse a file.
    pub fn load(path: impl AsRef<Path>) -> Result<Config, ConfigError> {
        let path = path.as_ref();
        let text = std::fs::read_to_string(path).map_err(|source| ConfigError::Io {
            path: path.display().to_string(),
            source,
        })?;
        toml::from_str(&text).map_err(|source| ConfigError::Parse {
            path: path.display().to_string(),
            source,
        })
    }

    /// Like [`Config::load`], but a missing file yields `Config::default()`.
    pub fn load_or_default(path: impl AsRef<Path>) -> Result<Config, ConfigError> {
        match Config::load(path) {
            Err(ConfigError::Io { source, .. }) if source.kind() == std::io::ErrorKind::NotFound => {
                Ok(Config::default())
            }
            other => other,
        }
    }

    /// Serialize to TOML (parseable back to an equal `Config`).
    pub fn to_toml(&self) -> Result<String, ConfigError> {
        Ok(toml::to_string(self)?)
    }

    /// The §16 text (see [`DEFAULT_TOML`]).
    pub fn default_toml() -> &'static str {
        DEFAULT_TOML
    }

    /// Minutes per block.
    pub fn block_min(&self) -> u32 {
        self.day.block_min
    }

    /// True when `tm arrive` should sync the calendar: `sync_on_arrive` and
    /// at least one ICS address configured.
    pub fn sync_on_arrive_possible(&self) -> bool {
        self.calendar.sync_on_arrive && !self.calendar.ics_urls.is_empty()
    }

    /// Prior energy at a location `hours_since_wake` hours after waking.
    /// Unknown locations fall back to `lounge`, then to the first curve;
    /// with no curves at all the answer is 3.
    pub fn prior_energy(&self, loc: &str, hours_since_wake: f64) -> u8 {
        let curve = self
            .energy
            .prior
            .get(loc)
            .or_else(|| self.energy.prior.get("lounge"))
            .or_else(|| self.energy.prior.values().next());
        curve.map(|c| c.at(hours_since_wake)).unwrap_or(3)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_toml_matches_default() {
        let parsed = Config::parse(Config::default_toml()).unwrap();
        assert_eq!(parsed, Config::default());
    }

    #[test]
    fn to_toml_round_trips() {
        let cfg = Config::default();
        let text = cfg.to_toml().unwrap();
        assert!(text.contains("[energy.prior.lounge]"), "{text}");
        assert!(text.contains("window_cap = \"19:00\""), "{text}");
        assert_eq!(Config::parse(&text).unwrap(), cfg);
    }

    #[test]
    fn partial_and_empty_config() {
        let cfg = Config::parse("").unwrap();
        assert_eq!(cfg, Config::default());
        let cfg = Config::parse("[day]\nblock_min = 45\n[priority]\nsafety = 1.5\n").unwrap();
        assert_eq!(cfg.day.block_min, 45);
        assert_eq!(cfg.day.break_min, 20);
        assert_eq!(cfg.priority.safety, 1.5);
        assert_eq!(cfg.priority.default_priority, 3);
        assert_eq!(cfg.tz, Tz::America__Chicago);
        let cfg = Config::parse("tz = \"Europe/Berlin\"\n").unwrap();
        assert_eq!(cfg.tz, Tz::Europe__Berlin);
    }

    #[test]
    fn unknown_keys_are_errors() {
        // Regression: a misspelled key used to fall back to the default silently.
        for bad in [
            "[day]\nblock_mins = 45\n",
            "[location]\nhome_max_c = 2\n",
            "[priority]\ndefault_prio = 2\n",
            "[calendar]\nurl = \"x\"\n",
            "[energy]\nprior_weigth = 5\n",
            "[energy.sleep_debt]\nunder = 7\n",
            "[expected]\narrival = { Mon = \"07:00\", Mo = \"07:00\" }\n",
            "[expected]\np_lounge = { Mon = 0.9, Monday = 0.9 }\n",
            "[tui]\nwidth = 100\n",
            "[week]\nratio = 0.8\n",
            "timezone = \"UTC\"\n",
            "[nope]\nx = 1\n",
        ] {
            let r = Config::parse(bad);
            assert!(matches!(r, Err(ConfigError::Parse { .. })), "{bad:?} -> {r:?}");
        }
        // Known keys and extra prior curves still parse.
        let cfg = Config::parse("[energy.prior.cafe]\n\"0-4\" = 3\n\"4+\" = 2\n").unwrap();
        assert_eq!(cfg.prior_energy("cafe", 5.0), 2);
    }

    #[test]
    fn default_has_no_calendar_urls() {
        // Regression: the default carried the spec's placeholder URL, so a
        // missing config would try to fetch it on `tm arrive`.
        let c = Config::default();
        assert!(c.calendar.ics_urls.is_empty());
        assert!(!c.sync_on_arrive_possible());
        let parsed = Config::parse(DEFAULT_TOML).unwrap();
        assert!(parsed.calendar.ics_urls.is_empty());
        assert!(DEFAULT_TOML.contains("ics_urls       = []"));
        let with = Config::parse("[calendar]\nics_urls = [\"https://example.com/a.ics\"]\n").unwrap();
        assert!(with.sync_on_arrive_possible());
    }

    #[test]
    fn values_from_spec() {
        let c = Config::default();
        assert_eq!(c.day.window_cap, hm(19, 0));
        assert_eq!(c.day.wind_down, hm(21, 30));
        assert_eq!(c.day.bed, hm(22, 0));
        assert_eq!(c.day.window_hours, 8.0);
        assert_eq!(c.priority.bins, vec![0.5, 0.25, 0.1]);
        assert_eq!(*c.expected.arrival.get(Weekday::Mon), hm(7, 0));
        assert_eq!(*c.expected.arrival.get(Weekday::Sat), hm(10, 0));
        assert_eq!(*c.expected.p_lounge.get(Weekday::Sun), 0.4);
        assert_eq!(c.calendar.flight_regex, "\\b[A-Z]{2} ?\\d{2,4}\\b");
        assert!(regex::Regex::new(&c.calendar.flight_regex).is_ok());
        assert_eq!(c.tui.palette.len(), 12);
        assert_eq!(c.energy.sleep_debt.under_hours, 7.0);
    }

    #[test]
    fn prior_energy_lookup() {
        let c = Config::default();
        assert_eq!(c.prior_energy("lounge", 0.0), 4);
        assert_eq!(c.prior_energy("lounge", 0.5), 4);
        assert_eq!(c.prior_energy("lounge", 1.0), 5);
        assert_eq!(c.prior_energy("lounge", 4.99), 5);
        assert_eq!(c.prior_energy("lounge", 5.0), 4);
        assert_eq!(c.prior_energy("lounge", 9.0), 3);
        assert_eq!(c.prior_energy("lounge", 10.0), 2);
        assert_eq!(c.prior_energy("lounge", 30.0), 2);
        assert_eq!(c.prior_energy("lounge", -1.0), 4);
        assert_eq!(c.prior_energy("home", 2.0), 4);
        assert_eq!(c.prior_energy("home", 8.0), 2);
        assert_eq!(c.prior_energy("zoom", 2.0), 5);
        let empty = Config::parse("[energy]\nprior = {}\n").unwrap();
        assert_eq!(empty.prior_energy("lounge", 2.0), 3);
    }

    #[test]
    fn step_fn_keys_and_errors() {
        assert_eq!(StepFn::parse_key("0-1").unwrap(), (0.0, Some(1.0)));
        assert_eq!(StepFn::parse_key("10+").unwrap(), (10.0, None));
        assert_eq!(StepFn::parse_key("1.5-2").unwrap(), (1.5, Some(2.0)));
        assert!(StepFn::parse_key("x").is_err());
        let f = StepFn::from_pairs([("5+", 1), ("0-5", 4)]).unwrap();
        assert_eq!(StepFn::key(&f.0[0]), "0-5");
        assert_eq!(StepFn::key(&f.0[1]), "5+");
        assert!(Config::parse("[energy.prior.lounge]\n\"bad\" = 3\n").is_err());
        assert!(Config::parse("[energy.prior.lounge]\n\"0-1\" = 9\n").is_err());
        assert!(Config::parse("[day]\nwindow_cap = \"25:00\"\n").is_err());
        assert!(Config::parse("tz = \"Mars/Olympus\"\n").is_err());
    }

    #[test]
    fn load_from_disk() {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("config.toml");
        assert!(Config::load(&p).is_err());
        assert_eq!(Config::load_or_default(&p).unwrap(), Config::default());
        std::fs::write(&p, "[day]\nblock_min = 50\n").unwrap();
        assert_eq!(Config::load(&p).unwrap().day.block_min, 50);
        std::fs::write(&p, "[day]\nblock_min = \"x\"\n").unwrap();
        assert!(matches!(Config::load(&p), Err(ConfigError::Parse { .. })));
    }
}
