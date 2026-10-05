//! Energy — tm-spec-v1.md §8.5: the prior curve, today's posterior, the
//! learned model (`.tm/model.json`) and the duration multipliers, plus the
//! §11 calibration monitors and the `tm model --fit | --show | --compare`
//! machinery (§13).
//!
//! # API overview
//!
//! * [`Model`] mirrors the §8.5 `model.json` exactly:
//!   `energy` (curve name → 12 levels, index = `floor(hsw)`),
//!   `sleep_debt_shift`, `duration` (tag → multiplier, plus `"_default"`),
//!   `p_lounge` and `expected_arrival` ([`WeekdayMap`], `Mon`..`Sun` order),
//!   `fitted`, `n_obs`. [`Model::default`] is the empty model (everything
//!   falls back to the config priors); [`Model::from_config`] writes the
//!   config priors out as a model; [`Model::load`] reads the file (the path is
//!   injected — nothing here knows about `.tm/`). There is no writer here: the
//!   one writer is `tm model --fit`, through [`crate::store::Store`] at
//!   `store::MODEL_PATH`, where D35's gate and the undo recorder can see it.
//!   `Model::save`, a second and ungated `fs::write` of that same file with no
//!   production caller, was deleted at W-19 (README gaps 776 and 834).
//! * [`Features`] + [`predict`] — the slot-energy prediction: the learned
//!   `energy[curve][floor(hsw)]` when the model has it, else
//!   [`Config::prior_energy`], minus the sleep-debt shift when
//!   `slept < under_hours`, clamped to `0..=5`. [`curve_key`] says which
//!   curve a [`Loc`] uses.
//! * [`Posterior`] — today's reports. [`Posterior::from_reports`] takes
//!   `(time, pred, rep)` triples, [`Posterior::correct`] applies `δ·w` to a
//!   later slot, `w = 1` for `posterior_full_hours` falling linearly to 0 at
//!   `posterior_zero_hours` ([`posterior_weight`]).
//! * Fitting (§8.5 v1, bucketed shrinkage means): [`fit`] over a
//!   [`FitInput`] of [`crate::log::EnergyObs`], [`crate::log::DurationObs`]
//!   and [`ArrivalObs`], or [`fit_observations`] from the three observation
//!   lists themselves (design §11.2's hand-back; [`arrivals_from_replay`]
//!   extracts the arrivals from a [`crate::log::Replay`]). [`show`] renders a
//!   model for `tm model --show`;
//!   [`compare`] scores two models against the same observations for
//!   `tm model --compare`.
//! * Monitors (§11): [`calibration`] (MAE and bias of the *logged* `pred`
//!   against `rep`, overall and by clock hour) and [`estimate_calibration`]
//!   (`actual/est` per tag with the shrunken multiplier and a 7-day trend).
//! * Duration multipliers: [`duration_multiplier`] (`"<ci>:<tag>"`, then
//!   `"<tag>"`, then `"_default"`, then 1.0), [`planned_minutes`] and the
//!   display helpers [`fmt_multiplier`] / [`fmt_planned`] (`2b×1.6`).
//!
//! # Interpretation notes (where the spec needed a decision)
//!
//! * **Sleep-debt sign.** §8.5 writes `sleep_debt_shift = shrunken mean of
//!   (rep − energy[b])`, but the same section subtracts the shift from the
//!   prior and the example value is `+0.8`. Both cannot hold, so [`fit`]
//!   learns the *deficit* `mean(energy[b] − rep)` — a positive number when
//!   short sleep depresses the reports — which is what [`predict`]
//!   subtracts.
//! * **Absent vs. zero.** §8.5 wants `model.json` hand-editable and its own
//!   example is partial (`expected_arrival` has only `Mon` and `Sat`), so
//!   this module distinguishes "not learned" from a learned zero:
//!   `sleep_debt_shift` is an `Option` (absent → the config shift, present →
//!   used as written, `0.0` included), and [`fit`] writes `p_lounge` /
//!   `expected_arrival` only for weekdays that have an `arrive` observation
//!   or a value in the base model. A fit therefore never bakes the current
//!   `[expected]` config into the file, and editing config.toml keeps
//!   working for the weekdays nothing was learned on.
//! * **Multiple reports.** §8.5 defines the correction for a single report.
//!   [`Posterior`] uses the most recent report at or before the slot; older
//!   reports are superseded rather than summed (summing would double-count
//!   the same drift).
//! * **Locations.** The learned/prior curve of a location is its own name
//!   when one exists, otherwise `home`: `Out`, `Any` and unknown named
//!   locations are assumed to be no better than home (the conservative
//!   choice; `Config::prior_energy` alone would fall back to `lounge`).
//! * **`duration[(ci, tag)]`.** v1 keys the learned multipliers by the first
//!   tag (plus `_default`), as §8.5's own example does; the lookup still
//!   tries the fully-keyed `"<ci>:<tag>"` first so a hand-edited model can
//!   carry the ci-specific value the formula names.
//! * **A day with no `wake`.** §8.5 measures the prior in hours since wake
//!   but never says what an unlogged day starts at, and `tm wake` is
//!   optional. [`Model::wake_or_expected`] is the single answer every caller
//!   uses — planner and CLI alike: the weekday's expected arrival
//!   ([`Model::expected_arrival_on`], §8.4's own assumption for days it
//!   cannot observe, §16's `[expected] arrival` until it is learned).

use std::collections::BTreeMap;
use std::fmt;
use std::fmt::Write as _;
use std::path::Path;

use chrono::{DateTime, Datelike, NaiveDate, NaiveTime, Timelike, Weekday};
use chrono_tz::Tz;
use serde::de::{self, MapAccess, Visitor};
use serde::ser::SerializeMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use thiserror::Error;

use crate::config::{hhmm, Config};
use crate::log::{DurationObs, EnergyObs, Replay};
use crate::model::{Dur, Loc};

/// Number of hours-since-wake buckets in a learned curve (`floor(hsw)`
/// clamped to `0..=11`, §8.5).
pub const HSW_BUCKETS: usize = 12;

/// The multiplier key used when no tag matches (§8.5).
pub const DEFAULT_TAG: &str = "_default";

/// Weekday keys in `Mon`..`Sun` order, as written in `model.json`.
pub const WEEKDAY_KEYS: [&str; 7] = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];

/// The weekdays in `Mon`..`Sun` order.
pub const WEEKDAYS: [Weekday; 7] = [
    Weekday::Mon,
    Weekday::Tue,
    Weekday::Wed,
    Weekday::Thu,
    Weekday::Fri,
    Weekday::Sat,
    Weekday::Sun,
];

/// Errors from reading or writing `model.json`.
#[derive(Debug, Error)]
pub enum EnergyError {
    /// The file could not be read or written.
    #[error("cannot read or write {path}: {source}")]
    Io {
        /// Path attempted.
        path: String,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// The JSON did not parse or did not match the schema.
    #[error("invalid model {path}: {source}")]
    Json {
        /// Path attempted.
        path: String,
        /// Underlying error.
        #[source]
        source: serde_json::Error,
    },
}

// ---------------------------------------------------------------------------
// Small serde helpers: HH:MM values and Mon..Sun maps
// ---------------------------------------------------------------------------

/// A clock time serialized as `"HH:MM"` (the form `model.json` uses).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Hhmm(pub NaiveTime);

impl Hhmm {
    /// The wrapped time.
    pub fn time(&self) -> NaiveTime {
        self.0
    }
}

impl From<NaiveTime> for Hhmm {
    fn from(t: NaiveTime) -> Hhmm {
        Hhmm(t)
    }
}

impl fmt::Display for Hhmm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&hhmm::format(&self.0))
    }
}

impl Serialize for Hhmm {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&hhmm::format(&self.0))
    }
}

impl<'de> Deserialize<'de> for Hhmm {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Hhmm, D::Error> {
        let s = String::deserialize(d)?;
        hhmm::parse(&s).map(Hhmm).map_err(de::Error::custom)
    }
}

/// The `Mon`..`Sun` key of a weekday.
pub fn weekday_key(wd: Weekday) -> &'static str {
    WEEKDAY_KEYS[wd.num_days_from_monday() as usize]
}

/// Parse a `Mon`..`Sun` key (also accepts full names, any case).
pub fn parse_weekday_key(s: &str) -> Option<Weekday> {
    s.parse::<Weekday>().ok()
}

/// A partial map from weekday to `T`, serialized as a JSON object in
/// `Mon`..`Sun` order with the missing days omitted.
#[derive(Clone, Debug, PartialEq)]
pub struct WeekdayMap<T>([Option<T>; 7]);

impl<T> Default for WeekdayMap<T> {
    fn default() -> WeekdayMap<T> {
        WeekdayMap(std::array::from_fn(|_| None))
    }
}

impl<T> WeekdayMap<T> {
    /// An empty map.
    pub fn new() -> WeekdayMap<T> {
        WeekdayMap::default()
    }
    /// The value for a weekday, if any.
    pub fn get(&self, wd: Weekday) -> Option<&T> {
        self.0[wd.num_days_from_monday() as usize].as_ref()
    }
    /// Set the value for a weekday.
    pub fn set(&mut self, wd: Weekday, value: T) {
        self.0[wd.num_days_from_monday() as usize] = Some(value);
    }
    /// The present entries, `Mon` first.
    pub fn iter(&self) -> impl Iterator<Item = (Weekday, &T)> {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, v)| v.as_ref().map(|v| (WEEKDAYS[i], v)))
    }
    /// Number of days with a value.
    pub fn len(&self) -> usize {
        self.0.iter().filter(|v| v.is_some()).count()
    }
    /// True when no day has a value.
    pub fn is_empty(&self) -> bool {
        self.0.iter().all(|v| v.is_none())
    }
}

impl<T> FromIterator<(Weekday, T)> for WeekdayMap<T> {
    fn from_iter<I: IntoIterator<Item = (Weekday, T)>>(iter: I) -> WeekdayMap<T> {
        let mut m = WeekdayMap::default();
        for (wd, v) in iter {
            m.set(wd, v);
        }
        m
    }
}

impl<T: Serialize> Serialize for WeekdayMap<T> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let mut m = s.serialize_map(Some(self.len()))?;
        for (wd, v) in self.iter() {
            m.serialize_entry(weekday_key(wd), v)?;
        }
        m.end()
    }
}

impl<'de, T: Deserialize<'de>> Deserialize<'de> for WeekdayMap<T> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<WeekdayMap<T>, D::Error> {
        struct V<T>(std::marker::PhantomData<T>);
        impl<'de, T: Deserialize<'de>> Visitor<'de> for V<T> {
            type Value = WeekdayMap<T>;
            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("a table keyed by weekday (Mon..Sun)")
            }
            fn visit_map<A: MapAccess<'de>>(self, mut m: A) -> Result<WeekdayMap<T>, A::Error> {
                let mut out = WeekdayMap::default();
                while let Some((k, v)) = m.next_entry::<String, T>()? {
                    let wd = parse_weekday_key(&k)
                        .ok_or_else(|| de::Error::custom(format!("unknown weekday {k:?}")))?;
                    out.set(wd, v);
                }
                Ok(out)
            }
        }
        d.deserialize_map(V(std::marker::PhantomData))
    }
}

// ---------------------------------------------------------------------------
// The model
// ---------------------------------------------------------------------------

/// The learned model, `.tm/model.json` (§8.5).
///
/// Every field is optional on the way in (`serde(default)`), so a partial or
/// hand-written file works and an unknown key is ignored rather than fatal —
/// §8.5 wants the file to be hand-editable. The field order is the spec's.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
#[serde(default)]
pub struct Model {
    /// Curve name (`lounge`, `home`, …) → energy level per `floor(hsw)`
    /// bucket, `HSW_BUCKETS` long.
    pub energy: BTreeMap<String, Vec<u8>>,
    /// Levels subtracted when `slept < config.energy.sleep_debt.under_hours`.
    /// `None` = not learned and not hand-written: [`Model::sleep_shift`]
    /// then falls back to `config.energy.sleep_debt.shift`. A value written
    /// in the file — by a fit or by hand — is always honoured, including
    /// `0.0` ("short nights do not cost me anything").
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sleep_debt_shift: Option<f64>,
    /// Tag (or `"_default"`) → `actual/est` multiplier.
    pub duration: BTreeMap<String, f64>,
    /// `P(lounge | weekday)`.
    pub p_lounge: WeekdayMap<f64>,
    /// Expected arrival per weekday.
    pub expected_arrival: WeekdayMap<Hhmm>,
    /// The day the model was fitted.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fitted: Option<NaiveDate>,
    /// Number of energy observations behind the fit.
    pub n_obs: u32,
}

impl Model {
    /// True when nothing has been learned or written (every lookup falls
    /// back to the config priors).
    pub fn is_empty(&self) -> bool {
        self.energy.is_empty()
            && self.duration.is_empty()
            && self.p_lounge.is_empty()
            && self.expected_arrival.is_empty()
            && self.sleep_debt_shift.is_none()
    }

    /// True when the file came from a fit (or records observations).
    pub fn is_fitted(&self) -> bool {
        self.fitted.is_some() || self.n_obs > 0
    }

    /// The config priors written out as a model (§8.5 "prior curve").
    pub fn from_config(cfg: &Config) -> Model {
        let energy = cfg
            .energy
            .prior
            .keys()
            .map(|loc| {
                let curve = (0..HSW_BUCKETS)
                    .map(|b| cfg.prior_energy(loc, b as f64))
                    .collect();
                (loc.clone(), curve)
            })
            .collect();
        let duration = BTreeMap::from([(DEFAULT_TAG.to_string(), 1.0)]);
        let p_lounge =
            WeekdayMap::from_iter(WEEKDAYS.iter().map(|wd| (*wd, *cfg.expected.p_lounge.get(*wd))));
        let expected_arrival = WeekdayMap::from_iter(
            WEEKDAYS
                .iter()
                .map(|wd| (*wd, Hhmm(*cfg.expected.arrival.get(*wd)))),
        );
        Model {
            energy,
            sleep_debt_shift: Some(cfg.energy.sleep_debt.shift),
            duration,
            p_lounge,
            expected_arrival,
            fitted: None,
            n_obs: 0,
        }
    }

    /// The learned level for a curve at `hours_since_wake`, if the model has
    /// that curve and bucket.
    pub fn energy_at(&self, curve: &str, hours_since_wake: f64) -> Option<u8> {
        self.energy
            .get(curve)
            .and_then(|c| c.get(bucket(hours_since_wake)))
            .copied()
    }

    /// The shift [`predict`] subtracts under sleep debt: the one written in
    /// the model when it has one (fitted or hand-edited), else the config's.
    pub fn sleep_shift(&self, cfg: &Config) -> f64 {
        self.sleep_debt_shift
            .unwrap_or(cfg.energy.sleep_debt.shift)
    }

    /// `P(lounge | weekday)`: learned, else `config.expected.p_lounge`.
    pub fn p_lounge_on(&self, wd: Weekday, cfg: &Config) -> f64 {
        self.p_lounge
            .get(wd)
            .copied()
            .unwrap_or_else(|| *cfg.expected.p_lounge.get(wd))
    }

    /// Expected arrival: learned, else `config.expected.arrival`.
    pub fn expected_arrival_on(&self, wd: Weekday, cfg: &Config) -> NaiveTime {
        self.expected_arrival
            .get(wd)
            .map(|t| t.0)
            .unwrap_or_else(|| *cfg.expected.arrival.get(wd))
    }

    /// The wake §8.5 measures `hsw` from — **the one fallback for a day with
    /// no `wake`**, shared by the planner and the CLI.
    ///
    /// `logged` is the wake the day actually has: `state.json`'s `wake`
    /// (§10.2), else the `wake` event of that day (§10.1). Having neither is a
    /// normal state — `tm wake` is optional, the day simply started
    /// unrecorded — so the fallback has to produce a sane day. The only start
    /// the spec has for a day it did not watch begin is the weekday's
    /// **expected arrival**: learned ([`Model::expected_arrival_on`], §8.5),
    /// else `config.expected.arrival` (§16). That is exactly what §8.4's
    /// lookahead already assumes for every day but today, so today and
    /// tomorrow are simulated the same way.
    ///
    /// Midnight is the trap this exists to close: it puts `hsw` at 9–11 h by
    /// mid-morning, where §8.5's prior curve is in its `3`/`2` tail, so every
    /// ci-4 and ci-5 item is ineligible and the whole day fills with ci-2
    /// work.
    pub fn wake_or_expected(
        &self,
        logged: Option<NaiveTime>,
        wd: Weekday,
        cfg: &Config,
    ) -> NaiveTime {
        logged.unwrap_or_else(|| self.expected_arrival_on(wd, cfg))
    }

    /// Parse `model.json` text.
    pub fn from_json(text: &str) -> Result<Model, serde_json::Error> {
        serde_json::from_str(text)
    }

    /// Render as pretty JSON with a trailing newline (what `tm model --fit`
    /// writes through the store; §8.5 wants the file human-readable, so objects
    /// are indented and the curves stay on one line each).
    pub fn to_json(&self) -> String {
        let mut buf = Vec::new();
        let mut ser = serde_json::Serializer::with_formatter(&mut buf, CompactArrays::default());
        self.serialize(&mut ser).expect("model is always serializable");
        buf.push(b'\n');
        String::from_utf8(buf).expect("serde_json writes UTF-8")
    }

    /// Read a model file; `Ok(None)` when it does not exist.
    pub fn load(path: &Path) -> Result<Option<Model>, EnergyError> {
        let text = match std::fs::read_to_string(path) {
            Ok(t) => t,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(source) => {
                return Err(EnergyError::Io {
                    path: path.display().to_string(),
                    source,
                })
            }
        };
        Model::from_json(&text).map(Some).map_err(|source| EnergyError::Json {
            path: path.display().to_string(),
            source,
        })
    }

    /// Read a model file, falling back to [`Model::default`] when missing.
    pub fn load_or_default(path: &Path) -> Result<Model, EnergyError> {
        Ok(Model::load(path)?.unwrap_or_default())
    }

}

/// A JSON formatter that indents objects like `serde_json`'s pretty printer
/// but keeps arrays on one line — a 12-level curve reads as a curve.
#[derive(Default)]
struct CompactArrays {
    level: usize,
    has_value: bool,
}

impl CompactArrays {
    fn indent<W: ?Sized + std::io::Write>(&self, w: &mut W) -> std::io::Result<()> {
        for _ in 0..self.level {
            w.write_all(b"  ")?;
        }
        Ok(())
    }
}

impl serde_json::ser::Formatter for CompactArrays {
    fn begin_array<W: ?Sized + std::io::Write>(&mut self, w: &mut W) -> std::io::Result<()> {
        w.write_all(b"[")
    }
    fn end_array<W: ?Sized + std::io::Write>(&mut self, w: &mut W) -> std::io::Result<()> {
        w.write_all(b"]")
    }
    fn begin_array_value<W: ?Sized + std::io::Write>(
        &mut self,
        w: &mut W,
        first: bool,
    ) -> std::io::Result<()> {
        if first {
            Ok(())
        } else {
            w.write_all(b", ")
        }
    }
    fn end_array_value<W: ?Sized + std::io::Write>(&mut self, _w: &mut W) -> std::io::Result<()> {
        self.has_value = true;
        Ok(())
    }
    fn begin_object<W: ?Sized + std::io::Write>(&mut self, w: &mut W) -> std::io::Result<()> {
        self.level += 1;
        self.has_value = false;
        w.write_all(b"{")
    }
    fn end_object<W: ?Sized + std::io::Write>(&mut self, w: &mut W) -> std::io::Result<()> {
        self.level -= 1;
        if self.has_value {
            w.write_all(b"\n")?;
            self.indent(w)?;
        }
        w.write_all(b"}")
    }
    fn begin_object_key<W: ?Sized + std::io::Write>(
        &mut self,
        w: &mut W,
        first: bool,
    ) -> std::io::Result<()> {
        w.write_all(if first { b"\n" } else { b",\n" })?;
        self.indent(w)
    }
    fn begin_object_value<W: ?Sized + std::io::Write>(&mut self, w: &mut W) -> std::io::Result<()> {
        w.write_all(b": ")
    }
    fn end_object_value<W: ?Sized + std::io::Write>(&mut self, _w: &mut W) -> std::io::Result<()> {
        self.has_value = true;
        Ok(())
    }
}

/// The `floor(hsw)` bucket index, clamped to `0..HSW_BUCKETS`.
pub fn bucket(hours_since_wake: f64) -> usize {
    if hours_since_wake.is_nan() || hours_since_wake <= 0.0 {
        return 0;
    }
    (hours_since_wake.floor() as usize).min(HSW_BUCKETS - 1)
}

/// The curve name a location uses: its own when the model or the config has
/// one, otherwise `home` (see the module note on locations).
pub fn curve_key(loc: &Loc, cfg: &Config, model: &Model) -> String {
    let name = match loc {
        Loc::Lounge => return "lounge".to_string(),
        Loc::Home => return "home".to_string(),
        Loc::Any => return "home".to_string(),
        Loc::Out => "out",
        Loc::Named(n) => n.as_str(),
    };
    if model.energy.contains_key(name) || cfg.energy.prior.contains_key(name) {
        name.to_string()
    } else {
        "home".to_string()
    }
}

/// The prior level for a curve key: the configured curve for that key, else
/// the `home` curve, else whatever [`Config::prior_energy`] falls back to.
pub fn prior_level(cfg: &Config, curve: &str, hours_since_wake: f64) -> u8 {
    if cfg.energy.prior.contains_key(curve) || !cfg.energy.prior.contains_key("home") {
        cfg.prior_energy(curve, hours_since_wake)
    } else {
        cfg.prior_energy("home", hours_since_wake)
    }
}

// ---------------------------------------------------------------------------
// Prediction
// ---------------------------------------------------------------------------

/// The features a prediction is made from (§8.5; v1 uses `loc`, `hsw` and
/// `slept_min`, v2's ordinal regression uses the rest).
#[derive(Clone, Debug, PartialEq)]
pub struct Features {
    /// Where you are.
    pub loc: Loc,
    /// Hours since wake.
    pub hsw: f64,
    /// Hour of day (fractional), for v2.
    pub hod: f64,
    /// Minutes slept, when known.
    pub slept_min: Option<u32>,
    /// Weekday, for v2.
    pub weekday: Weekday,
    /// Blocks already done today, for v2.
    pub blocks_done: u32,
    /// Minutes since the last break, for v2.
    pub since_break_min: u32,
}

impl Default for Features {
    fn default() -> Features {
        Features {
            loc: Loc::Any,
            hsw: 0.0,
            hod: 0.0,
            slept_min: None,
            weekday: Weekday::Mon,
            blocks_done: 0,
            since_break_min: 0,
        }
    }
}

impl Features {
    /// Features for a location at `hours_since_wake`.
    pub fn new(loc: Loc, hours_since_wake: f64) -> Features {
        Features {
            loc,
            hsw: hours_since_wake,
            ..Features::default()
        }
    }

    /// Features for an instant, deriving `hsw`, `hod` and `weekday` from it.
    pub fn at(t: DateTime<Tz>, wake: DateTime<Tz>, loc: Loc) -> Features {
        Features {
            loc,
            hsw: crate::log::hours_since_wake(&t, &wake),
            hod: t.hour() as f64 + t.minute() as f64 / 60.0,
            weekday: t.weekday(),
            ..Features::default()
        }
    }

    /// Set the minutes slept.
    pub fn with_slept(mut self, slept_min: Option<u32>) -> Features {
        self.slept_min = slept_min;
        self
    }

    /// Set the day-progress features.
    pub fn with_progress(mut self, blocks_done: u32, since_break_min: u32) -> Features {
        self.blocks_done = blocks_done;
        self.since_break_min = since_break_min;
        self
    }

    /// True when the night was shorter than `config.energy.sleep_debt.under_hours`.
    pub fn under_slept(&self, cfg: &Config) -> bool {
        self.slept_min
            .is_some_and(|m| m as f64 / 60.0 < cfg.energy.sleep_debt.under_hours)
    }
}

/// Predicted energy 0..=5 for a slot (§8.5): the learned curve when the model
/// has the bucket, else the config prior, minus the sleep-debt shift when the
/// night was short.
pub fn predict(model: &Model, cfg: &Config, f: &Features) -> u8 {
    let curve = curve_key(&f.loc, cfg, model);
    let base = model
        .energy_at(&curve, f.hsw)
        .unwrap_or_else(|| prior_level(cfg, &curve, f.hsw)) as i32;
    let shift = if f.under_slept(cfg) {
        model.sleep_shift(cfg).round() as i32
    } else {
        0
    };
    (base - shift).clamp(0, 5) as u8
}

// ---------------------------------------------------------------------------
// Today's posterior
// ---------------------------------------------------------------------------

/// One energy report (§8.5): what was predicted and what you said.
#[derive(Clone, Debug, PartialEq)]
pub struct Report {
    /// When the report was made.
    pub t: DateTime<Tz>,
    /// The prediction at that time.
    pub pred: u8,
    /// The reported level.
    pub rep: u8,
}

impl Report {
    /// `δ = rep − pred`.
    pub fn delta(&self) -> f64 {
        self.rep as f64 - self.pred as f64
    }
}

/// The weight of a report `hours_since` hours old: 1 up to `full_hours`,
/// falling linearly to 0 at `zero_hours`, and 0 for a report in the future.
pub fn posterior_weight(hours_since: f64, full_hours: f64, zero_hours: f64) -> f64 {
    if hours_since < 0.0 {
        return 0.0;
    }
    if hours_since <= full_hours {
        return 1.0;
    }
    if hours_since >= zero_hours || zero_hours <= full_hours {
        return 0.0;
    }
    (zero_hours - hours_since) / (zero_hours - full_hours)
}

/// Today's energy reports and the correction they imply (§8.5).
#[derive(Clone, Debug, PartialEq)]
pub struct Posterior {
    reports: Vec<Report>,
    full_hours: f64,
    zero_hours: f64,
}

impl Default for Posterior {
    fn default() -> Posterior {
        Posterior {
            reports: Vec::new(),
            full_hours: 3.0,
            zero_hours: 6.0,
        }
    }
}

impl Posterior {
    /// No reports yet: [`Posterior::correct`] is the identity.
    pub fn none(cfg: &Config) -> Posterior {
        Posterior::from_reports(&[], cfg)
    }

    /// Build from `(time, pred, rep)` triples in any order.
    pub fn from_reports(reports: &[(DateTime<Tz>, u8, u8)], cfg: &Config) -> Posterior {
        let mut reports: Vec<Report> = reports
            .iter()
            .map(|(t, pred, rep)| Report {
                t: *t,
                pred: *pred,
                rep: *rep,
            })
            .collect();
        reports.sort_by_key(|r| r.t);
        Posterior {
            reports,
            full_hours: cfg.energy.posterior_full_hours,
            zero_hours: cfg.energy.posterior_zero_hours,
        }
    }

    /// Build from the day's logged observations (`start` with a `rep`, and
    /// `energy` events); `tz` is `config.tz`.
    pub fn from_observations(obs: &[EnergyObs], tz: Tz, cfg: &Config) -> Posterior {
        let triples: Vec<(DateTime<Tz>, u8, u8)> = obs
            .iter()
            .map(|o| (o.t.with_timezone(&tz), o.pred, o.rep))
            .collect();
        Posterior::from_reports(&triples, cfg)
    }

    /// The reports, oldest first.
    pub fn reports(&self) -> &[Report] {
        &self.reports
    }

    /// True when there is nothing to correct with.
    pub fn is_empty(&self) -> bool {
        self.reports.is_empty()
    }

    /// The most recent report at or before `t`.
    pub fn latest_before(&self, t: DateTime<Tz>) -> Option<&Report> {
        self.reports.iter().rev().find(|r| r.t <= t)
    }

    /// The correction `δ·w` that applies at `t` (0 with no usable report).
    pub fn adjustment(&self, t: DateTime<Tz>) -> f64 {
        let Some(r) = self.latest_before(t) else {
            return 0.0;
        };
        let hours = (t - r.t).num_seconds() as f64 / 3600.0;
        r.delta() * posterior_weight(hours, self.full_hours, self.zero_hours)
    }

    /// Apply the correction to a predicted level, clamped to `0..=5`.
    pub fn correct(&self, t: DateTime<Tz>, pred: u8) -> u8 {
        let corrected = pred as f64 + self.adjustment(t);
        corrected.round().clamp(0.0, 5.0) as u8
    }
}

// ---------------------------------------------------------------------------
// Duration multipliers
// ---------------------------------------------------------------------------

/// The duration multiplier for an item (§8.5): `"<ci>:<tag>"` for the first
/// matching tag, then `"<tag>"`, then `"_default"`, then 1.0.
pub fn duration_multiplier(model: &Model, ci: u8, tags: &[String]) -> f64 {
    for tag in tags {
        if let Some(m) = model.duration.get(&format!("{ci}:{tag}")) {
            return *m;
        }
    }
    for tag in tags {
        if let Some(m) = model.duration.get(tag) {
            return *m;
        }
    }
    model.duration.get(DEFAULT_TAG).copied().unwrap_or(1.0)
}

/// **How long a ghost block ran for** (§8.5): the item's planned or remaining
/// estimate × its duration multiplier, falling back to one block and floored at
/// `MIN_REMAINING_MIN`. The one body both readers call — `cli::ghost`'s ghost
/// rows and the TUI's (`App::ghost_block_min`): until the W-46 repair the TUI
/// carried its own copy of it (README gap 4874, AGENTS §5.3), and it lives here
/// because the TUI's modules are compiled into tests that hold no `cli`.
pub fn ghost_block_minutes(
    id: Option<&crate::model::Id>,
    block_min: u32,
    model: &Model,
    tree: &crate::tree::Tree,
) -> u32 {
    let Some(id) = id else {
        return block_min;
    };
    let Some(item) = tree.get(id) else {
        return block_min;
    };
    let est = tree
        .planned_minutes(id)
        .or_else(|| tree.remaining(id))
        .filter(|m| *m > 0)
        .unwrap_or(block_min);
    let multiplier = duration_multiplier(model, item.ci, &tree.tags_effective(id));
    planned_minutes(est, multiplier).max(crate::horizon::MIN_REMAINING_MIN)
}

/// Minutes the planner schedules for an estimate: `round(est × multiplier)`.
pub fn planned_minutes(est_min: u32, multiplier: f64) -> u32 {
    if !multiplier.is_finite() || multiplier <= 0.0 {
        return est_min;
    }
    (est_min as f64 * multiplier).round().max(0.0) as u32
}

/// A multiplier as written in the timeline: `1.6`, `1.25`, `1`.
pub fn fmt_multiplier(multiplier: f64) -> String {
    let s = format!("{multiplier:.2}");
    let s = s.trim_end_matches('0').trim_end_matches('.');
    s.to_string()
}

/// The §4.3 estimate column: `2b×1.6`, or just `2b` when the multiplier is 1.
pub fn fmt_planned(est: &Dur, multiplier: f64) -> String {
    if (multiplier - 1.0).abs() < 0.005 {
        est.to_string()
    } else {
        format!("{}×{}", est, fmt_multiplier(multiplier))
    }
}

// ---------------------------------------------------------------------------
// Fitting (§8.5 v1)
// ---------------------------------------------------------------------------

/// One `arrive` event, reduced to what the fit needs.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ArrivalObs {
    /// The day it belongs to.
    pub date: NaiveDate,
    /// Local arrival time.
    pub time: NaiveTime,
    /// Location arrived at.
    pub loc: String,
}

/// What [`fit`] learns from.
#[derive(Clone, Copy, Debug, Default)]
pub struct FitInput<'a> {
    /// Energy observations (`start` with a `rep`, and `energy` events).
    pub energy: &'a [EnergyObs],
    /// Duration observations (timed `done` events).
    pub durations: &'a [DurationObs],
    /// `arrive` events.
    pub arrivals: &'a [ArrivalObs],
    /// The model to shrink towards; `None` = the config priors. §8.5: "hand
    /// edits become the new prior", so `tm model --fit` passes the model
    /// currently on disk.
    pub base: Option<&'a Model>,
}

impl<'a> FitInput<'a> {
    /// All three observation sets, shrinking towards the config priors.
    pub fn new(
        energy: &'a [EnergyObs],
        durations: &'a [DurationObs],
        arrivals: &'a [ArrivalObs],
    ) -> FitInput<'a> {
        FitInput {
            energy,
            durations,
            arrivals,
            base: None,
        }
    }
    /// Shrink towards `base` instead of the config priors.
    pub fn with_base(mut self, base: &'a Model) -> FitInput<'a> {
        self.base = Some(base);
        self
    }
}

/// The age weight of an observation: `exp(−age_days / decay_days)`.
fn age_weight(day: NaiveDate, today: NaiveDate, decay_days: f64) -> f64 {
    let age = (today - day).num_days().max(0) as f64;
    if decay_days <= 0.0 {
        return if age == 0.0 { 1.0 } else { 0.0 };
    }
    (-age / decay_days).exp()
}

/// The §8.5 `went` weight: 3 (collapsed) counts double, 2 counts 1.5.
fn went_weight(went: Option<u8>) -> f64 {
    match went {
        Some(3) => 2.0,
        Some(2) => 1.5,
        _ => 1.0,
    }
}

/// The full weight of an observation: age decay × `went`.
pub fn observation_weight(day: NaiveDate, went: Option<u8>, today: NaiveDate, cfg: &Config) -> f64 {
    age_weight(day, today, cfg.energy.decay_days) * went_weight(went)
}

/// A shrunken mean: `(n0·prior + Σ wᵢ xᵢ) / (n0 + Σ wᵢ)` (§8.5).
pub fn shrunken_mean(prior: f64, n0: f64, weighted: &[(f64, f64)]) -> f64 {
    let mut num = n0 * prior;
    let mut den = n0;
    for (w, x) in weighted {
        num += w * x;
        den += w;
    }
    if den == 0.0 {
        prior
    } else {
        num / den
    }
}

/// Fit the v1 model (§8.5): bucketed shrinkage means for the energy curves,
/// the sleep-debt shift, the duration multipliers, `p_lounge` and
/// `expected_arrival`.
///
/// `today` anchors the age decay; nothing here reads a clock.
pub fn fit(cfg: &Config, input: &FitInput, today: NaiveDate) -> Model {
    let n0 = cfg.energy.prior_weight;
    let base = input.base;

    // --- energy curves -----------------------------------------------------
    let mut curves: Vec<String> = cfg.energy.prior.keys().cloned().collect();
    if let Some(m) = base {
        for k in m.energy.keys() {
            if !curves.contains(k) {
                curves.push(k.clone());
            }
        }
    }
    for o in input.energy {
        if !curves.contains(&o.loc) {
            curves.push(o.loc.clone());
        }
    }
    curves.sort();

    let mut energy: BTreeMap<String, Vec<u8>> = BTreeMap::new();
    for curve in &curves {
        let mut levels = Vec::with_capacity(HSW_BUCKETS);
        for b in 0..HSW_BUCKETS {
            let prior = base
                .and_then(|m| m.energy.get(curve))
                .and_then(|c| c.get(b))
                .map(|v| *v as f64)
                .unwrap_or_else(|| prior_level(cfg, curve, b as f64) as f64);
            let obs: Vec<(f64, f64)> = input
                .energy
                .iter()
                .filter(|o| &o.loc == curve && bucket(o.hsw) == b)
                .map(|o| {
                    (
                        observation_weight(o.day, o.went, today, cfg),
                        o.rep as f64,
                    )
                })
                .collect();
            let level = shrunken_mean(prior, n0, &obs).round().clamp(0.0, 5.0) as u8;
            levels.push(level);
        }
        energy.insert(curve.clone(), levels);
    }

    // --- sleep-debt shift --------------------------------------------------
    // The learned *deficit* mean(energy[b] − rep) over short nights; see the
    // module note on the sign.
    let under = cfg.energy.sleep_debt.under_hours;
    let shift_prior = base
        .and_then(|m| m.sleep_debt_shift)
        .unwrap_or(cfg.energy.sleep_debt.shift);
    let shift_obs: Vec<(f64, f64)> = input
        .energy
        .iter()
        .filter(|o| o.slept_min.is_some_and(|m| m as f64 / 60.0 < under))
        .map(|o| {
            let learned = energy
                .get(&o.loc)
                .and_then(|c| c.get(bucket(o.hsw)))
                .map(|v| *v as f64)
                .unwrap_or_else(|| prior_level(cfg, &o.loc, o.hsw) as f64);
            (
                observation_weight(o.day, o.went, today, cfg),
                learned - o.rep as f64,
            )
        })
        .collect();
    // Nothing observed and nothing in the base → leave it absent, so the
    // config shift keeps applying (see the module note on absent vs. zero).
    let sleep_debt_shift = (!shift_obs.is_empty()
        || base.and_then(|m| m.sleep_debt_shift).is_some())
    .then(|| round2(shrunken_mean(shift_prior, n0, &shift_obs)));

    // --- duration multipliers ---------------------------------------------
    let dn0 = cfg.energy.duration_prior_weight;
    let mut by_tag: BTreeMap<String, Vec<(f64, f64)>> = BTreeMap::new();
    let mut all: Vec<(f64, f64)> = Vec::new();
    for o in input.durations {
        let Some(ratio) = o.ratio() else { continue };
        let w = observation_weight(o.day, o.went, today, cfg);
        all.push((w, ratio));
        if let Some(tag) = o.tags.first() {
            by_tag.entry(tag.clone()).or_default().push((w, ratio));
        }
    }
    let mut duration: BTreeMap<String, f64> = BTreeMap::new();
    for (tag, obs) in &by_tag {
        let prior = base.and_then(|m| m.duration.get(tag)).copied().unwrap_or(1.0);
        duration.insert(tag.clone(), round2(shrunken_mean(prior, dn0, obs)));
    }
    let default_prior = base
        .and_then(|m| m.duration.get(DEFAULT_TAG))
        .copied()
        .unwrap_or(1.0);
    duration.insert(
        DEFAULT_TAG.to_string(),
        round2(shrunken_mean(default_prior, dn0, &all)),
    );

    // --- arrivals ----------------------------------------------------------
    let mut p_lounge = WeekdayMap::default();
    let mut expected_arrival = WeekdayMap::default();
    for wd in WEEKDAYS {
        let day_obs: Vec<&ArrivalObs> = input
            .arrivals
            .iter()
            .filter(|a| a.date.weekday() == wd)
            .collect();
        let weights: Vec<f64> = day_obs
            .iter()
            .map(|a| age_weight(a.date, today, cfg.energy.decay_days))
            .collect();

        // A weekday nothing was observed on stays *absent*, so the lookahead
        // keeps falling back to `[expected]` in config.toml (§8.4) and an
        // edit there still takes effect after a fit. A base value is kept:
        // it was learned once, and a fit with no new data must not lose it.
        let base_lounge = base.and_then(|m| m.p_lounge.get(wd).copied());
        if !day_obs.is_empty() || base_lounge.is_some() {
            let lounge_prior = base_lounge.unwrap_or_else(|| *cfg.expected.p_lounge.get(wd));
            let lounge: Vec<(f64, f64)> = day_obs
                .iter()
                .zip(&weights)
                .map(|(a, w)| (*w, if a.loc == "lounge" { 1.0 } else { 0.0 }))
                .collect();
            p_lounge.set(wd, round2(shrunken_mean(lounge_prior, n0, &lounge)));
        }

        let base_arrival = base.and_then(|m| m.expected_arrival.get(wd).map(|t| t.0));
        if !day_obs.is_empty() || base_arrival.is_some() {
            let arr_prior = base_arrival.unwrap_or_else(|| *cfg.expected.arrival.get(wd));
            let arrivals: Vec<(f64, f64)> = day_obs
                .iter()
                .zip(&weights)
                .map(|(a, w)| (*w, minutes_of(a.time) as f64))
                .collect();
            let mean = shrunken_mean(minutes_of(arr_prior) as f64, n0, &arrivals);
            let minutes = mean.round().clamp(0.0, 24.0 * 60.0 - 1.0) as u32;
            expected_arrival.set(
                wd,
                Hhmm(NaiveTime::from_hms_opt(minutes / 60, minutes % 60, 0).expect("clamped")),
            );
        }
    }

    Model {
        energy,
        sleep_debt_shift,
        duration,
        p_lounge,
        expected_arrival,
        fitted: Some(today),
        n_obs: input.energy.len() as u32,
    }
}

/// Fit from the observations themselves (`tm model --fit`).
///
/// Stage 5 D9 step F1 (design §14.7): the fit takes the three observation
/// lists — the energy observations, the duration observations and the
/// arrivals — and never a whole [`Replay`]. At the `All` scope those lists
/// are what the kernel hands back (design §11.2), so this is the fit reading
/// the kernel's observations directly.
pub fn fit_observations(
    cfg: &Config,
    energy: &[EnergyObs],
    durations: &[DurationObs],
    arrivals: &[ArrivalObs],
    today: NaiveDate,
) -> Model {
    fit(cfg, &FitInput::new(energy, durations, arrivals), today)
}

/// The `arrive` events of a replay, in `config.tz` local time.
pub fn arrivals_from_replay(cfg: &Config, replay: &Replay) -> Vec<ArrivalObs> {
    replay
        .days
        .values()
        .filter_map(|d| {
            let t = d.arrival?.with_timezone(&cfg.tz);
            Some(ArrivalObs {
                date: d.date,
                time: t.time(),
                loc: d.loc.clone().unwrap_or_default(),
            })
        })
        .collect()
}

fn minutes_of(t: NaiveTime) -> u32 {
    t.hour() * 60 + t.minute()
}

fn round2(x: f64) -> f64 {
    (x * 100.0).round() / 100.0
}

// ---------------------------------------------------------------------------
// Monitors and comparison (§11, §13)
// ---------------------------------------------------------------------------

/// Two models scored against the same observations (`tm model --compare`).
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct Comparison {
    /// Observations scored.
    pub n: usize,
    /// Mean absolute error of model A.
    pub mae_a: f64,
    /// Mean absolute error of model B.
    pub mae_b: f64,
    /// Mean signed error `rep − pred` of model A.
    pub bias_a: f64,
    /// Mean signed error `rep − pred` of model B.
    pub bias_b: f64,
    /// `(clock hour, mae_a, mae_b)`, hours with observations only.
    pub by_hour: Vec<(u32, f64, f64)>,
}

impl Comparison {
    /// True when B's overall MAE is lower (the promotion rule in §8.5).
    pub fn b_is_better(&self) -> bool {
        self.mae_b < self.mae_a
    }
}

/// Score two models on the same energy observations by re-predicting each
/// one (§13 `tm model --compare`, §11 energy calibration).
///
/// `cfg` is needed because a model falls back to the config priors for a
/// bucket it has not learned.
pub fn compare(cfg: &Config, a: &Model, b: &Model, obs: &[EnergyObs]) -> Comparison {
    let mut hours: BTreeMap<u32, (Vec<f64>, Vec<f64>)> = BTreeMap::new();
    let (mut errs_a, mut errs_b) = (Vec::new(), Vec::new());
    for o in obs {
        let f = features_of(o);
        let pa = predict(a, cfg, &f) as f64;
        let pb = predict(b, cfg, &f) as f64;
        let rep = o.rep as f64;
        let (ea, eb) = (rep - pa, rep - pb);
        errs_a.push(ea);
        errs_b.push(eb);
        let hour = o.t.with_timezone(&cfg.tz).hour();
        let entry = hours.entry(hour).or_default();
        entry.0.push(ea);
        entry.1.push(eb);
    }
    Comparison {
        n: obs.len(),
        mae_a: mean(&errs_a.iter().map(|e| e.abs()).collect::<Vec<_>>()),
        mae_b: mean(&errs_b.iter().map(|e| e.abs()).collect::<Vec<_>>()),
        bias_a: mean(&errs_a),
        bias_b: mean(&errs_b),
        by_hour: hours
            .into_iter()
            .map(|(h, (a, b))| {
                (
                    h,
                    mean(&a.iter().map(|e| e.abs()).collect::<Vec<_>>()),
                    mean(&b.iter().map(|e| e.abs()).collect::<Vec<_>>()),
                )
            })
            .collect(),
    }
}

/// The features of a logged observation (what the model would predict from).
pub fn features_of(o: &EnergyObs) -> Features {
    let loc = Loc::parse(&o.loc).unwrap_or(Loc::Any);
    Features {
        loc,
        hsw: o.hsw,
        hod: 0.0,
        slept_min: o.slept_min,
        weekday: Weekday::Mon,
        blocks_done: 0,
        since_break_min: 0,
    }
}

/// The §11 energy-calibration monitor: MAE and bias of the *logged*
/// predictions against the reports, overall and by clock hour.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct Calibration {
    /// Observations scored.
    pub n: usize,
    /// Mean absolute error.
    pub mae: f64,
    /// Mean signed error `rep − pred` (negative = you report lower than
    /// predicted).
    pub bias: f64,
    /// `(clock hour, n, mae, bias)`.
    pub by_hour: Vec<(u32, usize, f64, f64)>,
}

/// Compute the §11 energy calibration from logged observations.
pub fn calibration(cfg: &Config, obs: &[EnergyObs]) -> Calibration {
    let mut hours: BTreeMap<u32, Vec<f64>> = BTreeMap::new();
    let mut errs = Vec::new();
    for o in obs {
        let e = o.delta() as f64;
        errs.push(e);
        hours
            .entry(o.t.with_timezone(&cfg.tz).hour())
            .or_default()
            .push(e);
    }
    Calibration {
        n: obs.len(),
        mae: mean(&errs.iter().map(|e| e.abs()).collect::<Vec<_>>()),
        bias: mean(&errs),
        by_hour: hours
            .into_iter()
            .map(|(h, es)| {
                (
                    h,
                    es.len(),
                    mean(&es.iter().map(|e| e.abs()).collect::<Vec<_>>()),
                    mean(&es),
                )
            })
            .collect(),
    }
}

/// One row of the §11 estimate-calibration monitor (`lean ×1.6 (n=9)`).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct TagStats {
    /// The tag (or `"_default"` for the all-observations row).
    pub tag: String,
    /// Observations.
    pub n: usize,
    /// Plain mean of `actual/est`.
    pub mean_ratio: f64,
    /// The shrunken multiplier a fit would write.
    pub multiplier: f64,
    /// Mean ratio over the last 7 days, when there are observations there
    /// (the "trend" column).
    pub recent_ratio: Option<f64>,
}

/// The §11 estimate-calibration monitor: `actual/est` per tag, with the
/// shrunken multiplier and a 7-day trend. Sorted by tag, `_default` last.
pub fn estimate_calibration(cfg: &Config, durations: &[DurationObs], today: NaiveDate) -> Vec<TagStats> {
    let mut by_tag: BTreeMap<String, Vec<&DurationObs>> = BTreeMap::new();
    let mut all: Vec<&DurationObs> = Vec::new();
    for o in durations {
        if o.ratio().is_none() {
            continue;
        }
        all.push(o);
        if let Some(tag) = o.tags.first() {
            by_tag.entry(tag.clone()).or_default().push(o);
        }
    }
    let stats = |tag: &str, obs: &[&DurationObs]| {
        let ratios: Vec<f64> = obs.iter().filter_map(|o| o.ratio()).collect();
        let weighted: Vec<(f64, f64)> = obs
            .iter()
            .filter_map(|o| {
                o.ratio()
                    .map(|r| (observation_weight(o.day, o.went, today, cfg), r))
            })
            .collect();
        let recent: Vec<f64> = obs
            .iter()
            .filter(|o| (today - o.day).num_days() < 7)
            .filter_map(|o| o.ratio())
            .collect();
        TagStats {
            tag: tag.to_string(),
            n: ratios.len(),
            mean_ratio: round2(mean(&ratios)),
            multiplier: round2(shrunken_mean(
                1.0,
                cfg.energy.duration_prior_weight,
                &weighted,
            )),
            recent_ratio: (!recent.is_empty()).then(|| round2(mean(&recent))),
        }
    };
    let mut out: Vec<TagStats> = by_tag.iter().map(|(t, o)| stats(t, o)).collect();
    if !all.is_empty() {
        out.push(stats(DEFAULT_TAG, &all));
    }
    out
}

fn mean(xs: &[f64]) -> f64 {
    if xs.is_empty() {
        return 0.0;
    }
    round2(xs.iter().sum::<f64>() / xs.len() as f64)
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

/// A human-readable model table (`tm model --show`).
pub fn show(model: &Model) -> String {
    let mut s = String::new();
    match model.fitted {
        Some(d) => writeln!(s, "model  fitted {d} · {} obs", model.n_obs).ok(),
        None if model.is_empty() => writeln!(s, "model  not fitted (using config priors)").ok(),
        None => writeln!(s, "model  not fitted · {} obs", model.n_obs).ok(),
    };
    if !model.energy.is_empty() {
        writeln!(s, "energy    hsw {}", hsw_header()).ok();
        for (curve, levels) in &model.energy {
            let cells: Vec<String> = levels.iter().map(|l| format!("{l:>2}")).collect();
            writeln!(s, "  {:<10}  {}", curve, cells.join(" ")).ok();
        }
    }
    writeln!(
        s,
        "sleep     debt shift {}",
        match model.sleep_debt_shift {
            Some(x) => fmt_multiplier(x),
            None => "- (config)".to_string(),
        }
    )
    .ok();
    if !model.duration.is_empty() {
        let cells: Vec<String> = model
            .duration
            .iter()
            .map(|(t, m)| format!("{t} ×{}", fmt_multiplier(*m)))
            .collect();
        writeln!(s, "duration  {}", cells.join(" · ")).ok();
    }
    if !model.p_lounge.is_empty() || !model.expected_arrival.is_empty() {
        let days: Vec<&str> = WEEKDAY_KEYS.to_vec();
        writeln!(
            s,
            "weekday   {}",
            days.iter()
                .map(|d| format!("{d:>6}"))
                .collect::<Vec<_>>()
                .join("")
        )
        .ok();
        if !model.p_lounge.is_empty() {
            let cells: Vec<String> = WEEKDAYS
                .iter()
                .map(|wd| match model.p_lounge.get(*wd) {
                    Some(p) => format!("{p:>6.2}"),
                    None => format!("{:>6}", "-"),
                })
                .collect();
            writeln!(s, "p(lounge) {}", cells.join("")).ok();
        }
        if !model.expected_arrival.is_empty() {
            let cells: Vec<String> = WEEKDAYS
                .iter()
                .map(|wd| match model.expected_arrival.get(*wd) {
                    Some(t) => format!("{:>6}", t.to_string()),
                    None => format!("{:>6}", "-"),
                })
                .collect();
            writeln!(s, "arrival   {}", cells.join("")).ok();
        }
    }
    s
}

fn hsw_header() -> String {
    (0..HSW_BUCKETS)
        .map(|b| format!("{b:>2}"))
        .collect::<Vec<_>>()
        .join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::TimeZone;

    fn cfg() -> Config {
        Config::default()
    }

    fn t(h: u32, m: u32) -> DateTime<Tz> {
        chrono_tz::America::Chicago
            .with_ymd_and_hms(2026, 9, 7, h, m, 0)
            .single()
            .expect("valid local time")
    }

    #[test]
    fn buckets_clamp() {
        assert_eq!(bucket(-1.0), 0);
        assert_eq!(bucket(0.0), 0);
        assert_eq!(bucket(0.99), 0);
        assert_eq!(bucket(1.0), 1);
        assert_eq!(bucket(11.9), 11);
        assert_eq!(bucket(30.0), 11);
    }

    #[test]
    fn predict_falls_back_to_the_prior() {
        let cfg = cfg();
        let m = Model::default();
        assert_eq!(predict(&m, &cfg, &Features::new(Loc::Lounge, 0.99)), 4);
        assert_eq!(predict(&m, &cfg, &Features::new(Loc::Lounge, 1.0)), 5);
        assert_eq!(predict(&m, &cfg, &Features::new(Loc::Home, 2.0)), 4);
        // Out / Any / unknown named locations use the home curve.
        assert_eq!(predict(&m, &cfg, &Features::new(Loc::Out, 2.0)), 4);
        assert_eq!(predict(&m, &cfg, &Features::new(Loc::Any, 2.0)), 4);
        assert_eq!(
            predict(&m, &cfg, &Features::new(Loc::Named("zoom".into()), 2.0)),
            4
        );
    }

    #[test]
    fn from_config_reproduces_the_prior() {
        let cfg = cfg();
        let m = Model::from_config(&cfg);
        assert_eq!(m.energy["lounge"], vec![4, 5, 5, 5, 5, 4, 4, 4, 3, 3, 2, 2]);
        assert_eq!(m.energy["home"], vec![3, 4, 4, 4, 3, 3, 3, 3, 2, 2, 2, 2]);
        for hsw in [0.0, 0.99, 1.0, 5.0, 8.0, 10.0, 11.5] {
            assert_eq!(
                predict(&m, &cfg, &Features::new(Loc::Lounge, hsw)),
                predict(&Model::default(), &cfg, &Features::new(Loc::Lounge, hsw)),
                "hsw {hsw}"
            );
        }
    }

    #[test]
    fn sleep_debt_shift_applies() {
        let cfg = cfg();
        let m = Model::default();
        let f = Features::new(Loc::Lounge, 2.0).with_slept(Some(6 * 60));
        assert_eq!(predict(&m, &cfg, &f), 4);
        let f = Features::new(Loc::Lounge, 2.0).with_slept(Some(8 * 60));
        assert_eq!(predict(&m, &cfg, &f), 5);
    }

    #[test]
    fn posterior_weights() {
        assert_eq!(posterior_weight(0.0, 3.0, 6.0), 1.0);
        assert_eq!(posterior_weight(3.0, 3.0, 6.0), 1.0);
        assert_eq!(posterior_weight(4.5, 3.0, 6.0), 0.5);
        assert_eq!(posterior_weight(6.0, 3.0, 6.0), 0.0);
        assert_eq!(posterior_weight(-1.0, 3.0, 6.0), 0.0);
    }

    #[test]
    fn posterior_corrects_later_slots() {
        let cfg = cfg();
        let p = Posterior::from_reports(&[(t(9, 0), 5, 4)], &cfg);
        assert_eq!(p.correct(t(10, 0), 5), 4);
        assert_eq!(p.correct(t(8, 0), 5), 5); // before the report
        assert_eq!(p.correct(t(15, 0), 5), 5); // fully decayed
                                               // The most recent report wins.
        let p = Posterior::from_reports(&[(t(9, 0), 5, 3), (t(11, 0), 4, 4)], &cfg);
        assert_eq!(p.correct(t(12, 0), 4), 4);
    }

    #[test]
    fn multipliers_and_display() {
        let mut m = Model::default();
        m.duration.insert("lean".into(), 1.6);
        m.duration.insert(DEFAULT_TAG.into(), 1.3);
        assert_eq!(duration_multiplier(&m, 4, &["lean".to_string()]), 1.6);
        assert_eq!(duration_multiplier(&m, 4, &["admin".to_string()]), 1.3);
        assert_eq!(duration_multiplier(&m, 4, &[]), 1.3);
        assert_eq!(planned_minutes(120, 1.6), 192);
        let est = Dur::blocks(2, 60);
        assert_eq!(fmt_planned(&est, 1.6), "2b×1.6");
        assert_eq!(fmt_planned(&est, 1.0), "2b");
    }

    #[test]
    fn json_round_trip() {
        let cfg = cfg();
        let m = Model::from_config(&cfg);
        let text = m.to_json();
        assert_eq!(Model::from_json(&text).unwrap(), m);
        assert!(text.contains("\"Mon\""), "{text}");
    }
}
