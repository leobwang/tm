//! **The one encoder of the capacity request** (stage 5 D10 step L8, host half;
//! design `kernel/design/stage5/stage5-D9-D10-design.md` §13.6, §13.8).
//!
//! Since this step the shipped binary's §8.4 lookahead and every §7 priority
//! come from the kernel: `Look.lookahead` (the owner's D10: each future day an
//! exact mixture of the day at the lounge and the day at home, in units over
//! `capDen = 10^18`, D17) and `Look.prioritiesWithFloors` (step 3's EDF pass,
//! §7.1's bin at the exact availability, §7.2's row, §7.4's hysteresis, and the
//! floor pass). Nothing else in the Rust builds a capacity request, and nothing
//! else reads one back:
//!
//! * [`written_pair`] is the only way a configured decimal reaches the kernel:
//!   **the text its file writes** ([`Written`]: TOML spans, JSON raw values),
//!   read as the exact decimal it is, never its double (`0.1000000000000000001`
//!   has 19 places, though its double prints `0.1`; W-3's audit). A value no file
//!   writes (a default) is its double's shortest text, [`decimal_pair`], never
//!   the binary expansion (`0.9` is `9/10`). T15 is the latter's proptest.
//! * [`check_inputs`] runs the same encoding over `config.toml` and
//!   `.tm/model.json` before a request is built, so a weight outside `[0, 1]` or
//!   with more than 18 written decimal places fails every verb that computes capacity or
//!   priority **by file and key** (§13.2, parity P26); the kernel's refusal stays
//!   the authority, and [`named_refusal`] names the file and key of every
//!   refusal a configured value can cause.
//! * [`request`] builds the whole request: the plan's documents (walls are the
//!   kernel's reading, gap 111), `now`, `blockMin`, the zone table from
//!   [`super::tz_table`] (the one zone encoder), a **`log` section** (D24's
//!   seam), and the `capacity` section: both weekday tables raw (the kernel
//!   picks, D10-4), today's `wake` (`state.json`'s clock, else the literal
//!   `"log"` — the fork's precedence, gap 261), the learned curves, the prior,
//!   `[day]`, `[priority]`, `days`, and day 0's own host-only facts — `at`,
//!   `state`, `posterior`, `sleep` — with the candidates when priorities are
//!   asked for (their facts are the host's, gap 113).
//!
//!   **`day0` is gone (step L9, gap 93 closed).** The host no longer hands in a
//!   histogram of today: the kernel derives day 0 from its own replay of the
//!   `log` section, and refuses `day0WithoutLog` when a capacity request
//!   carries none. What still crosses is only what the kernel cannot know —
//!   the instant the verb ran, `.tm/state.json`'s runtime facts, `--allow-home`,
//!   and the `[energy]` decimals the posterior and the sleep debt read. Today's
//!   sleep and energy reports do **not** cross.
//! * [`read_answer`] parses the response: `den` must be `capDen`, unit counts are
//!   digit strings read into `u128` (D17), and each grant becomes a [`Prio`]
//!   whose integer minutes are floors beside their exact values (D15).
//!
//! **The horizon (gap 98).** The kernel's lookahead is at most 3,660 days
//! (`Look.maxLookaheadDays`) and never runs past 9999-12-31. [`horizon`] clamps
//! the fork's `priority::lookahead_days` to both and says so on stderr when it
//! clamps (parity P30: a deadline past it sees the capacity of the days it has).

use std::collections::BTreeMap;

use chrono::{NaiveDate, Timelike};
use serde_json::{json, Map, Value};

use tm_core::capacity::{self, Exact, UnitCapacity, CAP_DEN};
use tm_core::config::Config;
use tm_core::energy::{weekday_key, Model};
use tm_core::model::Id;
use tm_core::priority::{self, Candidate, Prio, PrioClass};
use tm_core::store::Store;

use super::ctx::Ctx;
use super::kernel_bridge;
use super::kernel_log;
use super::out::CliError;
use super::tz_table;

/// `Look.maxLookaheadDays`: the most days one capacity request covers.
pub const MAX_LOOKAHEAD_DAYS: u32 = 3660;
/// The most decimal places a lounge weight may have (`capDen = 10^18`, D17).
pub const WEIGHT_PLACES: u32 = 18;
/// The most decimal places of a `[day]` ratio or a prior range key
/// (`den ∈ [1, 10^6]`, design §13.6's table).
pub const RATIO_PLACES: u32 = 6;
/// The most decimal places of a `[priority]` edge or the safety (`den ≤ 10^18`).
pub const PRIORITY_PLACES: u32 = 18;
/// The seven weekdays, Monday first.
const WEEK: [chrono::Weekday; 7] = [
    chrono::Weekday::Mon,
    chrono::Weekday::Tue,
    chrono::Weekday::Wed,
    chrono::Weekday::Thu,
    chrono::Weekday::Fri,
    chrono::Weekday::Sat,
    chrono::Weekday::Sun,
];
/// The two curves a future day reads (`Look.readEnergyIn`).
const LOCATIONS: [&str; 2] = ["lounge", "home"];

// ---------------------------------------------------------------------------
// decimal_pair
// ---------------------------------------------------------------------------

/// Why a double has no decimal pair the kernel can read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairErr {
    /// NaN or an infinity.
    NotFinite,
    /// Below zero.
    Negative,
    /// More decimal places than allowed (the count it has).
    TooManyPlaces(usize),
}

/// **A double as the decimal it is written as** (design §13.6): the shortest
/// round-trip `Display` text of `x`, read by [`written_pair`]. `-0.0` is `0/1`.
/// Refuses NaN, the infinities, negatives, and more than `max_places` decimal
/// places. The fallback for a value no file writes (a default of [`Config`]);
/// a value a file writes is sent as its file's text (D17, [`Written`]).
pub fn decimal_pair(x: f64, max_places: u32) -> Result<(String, String), PairErr> {
    written_pair(&format!("{x}"), max_places)
}

/// **A decimal literal as the exact rational it writes** (D10, D17): the text of
/// a TOML or JSON number (`0.1234567890123456789`, `+0.5`, `1e-3`, `1_000.5`,
/// `inf`, `nan`) as `(numerator, denominator)` digit strings, the denominator
/// `10^places` and `places` the literal's decimal places **of its value**
/// (trailing zeros after the point do not count: `0.500` is `5/10`). Nothing is
/// rounded: a literal with 19 places is refused as `TooManyPlaces(19)` even
/// where its nearest double has fewer. Refuses NaN and the infinities, a
/// negative value (`-0` and `-0.000` are `0/1`), text that is not a number
/// (`NotFinite`), and more than `max_places` places.
pub fn written_pair(text: &str, max_places: u32) -> Result<(String, String), PairErr> {
    let t: String = text.trim().chars().filter(|c| *c != '_').collect();
    let (neg, body) = match t.as_bytes().first() {
        Some(b'-') => (true, &t[1..]),
        Some(b'+') => (false, &t[1..]),
        _ => (false, t.as_str()),
    };
    let (mant, exp) = match body.find(['e', 'E']) {
        Some(i) => (&body[..i], Some(&body[i + 1..])),
        None => (body, None),
    };
    let (int, frac) = mant.split_once('.').unwrap_or((mant, ""));
    let digits_ok = |s: &str| s.bytes().all(|b| b.is_ascii_digit());
    if (int.is_empty() && frac.is_empty()) || !digits_ok(int) || !digits_ok(frac) {
        return Err(PairErr::NotFinite);
    }
    let exp: i64 = match exp {
        None => 0,
        Some(e) => {
            let unsigned = e.strip_prefix(['+', '-']).unwrap_or(e);
            if unsigned.is_empty() || !digits_ok(unsigned) {
                return Err(PairErr::NotFinite);
            }
            // Past 10^6 the exponent's size alone refuses (or no double holds it).
            if unsigned.len() > 6 {
                return if e.starts_with('-') { Err(PairErr::TooManyPlaces(usize::MAX)) } else { Err(PairErr::NotFinite) };
            }
            let n: i64 = unsigned.parse().unwrap_or(0);
            if e.starts_with('-') { -n } else { n }
        }
    };
    let mut digits = format!("{int}{frac}");
    let mut places = frac.len() as i64 - exp;
    if places < 0 {
        digits.push_str(&"0".repeat(places.unsigned_abs() as usize));
        places = 0;
    }
    // Trailing zeros after the point are not places of the value.
    while places > 0 && digits.ends_with('0') {
        digits.pop();
        places -= 1;
    }
    let num = digits.trim_start_matches('0');
    let num = if num.is_empty() { "0".to_string() } else { num.to_string() };
    let places = usize::try_from(places).unwrap_or(usize::MAX);
    if neg && num != "0" {
        return Err(PairErr::Negative);
    }
    if places > max_places as usize {
        return Err(PairErr::TooManyPlaces(places));
    }
    Ok((num, format!("1{}", "0".repeat(places))))
}

/// **A decimal literal as the exact rational it writes, with its sign** (stage 6 step L9, site
/// R10): the same reading as [`written_pair`], except that a negative value comes back as
/// `(true, num, den)` instead of [`PairErr::Negative`]. §8.5 fits `sleep_debt_shift` as a shrunken
/// **mean**, so the shift is genuinely signed, and the kernel rounds it half away from zero
/// (`Arith.roundAway`). `-0`, `-0.000` and `-0e3` are `(false, "0", "1")`, as they are unsigned.
pub fn signed_written_pair(text: &str, max_places: u32) -> Result<(bool, String, String), PairErr> {
    match written_pair(text, max_places) {
        Ok((n, d)) => Ok((false, n, d)),
        Err(PairErr::Negative) => {
            let t = text.trim();
            let (n, d) = written_pair(t.strip_prefix('-').unwrap_or(t), max_places)?;
            Ok((n != "0", n, d))
        }
        Err(e) => Err(e),
    }
}

/// `num / den > 1` for a pair of [`written_pair`] (digit strings, no leading zeros).
fn above_one(num: &str, den: &str) -> bool {
    num.len() > den.len() || (num.len() == den.len() && num > den)
}

/// A pair as the kernel's JSON naturals (`{"num": n, "den": d}`), for the
/// pairs whose parts are bounded well inside `u64` (`[day]`, `[priority]`, the
/// prior's keys).
fn nat_pair_of((n, d): (String, String)) -> Value {
    // `places ≤ 18`, so the denominator fits; a numerator past u64 is a value
    // no bound admits, and is sent as the largest natural so the kernel refuses it.
    json!({"num": n.parse::<u64>().unwrap_or(u64::MAX), "den": d.parse::<u64>().unwrap_or(u64::MAX)})
}

// ---------------------------------------------------------------------------
// The written text of every configured decimal (D10, D17)
// ---------------------------------------------------------------------------

/// **The configured decimals as their files write them.** `config.toml` and
/// `.tm/model.json` are read by serde into `f64`, which rounds a literal of more
/// than 17 significant digits to its nearest double; D10 forbids rounding and
/// D17 refuses a weight of more than 18 places, so the host re-reads each
/// decimal the capacity request carries as **the literal's text** (TOML spans,
/// JSON raw values) and [`written_pair`] reads that text. A key no file writes
/// is `None` and falls back to [`decimal_pair`] of its (default) double.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Written {
    /// `.tm/model.json`'s `p_lounge`, Monday first (the last entry for a weekday wins, as in [`Model`]).
    pub model_p: [Option<String>; 7],
    /// `config.toml`'s `expected.p_lounge`, Monday first.
    pub config_p: [Option<String>; 7],
    /// `day.window_hours`.
    pub window_hours: Option<String>,
    /// `day.budget_ratio`.
    pub budget_ratio: Option<String>,
    /// `priority.bins`, index for index (`None` when the file writes no `bins`).
    pub bins: Option<Vec<String>>,
    /// `priority.safety`.
    pub safety: Option<String>,
    /// Each `energy.prior.<curve>` range key as written: `(curve, key)`.
    pub prior_keys: Vec<(String, String)>,
    /// `energy.posterior_full_hours` (stage 6 L9, site R5).
    pub posterior_full_hours: Option<String>,
    /// `energy.posterior_zero_hours`.
    pub posterior_zero_hours: Option<String>,
    /// `energy.sleep_debt.under_hours` (site R10's comparison).
    pub sleep_under_hours: Option<String>,
    /// `energy.sleep_debt.shift` (site R10).
    pub sleep_shift: Option<String>,
    /// `.tm/model.json`'s fitted `sleep_debt_shift`, when the file writes one.
    pub model_sleep_shift: Option<String>,
}

/// The shadow of `config.toml` that keeps the literals (every other key ignored).
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct CfgText {
    expected: ExpectedText,
    day: DayText,
    priority: PriorityText,
    energy: EnergyText,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct ExpectedText {
    p_lounge: BTreeMap<String, toml::Spanned<toml::Value>>,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct DayText {
    window_hours: Option<toml::Spanned<toml::Value>>,
    budget_ratio: Option<toml::Spanned<toml::Value>>,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct PriorityText {
    bins: Option<Vec<toml::Spanned<toml::Value>>>,
    safety: Option<toml::Spanned<toml::Value>>,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct EnergyText {
    prior: BTreeMap<String, BTreeMap<String, toml::Value>>,
    posterior_full_hours: Option<toml::Spanned<toml::Value>>,
    posterior_zero_hours: Option<toml::Spanned<toml::Value>>,
    sleep_debt: SleepDebtText,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct SleepDebtText {
    under_hours: Option<toml::Spanned<toml::Value>>,
    shift: Option<toml::Spanned<toml::Value>>,
}

/// The shadow of `.tm/model.json`: `p_lounge`'s entries in file order, as raw text.
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct ModelText {
    #[serde(deserialize_with = "raw_entries")]
    p_lounge: Vec<(String, Box<serde_json::value::RawValue>)>,
    sleep_debt_shift: Option<Box<serde_json::value::RawValue>>,
}

/// A JSON object's entries in file order, each value's raw text.
fn raw_entries<'de, D: serde::Deserializer<'de>>(
    d: D,
) -> Result<Vec<(String, Box<serde_json::value::RawValue>)>, D::Error> {
    struct V;
    impl<'de> serde::de::Visitor<'de> for V {
        type Value = Vec<(String, Box<serde_json::value::RawValue>)>;
        fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.write_str("a table keyed by weekday")
        }
        fn visit_map<A: serde::de::MapAccess<'de>>(self, mut m: A) -> Result<Self::Value, A::Error> {
            let mut out = Vec::new();
            while let Some(e) = m.next_entry()? {
                out.push(e);
            }
            Ok(out)
        }
    }
    d.deserialize_map(V)
}

/// The weekday index (Monday 0) of a key [`Model`] and [`Config`] accept.
fn weekday_slot(key: &str) -> Option<usize> {
    tm_core::energy::parse_weekday_key(key).map(|wd| wd.num_days_from_monday() as usize)
}

impl Written {
    /// **Read the literals** of `config.toml` (`None` when absent) and
    /// `.tm/model.json` (`None` when absent): the texts `Ctx` parsed.
    pub fn parse(config: Option<&str>, model: Option<&str>) -> Result<Written, CliError> {
        let mut w = Written::default();
        if let Some(text) = config {
            let c: CfgText = toml::from_str(text)
                .map_err(|e| CliError::msg(format!("{CONFIG_FILE}: {e}")))?;
            let lit = |v: &toml::Spanned<toml::Value>| text.get(v.span()).unwrap_or_default().to_string();
            for (k, v) in &c.expected.p_lounge {
                if let Some(i) = weekday_slot(k) {
                    w.config_p[i] = Some(lit(v));
                }
            }
            w.window_hours = c.day.window_hours.as_ref().map(lit);
            w.budget_ratio = c.day.budget_ratio.as_ref().map(lit);
            w.bins = c.priority.bins.as_ref().map(|b| b.iter().map(lit).collect());
            w.safety = c.priority.safety.as_ref().map(lit);
            for (curve, keys) in &c.energy.prior {
                w.prior_keys.extend(keys.keys().map(|k| (curve.clone(), k.clone())));
            }
            w.posterior_full_hours = c.energy.posterior_full_hours.as_ref().map(lit);
            w.posterior_zero_hours = c.energy.posterior_zero_hours.as_ref().map(lit);
            w.sleep_under_hours = c.energy.sleep_debt.under_hours.as_ref().map(lit);
            w.sleep_shift = c.energy.sleep_debt.shift.as_ref().map(lit);
        }
        if let Some(text) = model {
            let m: ModelText = serde_json::from_str(text)
                .map_err(|e| CliError::msg(format!("{MODEL_FILE}: {e}")))?;
            for (k, v) in &m.p_lounge {
                if let Some(i) = weekday_slot(k) {
                    w.model_p[i] = Some(v.get().to_string());
                }
            }
            w.model_sleep_shift = m.sleep_debt_shift.as_ref().map(|v| v.get().to_string());
        }
        Ok(w)
    }

    /// The literals of the plan `ctx` loaded, read from its files now.
    pub fn of(ctx: &Ctx) -> Result<Written, CliError> {
        let read = |rel: &str| -> Result<Option<String>, CliError> {
            if ctx.store.exists(rel) {
                Ok(Some(ctx.store.read_text(rel)?))
            } else {
                Ok(None)
            }
        };
        Written::parse(read(tm_core::store::CONFIG_PATH)?.as_deref(), read(tm_core::store::MODEL_PATH)?.as_deref())
    }
}

/// **The text a configured value is sent as**: its file's literal when the file
/// writes one, else its double's shortest text. A literal whose nearest double is
/// not (within one step of) the value `Ctx` loaded means the file changed while
/// the verb ran, and the verb stops rather than send one value and plan another.
fn text_of(file: &str, key: &str, written: Option<&str>, x: f64) -> Result<String, CliError> {
    let Some(lit) = written else {
        return Ok(format!("{x}"));
    };
    let parsed: Option<f64> = lit.trim().replace('_', "").parse().ok();
    let same = parsed.is_some_and(|p| {
        (p.is_nan() && x.is_nan()) || p == x || p.to_bits().abs_diff(x.to_bits()) <= 1
    });
    if !same {
        return Err(CliError::msg(format!(
            "{file}: {key} = {lit} changed while tm was reading it; run the verb again"
        )));
    }
    Ok(lit.trim().to_string())
}

// ---------------------------------------------------------------------------
// The inputs, checked by file and key (§13.2, P26)
// ---------------------------------------------------------------------------

/// The plan-relative path of the learned model, as messages name it.
const MODEL_FILE: &str = ".tm/model.json";
/// The configuration, as messages name it.
const CONFIG_FILE: &str = "config.toml";

/// The failure of a configured value, by file and key, quoting its written text.
fn bad_value(file: &str, key: &str, text: &str, why: &str) -> CliError {
    CliError::msg(format!(
        "{file}: {key} = {text} {why}; tm cannot compute capacity or priorities until it is fixed \
         (kernel/README.md parity P26)"
    ))
}

/// A pair's refusal, in words.
fn pair_why(e: PairErr, places: u32) -> String {
    match e {
        PairErr::NotFinite => "is not a number".to_string(),
        PairErr::Negative => "is below zero".to_string(),
        PairErr::TooManyPlaces(usize::MAX) => format!("has too many decimal places (at most {places})"),
        PairErr::TooManyPlaces(n) => format!("has {n} decimal places (at most {places})"),
    }
}

/// **A lounge weight**, as written: a decimal of at most 18 places in `[0, 1]`.
/// Returns its pair.
fn check_weight(file: &str, key: &str, written: Option<&str>, x: f64) -> Result<(String, String), CliError> {
    let text = text_of(file, key, written, x)?;
    let (n, d) = match written_pair(&text, WEIGHT_PLACES) {
        Err(PairErr::Negative) => return Err(bad_value(file, key, &text, "is outside [0, 1]")),
        Err(e) => return Err(bad_value(file, key, &text, &pair_why(e, WEIGHT_PLACES))),
        Ok(p) => p,
    };
    if above_one(&n, &d) {
        return Err(bad_value(file, key, &text, "is outside [0, 1]"));
    }
    Ok((n, d))
}

/// A configured decimal of `config.toml` with at most `places` places, as written.
fn check_places(key: &str, written: Option<&str>, x: f64, places: u32) -> Result<(String, String), CliError> {
    let text = text_of(CONFIG_FILE, key, written, x)?;
    written_pair(&text, places).map_err(|e| bad_value(CONFIG_FILE, key, &text, &pair_why(e, places)))
}

/// Every configured decimal the request carries, as the pairs it sends.
struct Pairs {
    model_p: [Option<(String, String)>; 7],
    config_p: [(String, String); 7],
    window_hours: (String, String),
    budget_ratio: (String, String),
    bins: Vec<(String, String)>,
    safety: (String, String),
    /// Stage 6 L9, site R5: `energy.posterior_full_hours` and `posterior_zero_hours`.
    posterior_full: (String, String),
    posterior_zero: (String, String),
    /// Stage 6 L9, site R10: `energy.sleep_debt.under_hours`, and the two shifts (signed).
    sleep_under: (String, String),
    sleep_shift: (bool, String, String),
    model_sleep_shift: Option<(bool, String, String)>,
}

/// A **signed** configured decimal of a file, as written (site R10).
fn check_signed(file: &str, key: &str, written: Option<&str>, x: f64, places: u32)
    -> Result<(bool, String, String), CliError> {
    let text = text_of(file, key, written, x)?;
    signed_written_pair(&text, places).map_err(|e| bad_value(file, key, &text, &pair_why(e, places)))
}

/// The checks of [`check_inputs`], keeping the pairs they read.
fn pairs_of(cfg: &Config, model: &Model, written: &Written) -> Result<Pairs, CliError> {
    let mut model_p: [Option<(String, String)>; 7] = Default::default();
    for (wd, x) in model.p_lounge.iter() {
        let i = wd.num_days_from_monday() as usize;
        let key = format!("p_lounge.{}", weekday_key(wd));
        model_p[i] = Some(check_weight(MODEL_FILE, &key, written.model_p[i].as_deref(), *x)?);
    }
    let mut config_p: Vec<(String, String)> = Vec::with_capacity(7);
    for (i, wd) in WEEK.iter().enumerate() {
        let key = format!("expected.p_lounge.{}", weekday_key(*wd));
        config_p.push(check_weight(CONFIG_FILE, &key, written.config_p[i].as_deref(), *cfg.expected.p_lounge.get(*wd))?);
    }
    let config_p: [(String, String); 7] = config_p.try_into().unwrap_or_else(|_| Default::default());
    let window_hours = check_places("day.window_hours", written.window_hours.as_deref(), cfg.day.window_hours, RATIO_PLACES)?;
    let budget_ratio = check_places("day.budget_ratio", written.budget_ratio.as_deref(), cfg.day.budget_ratio, RATIO_PLACES)?;
    let mut bins = Vec::with_capacity(cfg.priority.bins.len());
    for (i, edge) in cfg.priority.bins.iter().enumerate() {
        let lit = written.bins.as_ref().and_then(|b| b.get(i)).map(String::as_str);
        bins.push(check_places(&format!("priority.bins[{i}]"), lit, *edge, PRIORITY_PLACES)?);
    }
    let safety = check_places("priority.safety", written.safety.as_deref(), cfg.priority.safety, PRIORITY_PLACES)?;
    // Stage 6 L9: the four `[energy]` decimals day 0 reads (design §13.5 says two; the repo has
    // four, and the model's fitted shift is a fifth).  The shift is signed: §8.5 fits it as a mean.
    let posterior_full = check_places(
        "energy.posterior_full_hours", written.posterior_full_hours.as_deref(), cfg.energy.posterior_full_hours, RATIO_PLACES)?;
    let posterior_zero = check_places(
        "energy.posterior_zero_hours", written.posterior_zero_hours.as_deref(), cfg.energy.posterior_zero_hours, RATIO_PLACES)?;
    let sleep_under = check_places(
        "energy.sleep_debt.under_hours", written.sleep_under_hours.as_deref(), cfg.energy.sleep_debt.under_hours, RATIO_PLACES)?;
    let sleep_shift = check_signed(
        CONFIG_FILE, "energy.sleep_debt.shift", written.sleep_shift.as_deref(), cfg.energy.sleep_debt.shift, RATIO_PLACES)?;
    let model_sleep_shift = match model.sleep_debt_shift {
        None => None,
        Some(x) => Some(check_signed(MODEL_FILE, "sleep_debt_shift", written.model_sleep_shift.as_deref(), x, RATIO_PLACES)?),
    };
    // The prior's range keys, as written.  At most 6 places and at most 48 hours,
    // a key has at most 8 significant digits, so its double's shortest text is
    // exactly the written decimal and the request may send the double's pair.
    for (curve, key) in &written.prior_keys {
        let name = format!("energy.prior.{curve}.\"{key}\"");
        let parts: Vec<&str> = match key.strip_suffix('+') {
            Some(a) => vec![a],
            None => key.split_once('-').map(|(a, b)| vec![a, b]).unwrap_or_default(),
        };
        for part in parts {
            written_pair(part, RATIO_PLACES).map_err(|e| bad_value(CONFIG_FILE, &name, part.trim(), &pair_why(e, RATIO_PLACES)))?;
        }
    }
    for (curve, steps) in &cfg.energy.prior {
        for step in &steps.0 {
            let key = format!("energy.prior.{curve}.\"{}\"", tm_core::config::StepFn::key(step));
            check_places(&key, None, step.from, RATIO_PLACES)?;
            if let Some(to) = step.to {
                check_places(&key, None, to, RATIO_PLACES)?;
            }
        }
    }
    Ok(Pairs { model_p, config_p, window_hours, budget_ratio, bins, safety,
        posterior_full, posterior_zero, sleep_under, sleep_shift, model_sleep_shift })
}

/// **Every configured decimal the capacity request carries, checked before it is
/// built, as its file writes it** (`written`; D10, D17): the model's and the
/// config's lounge weights (§13.2: every pair is sent, so both are checked),
/// `[day]`'s two ratios, `[priority]`'s edges and safety, and the prior's range
/// keys. The message names the file and the key and quotes the written text.
pub fn check_inputs(cfg: &Config, model: &Model, written: &Written) -> Result<(), CliError> {
    pairs_of(cfg, model, written).map(|_| ())
}

/// [`check_inputs`] over the plan `ctx` loaded, its literals read from its files.
pub fn check_plan(ctx: &Ctx) -> Result<(), CliError> {
    check_inputs(&ctx.cfg, &ctx.model, &Written::of(ctx)?)
}

/// **A capacity refusal a configured value causes, by file and key** (P26).
/// `None` for a refusal only a defect of this module can cause (the clock, the
/// zone table, the candidates' shape): those stay the kernel's named issue.
pub fn named_refusal(issue: &super::out::KernelIssue) -> Option<CliError> {
    let text = issue.message.strip_prefix("kernel refusal: ")?;
    let text = text.split(" — ").next()?;
    let (name, key) = text.split_once(' ').unwrap_or((text, ""));
    let weekday = |k: &str| k.rsplit('.').next().unwrap_or_default().to_string();
    let (file, what): (&str, String) = match name {
        "badWeight" | "weightAboveOne" | "weightPrecision" if key.starts_with("pLounge.model.") => {
            (MODEL_FILE, format!("p_lounge.{}", weekday(key)))
        }
        "badWeight" | "weightAboveOne" | "weightPrecision" => {
            (CONFIG_FILE, format!("expected.p_lounge.{}", weekday(key)))
        }
        "badClock" if key.starts_with("arrival.model.") => {
            (MODEL_FILE, format!("expected_arrival.{}", weekday(key)))
        }
        "badClock" if key == "day.windowCap" => (CONFIG_FILE, "day.window_cap".to_string()),
        "badClock" if key == "day.windDown" => (CONFIG_FILE, "day.wind_down".to_string()),
        "badClock" if key == "day.bed" => (CONFIG_FILE, "day.bed".to_string()),
        "badClock" => (CONFIG_FILE, format!("expected.arrival.{}", weekday(key))),
        "badCurve" => (MODEL_FILE, key.to_string()),
        "badPrior" | "badStep" | "badLevel" => (CONFIG_FILE, format!("energy.{key}")),
        "badCap" => (CONFIG_FILE, "location.home_max_ci".to_string()),
        "badDay" => {
            let k = match key {
                "blockMin" => "day.block_min",
                "breakMin" => "day.break_min",
                "breakAfterBlocks" => "day.break_after_blocks",
                "minLastBlockMin" => "day.min_last_block_min",
                "windowHours" => "day.window_hours",
                "budgetRatio" => "day.budget_ratio",
                _ => return None,
            };
            (CONFIG_FILE, k.to_string())
        }
        // Stage 6 step L9: day 0's four configured decimals, and the model's fitted shift.
        "badPosterior" => {
            let k = match key {
                "posterior.fullHours" => "energy.posterior_full_hours",
                "posterior.zeroHours" => "energy.posterior_zero_hours",
                _ => return None,
            };
            (CONFIG_FILE, k.to_string())
        }
        "badSleep" if key == "sleep.shiftModel" => (MODEL_FILE, "sleep_debt_shift".to_string()),
        "badSleep" => {
            let k = match key {
                "sleep.shiftConfig" => "energy.sleep_debt.shift",
                "sleep.underHours" => "energy.sleep_debt.under_hours",
                _ => return None,
            };
            (CONFIG_FILE, k.to_string())
        }
        "badBins" => (CONFIG_FILE, "priority.bins".to_string()),
        "badSafety" => (CONFIG_FILE, "priority.safety".to_string()),
        "badDefaultPriority" => (CONFIG_FILE, "priority.default_priority".to_string()),
        _ => return None,
    };
    Some(CliError::msg(format!(
        "{file}: {what} is outside what the kernel accepts ({text}); tm cannot compute capacity or \
         priorities until it is fixed (kernel/README.md parity P26)"
    )))
}

// ---------------------------------------------------------------------------
// The horizon (gap 98)
// ---------------------------------------------------------------------------

/// **The lookahead's length** for `want` days from `today`: at most
/// [`MAX_LOOKAHEAD_DAYS`], never past 9999-12-31, at least one. Returns the
/// days and whether it clamped.
pub fn horizon(today: NaiveDate, want: u32) -> (u32, bool) {
    let last = NaiveDate::from_ymd_opt(9999, 12, 31).unwrap_or(NaiveDate::MAX);
    let to_end = u32::try_from((last - today).num_days() + 1).unwrap_or(0);
    let days = want.min(MAX_LOOKAHEAD_DAYS).min(to_end).max(1);
    (days, days < want)
}

/// Say on stderr that the horizon clamped (not while the TUI owns the screen).
fn say_clamped(today: NaiveDate, want: u32, days: u32) {
    if kernel_bridge::capturing_kernel_stderr() {
        return;
    }
    let through = today + chrono::Duration::days(i64::from(days) - 1);
    eprintln!(
        "tm: the capacity lookahead is clamped to {days} days (through {through}; {want} were needed): a \
         deadline or floor after that sees only those days' capacity (kernel/README.md gap 98, parity P30)"
    );
}

// ---------------------------------------------------------------------------
// The request
// ---------------------------------------------------------------------------

/// `HH:MM`.
fn hhmm(t: chrono::NaiveTime) -> String {
    format!("{:02}:{:02}", t.hour(), t.minute())
}

/// The ranking half of a request: the candidates in the fork's service order,
/// and yesterday's priorities.
pub struct Ranked<'a> {
    /// The candidates, in `priority::collect_candidates` order.
    pub cands: &'a [Candidate],
    /// §7.4's comparison map (`Ctx::hysteresis_input`).
    pub yesterday: &'a BTreeMap<Id, u8>,
}

/// **The order the candidates are sent in**: the fork's `(effective_due,
/// own_order, index)` (`priority::compute`'s sort), so the kernel's stable sort
/// by due date serves a date's deadlines in the fork's order (P12 does not
/// bite). Undated candidates follow, in their own order.
fn send_order(cands: &[Candidate]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..cands.len()).collect();
    order.sort_by(|&a, &b| {
        let (ca, cb) = (&cands[a], &cands[b]);
        (ca.effective_due.is_none(), ca.effective_due, ca.own_order, a)
            .cmp(&(cb.effective_due.is_none(), cb.effective_due, cb.own_order, b))
    });
    order
}

/// One candidate record (Boundary.lean's `readCand`, `readFloor`).
fn cand_json(ctx: &Ctx, c: &Candidate, yesterday: &BTreeMap<Id, u8>) -> Value {
    let root_prio = ctx.tree.get(&ctx.tree.root(&c.id)).and_then(|r| r.priority);
    let floor = c.floor.as_ref().map(|r| {
        json!({
            "left": r.amount.as_minutes().saturating_sub(c.floor_done_min),
            "until": priority::period_range(r.per, ctx.today).1.to_string(),
        })
    });
    json!({
        "id": c.id.as_str(),
        "ci": c.ci,
        "rootPrio": root_prio,
        "remaining": c.remaining_min,
        "due": c.effective_due.map(|d| d.date_naive().to_string()),
        "window": c.window.is_some(),
        "wall": c.is_wall,
        "optional": c.is_optional,
        "overdue": c.overdue,
        "mandatory": c.mandatory,
        "hot": c.hot,
        "yesterday": yesterday.get(&c.id),
        "floor": floor,
    })
}

/// **The capacity request** for `days` days from today, with the candidates when
/// `ranked` is given. Returns the request and the order the candidates were
/// sent in.
pub fn request(ctx: &Ctx, allow_home: bool, days: u32, ranked: Option<&Ranked<'_>>) -> Result<(String, Vec<usize>), CliError> {
    // Every configured decimal as its file writes it (D10, D17): checked, then sent.
    let pairs = pairs_of(&ctx.cfg, &ctx.model, &Written::of(ctx)?)?;
    let cfg = &ctx.cfg;
    let model = &ctx.model;

    // The documents: the whole tree, as `kernel_bridge::apply` sends it.
    let mut docs = Vec::new();
    for rel in ctx.store.list_files()? {
        let text = ctx.store.read_text(&rel)?;
        docs.push(kernel_bridge::doc_json(&rel, &kernel_bridge::doc_lines(&text)));
    }

    let week_table = |f: &dyn Fn(chrono::Weekday) -> Option<Value>| -> Map<String, Value> {
        WEEK.iter().filter_map(|wd| f(*wd).map(|v| (weekday_key(*wd).to_string(), v))).collect()
    };
    let str_pair = |(n, d): &(String, String)| json!({"num": n, "den": d});
    let wd_slot = |wd: chrono::Weekday| wd.num_days_from_monday() as usize;
    let p_model = week_table(&|wd| pairs.model_p[wd_slot(wd)].as_ref().map(str_pair));
    let p_config = week_table(&|wd| Some(str_pair(&pairs.config_p[wd_slot(wd)])));
    let a_model = week_table(&|wd| model.expected_arrival.get(wd).map(|t| json!(hhmm(t.0))));
    let a_config = week_table(&|wd| Some(json!(hhmm(*cfg.expected.arrival.get(wd)))));
    let energy: Map<String, Value> = LOCATIONS
        .iter()
        .filter_map(|loc| model.energy.get(*loc).map(|c| (loc.to_string(), json!(c))))
        .collect();
    // The prior's keys: checked as written by `pairs_of`, and exactly their doubles' text.
    let pair = |x: f64, places: u32| decimal_pair(x, places).map(nat_pair_of).unwrap_or(Value::Null);
    let prior: Map<String, Value> = cfg
        .energy
        .prior
        .iter()
        .map(|(curve, steps)| {
            let steps: Vec<Value> = steps
                .0
                .iter()
                .map(|s| {
                    json!({"from": pair(s.from, RATIO_PLACES), "to": s.to.map(|t| pair(t, RATIO_PLACES)), "level": s.level})
                })
                .collect();
            (curve.clone(), Value::Array(steps))
        })
        .collect();
    // `Ctx::logged_wake` is `state.wake`, else the replay's `wake` of today.  The first disjunct
    // is `state.json`'s and the host sends it; the second is the kernel's own fact, and since D24
    // the kernel reads it off this call's replay rather than being told (`"log"`).  Sending the
    // clock when `state.wake` is set and `"log"` otherwise **is** the fork's precedence, written
    // down here because kernel/README.md gap 261 said it was written down nowhere.
    let wake = match ctx.state.wake {
        Some(t) => json!({"sec": t.num_seconds_from_midnight(), "ns": t.nanosecond()}),
        None => json!("log"),
    };
    let bins: Vec<Value> = pairs.bins.iter().cloned().map(nat_pair_of).collect();
    let signed_pair_of = |(neg, n, d): &(bool, String, String)| {
        let mut v = nat_pair_of((n.clone(), d.clone()));
        v["neg"] = json!(neg);
        v
    };

    let mut section = json!({
        "pLounge": {"model": p_model, "config": p_config},
        "arrival": {"model": a_model, "config": a_config},
        "wake": wake,
        "energy": energy,
        "prior": prior,
        "homeMaxCi": cfg.location.home_max_ci,
        "day": {
            "breakMin": cfg.day.break_min,
            "breakAfterBlocks": cfg.day.break_after_blocks,
            "minLastBlockMin": cfg.day.min_last_block_min,
            "windowHours": nat_pair_of(pairs.window_hours.clone()),
            "windowCap": hhmm(cfg.day.window_cap),
            "budgetRatio": nat_pair_of(pairs.budget_ratio.clone()),
            // Stage 6 step P2: `[day]`'s evening half.  §8.2 step 2 states "sleep and wind-down
            // define the hard end of the day" over exactly these two keys, and the kernel reads
            // `[day]` in one place (`Look.DayCfg`), so the whole section crosses -- sending half
            // of it was what let the planner keep a second copy.
            "windDown": hhmm(cfg.day.wind_down),
            "bed": hhmm(cfg.day.bed),
        },
        "priority": {
            "bins": bins,
            "safety": nat_pair_of(pairs.safety.clone()),
            "defaultPriority": cfg.priority.default_priority,
        },
        "days": days,
        // Stage 6 step L9 (gap 93): day 0 is the kernel's own.  What crosses is what only the host
        // knows — the instant the verb ran, `.tm/state.json`'s runtime facts and the CLI flag —
        // plus the `[energy]` decimals the posterior and the sleep debt read.  Today's sleep and
        // energy reports do **not** cross: the kernel reads them off the `log` section below.
        "at": tm_core::log::fmt_timestamp(&ctx.now_tz.fixed_offset()),
        "state": {
            "date": ctx.state.date.map(|d| d.to_string()),
            "window": ctx.state.window.map(|(f, t)| json!({"from": hhmm(f), "to": hhmm(t)})),
            "budget": ctx.state.budget,
            "arrival": ctx.state.arrival.map(hhmm),
            "loc": ctx.loc().as_str(),
            "allowHome": allow_home,
        },
        "posterior": {
            "fullHours": nat_pair_of(pairs.posterior_full.clone()),
            "zeroHours": nat_pair_of(pairs.posterior_zero.clone()),
        },
        "sleep": {
            "shiftModel": pairs.model_sleep_shift.as_ref().map(signed_pair_of),
            "shiftConfig": signed_pair_of(&pairs.sleep_shift),
            "underHours": nat_pair_of(pairs.sleep_under.clone()),
        },
    });
    let mut order = Vec::new();
    if let Some(r) = ranked {
        order = send_order(r.cands);
        let items: Vec<Value> = order.iter().map(|&i| cand_json(ctx, &r.cands[i], r.yesterday)).collect();
        section["candidates"] = json!({"hysteresis": cfg.priority.hysteresis, "items": items});
    }
    let cache = ctx.store.root().join(".tm/cache/replay");
    let tz_wire = tz_table::wire_for(Some(&cache), cfg.tz);
    // Stage 6 step L9: the `log` section day 0 is derived from (D24's seam).  The kernel answers
    // both sections in one call and `runCapZ` hands the log answer's replay to the capacity
    // reader; without it the kernel refuses `day0WithoutLog` rather than invent an empty day.
    let log = kernel_log::capacity_log_section(
        ctx.store.root(), &Ctx::log_bytes(&ctx.store)?, &tz_wire, kernel_log::day_of(ctx.today))
        .map_err(super::ctx::genesis_error)?;
    let rest = json!({
        "docs": docs,
        "now": ctx.today.to_string(),
        "blockMin": ctx.block_min(),
        "tz": tz_wire,
        "capacity": section,
    })
    .to_string();
    // The `log` section is **spliced as text**: its checkpoint is read in build order
    // (`Seal.readCkptFields`) and `serde_json::Value` is a `BTreeMap`, so parsing it here would
    // alphabetise those keys and the kernel would refuse `badCkpt v`.
    let request = format!("{{\"log\":{log},{}", &rest[1..]);
    Ok((request, order))
}

// ---------------------------------------------------------------------------
// The answer
// ---------------------------------------------------------------------------

/// What the kernel answered: the first `min(days, 7)` days in units, and one
/// priority per candidate in the candidates' own order.
#[derive(Clone, Debug, Default)]
pub struct Answer {
    /// The lookahead's first days (at most seven), exact units over [`CAP_DEN`].
    pub days: Vec<UnitCapacity>,
    /// One [`Prio`] per candidate, in `collect_candidates` order.
    pub prios: Vec<Prio>,
}

/// A response defect: loud, named, never a wrong answer.
fn defect(what: &str) -> CliError {
    CliError::Kernel(kernel_bridge::fault_issue(&format!("capacity response: {what}"), ""))
}

/// A digit string as `u128` (D17).
fn units_of(v: &Value, what: &str) -> Result<u128, CliError> {
    v.as_str()
        .filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
        .and_then(|s| s.parse::<u128>().ok())
        .ok_or_else(|| defect(&format!("{what} is not a digit string that fits u128")))
}

/// A `YYYY-MM-DD`.
fn date_of(v: &Value, what: &str) -> Result<NaiveDate, CliError> {
    v.as_str()
        .and_then(|s| NaiveDate::parse_from_str(s, "%Y-%m-%d").ok())
        .ok_or_else(|| defect(&format!("{what} is not a date")))
}

/// A small natural.
fn small(v: &Value, what: &str) -> Result<u8, CliError> {
    v.as_u64().and_then(|n| u8::try_from(n).ok()).ok_or_else(|| defect(&format!("{what} is not a small natural")))
}

/// Fork `PrioClass`'s serde name.
fn class_of(name: &str) -> Option<PrioClass> {
    Some(match name {
        "wall" => PrioClass::Wall,
        "hot" => PrioClass::Hot,
        "impossible" => PrioClass::Impossible,
        "overdue" => PrioClass::Overdue,
        "mandatory" => PrioClass::Mandatory,
        "hotflag" => PrioClass::HotFlag,
        "dated" => PrioClass::Dated,
        "floor" => PrioClass::Floor,
        "rank" => PrioClass::Rank,
        "optional" => PrioClass::Optional,
        _ => return None,
    })
}

/// **One grant as a [`Prio`]**: the kernel's class, `k`, `p`, raw `p`, need,
/// `until` and bin; availability, allocation and shortfall as floors beside their
/// exact values (D15). `u` is display only: the exact `need / avail` as a
/// double, held on the kernel's side of 1 (`u ≥ 1` exactly when the kernel's bin
/// is HOT), so [`Prio::is_hot`] agrees with the kernel.
fn prio_of(g: &Value) -> Result<Prio, CliError> {
    let id = g["id"].as_str().ok_or_else(|| defect("a grant has no id"))?;
    let class = g["class"].as_str().and_then(class_of).ok_or_else(|| defect("a grant's class is unknown"))?;
    let k = small(&g["k"], "k")?;
    let p = if g["p"].is_null() { None } else { Some(small(&g["p"], "p")?) };
    let raw = if g["rawP"].is_null() { None } else { Some(small(&g["rawP"], "rawP")?) };
    let need = g["need"].as_u64().and_then(|n| u32::try_from(n).ok()).ok_or_else(|| defect("need"))?;
    let until = if g["until"].is_null() { None } else { Some(date_of(&g["until"], "until")?) };
    let avail = units_of(&g["avail"], "avail")?;
    let allocation = units_of(&g["allocation"], "allocation")?;
    let shortfall = units_of(&g["shortfall"], "shortfall")?;
    let bin = if g["bin"].is_null() { None } else { Some(small(&g["bin"], "bin")?) };
    let passed = until.is_some() && class != PrioClass::Wall;
    let u = passed.then(|| {
        let exact = if avail == 0 {
            f64::INFINITY
        } else {
            (u128::from(need) * CAP_DEN) as f64 / avail as f64
        };
        match bin {
            None => exact.max(1.0),
            Some(_) => exact.min(1.0 - f64::EPSILON),
        }
    });
    Ok(Prio {
        id: Id::new(id),
        p: p.unwrap_or(0),
        class,
        k,
        u,
        bin,
        need_min: need,
        avail_min: capacity::floor_minutes(avail),
        avail_min_exact: Exact::of_units(avail),
        allocation_min: capacity::floor_minutes(allocation),
        allocation_min_exact: Exact::of_units(allocation),
        shortfall_min: capacity::floor_minutes(shortfall),
        shortfall_min_exact: Exact::of_units(shortfall),
        until,
        hysteresis_applied: p != raw,
        raw_p: raw.unwrap_or(0),
    })
}

/// **Read the response** of a request built by [`request`] with `order`.
pub fn read_answer(resp: &Value, order: &[usize], ranked: bool) -> Result<Answer, CliError> {
    let la = &resp["ok"]["lookahead"];
    if la["den"].as_str() != Some(CAP_DEN.to_string().as_str()) {
        return Err(defect("den is not capDen"));
    }
    let days = la["days"]
        .as_array()
        .ok_or_else(|| defect("no days"))?
        .iter()
        .map(|d| {
            let date = date_of(&d["day"], "a day")?;
            let at = d["numAt"].as_array().filter(|a| a.len() == 6).ok_or_else(|| defect("numAt"))?;
            let mut units = [0u128; 6];
            for (l, v) in at.iter().enumerate() {
                units[l] = units_of(v, "numAt")?;
            }
            Ok(UnitCapacity { date, units })
        })
        .collect::<Result<Vec<_>, CliError>>()?;
    let mut prios = Vec::new();
    if ranked {
        let grants = la["grants"].as_array().ok_or_else(|| defect("no grants"))?;
        if grants.len() != order.len() {
            return Err(defect("one grant per candidate"));
        }
        let mut slots: Vec<Option<Prio>> = vec![None; order.len()];
        for (g, &i) in grants.iter().zip(order) {
            slots[i] = Some(prio_of(g)?);
        }
        prios = slots.into_iter().map(|p| p.ok_or_else(|| defect("a candidate without a grant"))).collect::<Result<_, _>>()?;
    }
    Ok(Answer { days, prios })
}

/// **Ask the kernel** for `want` days of capacity from today (clamped by
/// [`horizon`]), and the priorities of `ranked` when given.
pub fn ask(ctx: &Ctx, allow_home: bool, want: u32, ranked: Option<&Ranked<'_>>) -> Result<Answer, CliError> {
    let (days, clamped) = horizon(ctx.today, want);
    if clamped {
        say_clamped(ctx.today, want, days);
    }
    let (req, order) = request(ctx, allow_home, days, ranked)?;
    let (resp, _) = match kernel_bridge::call_text(&req) {
        Ok(r) => r,
        Err(CliError::Kernel(issue)) => {
            return Err(named_refusal(&issue).unwrap_or(CliError::Kernel(issue)));
        }
        Err(e) => return Err(e),
    };
    let answer = read_answer(&resp, &order, ranked.is_some())?;
    if let Some(r) = ranked {
        for (c, p) in r.cands.iter().zip(&answer.prios) {
            if c.id != p.id {
                return Err(defect("a grant answers another candidate"));
            }
        }
    }
    Ok(answer)
}

/// **§7 and §8.4 from the kernel**: the priorities of `cands` over a lookahead
/// long enough for every deadline and floor (`priority::lookahead_days`), and
/// its first days.
pub fn rank(ctx: &Ctx, cands: &[Candidate], yesterday: &BTreeMap<Id, u8>, allow_home: bool) -> Result<Answer, CliError> {
    let want = priority::lookahead_days(cands, ctx.today);
    ask(ctx, allow_home, want, Some(&Ranked { cands, yesterday }))
}

/// **`tm plan --week`'s seven days** from the kernel.
pub fn week(ctx: &Ctx, allow_home: bool) -> Result<Vec<UnitCapacity>, CliError> {
    Ok(ask(ctx, allow_home, 7, None)?.days)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn a_decimal_is_its_text_not_its_binary_expansion() {
        assert_eq!(decimal_pair(0.9, 18), Ok(("9".into(), "10".into())));
        assert_eq!(decimal_pair(1.0, 18), Ok(("1".into(), "1".into())));
        assert_eq!(decimal_pair(0.0, 18), Ok(("0".into(), "1".into())));
        assert_eq!(decimal_pair(-0.0, 18), Ok(("0".into(), "1".into())));
        assert_eq!(decimal_pair(0.05, 18), Ok(("5".into(), "100".into())));
        assert_eq!(decimal_pair(7.33, 6), Ok(("733".into(), "100".into())));
        assert_eq!(decimal_pair(0.1 + 0.2, 18), Ok(("30000000000000004".into(), "100000000000000000".into())));
        assert_eq!(decimal_pair(f64::NAN, 18), Err(PairErr::NotFinite));
        assert_eq!(decimal_pair(f64::INFINITY, 18), Err(PairErr::NotFinite));
        assert_eq!(decimal_pair(-0.5, 18), Err(PairErr::Negative));
        assert_eq!(decimal_pair(1e-19, 18), Err(PairErr::TooManyPlaces(19)));
        assert_eq!(decimal_pair(0.3333333, 6), Err(PairErr::TooManyPlaces(7)));
    }

    #[test]
    fn the_horizon_is_clamped_to_the_kernels_cap_and_the_calendar() {
        let d = |s: &str| NaiveDate::parse_from_str(s, "%Y-%m-%d").unwrap();
        assert_eq!(horizon(d("2026-09-14"), 7), (7, false));
        assert_eq!(horizon(d("2026-09-14"), 3660), (3660, false));
        assert_eq!(horizon(d("2026-09-14"), 3661), (3660, true));
        assert_eq!(horizon(d("9999-12-30"), 7), (2, true));
    }

    #[test]
    fn a_weight_outside_its_domain_is_named_by_file_and_key() {
        let mut model = Model::default();
        model.p_lounge.set(chrono::Weekday::Mon, 1.2);
        let err = check_inputs(&Config::default(), &model, &Written::default()).unwrap_err().to_string();
        assert!(err.starts_with(".tm/model.json: p_lounge.Mon = 1.2 is outside [0, 1]"), "{err}");
        let mut cfg = Config::default();
        cfg.expected.p_lounge.tue = 0.1234567890123456789e-3;
        let err = check_inputs(&cfg, &Model::default(), &Written::default()).unwrap_err().to_string();
        assert!(err.starts_with("config.toml: expected.p_lounge.Tue = "), "{err}");
        assert!(err.contains("decimal places (at most 18)"), "{err}");
        let mut cfg = Config::default();
        cfg.expected.p_lounge.sun = f64::NAN;
        assert!(check_inputs(&cfg, &Model::default(), &Written::default()).unwrap_err().to_string().contains("expected.p_lounge.Sun = NaN is not a number"));
        assert!(check_inputs(&Config::default(), &Model::default(), &Written::default()).is_ok());
    }

    /// The audit's defect (W-3): a weight of 19 written places whose nearest
    /// double has 17 was sent as that double.  Read as written, it is refused.
    fn parse_both(config: &str, model: &str) -> (Config, Model, Written) {
        let cfg = Config::parse(config).unwrap();
        let m: Model = serde_json::from_str(model).unwrap();
        (cfg, m, Written::parse(Some(config), Some(model)).unwrap())
    }

    #[test]
    fn a_literal_is_its_exact_decimal() {
        let ok = |t: &str, n: &str, d: &str| assert_eq!(written_pair(t, 18), Ok((n.into(), d.into())), "{t}");
        ok("0.9", "9", "10");
        ok("0.500", "5", "10");
        ok("1", "1", "1");
        ok("+0.25", "25", "100");
        ok("-0", "0", "1");
        ok("-0.000", "0", "1");
        ok("1e-3", "1", "1000");
        ok("2.5E+2", "250", "1");
        ok("1_000.5", "10005", "10");
        ok("0.123456789012345678", "123456789012345678", "1000000000000000000");
        ok(" 0.75 ", "75", "100");
        let err = |t: &str, e: PairErr| assert_eq!(written_pair(t, 18), Err(e), "{t}");
        err("0.1234567890123456789", PairErr::TooManyPlaces(19));
        err("0.1000000000000000001", PairErr::TooManyPlaces(19));
        err("1e-19", PairErr::TooManyPlaces(19));
        err("1.5e-18", PairErr::TooManyPlaces(19));
        err("1e-9999999", PairErr::TooManyPlaces(usize::MAX));
        err("-0.5", PairErr::Negative);
        err("nan", PairErr::NotFinite);
        err("inf", PairErr::NotFinite);
        err("+inf", PairErr::NotFinite);
        err("", PairErr::NotFinite);
        err(".", PairErr::NotFinite);
        err("1e", PairErr::NotFinite);
        assert!(above_one("11", "10") && above_one("2", "1") && !above_one("1", "1") && !above_one("9", "10"));
    }

    #[test]
    fn a_weight_past_18_written_places_is_refused_though_its_double_is_shorter() {
        for v in ["0.1234567890123456789", "0.1000000000000000001"] {
            let (cfg, model, w) = parse_both("", &format!("{{\"p_lounge\": {{\"Tue\": {v}}}}}"));
            let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
            assert!(err.starts_with(&format!(".tm/model.json: p_lounge.Tue = {v} has 19 decimal places (at most 18)")), "{err}");
            let (cfg, model, w) = parse_both(&format!("[expected]\np_lounge = {{ Mon = 0.9, Tue = {v}, Wed = 0.9, Thu = 0.9, Fri = 0.8, Sat = 0.5, Sun = 0.4 }}\n"), "{}");
            let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
            assert!(err.starts_with(&format!("config.toml: expected.p_lounge.Tue = {v} has 19 decimal places (at most 18)")), "{err}");
        }
        // The last entry for a weekday wins, as in the model's own reading.
        let (cfg, model, w) = parse_both("", r#"{"p_lounge": {"Tue": 0.1000000000000000001, "Tuesday": 0.5}}"#);
        assert_eq!(w.model_p[1].as_deref(), Some("0.5"));
        assert!(check_inputs(&cfg, &model, &w).is_ok());
        // 18 written places are sent exactly, not as their nearest double.
        let (cfg, model, w) = parse_both("[expected.p_lounge]\nMon = 0\nTue = 0\nWed = 0.123456789012345678\nThu = 0\nFri = 0\nSat = 0\nSun = 0\n", "{}");
        let p = pairs_of(&cfg, &model, &w).unwrap();
        assert_eq!(p.config_p[2], ("123456789012345678".into(), "1000000000000000000".into()));
        // Every other configured decimal the request carries is read as written too.
        let (cfg, model, w) = parse_both("[priority]\nsafety = 1.3000000000000000001\n", "{}");
        let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
        assert!(err.starts_with("config.toml: priority.safety = 1.3000000000000000001 has 19 decimal places (at most 18)"), "{err}");
        let (cfg, model, w) = parse_both("[priority]\nbins = [0.5, 0.2500000000000000001, 0.1]\n", "{}");
        let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
        assert!(err.starts_with("config.toml: priority.bins[1] = 0.2500000000000000001 has 19 decimal places"), "{err}");
        let (cfg, model, w) = parse_both("[day]\nwindow_hours = 8.0000000000000000001\n", "{}");
        let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
        assert!(err.starts_with("config.toml: day.window_hours = 8.0000000000000000001 has 19 decimal places (at most 6)"), "{err}");
        let (cfg, model, w) = parse_both("[energy.prior.lounge]\n\"0-1.0000000000000000001\" = 4\n", "{}");
        let err = check_inputs(&cfg, &model, &w).unwrap_err().to_string();
        assert!(err.starts_with("config.toml: energy.prior.lounge.\"0-1.0000000000000000001\" = 1.0000000000000000001 has 19 decimal places (at most 6)"), "{err}");
        // A written value its double does not read is a file that changed under the verb.
        let cfg = Config::parse("[expected]\np_lounge = { Mon = 0, Tue = 0.5, Wed = 0, Thu = 0, Fri = 0, Sat = 0, Sun = 0 }\n").unwrap();
        let w = Written::parse(Some("[expected]\np_lounge = { Mon = 0, Tue = 0.25, Wed = 0, Thu = 0, Fri = 0, Sat = 0, Sun = 0 }\n"), None).unwrap();
        let err = check_inputs(&cfg, &Model::default(), &w).unwrap_err().to_string();
        assert!(err.contains("changed while tm was reading it"), "{err}");
        // Integers, signs, exponents and underscores are the literals TOML and JSON allow.
        let (cfg, model, w) = parse_both("[expected]\np_lounge = { Mon = 1, Tue = +0.5, Wed = 5e-1, Thu = 0.000_5, Fri = 0, Sat = 0, Sun = 0 }\n", r#"{"p_lounge": {"Fri": 2.5E-1}}"#);
        let p = pairs_of(&cfg, &model, &w).unwrap();
        assert_eq!(p.config_p[0], ("1".into(), "1".into()));
        assert_eq!(p.config_p[3], ("5".into(), "10000".into()));
        assert_eq!(p.model_p[4], Some(("25".into(), "100".into())));
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(4096))]

        /// **T15**: every finite non-negative double's pair is exactly the value
        /// its shortest text writes (the pair, rendered back as a decimal, parses to
        /// the same double), the denominator is `10^places` with `places` the text's,
        /// and a pair is refused exactly when the text has more places than allowed.
        #[test]
        fn t15_decimal_pair_is_the_shortest_text(bits in any::<u64>(), max in 0u32..=20) {
            let x = f64::from_bits(bits);
            match decimal_pair(x, max) {
                Err(PairErr::NotFinite) => prop_assert!(!x.is_finite()),
                Err(PairErr::Negative) => prop_assert!(x.is_finite() && x < 0.0),
                Err(PairErr::TooManyPlaces(n)) => {
                    prop_assert!(x.is_finite() && x >= 0.0 && n > max as usize);
                    prop_assert_eq!(format!("{x}").split_once('.').map_or(0, |(_, f)| f.len()), n);
                }
                Ok((num, den)) => {
                    prop_assert!(x.is_finite() && x >= 0.0);
                    let places = den.len() - 1;
                    prop_assert!(places <= max as usize);
                    prop_assert!(den.starts_with('1') && den[1..].bytes().all(|b| b == b'0'));
                    prop_assert!(num.bytes().all(|b| b.is_ascii_digit()) && (num == "0" || !num.starts_with('0')));
                    let padded = format!("{num:0>width$}", width = places + 1);
                    let (int, frac) = padded.split_at(padded.len() - places);
                    let back: f64 = format!("{int}.{frac}0").parse().unwrap();
                    prop_assert_eq!(back.to_bits(), x.abs().to_bits());
                }
            }
        }

        /// T15 over the lounge weights a hand edit writes: every decimal of at most
        /// 18 places in [0, 1] is sent as exactly itself.
        #[test]
        fn t15_a_written_weight_is_sent_as_written(n in 0u64..=1_000_000_000_000_000u64, places in 0u32..=15) {
            let den = 10u64.pow(places);
            let n = n % (den + 1);
            let text = if places == 0 { format!("{n}") } else { format!("{}.{:0>w$}", n / den, n % den, w = places as usize) };
            let x: f64 = text.parse().unwrap();
            let (num, d) = decimal_pair(x, WEIGHT_PLACES).unwrap();
            // The pair equals the written decimal as rationals.
            let (num, d) = (num.parse::<u128>().unwrap(), d.parse::<u128>().unwrap());
            prop_assert_eq!(num * u128::from(den), u128::from(n) * d);
        }
    }
}
