//! The remaining verbs of tm-spec-v1.md §13: `close`, `sync-cal`, `review`,
//! `model`, `log`, `undo`, `check`, `tui`.
//!
//! # API overview
//!
//! * [`close`] — §6.3's lifecycle through `horizon.rs`, and the `closed`
//!   stamp in `state.json` that stops the auto-close running it again.
//! * [`sync_cal`] / [`sync_calendar`] — §15: fetch the configured feeds and
//!   write `calendar/<week>.md` for the three weeks of the window, keeping
//!   `manual` lines. `tm arrive` calls [`sync_calendar`] directly.
//! * [`review`] — §11's monitors for a day, week or month, computed from the
//!   log replay; `--write` puts the text in the file's `tm:review` section.
//!   (`review.rs` is still a stub, so the numbers are assembled here from
//!   `log::Replay` and `energy.rs`; the JSON shape is the review's.)
//! * [`model`] — `--fit` rewrites `.tm/model.json` from the log, `--show`
//!   prints it, `--compare` scores the stored model against a fresh fit
//!   (§8.5).
//! * [`log`] — `--tail`, `--since`, `--item` over `.tm/log.jsonl`.
//! * [`undo`] — the compensating event and the reverted edit (§13).
//! * [`check`] — `check.rs`, exit code 2 when the tree has errors.
//! * [`tui`] — the §12 terminal UI, not built yet.

use chrono::{Duration, NaiveDate};
use serde::Serialize;

use tm_core::check as validate;
use tm_core::energy::{self, Model};
use tm_core::horizon::{self, CloseReport, REVIEW_BLOCK};
use tm_core::ics;
use tm_core::log::LogEntry;
use tm_core::model::{parse_date, Horizon, Id, IsoWeek, Period, YearMonth};
use tm_core::store::{Store, MODEL_PATH};
use tm_core::tree::Tree;

use super::ctx::{Ctx, Globals};
use super::items::id_gen;
use super::out::{emit, CliError};
use super::undo as undo_stack;

/// `tm close --json`.
#[derive(Debug, Serialize)]
pub struct CloseOut {
    /// `day`, `week` or `month`.
    pub period: String,
    /// The period closed (`2026-09-07`, `2026-W37`, `2026-09`).
    pub key: String,
    /// What the close did (§6.3).
    pub report: CloseReport,
}

/// `tm close <day|week|month> [--drop ^id …]` (§6.3).
pub fn close(g: &Globals, args: &super::CloseArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let period: Period = args.period.into();
    let rec = undo_stack::Recorder::start(&ctx, "close")?;
    let (key, report) = match period {
        Period::Day => {
            let date = match &args.date {
                Some(d) => parse_date(d)?,
                None => ctx.today,
            };
            let r = horizon::close_day(&ctx.hz(), date)?;
            if ctx.state.closed.day.is_none_or(|d| d < date) {
                ctx.state.closed.day = Some(date);
            }
            (date.to_string(), r)
        }
        Period::Week => {
            let week = match &args.date {
                Some(d) => IsoWeek::parse(d)?,
                None => IsoWeek::from_date(ctx.today),
            };
            let r = horizon::close_week(&ctx.hz(), week)?;
            if ctx.state.closed.week.is_none_or(|w| w < week) {
                ctx.state.closed.week = Some(week);
            }
            (week.to_string(), r)
        }
        Period::Month => {
            let month = match &args.date {
                Some(d) => YearMonth::parse(d)?,
                None => YearMonth::from_date(ctx.today),
            };
            let drops: Vec<Id> = args.drop.iter().map(|d| Ctx::key(d)).collect();
            let r = horizon::close_month(&ctx.hz(), month, &drops)?;
            if ctx.state.closed.month.is_none_or(|m| m < month) {
                ctx.state.closed.month = Some(month);
            }
            (month.to_string(), r)
        }
    };
    ctx.save_state()?;
    ctx.reload()?;
    rec.finish(&ctx, format!("close {} {key}", horizon::period_name(period)))?;

    let out = CloseOut {
        period: horizon::period_name(period).to_string(),
        key,
        report,
    };
    emit(
        ctx.json,
        || {
            format!(
                "closed {} {} · {} moved · {} demoted · {} reopened · {} dropped",
                out.period,
                out.key,
                out.report.moved.len(),
                out.report.demoted.len(),
                out.report.reopened.len(),
                out.report.dropped.len()
            )
        },
        &out,
    )?;
    Ok(0)
}

/// `tm sync-cal --json` (§15).
#[derive(Clone, Debug, Default, Serialize)]
pub struct SyncOut {
    /// The weeks written.
    pub weeks: Vec<String>,
    /// The files written.
    pub files: Vec<String>,
    /// How many occurrences were rendered.
    pub events: usize,
    /// Anything the feeds complained about.
    pub warnings: Vec<String>,
}

/// The feed reader `tm sync-cal` uses: HTTP for the Google Calendar private
/// addresses §15 names, and the local file for a `file://…` (or plain path)
/// `ics_urls` entry — an exported `.ics` on disk is a legitimate feed, and it
/// is what makes §17 M9's "sync against a fixture `.ics`" testable through
/// the CLI rather than only through `ics.rs`.
struct CliFetcher;

impl ics::Fetcher for CliFetcher {
    fn fetch(&self, url: &str) -> Result<String, ics::IcsError> {
        let local = url
            .strip_prefix("file://")
            .map(str::to_string)
            .or_else(|| (!url.contains("://")).then(|| url.to_string()));
        match local {
            Some(path) => std::fs::read_to_string(&path).map_err(|e| ics::IcsError::Body {
                url: url.to_string(),
                source: e,
            }),
            None => ics::fetch(url),
        }
    }
}

/// Fetch the feeds and write `calendar/<week>.md` (§15). Returns what
/// changed; a directory with no `ics_urls` is a no-op with a warning.
pub fn sync_calendar(ctx: &Ctx) -> Result<SyncOut, CliError> {
    if ctx.cfg.calendar.ics_urls.is_empty() {
        return Ok(SyncOut {
            warnings: vec!["no calendar feeds configured (config.toml [calendar] ics_urls)".into()],
            ..SyncOut::default()
        });
    }
    let week = IsoWeek::from_date(ctx.today);
    let mut existing = Vec::new();
    for w in ics::sync_weeks(week) {
        let path = Horizon::Calendar(w).path();
        if ctx.store.exists(&path) {
            existing.push((w, ctx.store.read_text(&path)?));
        }
    }
    let result = ics::sync_report(&CliFetcher, &ctx.cfg, ctx.today, &existing)?;
    let mut out = SyncOut {
        events: result.events.len(),
        warnings: result.warnings.clone(),
        ..SyncOut::default()
    };
    for (w, text) in &result.files {
        let path = Horizon::Calendar(*w).path();
        let same = existing
            .iter()
            .any(|(ew, et)| ew == w && et == text);
        if !same {
            ctx.store.write_file(&path, text)?;
            out.files.push(path);
        }
        out.weeks.push(w.to_string());
    }
    Ok(out)
}

/// `tm sync-cal`.
pub fn sync_cal(g: &Globals) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let rec = undo_stack::Recorder::start(&ctx, "sync-cal")?;
    let out = sync_calendar(&ctx)?;
    ctx.reload()?;
    rec.finish(&ctx, "sync-cal")?;
    emit(
        ctx.json,
        || {
            let mut s = format!("{} events · {} files written", out.events, out.files.len());
            for w in &out.warnings {
                s.push_str(&format!("\n! {w}"));
            }
            s
        },
        &out,
    )?;
    Ok(0)
}

/// One day's numbers in a review (§11, §12.4).
#[derive(Clone, Debug, Default, Serialize)]
pub struct ReviewDay {
    /// The date.
    pub date: String,
    /// Blocks done.
    pub blocks: u32,
    /// Block minutes.
    pub block_min: u32,
    /// Σ block_min × ci / 5 (§11).
    pub load: f64,
    /// Minutes attributed `leak`.
    pub leak_min: u32,
    /// Minutes lost to interruptions.
    pub lost_min: u32,
    /// Items finished.
    pub done: Vec<String>,
}

/// `tm review --json`.
#[derive(Clone, Debug, Serialize)]
pub struct ReviewOut {
    /// `day`, `week` or `month`.
    pub period: String,
    /// The period reviewed.
    pub key: String,
    /// Per-day numbers (one row for a day review).
    pub days: Vec<ReviewDay>,
    /// Blocks done over the period.
    pub blocks: u32,
    /// Block minutes over the period.
    pub block_min: u32,
    /// Leak minutes over the period (§11's ledger).
    pub leak_min: u32,
    /// Lost minutes over the period.
    pub lost_min: u32,
    /// Energy calibration: MAE and bias of the logged predictions (§11).
    pub energy_mae: Option<f64>,
    /// Bias (mean `rep − pred`).
    pub energy_bias: Option<f64>,
    /// Estimate calibration per tag (§11).
    pub estimates: Vec<TagOut>,
    /// Items with ≥ 2 demotion stamps (§11's churn; month review).
    pub churn: Vec<String>,
    /// The file `--write` wrote to.
    pub wrote: Option<String>,
}

/// One tag's estimate calibration.
#[derive(Clone, Debug, Serialize)]
pub struct TagOut {
    /// The tag.
    pub tag: String,
    /// How many observations.
    pub n: usize,
    /// The learned multiplier.
    pub multiplier: f64,
}

/// The dates a review covers.
fn review_range(ctx: &Ctx, period: Period, date: Option<&str>) -> Result<(String, Vec<NaiveDate>), CliError> {
    Ok(match period {
        Period::Day => {
            let d = match date {
                Some(s) => parse_date(s)?,
                None => ctx.today,
            };
            (d.to_string(), vec![d])
        }
        Period::Week => {
            let w = match date {
                Some(s) => IsoWeek::parse(s)?,
                None => IsoWeek::from_date(ctx.today),
            };
            (w.to_string(), w.dates().to_vec())
        }
        Period::Month => {
            let m = match date {
                Some(s) => YearMonth::parse(s)?,
                None => YearMonth::from_date(ctx.today),
            };
            let (from, to) = m.range();
            let mut days = Vec::new();
            let mut d = from;
            while d <= to {
                days.push(d);
                d += Duration::days(1);
            }
            (m.to_string(), days)
        }
    })
}

/// `tm review <day|week|month> [--write] [--date …]` (§11, §12.4).
pub fn review(g: &Globals, args: &super::ReviewArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let period: Period = args.period.into();
    let (key, dates) = review_range(&ctx, period, args.date.as_deref())?;

    let mut days = Vec::new();
    for date in &dates {
        let Some(d) = ctx.replay.day(*date) else {
            continue;
        };
        days.push(ReviewDay {
            date: date.to_string(),
            blocks: d.blocks_done,
            block_min: d.block_min,
            load: (d.load * 100.0).round() / 100.0,
            leak_min: d.leak_min,
            lost_min: d.lost_min,
            done: d.done.clone(),
        });
    }
    let obs: Vec<_> = dates
        .iter()
        .flat_map(|d| ctx.replay.energy_on(*d).cloned())
        .collect();
    let cal = energy::calibration(&ctx.cfg, &obs);
    let durations: Vec<_> = dates
        .iter()
        .flat_map(|d| ctx.replay.durations_on(*d).cloned())
        .collect();
    let estimates: Vec<TagOut> = energy::estimate_calibration(&ctx.cfg, &durations, ctx.today)
        .into_iter()
        .map(|t| TagOut {
            tag: t.tag,
            n: t.n,
            multiplier: (t.multiplier * 100.0).round() / 100.0,
        })
        .collect();
    let churn = if period == Period::Month {
        horizon::churn(&ctx.tree, 2)
            .into_iter()
            .map(|(id, _)| id.to_string())
            .collect()
    } else {
        Vec::new()
    };

    let mut out = ReviewOut {
        period: horizon::period_name(period).to_string(),
        key: key.clone(),
        blocks: days.iter().map(|d| d.blocks).sum(),
        block_min: days.iter().map(|d| d.block_min).sum(),
        leak_min: days.iter().map(|d| d.leak_min).sum(),
        lost_min: days.iter().map(|d| d.lost_min).sum(),
        days,
        energy_mae: (cal.n > 0).then(|| (cal.mae * 100.0).round() / 100.0),
        energy_bias: (cal.n > 0).then(|| (cal.bias * 100.0).round() / 100.0),
        estimates,
        churn,
        wrote: None,
    };

    let text = review_text(&out);
    if args.write {
        let path = match period {
            Period::Day => Horizon::Day(dates[0]).path(),
            Period::Week => Horizon::Week(IsoWeek::parse(&key)?).path(),
            Period::Month => Horizon::Month(YearMonth::parse(&key)?).path(),
        };
        let rec = undo_stack::Recorder::start(&ctx, "review")?;
        ctx.store.replace_generated(&path, REVIEW_BLOCK, &text)?;
        out.wrote = Some(path.clone());
        ctx.reload()?;
        rec.finish(&ctx, format!("review {} {key}", out.period))?;
    }

    emit(ctx.json, || text.clone(), &out)?;
    Ok(0)
}

/// The §12.4 review, as text.
fn review_text(r: &ReviewOut) -> String {
    let mut s = format!(
        "{} {} · {} blocks · {}m · leak {}m · lost {}m",
        r.period, r.key, r.blocks, r.block_min, r.leak_min, r.lost_min
    );
    if let (Some(mae), Some(bias)) = (r.energy_mae, r.energy_bias) {
        s.push_str(&format!("\nenergy    MAE {mae}  bias {bias}"));
    }
    if !r.estimates.is_empty() {
        let tags: Vec<String> = r
            .estimates
            .iter()
            .map(|t| format!("{} ×{} (n={})", t.tag, t.multiplier, t.n))
            .collect();
        s.push_str(&format!("\nestimates {}", tags.join("   ")));
    }
    for d in &r.days {
        if r.days.len() > 1 {
            s.push_str(&format!(
                "\n{}  {} blocks  {}m  load {}",
                d.date, d.blocks, d.block_min, d.load
            ));
        } else if !d.done.is_empty() {
            s.push_str(&format!("\ndone      {}", d.done.join(" ")));
        }
    }
    if !r.churn.is_empty() {
        s.push_str(&format!("\nchurn     {}", r.churn.join(" ")));
    }
    s
}

/// `tm model --json`.
#[derive(Debug, Serialize)]
pub struct ModelOut {
    /// What ran: `show`, `fit` or `compare`.
    pub action: String,
    /// The model afterwards.
    pub model: Model,
    /// `--fit`: the file written.
    pub wrote: Option<String>,
    /// `--compare`: how the stored model and a fresh fit score (§8.5).
    pub comparison: Option<CompareOut>,
}

/// `tm model --compare` (§11's energy calibration).
#[derive(Debug, Serialize)]
pub struct CompareOut {
    /// Observations scored.
    pub n: usize,
    /// MAE of the stored model.
    pub mae_a: f64,
    /// MAE of the fresh fit.
    pub mae_b: f64,
    /// Bias of the stored model.
    pub bias_a: f64,
    /// Bias of the fresh fit.
    pub bias_b: f64,
    /// Whether the fresh fit is better.
    pub b_is_better: bool,
}

/// `tm model --fit | --show | --compare` (§8.5).
pub fn model(g: &Globals, args: &super::ModelArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    if args.fit {
        let rec = undo_stack::Recorder::start(&ctx, "model")?;
        let fitted = energy::fit_replay(&ctx.cfg, &ctx.replay, ctx.today);
        ctx.store.write_file(MODEL_PATH, &fitted.to_json())?;
        ctx.model = fitted.clone();
        ctx.reload()?;
        rec.finish(&ctx, "model --fit")?;
        let out = ModelOut {
            action: "fit".to_string(),
            model: fitted,
            wrote: Some(MODEL_PATH.to_string()),
            comparison: None,
        };
        emit(
            ctx.json,
            || format!("fitted from {} observations", out.model.n_obs),
            &out,
        )?;
        return Ok(0);
    }
    if args.compare {
        let fresh = energy::fit_replay(&ctx.cfg, &ctx.replay, ctx.today);
        let c = energy::compare(&ctx.cfg, &ctx.model, &fresh, &ctx.replay.energy);
        let out = ModelOut {
            action: "compare".to_string(),
            model: ctx.model.clone(),
            wrote: None,
            comparison: Some(CompareOut {
                n: c.n,
                mae_a: (c.mae_a * 1000.0).round() / 1000.0,
                mae_b: (c.mae_b * 1000.0).round() / 1000.0,
                bias_a: (c.bias_a * 1000.0).round() / 1000.0,
                bias_b: (c.bias_b * 1000.0).round() / 1000.0,
                b_is_better: c.b_is_better(),
            }),
        };
        emit(
            ctx.json,
            || {
                let c = out.comparison.as_ref().expect("a comparison");
                format!(
                    "n {} · stored MAE {} bias {} · fresh MAE {} bias {} · {}",
                    c.n,
                    c.mae_a,
                    c.bias_a,
                    c.mae_b,
                    c.bias_b,
                    if c.b_is_better { "fresh wins" } else { "stored wins" }
                )
            },
            &out,
        )?;
        return Ok(0);
    }
    let out = ModelOut {
        action: "show".to_string(),
        model: ctx.model.clone(),
        wrote: None,
        comparison: None,
    };
    emit(ctx.json, || energy::show(&out.model), &out)?;
    Ok(0)
}

/// `tm log --json`.
#[derive(Debug, Serialize)]
pub struct LogOut {
    /// How many entries the log holds.
    pub total: usize,
    /// The selected entries, oldest first.
    pub entries: Vec<LogEntry>,
}

/// `tm log --tail 20 | --since 7d | --item ^id` (§10.1).
pub fn log(g: &Globals, args: &super::LogArgs) -> Result<i32, CliError> {
    let ctx = Ctx::load(g, false)?;
    let total = ctx.log.entries.len();
    let mut entries: Vec<LogEntry> = match &args.item {
        Some(id) => {
            let key = Ctx::key(id);
            ctx.log.iter_item(key.as_str()).cloned().collect()
        }
        None => ctx.log.entries.clone(),
    };
    if let Some(since) = &args.since {
        let from = parse_since(since, ctx.today)?;
        let days = ctx.log.day_index(ctx.cfg.tz);
        entries.retain(|e| days.day_of(e.t) >= from);
    }
    let tail = args.tail.unwrap_or(if args.since.is_some() || args.item.is_some() {
        entries.len()
    } else {
        20
    });
    if entries.len() > tail {
        entries.drain(0..entries.len() - tail);
    }
    let out = LogOut { total, entries };
    emit(
        ctx.json,
        || {
            out.entries
                .iter()
                .map(|e| {
                    let mut v = serde_json::to_value(e).unwrap_or(serde_json::Value::Null);
                    let obj = v.as_object_mut();
                    let rest = obj
                        .map(|m| {
                            m.remove("t");
                            m.remove("ev");
                            m.iter()
                                .map(|(k, v)| format!("{k}={v}"))
                                .collect::<Vec<_>>()
                                .join(" ")
                        })
                        .unwrap_or_default();
                    format!(
                        "{} {} {}",
                        e.t.format("%Y-%m-%d %H:%M"),
                        e.ev.name(),
                        rest
                    )
                })
                .collect::<Vec<_>>()
                .join("\n")
        },
        &out,
    )?;
    Ok(0)
}

/// `--since 7d` or `--since 2026-09-01`.
fn parse_since(arg: &str, today: NaiveDate) -> Result<NaiveDate, CliError> {
    if let Some(days) = arg.strip_suffix('d').and_then(|n| n.parse::<i64>().ok()) {
        return Ok(today - Duration::days(days));
    }
    if let Some(weeks) = arg.strip_suffix('w').and_then(|n| n.parse::<i64>().ok()) {
        return Ok(today - Duration::weeks(weeks));
    }
    Ok(parse_date(arg)?)
}

/// `tm undo` (§13).
pub fn undo(g: &Globals) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, false)?;
    let out = undo_stack::undo(&mut ctx)?;
    emit(
        ctx.json,
        || {
            format!(
                "undid {} ({}) · {} file(s) restored · {} left",
                out.verb,
                out.summary,
                out.files.len(),
                out.remaining
            )
        },
        &out,
    )?;
    Ok(0)
}

/// `tm check --json`.
#[derive(Debug, Serialize)]
pub struct CheckOut {
    /// The problems found, file order (§1.3).
    pub problems: Vec<validate::CheckProblem>,
    /// `--fix-ids`: the ids assigned, as `(file, line, id)`.
    pub fixed: Vec<(String, usize, Id)>,
    /// `no problems` or `2 errors, 3 warnings`.
    pub summary: String,
    /// The exit code (§13: 2 when anything is an error).
    pub exit_code: i32,
}

/// `tm check [--fix-ids]` (§1.3, §13).
pub fn check(g: &Globals, args: &super::CheckArgs) -> Result<i32, CliError> {
    let ctx = Ctx::load(g, false)?;
    let mut files = ctx.files.files.clone();
    let fixed = if args.fix_ids {
        let mut gen = id_gen(&ctx, "fix-ids");
        validate::fix_ids(&ctx.store, &mut files, &mut gen)?
    } else {
        Vec::new()
    };
    let tree = Tree::build(&files, &ctx.cfg);
    let problems = validate::check(&files, &tree, &ctx.cfg);
    let code = validate::exit_code(&problems);
    let out = CheckOut {
        summary: validate::summary(&problems),
        problems,
        fixed,
        exit_code: code,
    };
    emit(
        ctx.json,
        || {
            let mut s = String::new();
            for (file, line, id) in &out.fixed {
                s.push_str(&format!("{file}:{line}: assigned {}\n", id.token()));
            }
            for p in &out.problems {
                s.push_str(&format!("{p}\n"));
            }
            s.push_str(&out.summary);
            s
        },
        &out,
    )?;
    Ok(code)
}

/// `tm tui` — §12's terminal UI; a later milestone fills it in.
pub fn tui() -> Result<i32, CliError> {
    eprintln!("tm tui: not built yet");
    Ok(1)
}
