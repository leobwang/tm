//! The remaining verbs of tm-spec-v1.md §13: `close`, `sync-cal`, `review`,
//! `model`, `log`, `undo`, `check`, `tui`.
//!
//! # API overview
//!
//! * [`close`] — §6.3's lifecycle through the kernel ([`closing`], stage 4
//!   step 6), and the `closed` stamp in `state.json` that stops the
//!   automatic close running it again.
//! * [`sync_cal`] / [`sync_calendar`] — §15: fetch the configured feeds and
//!   write `calendar/<week>.md` for the three weeks of the window, keeping
//!   `manual` lines. `tm arrive` calls [`sync_calendar`] directly.
//! * [`review`] — §12.4's day, week and month reviews: every §11 monitor,
//!   computed by `tm_core::review` and rendered by its `render_day` /
//!   `render_week` / `render_month`, so the CLI, the §12.4 screen and §17
//!   M8's hand-computed values are one set of numbers. `--write` puts the
//!   same text in the file's `tm:review` section. The plan-dependent
//!   monitors (adherence, the under-used count, the optional quota) need
//!   today's plan and `.tm/arrival_plan.json`, so they are filled in only for
//!   today ([`day_extras`]).
//! * [`model`] — `--fit` rewrites `.tm/model.json` from the log, `--show`
//!   prints it, `--compare` scores the stored model against a fresh fit
//!   (§8.5).
//! * [`log`] — `--tail`, `--since`, `--item` over `.tm/log.jsonl`.
//! * [`undo`] — the compensating event and the reverted edit (§13).
//! * [`check`] — `check.rs`, exit code 2 when the tree has errors.
//! * [`tui`] — the §12 terminal UI (all five screens).

use chrono::{Duration, NaiveDate};
use serde::Serialize;

use tm_core::check as validate;
use tm_core::energy::{self, Model};
use tm_core::horizon::{self, REVIEW_BLOCK};
use tm_core::ics;
use tm_core::log::{LogEntry, Replay, ViewRow};
use tm_core::priority;
use tm_core::review as core_review;
use tm_core::model::{parse_date, Horizon, Id, IsoWeek, Period, YearMonth};
use tm_core::store::{Store, MODEL_PATH};
use tm_core::tree::Tree;

use super::closing;
use super::ctx::{Ctx, Globals, ReplayScope};
use super::kernel_bridge::Grain;
use super::ghost;
use super::items::id_gen;
use super::out::{emit, CliError};
use super::planning;
use super::undo as undo_stack;

/// `tm close --json`.
#[derive(Debug, Serialize)]
pub struct CloseOut {
    /// `day`, `week` or `month`.
    pub period: String,
    /// The last period of that grain that has ended (`2026-09-06`,
    /// `2026-W36`, `2026-08`): the close takes every ended period of its
    /// grain, whatever its age, so this is the one it closed *through*.
    pub key: String,
    /// What the close did: the kernel's per-item list (D3).
    pub report: closing::ReportOut,
}

/// `tm close <day|week|month> [--drop ^id …]` (§6.3), kernel-backed (stage 4
/// step 6).
///
/// One request through the kernel bridge: the month's `--drop` ids first,
/// then `close <grain>` at the CLI's `now`, which takes every region of that
/// grain that has ended and files each line into the week or month
/// containing now (the owner's D1). The human line and `--json` are both
/// read off the kernel's report; `state.closed` is advanced and the log
/// written from it ([`closing::run`]). A refusal is named, writes nothing,
/// and stamps nothing closed.
///
/// `tm close` loads without the automatic close ([`Ctx::load_for_close`]):
/// the verb's own request is the close, so what it prints is what it did.
pub fn close(g: &Globals, args: &super::CloseArgs) -> Result<i32, CliError> {
    let period = args.period();
    // §6.3 gives `--drop` to the month close alone: it is the exception to
    // "moves them to the next month file". A day close moves pinned items to
    // the week and a week close demotes into the month, neither of which the
    // flag says anything about — so accepting it there would discard what the
    // user asked for without a word. `tm close day --help` does not offer the
    // flag (`CloseNoDropArgs` hides it); this catches it when it is typed
    // anyway, and says where it belongs.
    if !args.drops().is_empty() && period != Period::Month {
        return Err(CliError::msg(format!(
            "--drop belongs to `tm close month` (§6.3); `tm close {}` has no drop list — \
             use `tm drop ^id`",
            horizon::period_name(period)
        )));
    }
    // §11.1: `tm close day <date>` names an old date; every other close is Hot.
    let day_date = match period {
        Period::Day => args.date().and_then(|d| tm_core::model::parse_date(d).ok()),
        _ => None,
    };
    let mut ctx = Ctx::load_for_close(g, |_, _| match day_date {
        Some(d) => ReplayScope::Dates { from: d, to: d },
        None => ReplayScope::Hot,
    })?;
    let grain = Grain::of_period(period);
    if let Some(date) = args.date() {
        closing::check_date(grain, date, ctx.today)?;
    }
    // A `--drop` names an item with a line in a month file — an unfinished
    // outcome, or a record under `# Demoted` whose live line may be in a
    // week (§4.3's own `^m2`; the kernel's `drop` settles the live line, as
    // the fork-point close did) — and nothing else: anything else is refused
    // before the kernel is called, never dropped on the floor or elsewhere.
    let mut drops: Vec<Id> = Vec::new();
    for arg in args.drops() {
        let id = Ctx::key(arg);
        let item = ctx.item(&id)?;
        let in_a_month = ctx.files.files.iter().any(|f| {
            matches!(Horizon::from_path(&f.path), Some(Horizon::Month(_)))
                && f.items().any(|i| Tree::key_of(i) == id)
        });
        if !in_a_month {
            return Err(CliError::msg(format!(
                "{} has no line in a month file (it is in {}): `tm close month --drop` drops a \
                 month's outcomes and carried records — use `tm drop {}`",
                id.token(),
                item.horizon.path(),
                id.token()
            )));
        }
        drops.push(id);
    }
    let key = closing::last_ended_key(grain, ctx.today);
    let rec = undo_stack::Recorder::start(&ctx, "close")?;
    let report = closing::run_explained(&mut ctx, closing::Which::One(grain), &drops)?;
    ctx.reload()?;
    rec.finish(&ctx, format!("close {} {key}", grain.name()))?;

    let out = CloseOut {
        period: grain.name().to_string(),
        key,
        report,
    };
    let running = closing::running_key(grain, ctx.today);
    emit(
        ctx.json,
        || {
            let line = out.report.line(&out.period, &out.key);
            // `tm close day` at night used to close the day you were in; a
            // close now takes only periods that have ended, so an empty
            // close says which period it could not take, and when that one
            // will be closed.
            if out.report.closes.is_empty() {
                format!(
                    "{line}\n{} {running} is still running; it is closed on the first command after it ends",
                    out.period
                )
            } else {
                line
            }
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

/// `tm review --json`: the §12.4 review itself, whichever period was asked
/// for. Untagged, so the JSON is the [`DayReview`]/[`WeekReview`]/
/// [`MonthReview`] object §14's `/review-day` and `/review-week` skills read;
/// `period` beside it says which.
#[derive(Clone, Debug, Serialize)]
#[serde(untagged)]
pub enum ReviewBody {
    /// §12.4's day review.
    Day(Box<core_review::DayReview>),
    /// §12.4's week review.
    Week(Box<core_review::WeekReview>),
    /// §12.4's month review.
    Month(Box<core_review::MonthReview>),
}

/// `tm review --json`.
#[derive(Clone, Debug, Serialize)]
pub struct ReviewOut {
    /// `day`, `week` or `month`.
    pub period: String,
    /// The period reviewed (`2026-09-07`, `2026-W37`, `2026-09`).
    pub key: String,
    /// Every §11 monitor with a surface on that period.
    pub review: ReviewBody,
    /// The file `--write` wrote to.
    pub wrote: Option<String>,
}

/// The plan-dependent half of §11's day monitors (adherence, the under-used
/// count, tomorrow's first candidates, the optional quota, the budget).
///
/// Only *today* has a plan to read them from: §12.1's ghost row is
/// `.tm/arrival_plan.json`, which is written at `tm arrive` and is for the
/// current day only. Reviewing an earlier day gives what the log alone knows
/// — `day_review` treats an empty `plan_at_arrival` as "no adherence
/// denominator" rather than as 0%.
fn day_extras(ctx: &Ctx, date: NaiveDate) -> Result<core_review::DayExtras, CliError> {
    let mut extras = core_review::DayExtras {
        budget: ctx.state.budget.filter(|_| ctx.state.date == Some(date)),
        // §12.4's `lost 55m (call)` names what the day was lost *to*, which
        // §10.1's `interrupt` event does not record (it carries the
        // interrupted item, not the reason). Left unset rather than guessed.
        lost_note: None,
        ..core_review::DayExtras::default()
    };
    if date != ctx.today {
        return Ok(extras);
    }
    let blocks = ghost::blocks(ctx);
    extras.plan_at_arrival = blocks
        .iter()
        .filter_map(|b| {
            Some(core_review::PlannedBlock::new(
                b.id.clone()?,
                tm_core::capacity::local_dt(ctx.cfg.tz, date, b.start),
            ))
        })
        .collect();
    let (plan, cands, prios) = planning::build_ranked(ctx, false)?;
    extras.underused = plan.diagnostics.underused.len();
    extras.optional = Some(optional_quota(&plan, &ctx.tree));
    // §12.4's `tomorrow  first candidate t5 (after t4) · d1 p1 u=0.6`: the
    // top-ranked candidates the day did not get to, with the reason each is
    // where it is.
    let planned: Vec<&Id> = plan.segments.iter().filter_map(|s| s.item.as_ref()).collect();
    extras.tomorrow_first = priority::sorted(&prios, &cands)
        .into_iter()
        .filter(|id| !planned.contains(&id) && !ctx.replay.is_done(id.as_str()))
        .take(3)
        .map(|id| {
            let note = prios.iter().find(|p| p.id == id).map(|p| match p.u {
                Some(u) => format!("p{} u={u:.2}", p.p),
                None => format!("p{}", p.p),
            });
            core_review::TomorrowCandidate::new(id, note.as_deref())
        })
        .collect();
    Ok(extras)
}

/// §11's optional quota for a day: minutes the plan gives `optional.md`
/// items, their `max:` cap, and how many of those minutes are outside a Rest
/// slot (§8.2 step 7 puts optionals in Rest).
fn optional_quota(plan: &tm_core::planner::DayPlan, tree: &Tree) -> core_review::OptionalQuota {
    let mut quota = core_review::OptionalQuota::default();
    let rest: Vec<(_, _)> = plan
        .segments
        .iter()
        .filter(|s| matches!(s.kind, tm_core::planner::SegKind::Rest))
        .map(|s| (s.start, s.end))
        .collect();
    for seg in plan
        .segments
        .iter()
        .filter(|s| matches!(s.kind, tm_core::planner::SegKind::Optional))
    {
        quota.minutes += seg.minutes();
        if !rest.iter().any(|(a, b)| *a <= seg.start && seg.end <= *b) {
            quota.outside_rest_min += seg.minutes();
        }
        if let Some(cap) = seg
            .item
            .as_ref()
            .and_then(|id| tree.get(id))
            .and_then(|i| i.budget.cap.as_ref())
        {
            quota.cap_min = Some(quota.cap_min.unwrap_or(0) + cap.amount.minutes);
        }
    }
    quota
}

/// `tm review <day|week|month> [--write] [--date …]` (§11, §12.4).
///
/// The numbers are `tm_core::review`'s — the module §17 M8's hand-computed
/// monitors verify — so the CLI, the §12.4 Review screen and the tests all
/// report one set of monitors.
pub fn review(g: &Globals, args: &super::ReviewArgs) -> Result<i32, CliError> {
    // §11.1: every review reads every day (`lounge_rate`) or every duration
    // (`estimate_calibration`).
    let mut ctx = Ctx::load_scoped(g, true, |_, _| ReplayScope::All)?;
    let period: Period = args.period.into();
    let (key, body, path) = match period {
        Period::Day => {
            let date = match &args.date {
                Some(d) => parse_date(d)?,
                None => ctx.today,
            };
            let extras = day_extras(&ctx, date)?;
            let r = core_review::day_review(
                &ctx.tree,
                &ctx.replay,
                &ctx.cfg,
                &ctx.model,
                date,
                ctx.cfg.tz,
                &extras,
            );
            (
                date.to_string(),
                ReviewBody::Day(Box::new(r)),
                Horizon::Day(date).path(),
            )
        }
        Period::Week => {
            let week = match &args.date {
                Some(d) => IsoWeek::parse(d)?,
                None => IsoWeek::from_date(ctx.today),
            };
            let extras = core_review::WeekExtras {
                deadline_health: match week.contains(ctx.today) {
                    true => {
                        let (cands, prios, _) = ctx.priorities(false)?;
                        Some(priority::deadline_health(&prios, &cands, ctx.today))
                    }
                    false => None,
                },
                ..core_review::WeekExtras::default()
            };
            let r = core_review::week_review(
                &ctx.tree,
                &ctx.replay,
                &ctx.cfg,
                &ctx.model,
                week,
                ctx.cfg.tz,
                &extras,
            );
            (
                week.to_string(),
                ReviewBody::Week(Box::new(r)),
                Horizon::Week(week).path(),
            )
        }
        Period::Month => {
            let month = match &args.date {
                Some(d) => YearMonth::parse(d)?,
                None => YearMonth::from_date(ctx.today),
            };
            let r = core_review::month_review(
                &ctx.tree,
                &ctx.replay,
                &ctx.cfg,
                month,
                ctx.cfg.tz,
                &core_review::MonthExtras::default(),
            );
            (
                month.to_string(),
                ReviewBody::Month(Box::new(r)),
                Horizon::Month(month).path(),
            )
        }
    };

    let text = match &body {
        ReviewBody::Day(r) => core_review::render_day(r),
        ReviewBody::Week(r) => core_review::render_week(r),
        ReviewBody::Month(r) => core_review::render_month(r),
    };
    let mut out = ReviewOut {
        period: horizon::period_name(period).to_string(),
        key: key.clone(),
        review: body,
        wrote: None,
    };
    if args.write {
        let rec = undo_stack::Recorder::start(&ctx, "review")?;
        ctx.store.replace_generated(&path, REVIEW_BLOCK, &text)?;
        out.wrote = Some(path.clone());
        ctx.reload()?;
        rec.finish(&ctx, format!("review {} {key}", out.period))?;
    }

    emit(ctx.json, || text.trim_end().to_string(), &out)?;
    Ok(0)
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
    // §11.1: the fit (and `--compare`, which refits) reads every observation.
    let history = args.fit || args.compare;
    let mut ctx = Ctx::load_scoped(g, true, |_, _| {
        if history {
            ReplayScope::All
        } else {
            ReplayScope::Hot
        }
    })?;
    if args.fit {
        let rec = undo_stack::Recorder::start(&ctx, "model")?;
        let fitted = energy::fit_observations(
            &ctx.cfg,
            &ctx.replay.energy,
            &ctx.replay.durations,
            &energy::arrivals_from_replay(&ctx.cfg, &ctx.replay),
            ctx.today,
        );
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
        let fresh = energy::fit_observations(
            &ctx.cfg,
            &ctx.replay.energy,
            &ctx.replay.durations,
            &energy::arrivals_from_replay(&ctx.cfg, &ctx.replay),
            ctx.today,
        );
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
    let ctx = Ctx::load_scoped(g, false, |_, today| log_scope(args, today))?;
    let rows = log_rows(&ctx.replay, args, ctx.today)?;
    let out = LogOut {
        total: ctx.replay.entry_count(),
        entries: rows.iter().map(|r| r.entry.clone()).collect(),
    };
    emit(ctx.json, || log_human(&rows), &out)?;
    Ok(0)
}

/// The rows `tm log` prints, from [`Replay::view`] (design §11.4 step 2):
/// `--item` keeps the surviving entries whose primary id is the key,
/// `--since` the entries whose wake-attributed day is on or after the bound
/// (cancelled ones included), and `--tail` the last *n* (20 when neither
/// selector is given, else all).
fn log_rows<'a>(
    replay: &'a Replay,
    args: &super::LogArgs,
    today: NaiveDate,
) -> Result<Vec<&'a ViewRow>, CliError> {
    let mut rows: Vec<&ViewRow> = match &args.item {
        Some(id) => {
            let key = Ctx::key(id);
            replay
                .view()
                .iter()
                .filter(|r| !r.cancelled && r.entry.ev.primary_id() == Some(key.as_str()))
                .collect()
        }
        None => replay.view().iter().collect(),
    };
    if let Some(since) = &args.since {
        let from = parse_since(since, today)?;
        rows.retain(|r| r.day >= from);
    }
    let tail = args.tail.unwrap_or(if args.since.is_some() || args.item.is_some() {
        rows.len()
    } else {
        20
    });
    if rows.len() > tail {
        rows.drain(0..rows.len() - tail);
    }
    Ok(rows)
}

/// `tm log`'s human lines: the row's display text, the tag, and the `k=v`
/// pairs of the entry's JSON without `t` and `ev`.
fn log_human(rows: &[&ViewRow]) -> String {
    rows.iter()
        .map(|r| {
            let mut v = serde_json::to_value(&r.entry).unwrap_or(serde_json::Value::Null);
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
            format!("{} {} {}", r.display(), r.entry.ev.name(), rest)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The scope `tm log` asks for (§11.1): `--item` reads every day's headers,
/// `--since` the days from its bound to today, and the tail a scope wide
/// enough to hold the last *n* entries (gap 117).
fn log_scope(args: &super::LogArgs, today: NaiveDate) -> ReplayScope {
    match (&args.item, &args.since) {
        (Some(_), _) => ReplayScope::All,
        (None, Some(since)) => match parse_since(since, today) {
            Ok(from) => ReplayScope::Dates { from: from.min(today), to: today },
            // `log_rows` refuses the bound; nothing is read for it.
            Err(_) => ReplayScope::Hot,
        },
        // **Gap 117, closed here.** §11.4 step 2 takes "the last *n*", and
        // `Hot` holds no day record, so after the switch a user with fewer
        // than *n* entries since the horizon `H` would see fewer than *n* —
        // `tm log` would silently come out short. `All` is the scope that can
        // always hold the tail. §11.1's narrower reading — `Dates` reaching
        // back just far enough for *n* headers — needs a first answer to know
        // how far back that is, so it is a two-step narrowing: a latency
        // lever for S, not a correctness fix, and it is recorded as one.
        (None, None) => ReplayScope::All,
    }
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

/// `tm tui` — §12's terminal UI (see [`crate::tui`]).
pub fn tui(g: &Globals) -> Result<i32, CliError> {
    crate::tui::run(g)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(tail: Option<usize>, since: Option<&str>, item: Option<&str>) -> crate::cli::LogArgs {
        crate::cli::LogArgs {
            tail,
            since: since.map(str::to_string),
            item: item.map(str::to_string),
        }
    }

    /// **`tm log`'s tail asks for a scope that can hold it** — gap 117, closed.
    /// §11.4 step 2 builds the last *n* from the day records in scope plus the
    /// open days and the tail; `Hot` carries no day record, so asking `Hot` for
    /// a plain `tm log` or `--tail n` lets the list come out short once the
    /// switch makes the scope real. This pins the scope each selector asks for.
    ///
    /// It is a scope test, not a behaviour test, and that is the whole of what
    /// can be checked before S: `Ctx::replay_with` still answers every scope
    /// with the whole log, so a `tm log --tail n` run over a three-year log
    /// returns the same *n* lines either way and could not fail. The guard
    /// that a three-year log would give is owed to S, with the switch.
    #[test]
    fn the_log_tail_asks_a_scope_that_can_hold_the_last_n() {
        let d = |s: &str| tm_core::model::parse_date(s).expect("date");
        let today = d("2026-09-14");

        // Plain `tm log`, and an explicit tail of any size.
        assert_eq!(log_scope(&args(None, None, None), today), ReplayScope::All);
        assert_eq!(log_scope(&args(Some(20), None, None), today), ReplayScope::All);
        assert_eq!(log_scope(&args(Some(5_000), None, None), today), ReplayScope::All);

        // `--item` reads every day's headers (§11.1), tail or no tail.
        assert_eq!(log_scope(&args(None, None, Some("^a1")), today), ReplayScope::All);
        assert_eq!(log_scope(&args(Some(20), None, Some("^a1")), today), ReplayScope::All);

        // `--since` pins both ends, and a tail beside it is selected inside them.
        assert_eq!(
            log_scope(&args(None, Some("7d"), None), today),
            ReplayScope::Dates { from: d("2026-09-07"), to: today }
        );
        assert_eq!(
            log_scope(&args(Some(20), Some("2026-09-01"), None), today),
            ReplayScope::Dates { from: d("2026-09-01"), to: today }
        );
        // A bound `log_rows` will refuse: nothing is read for it.
        assert_eq!(log_scope(&args(None, Some("not a date"), None), today), ReplayScope::Hot);
    }
}
