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

use std::collections::BTreeMap;

use chrono::{Duration, NaiveDate};
use serde::Serialize;
use serde_json::value::RawValue;

use tm_core::check as validate;
use tm_core::energy::{self, Model};
use tm_core::horizon::{self, REVIEW_BLOCK};
use tm_core::ics;
use tm_core::log::{Replay, ViewRow};
use tm_core::priority;
use tm_core::review as core_review;
use tm_core::model::{parse_date, Horizon, Id, IsoWeek, Period, YearMonth};
use tm_core::store::{Store, LOG_PATH, MODEL_PATH};
use tm_core::tree::Tree;

use super::closing;
use super::ctx::{Ctx, Globals, ReplayScope};
use super::kernel_bridge::Grain;
use super::kernel_log;
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
    let verb = format!("close {}", grain.name());
    let report = closing::run_explained(&mut ctx, closing::Which::One(grain), &verb, &drops)?;
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
    super::kernel_bridge::gate(&ctx, "sync-cal")?;
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
    // **The write gate goes FIRST, not beside the write** (README gap 1080).
    // It is the same one call it always was — `--write` has always paid it —
    // moved ahead of the body that computes the review. It has to be: on a
    // tree the kernel refuses, `day_extras` (and the week's
    // `Ctx::priorities`) reaches the kernel first and the user got the
    // kernel's sentence with no word about whether their `--write` happened,
    // which is the one thing D35 bought. A read that refuses ahead of a
    // pre-write check is a pre-write check in the wrong place.
    if args.write {
        super::kernel_bridge::gate(&ctx, "review --write")?;
    }
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
                Some(d) => closing::week_key(d)?,
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
                Some(d) => closing::month_key(d)?,
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
        super::kernel_bridge::gate(&ctx, "model --fit")?;
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
///
/// **`entries` holds each line's own JSON bytes** ([`RawValue`]), not a parsed
/// value — the owner's **D22** (2026-09-16; AGENTS §4), which corrects design
/// §11.4 step 5. See [`entry_json_of`] for why, and for the pretty-printing that
/// has to be re-emitted by hand once the bytes are carried rather than
/// re-serialised.
#[derive(Debug, Serialize)]
pub struct LogOut {
    /// How many entries the log holds.
    pub total: usize,
    /// The selected entries, oldest first, each as the bytes of its own line.
    pub entries: Vec<Box<RawValue>>,
}

/// `tm log --tail 20 | --since 7d | --item ^id` (§10.1).
pub fn log(g: &Globals, args: &super::LogArgs) -> Result<i32, CliError> {
    let ctx = Ctx::load_scoped(g, false, |_, today| log_scope(args, today))?;
    let rows = log_rows(&ctx.replay, args, ctx.today)?;
    // §11.4's order: select headers, then read the bytes of the selected lines
    // (`Ctx::entries_at`, the kernel's `render` op after the switch), then
    // render. Only the selected lines are read, not the whole log again.
    let lines: Vec<u64> = rows.iter().map(|r| r.line).collect();
    let entries = Ctx::entries_at(&ctx.store, &ctx.cfg, ctx.today, &lines)?;
    let out = LogOut {
        total: ctx.replay.entry_count(),
        // **D22**: the payload is the line's own bytes, never a re-serialised
        // `Value`. Since S they are the kernel's `render` op's
        // (`kernel_log::render_lines`, which hands back a `RawValue`); before it
        // they were the writer's `LogEntry::to_json`. **This renderer did not
        // change when they moved** — that is what D22's seam bought, and
        // `tm_log_is_byte_identical_on_the_corpus` is what says so.
        entries: lines
            .iter()
            .filter_map(|l| entries.get(l))
            .map(|(raw, _)| entry_json_of(raw.get()))
            .collect::<Result<Vec<_>, CliError>>()?,
    };
    emit(ctx.json, || log_human(&rows, &entries), &out)?;
    Ok(0)
}

/// Where `entries`' elements sit in `tm log --json`'s document: `{` is depth 0,
/// `"entries": [` opens depth 1, and each entry object is an element of that
/// array, so its own braces sit at depth 2.
///
/// It is a constant because [`emit`] formats the document and this function
/// formats the fragment, and the two have to agree. `the_log_documents_shape_is_serde_jsons`
/// is the test that fails if this number and [`LogOut`]'s shape ever part company.
const ENTRY_DEPTH: usize = 2;

/// **One log line, as the bytes `tm log --json` prints** — the owner's **D22**.
///
/// Design §11.4 step 5 asked for two things that cannot both hold: that `--json`
/// emit "each rendering **parsed as a generic `serde_json::Value`**", and that it
/// be "**byte-identical to today**". This workspace's `serde_json` is built
/// without `preserve_order`, so [`serde_json::Value`]'s object is a `BTreeMap`
/// and parsing **alphabetises every key**, where the writer emits `t` first.
/// Measured at W-9: taking the sentence literally moved `tm log --json` on **7 of
/// 69** corpus invocations, every difference a key order and no value. D22 settles
/// it in favour of byte-identity, and scopes the fix to this function.
///
/// **The pretty-printing is re-emitted here, not inherited.** A [`RawValue`] is
/// written into the enclosing document *verbatim*, so
/// `serde_json::to_string_pretty` — which formats every value it can see — cannot
/// indent bytes it is handed as one opaque fragment, and an entry would print
/// compact on a single line. That is a real byte change and it is the trap D22
/// names. So the fragment is indented here, by [`reindent`], exactly as
/// serde_json's own `PrettyFormatter` would have indented the same value at
/// [`ENTRY_DEPTH`].
// (`entry_json`, which took a parsed `LogEntry` and re-serialised it with the
// writer, went at S with `Ctx::entries_at`'s old body: the kernel's `render`
// hands back the bytes, so there is nothing left to re-serialise. The seam
// below is the one that survived, unchanged, which is the point of it.)

/// The seam itself: **one line's JSON bytes in, the bytes `--json` prints out**.
///
/// It is written over `&str` and not over [`LogEntry`] on purpose. Today its
/// argument is the writer's `to_json`; at S it is the kernel's rendering
/// (`kernel_log::render_lines`, already a [`RawValue`]), and §12 deletes the
/// reader that would otherwise stand between them. A function that took a parsed
/// entry would have to be rewritten at the switch; this one does not, and its
/// tests do not either.
fn entry_json_of(raw: &str) -> Result<Box<RawValue>, CliError> {
    RawValue::from_string(reindent(raw, ENTRY_DEPTH)).map_err(CliError::from)
}

/// Re-indent compact JSON as `serde_json::to_string_pretty` would at nesting
/// depth `depth`, **without parsing it** — so key order, number lexemes and
/// string escapes are the input's own bytes.
///
/// serde_json's `PrettyFormatter` is two spaces per level; it opens a non-empty
/// object or array with a newline and an indent, writes `": "` between a key and
/// its value, puts each element after a `,` on its own line, and closes on a
/// fresh line at the parent's indent — while an **empty** object or array stays
/// `{}` or `[]` with nothing between the braces. That is the whole of what this
/// reproduces. `the_reindent_is_serde_jsons_pretty_printer` checks it against
/// `to_string_pretty` itself over values whose keys are already alphabetical, so
/// the comparison is about *formatting* and the ordering is not in the way.
fn reindent(raw: &str, depth: usize) -> String {
    let b = raw.as_bytes();
    let mut out = String::with_capacity(raw.len() * 2);
    let mut depth = depth;
    let mut i = 0;
    let newline = |out: &mut String, depth: usize| {
        out.push('\n');
        for _ in 0..depth {
            out.push_str("  ");
        }
    };
    while i < b.len() {
        match b[i] {
            // A string is copied verbatim, escapes and all: this function never
            // re-escapes a byte, which is half of why it is byte-faithful.
            b'"' => {
                let start = i;
                i += 1;
                while i < b.len() {
                    match b[i] {
                        b'\\' => i += 2,
                        b'"' => {
                            i += 1;
                            break;
                        }
                        _ => i += 1,
                    }
                }
                out.push_str(&raw[start..i.min(raw.len())]);
            }
            open @ (b'{' | b'[') => {
                let close = if open == b'{' { b'}' } else { b']' };
                let mut j = i + 1;
                while j < b.len() && (b[j] as char).is_ascii_whitespace() {
                    j += 1;
                }
                out.push(open as char);
                if j < b.len() && b[j] == close {
                    // Empty: serde_json writes `{}` / `[]` with no newline.
                    out.push(close as char);
                    i = j + 1;
                } else {
                    depth += 1;
                    newline(&mut out, depth);
                    i += 1;
                }
            }
            close @ (b'}' | b']') => {
                depth = depth.saturating_sub(1);
                newline(&mut out, depth);
                out.push(close as char);
                i += 1;
            }
            b',' => {
                out.push(',');
                newline(&mut out, depth);
                i += 1;
            }
            b':' => {
                out.push_str(": ");
                i += 1;
            }
            c if (c as char).is_ascii_whitespace() => i += 1,
            c => {
                out.push(c as char);
                i += 1;
            }
        }
    }
    out
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
                .filter(|r| !r.cancelled && r.id.as_deref() == Some(key.as_str()))
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
/// pairs of the line's JSON without `t` and `ev`.
///
/// The header comes from the row ([`ViewRow`]) and the payload from
/// `entries[line]`, the bytes [`Ctx::entries_at`] read for exactly these lines
/// (§11.4 step 3). A line whose payload did not come back — the file changed
/// under the command between the replay and the read — still prints its header,
/// which is what the kernel's `render` returns for a line it cannot render.
///
/// **The parse stays on the human path deliberately** (§11.4 step 5): its
/// alphabetical key order is what `tm log` prints today, and
/// `tm_log_is_byte_identical_on_the_corpus` pins it. Only `--json` carries the
/// line's own bytes (D22). The rendering parsed here is the kernel's since S;
/// it was the writer's before, and the bytes are the same bytes.
fn log_human(rows: &[&ViewRow], entries: &BTreeMap<u64, (Box<RawValue>, String)>) -> String {
    rows.iter()
        .map(|r| {
            let rest = entries
                .get(&r.line)
                .and_then(|(raw, _)| {
                    let mut v: serde_json::Value = serde_json::from_str(raw.get()).ok()?;
                    let m = v.as_object_mut()?;
                    m.remove("t");
                    m.remove("ev");
                    Some(
                        m.iter()
                            .map(|(k, v)| format!("{k}={v}"))
                            .collect::<Vec<_>>()
                            .join(" "),
                    )
                })
                .unwrap_or_default();
            format!("{} {} {}", r.display(), r.tag, rest)
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
    /// **`--fix-ids` was asked for and wrote nothing**, because the tree it
    /// would have written is one the kernel still refuses (the owner's D35,
    /// README gap 675). The sentence names the refusal; the refusal itself is
    /// already among `problems`, where `tm check` puts every kernel-load fault.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fix_refused: Option<String>,
    /// `no problems` or `2 errors, 3 warnings`.
    pub summary: String,
    /// The exit code (§13: 2 when anything is an error).
    pub exit_code: i32,
}

/// **Every line of `.tm/log.jsonl` the kernel refuses** (D18 (i), gap 134).
///
/// **Why this is its own read-only sweep and not the verb's replay.** The
/// kernel's `log` answer carries a `warnings` array that is **per call**
/// (`Boundary.logBody` over `logVerdicts`): a hot call sees only its own
/// tail's lines, and genesis returns only its **last chunk's**. So taking
/// `tm check`'s warnings from an answer would silently name the lines of the
/// final chunk alone — at *every* scope, `All` included, not just `Hot`. A
/// call that asks for no facts, no headers, no reseal and no sealed records
/// does not resume (`Boundary.LogReq.resumes`), so the kernel reads its lines
/// and answers their warnings with no replay at all: [`kernel_log::line_warnings`]
/// sweeps the whole file in those chunks, and is exact whatever scope the
/// verb's own replay asked for.
///
/// A sweep that cannot run reports **no lines and says so**, as its own
/// warning, rather than reporting a clean log: `tm check` is precisely the verb
/// that must keep working on a damaged log (D18), and the worst thing it could
/// do is call a log it could not read clean. Until S there was a second
/// answer to fall back on — the in-tree reader's warnings — and that fallback
/// went with the reader at S (design §12).
fn line_warnings(ctx: &Ctx) -> (Vec<tm_core::log::LogWarning>, Option<String>) {
    if !ctx.store.exists(LOG_PATH) {
        return (Vec::new(), None);
    }
    let bytes = match ctx.store.read_bytes(LOG_PATH) {
        Ok(b) => b,
        Err(e) => return (Vec::new(), Some(e.to_string())),
    };
    let cache = ctx.store.root().join(super::kernel_log::CACHE_DIR);
    let tz = super::tz_table::wire_for(Some(&cache), ctx.cfg.tz);
    let now = ctx.today.format("%Y-%m-%d").to_string();
    match super::kernel_log::line_warnings(&bytes, &now, &tz) {
        Ok(ws) => (ws, None),
        Err(why) => (Vec::new(), Some(why)),
    }
}

/// **What `tm check` says about `.tm/log.jsonl`** (the owner's D18 (i) and
/// (ii)): every line the reader refused — malformed JSON, an unknown field
/// type, a bad timestamp, bytes that are not UTF-8 — and every line stamped
/// more than [`validate::LOG_FUTURE_DAYS`] days after `now`, each as a
/// **warning** at its own physical line.
///
/// Warnings, so the exit code is exactly what the tree gives it. That is
/// D18's point: `tm check` is the one verb that must keep working on a
/// damaged log, because it is how the bad line is found. Before this repair
/// it said `no problems` about a log holding a truncated line and a line of
/// nonsense, and a line dated next year went unmentioned.
fn log_problems(ctx: &Ctx) -> Vec<validate::CheckProblem> {
    let (warnings, swept) = line_warnings(ctx);
    let quote = |text: &str| {
        let short: String = text.chars().take(72).collect();
        if short.chars().count() < text.chars().count() {
            format!("{short:?}…")
        } else {
            format!("{short:?}")
        }
    };
    let mut out: Vec<validate::CheckProblem> = warnings
        .iter()
        .map(|w| {
            validate::CheckProblem::warning(
                validate::LOG_LINE,
                LOG_PATH,
                w.line,
                None,
                format!("the log reader refused this line: {} ({})", w.error, quote(&w.text)),
            )
        })
        .collect();
    if let Some(why) = swept {
        out.push(validate::CheckProblem::warning(
            validate::LOG_LINE,
            LOG_PATH,
            1,
            None,
            format!(
                "the kernel could not sweep this log for unreadable lines ({why}); \
                 no line below is reported from it"
            ),
        ));
    }
    // **Gap 145 / D18 (iii): the fault that fails every other verb.** `tm check`
    // loaded tolerantly (`Ctx::load_tolerant`), so a log no rebuild can window
    // reaches the user here, by name, at the line that caused it — which is the
    // reason `tm check` is exempted from the fault at all.
    if let Some((line, fault)) = &ctx.replay_fault {
        out.push(validate::CheckProblem::warning(
            validate::LOG_LINE,
            LOG_PATH,
            *line,
            None,
            fault.clone(),
        ));
    }
    let fence = ctx.now + Duration::days(validate::LOG_FUTURE_DAYS);
    for row in ctx.replay.view() {
        if row.t > fence {
            out.push(validate::CheckProblem::warning(
                validate::LOG_FUTURE,
                LOG_PATH,
                row.line as usize,
                None,
                format!(
                    "a `{}` dated {}, more than {} days after now ({}); it changes nothing about \
                     today, and no verb refuses it",
                    row.tag,
                    row.display(),
                    validate::LOG_FUTURE_DAYS,
                    ctx.now.format("%Y-%m-%d %H:%M"),
                ),
            ));
        }
    }
    out.extend(stall_problems(ctx));
    out
}

/// **A stall, named** — design §9.4's "Stalls" and §18.7 (README gap 119,
/// design gap 88: "`tm check` names a stall longer than 7 days").
///
/// A block left open, or an interruption never resumed, holds the replay
/// checkpoint's **ledger day** `L` back. Every day from the stall onward then
/// stays an *open day* inside the checkpoint instead of going out once as a
/// sealed record, so the checkpoint grows by about 2.5 KB a stalled day and
/// every call carries the lot. No answer is wrong and no line is damaged,
/// which is why this is a **warning** like the other two and moves no exit
/// code (D18).
///
/// **The cause is what is named, not the lag — measured, not assumed.** The
/// obvious check is "the ledger day is more than seven days behind `now`", and
/// it is wrong: §9.4 folds only up to `min(T, M) - keepDays`, where `M` is the
/// greatest header day among survivors, so `L` trails the log's own last
/// activity rather than today. Measured on this branch over two trees
/// identical but for the open block, the **unstalled** one ran a ledger day
/// **twelve days** behind `now` while the stalled one pinned at the day its
/// block opened and never moved. A lag test would therefore have named a tree
/// with nothing wrong with it — a warning nobody can act on, and §5.8's
/// trapdoor. What is both actionable and exactly what §9.4 calls a stall is
/// the open block or open interruption itself, with its age; the ledger day
/// it holds is reported beside it as the consequence, when there is one.
fn stall_problems(ctx: &Ctx) -> Vec<validate::CheckProblem> {
    // The line the stall began on. A stall holds the ledger day at its own
    // day, so its line is unfolded and the view still carries it; line 0 is
    // `CheckProblem`'s "the file, no line", which is what a header this scope
    // cannot see honestly gets rather than a guess.
    let line_of = |tag: &str, id: Option<&str>| -> usize {
        ctx.replay
            .view()
            .iter()
            .rev()
            .find(|r| r.tag == tag && !r.cancelled && r.id.as_deref() == id)
            .map_or(0, |r| r.line as usize)
    };
    // The consequence clause, when anything is sealed at all. `None` is a tree
    // whose log is all recent lines (nothing folded) and `tm check`'s own
    // tolerant load after a `reachTooFar` — in both, no ledger day is being
    // held, so the sentence is simply not made.
    let held = ctx.ledger_day.map_or_else(String::new, |l| {
        format!(
            "; it holds the ledger day at {}, so every day since then stays open in the \
             replay checkpoint (about 2.5 KB a stalled day)",
            kernel_log::date_of(l)
        )
    });
    // Whole days in `cfg.tz`, the zone every day is attributed in.
    let days_since = |t: chrono::DateTime<chrono::FixedOffset>| -> i64 {
        (ctx.today - t.with_timezone(&ctx.cfg.tz).date_naive()).num_days()
    };
    let mut out = Vec::new();
    if let Some(b) = &ctx.replay.open_block {
        let age = days_since(b.started);
        if age > validate::LOG_STALL_DAYS {
            out.push(validate::CheckProblem::warning(
                validate::LOG_STALL,
                LOG_PATH,
                line_of("start", Some(b.id.as_str())),
                None,
                format!(
                    "a block on ^{} has been open since {}, {age} days ago (more than {}){held} \
                     — close it with `tm done` or `tm stop`",
                    b.id,
                    b.started.format("%Y-%m-%d %H:%M"),
                    validate::LOG_STALL_DAYS,
                ),
            ));
        }
    }
    // An interruption with no `start` is a `resume` that never had one: there
    // is no instant to age it from, so it is not named here.
    if let Some(i) = ctx.replay.open_interrupt.as_ref().filter(|i| i.start.is_some()) {
        let began = i.start.expect("filtered to `Some`");
        let age = days_since(began);
        if age > validate::LOG_STALL_DAYS {
            let what = i.id.as_ref().map_or_else(
                || "an interruption".to_string(),
                |id| format!("an interruption of ^{id}"),
            );
            out.push(validate::CheckProblem::warning(
                validate::LOG_STALL,
                LOG_PATH,
                line_of("interrupt", i.id.as_deref()),
                None,
                format!(
                    "{what} has been open since {}, {age} days ago (more than {}){held} \
                     — close it with `tm resume`",
                    began.format("%Y-%m-%d %H:%M"),
                    validate::LOG_STALL_DAYS,
                ),
            ));
        }
    }
    out
}

/// **What the kernel says about the tree** (the owner's D32, gap 476).
///
/// `tm check` is the one verb that loads **tolerantly** (D18, gap 145), so a
/// log no rebuild can window cannot stop it naming the bad line. It was also
/// the one verb that could not see a fault the kernel refuses the whole tree
/// for: since D31 two lines with one title are a store-key collision, and a
/// duplicated inbox note brings down `tm plan`, `tm now`, `tm review day` and
/// `tm drop` while this verb answered *"no problems"*, exit 0.
///
/// So it asks the kernel, with the **smallest request there is** —
/// `{"docs":…,"cmds":[]}`, the corpus round trip's own shape. That request
/// carries no `log` section, no `state.json` and no commands, so it reads
/// nothing a damaged log could spoil and writes nothing at all: **D18 is
/// untouched**, the tolerant load above still finds the line, and
/// [`Ctx::replay_fault`] is still the warning it always was.
///
/// **The question itself now lives in one place** (the owner's D35, gap 584):
/// [`kernel_bridge::tree_refusal`] asks it, this turns its answer into
/// `tm check`'s problems, and [`kernel_bridge::gate`] turns the same answer
/// into a host-only write's refusal. Before D35 only `tm check` asked, so a
/// user could keep editing a tree every reading verb refused. The documents
/// are assembled there with `doc_json`/`doc_lines`, the same two functions
/// every other kernel call in this binary uses, so there is no second reader
/// of "what is a request document" (AGENTS §5.3).
///
/// **Why the asker is not `kernel_bridge::apply(ctx, &[])`**, which is the
/// other load-the-tree-and-write-nothing call (`Ctx::resolve_timeouts` and
/// `day::preflight` use it): because `apply` ends in a write step, and it
/// writes back any document whose returned lines differ from the sent ones — a
/// *renormalisation* counts. That is right for a verb that is about to change
/// the tree and wrong for the one verb whose whole contract is to look.
/// `tm check` runs in the pre-commit hook and the post-edit hook of every
/// generated plan, so it must be unable to write **by construction**, not
/// merely unlikely to: `tree_refusal` goes through `kernel_bridge::call`
/// directly, which has no write step at all, and `check_never_writes_a_byte`
/// pins it.
///
/// A **fault** (the kernel returned nothing usable) is not a tree problem and
/// is propagated as this command's error; only a named **refusal** becomes
/// problems.
fn kernel_problems(ctx: &Ctx) -> Result<Vec<validate::CheckProblem>, CliError> {
    Ok(super::kernel_bridge::tree_refusal(ctx)?
        .as_ref()
        .map(load_problems)
        .unwrap_or_default())
}

/// One kernel load refusal, as `tm check` problems.
///
/// A **key collision** carries both colliding lines since D32 (gap 475), and
/// this follows `check`'s own duplicate-id convention: **one problem per line**
/// (§17.2), so an editor jumping through the list stops at both. It does not
/// append *"also at …"* the way `dup-id` does, because the kernel's own message
/// already names both positions — saying it twice in one line would be the
/// second reader of a fact that has one (AGENTS §5.3). `badLine` and
/// `unterminatedComment` carry one position and give one problem. Anything else — `itemCheck`, `duplicatePath`, a `kernel`
/// name — is about the tree rather than a line, and is reported with no
/// position, which [`validate::CheckProblem`]'s own `Display` prints without a
/// `file:line` prefix.
///
/// Every line number here is already 1-based: the bridge converts the kernel's
/// 0-based wire at the one place the two conventions meet (gap 479), and this
/// reads the converted detail rather than the wire, so the binary still emits
/// **one** convention.
fn load_problems(issue: &super::out::KernelIssue) -> Vec<validate::CheckProblem> {
    // **`tm check` does not tell the reader to run `tm check`** (W-16 repair,
    // gap 580). `itemCheck`'s refusal ends with
    // `kernel_bridge::CHECK_HINT` because it is a whole-tree fault with no
    // position and every other verb's user has to be sent somewhere; inside
    // this command's own output the advice is nonsense, and the two lines that
    // *do* name the file and the line are printed directly beneath it. One
    // spelling of the sentence, taken back off at the one place it is wrong.
    let message = issue.message.replace(super::kernel_bridge::CHECK_HINT, "");
    let spot = |k: &str| -> Option<(String, usize)> {
        let s = issue.detail.get(k)?;
        let path = s.get("path")?.as_str()?.to_string();
        let line = usize::try_from(s.get("line")?.as_u64()?).ok()?;
        Some((path, line))
    };
    let key = issue.detail.get("key").and_then(serde_json::Value::as_str).map(Id::new);
    if let (Some(a), Some(b)) = (spot("a"), spot("b")) {
        return [a, b]
            .into_iter()
            .map(|(path, line)| {
                validate::CheckProblem::error(
                    validate::KERNEL_LOAD,
                    &path,
                    line,
                    key.clone(),
                    message.clone(),
                )
            })
            .collect();
    }
    let path = issue.detail.get("path").and_then(serde_json::Value::as_str).unwrap_or_default();
    let line = issue
        .detail
        .get("line")
        .and_then(serde_json::Value::as_u64)
        .and_then(|n| usize::try_from(n).ok())
        .unwrap_or(0);
    vec![validate::CheckProblem::error(
        validate::KERNEL_LOAD,
        path,
        line,
        key,
        message,
    )]
}

/// `tm check [--fix-ids]` (§1.3, §13), plus the log's own warnings (D18) and
/// the kernel's own load (D32).
pub fn check(g: &Globals, args: &super::CheckArgs) -> Result<i32, CliError> {
    // **D18, gap 145**: the one verb that loads tolerantly, because it is the
    // one that must survive a log no rebuild can window — it is how the line is
    // found. Every other verb fails by name on that fault.
    let ctx = Ctx::load_tolerant(g)?;
    let mut files = ctx.files.files.clone();
    // **D35's gate on the one write this verb does** (README gap 675).
    // `--fix-ids` writes through the store, so it is a host-only write path and
    // it went ungated for four runs: on a tree the kernel refused for an
    // unrelated reason it rewrote a file, exited 0 on the write and left no undo
    // entry. It cannot take `kernel_bridge::gate` — a tree refused *for a
    // missing `^id`* is the tree this flag exists to repair — so it asks the
    // question D35 is actually about: does the tree this write produces load?
    // `kernel_bridge::fix_ids_refusal` runs the same `fix_ids` against a
    // `MemStore` mirror and asks the kernel about the result.
    let mut blocked = None;
    let fixed = if args.fix_ids {
        let mut gen = id_gen(&ctx, "fix-ids");
        let mut proposal = id_gen(&ctx, "fix-ids-proposal");
        match super::kernel_bridge::fix_ids_refusal(&ctx, &mut proposal)? {
            None => {
                // **D37, README gap 687: the write is undoable.** This verb
                // called no `Recorder::start` on any tree, ever — so
                // `tm check --fix-ids` assigned ids, exited 0, and `tm undo`
                // then said *"nothing to undo"*. The bytes were recoverable by
                // hand (only the `^id` token is appended) but not by the verb
                // the product tells users to back out with. D35's gate above
                // made `tm undo` *reachable* afterwards; it gave it nothing to
                // take back.
                //
                // **No `ctx.reload()` here, unlike every other recording
                // path.** `check` is D18/gap 145's one tolerant verb — it is
                // how a tree no other verb can load is diagnosed — and
                // `Ctx::reload` is a *strict* `read_tree` plus a replay, both
                // of which can fail on exactly the tree this verb exists for.
                // `Recorder::finish` does not need it: the file diff is read
                // back through the store, and `log_now` tolerates a log it
                // cannot tail. `--fix-ids` writes no log event and no state,
                // so there is nothing a reload would add to the entry.
                //
                // A `--fix-ids` that assigns nothing records nothing:
                // `Recorder::finish` pushes no entry when no file moved.
                let rec = undo_stack::Recorder::start(&ctx, "check")?;
                let fixed = validate::fix_ids(&ctx.store, &mut files, &mut gen)?;
                let n = fixed.len();
                rec.finish(
                    &ctx,
                    format!("--fix-ids: {n} id{} assigned", if n == 1 { "" } else { "s" }),
                )?;
                fixed
            }
            Some(issue) => {
                blocked = Some(issue);
                Vec::new()
            }
        }
    } else {
        Vec::new()
    };
    let fix_refused = blocked.as_ref().map(|issue| {
        format!(
            "--fix-ids wrote nothing: the tree it would have written is one the kernel still \
             refuses ({}) — the line is named below; fix it and run this again",
            issue.name
        )
    });
    let tree = Tree::build(&files, &ctx.cfg);
    let mut problems = validate::check(&files, &tree, &ctx.cfg);
    // `validate::check` sorts by `(file, line, code, message)`; this stable
    // sort by `(file, line)` merges the log's problems into that order
    // without disturbing it inside a line.
    problems.extend(log_problems(&ctx));
    // D32, gap 476: and what the kernel says about the same tree — after
    // `--fix-ids` has written, so the kernel is asked about the tree that is
    // now on disk and not the one that was.
    problems.extend(kernel_problems(&ctx)?);
    // **And the refusal that blocked `--fix-ids`, when it is not already
    // there** (gap 675). The kernel stops at its first refusal, so the tree on
    // disk can be refused for the very fault `--fix-ids` would have repaired
    // while the fault that BLOCKED it — the one the proposed tree still trips —
    // is named nowhere. Same `load_problems`, so the rows are spelled once.
    if let Some(issue) = &blocked {
        for p in load_problems(issue) {
            if !problems
                .iter()
                .any(|q| q.file == p.file && q.line == p.line && q.message == p.message)
            {
                problems.push(p);
            }
        }
    }
    problems.sort_by(|a, b| (a.file.as_str(), a.line).cmp(&(b.file.as_str(), b.line)));
    let code = validate::exit_code(&problems);
    let out = CheckOut {
        summary: validate::summary(&problems),
        problems,
        fixed,
        fix_refused,
        exit_code: code,
    };
    emit(
        ctx.json,
        || {
            let mut s = String::new();
            for (file, line, id) in &out.fixed {
                s.push_str(&format!("{file}:{line}: assigned {}\n", id.token()));
            }
            if let Some(why) = &out.fix_refused {
                s.push_str(&format!("{why}\n"));
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

    /// **[`reindent`] is serde_json's own pretty-printer, byte for byte** - D22's
    /// "pretty-printing must be re-emitted explicitly and **verified**".
    ///
    /// Every value here has **alphabetical** keys, so `serde_json::Value`'s
    /// `BTreeMap` order is the input's order and the comparison is purely about
    /// *formatting*: indentation, the space after a colon, where the newlines fall,
    /// and the empty object and array that stay on one line.
    ///
    /// Every value here also spells its numbers and escapes the way serde_json
    /// spells them, because `to_string_pretty` **re-prints lexemes**: a `1e3`
    /// becomes `1000.0`, and a unicode escape becomes the character it names. That
    /// is a difference in the *value's* printing and not in the formatting; it is
    /// parity **P29**, it is the behaviour this renderer is supposed to have, and
    /// the next test is what pins it.
    #[test]
    fn the_reindent_is_serde_jsons_pretty_printer() {
        let cases = [
            r#"{}"#,
            r#"[]"#,
            r#"{"a":1}"#,
            r#"{"a":1,"b":2}"#,
            r#"{"a":{},"b":[],"c":[1,2,3]}"#,
            r#"{"a":{"b":{"c":[{"d":1},{"e":[]}]}}}"#,
            r#"{"a":"x \" y \\ z","b":"\u0001\n\t"}"#,
            r#"{"a":-0.5,"b":true,"c":false,"d":null}"#,
            r#"[[],[[]],[{"a":[]}]]"#,
        ];
        for raw in cases {
            let value: serde_json::Value =
                serde_json::from_str(raw).unwrap_or_else(|e| panic!("{raw}: {e}"));
            let want = serde_json::to_string_pretty(&value).expect("pretty");
            assert_eq!(reindent(raw, 0), want, "reindent disagrees with serde_json on {raw}");
        }
    }

    /// **A hand-written numeral or escape is printed as written** - parity **P20**
    /// and **P29**, and the second half of why the bytes are carried rather than
    /// re-serialised.
    ///
    /// `.tm/log.jsonl` can be hand-edited, and serde_json re-prints whatever it
    /// parses: a `1e3` comes back `1000.0`, a `1.50` comes back `1.5`, and a unicode
    /// escape comes back as its character. The renderer hands back the line's own
    /// bytes, so `tm log` shows the user what is actually in their file. P29 records
    /// exactly this as a deliberate difference from the fork, which re-serialises
    /// through `Value`.
    #[test]
    fn a_hand_written_numeral_or_escape_is_printed_as_written() {
        let cases = [
            (r#"{"a":1e3}"#, "1e3"),
            (r#"{"a":1.50}"#, "1.50"),
            (r#"{"a":-0}"#, "-0"),
            (r#"{"a":3.0}"#, "3.0"),
            (r#"{"a":10000000000000000000000}"#, "10000000000000000000000"),
            (r#"{"a":"caf\u00e9"}"#, r#""caf\u00e9""#),
        ];
        for (raw, written) in cases {
            assert_eq!(
                reindent(raw, 0),
                format!("{{\n  \"a\": {written}\n}}"),
                "the renderer did not print {written} as written"
            );
        }
        // And the difference is real, not assumed: both of these are re-printed by
        // the reading D22 declined. Measured here rather than quoted.
        for raw in [r#"{"a":1e3}"#, r#"{"a":"caf\u00e9"}"#] {
            let twin = serde_json::to_string_pretty(
                &serde_json::from_str::<serde_json::Value>(raw).expect("parse"),
            )
            .expect("pretty");
            assert_ne!(reindent(raw, 0), twin, "serde_json no longer re-prints {raw}; P29 is stale");
        }
    }

    /// **The document `tm log --json` prints is serde_json's, at [`ENTRY_DEPTH`]**.
    ///
    /// [`emit`] formats the outer document and [`entry_json_of`] formats the
    /// fragment, so the two have to agree about how deep an entry sits. This builds
    /// the real [`LogOut`] and compares it with a twin of the same shape whose
    /// entries are parsed `Value`s - with alphabetical keys, so the twin's
    /// `BTreeMap` cannot reorder anything *inside* an entry and only the
    /// indentation is under test. If `LogOut` grew a field, or `entries` moved, this
    /// is what fails.
    ///
    /// **The twin has to be a struct.** Its first spelling built it with
    /// `serde_json::json!`, and the test failed with `entries` printed before
    /// `total`: a `Value` map alphabetised the *document's own* keys, which is the
    /// very reordering under test arriving one level up. That is how narrow the
    /// escape hatch is, and it is why D22 scopes `RawValue` to the renderer rather
    /// than reaching for `Value` anywhere near this path.
    #[test]
    fn the_log_documents_shape_is_serde_jsons() {
        #[derive(Serialize)]
        struct Twin {
            total: usize,
            entries: Vec<serde_json::Value>,
        }
        let raws = [r#"{"a":1,"b":{"c":[1,2]}}"#, r#"{"d":"x","e":{}}"#];
        let out = LogOut {
            total: 7,
            entries: raws.iter().map(|r| entry_json_of(r).expect("a valid fragment")).collect(),
        };
        let twin = Twin {
            total: 7,
            entries: raws
                .iter()
                .map(|r| serde_json::from_str::<serde_json::Value>(r).expect("parse"))
                .collect(),
        };
        assert_eq!(
            serde_json::to_string_pretty(&out).expect("the document"),
            serde_json::to_string_pretty(&twin).expect("the twin"),
            "`tm log --json`'s document is not serde_json's own formatting"
        );
    }

    /// **The key order is the writer's, and the declined reading would have moved
    /// it** — gap 144, and the assertion that gives D22 its teeth.
    ///
    /// The fork's `LogEntry` writes `t` first and its event's fields in
    /// declaration order. Design §11.4 step 5 asked for the rendering "parsed as a
    /// generic `serde_json::Value`"; this workspace's `serde_json` has no
    /// `preserve_order`, so that parse alphabetises — `actual_min` first, `t`
    /// last. Both halves are asserted here: what this renderer emits, and what the
    /// declined alternative would have emitted instead, so the test fails if
    /// someone reintroduces it *or* if the feature flag is ever turned on
    /// workspace-wide without this decision being revisited.
    #[test]
    fn the_renderer_keeps_the_writers_key_order_where_a_value_would_not() {
        let raw = r#"{"t":"2026-07-06T11:00:00-05:00","ev":"routine","item":"laundry","inst":"2026-07-06","status":"done","actual_min":30}"#;
        let keys = |text: &str| -> Vec<String> {
            text.lines()
                .filter_map(|l| l.trim().strip_prefix('"'))
                .filter_map(|l| l.split_once("\":"))
                .map(|(k, _)| k.to_string())
                .collect()
        };
        let written = ["t", "ev", "item", "inst", "status", "actual_min"];

        let ours = reindent(raw, 0);
        assert_eq!(keys(&ours), written, "the renderer did not keep the writer's key order");

        // The reading D22 declined, run here so the difference is measured and not
        // asserted from memory.
        let as_value: serde_json::Value = serde_json::from_str(raw).expect("parse");
        let alphabetised = serde_json::to_string_pretty(&as_value).expect("pretty");
        let mut sorted = written;
        sorted.sort_unstable();
        assert_eq!(keys(&alphabetised), sorted, "serde_json::Value no longer alphabetises");
        assert_ne!(ours, alphabetised, "the two readings agree, so this test proves nothing");

        // And the whole fragment, at the depth `tm log --json` prints it at.
        let entry = entry_json_of(raw).expect("a valid fragment");
        assert_eq!(
            entry.get(),
            "{\n      \"t\": \"2026-07-06T11:00:00-05:00\",\n      \"ev\": \"routine\",\n      \
             \"item\": \"laundry\",\n      \"inst\": \"2026-07-06\",\n      \"status\": \"done\",\n      \
             \"actual_min\": 30\n    }"
        );
    }
}
