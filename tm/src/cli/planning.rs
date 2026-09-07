//! `tm plan` and `tm now` (tm-spec-v1.md §8, §13).
//!
//! # API overview
//!
//! * [`plan`] — §8's `plan(state, now)`: collect the §6.2 candidates, size
//!   the §8.4 lookahead from the furthest deadline, run §7's priority pass,
//!   call [`tm_core::planner::plan`], then write the day file's
//!   `<!-- tm:plan … -->` section and `day/<date>.svg`, append the §10.1
//!   `plan` event and store the plan and its priorities (§7.4's hysteresis
//!   reads them tomorrow). `--week` prints the §8.4 capacity grid instead,
//!   `--diff` what moved since the last plan, `--explain ^id` §7's reasoning
//!   for one item.
//! * [`now`] — the running block and the next three segments (§13).
//!
//! The planner itself is still the placeholder of `planner.rs` (M4), so the
//! segment list is empty until it lands; everything around it — the window,
//! the budget, the priorities, the files written, the events logged — is
//! real, and the JSON shape is the final one.

use chrono::Timelike;
use serde::Serialize;
use tm_core::capacity::{self, DayCapacity};
use tm_core::log::Event;
use tm_core::model::{Id, IsoWeek};
use tm_core::planner::{self, DayPlan, Diagnostics, PlanInput, SegKind};
use tm_core::priority::{self, Prio};
use tm_core::store::Store;

use super::ctx::{Ctx, Globals, StoredPlan, StoredSegment};
use super::out::{emit, CliError};
use super::render;

/// One segment of `tm plan --json`.
#[derive(Clone, Debug, Serialize)]
pub struct SegOut {
    /// `HH:MM`.
    pub start: String,
    /// `HH:MM`.
    pub end: String,
    /// Minutes.
    pub minutes: u32,
    /// `block`, `break`, `wall`, …
    pub kind: String,
    /// Predicted slot energy (§8.5).
    pub energy: Option<u8>,
    /// The item, when the segment has one.
    pub item: Option<Id>,
    /// The §4.3 mark.
    pub mark: String,
    /// The rendered row text.
    pub text: String,
}

/// `tm plan --json`.
#[derive(Clone, Debug, Serialize)]
pub struct PlanOut {
    /// The day planned.
    pub date: String,
    /// `[start, end]` as `HH:MM` (§8.1).
    pub window: [String; 2],
    /// Blocks the day may spend (§8.1).
    pub budget_blocks: u32,
    /// Blocks already done today.
    pub blocks_done: u32,
    /// [`DayPlan::hash`].
    pub hash: String,
    /// The timeline.
    pub segments: Vec<SegOut>,
    /// §8.2 step 8.
    pub diagnostics: Diagnostics,
    /// Every candidate's `p` (§7).
    pub priorities: Vec<Prio>,
    /// Files this run wrote.
    pub wrote: Vec<String>,
    /// `--diff`.
    pub diff: Option<PlanDiff>,
    /// `--explain ^id`.
    pub explain: Option<String>,
}

/// `tm plan --diff` (§9, §14).
#[derive(Clone, Debug, Default, Serialize)]
pub struct PlanDiff {
    /// Whether there was a stored plan for this day at all.
    pub had_previous: bool,
    /// Items that were not in the previous plan.
    pub added: Vec<String>,
    /// Items that are no longer planned.
    pub removed: Vec<String>,
    /// `(item, from, to)` for items whose start moved.
    pub moved: Vec<(String, String, String)>,
    /// Σ minutes segments moved (§11's drift).
    pub drift_min: u32,
}

/// `tm plan --week --json` (§8.4).
#[derive(Clone, Debug, Serialize)]
pub struct WeekOut {
    /// The ISO week.
    pub week: String,
    /// One row per day.
    pub days: Vec<DayOut>,
    /// The rendered grid.
    pub grid: String,
}

/// One day of the week grid.
#[derive(Clone, Debug, Serialize)]
pub struct DayOut {
    /// The date.
    pub date: String,
    /// Minutes at each energy level 0..=5.
    pub minutes_at_level: [u32; 6],
    /// Total minutes.
    pub total: u32,
}

/// `HH:MM`.
fn hhmm(t: chrono::DateTime<chrono_tz::Tz>) -> String {
    format!("{:02}:{:02}", t.hour(), t.minute())
}

/// Build the plan for `ctx` (§8), with the priorities it was ordered by.
pub fn build(ctx: &Ctx, allow_home: bool) -> (DayPlan, Vec<Prio>) {
    let (cands, prios, caps) = ctx.priorities(allow_home);
    let input = PlanInput::new(
        &ctx.tree,
        &ctx.log,
        &ctx.replay,
        &ctx.cfg,
        &ctx.model,
        &ctx.state,
        ctx.now_tz,
    )
    .with_caps(&caps)
    .with_candidates(&cands);
    let mut plan = planner::plan(&input);
    if plan.priorities.is_empty() {
        plan.priorities = prios
            .iter()
            .map(|p| (p.id.clone(), p.clone()))
            .collect::<Vec<_>>();
    }
    (plan, prios)
}

/// The segments of a plan as JSON rows.
pub fn seg_out(plan: &DayPlan, ctx: &Ctx) -> Vec<SegOut> {
    let rows = render::rows(plan, &ctx.tree, &ctx.cfg);
    plan.segments
        .iter()
        .zip(rows)
        .map(|(seg, row)| SegOut {
            start: hhmm(seg.start),
            end: hhmm(seg.end),
            minutes: seg.minutes(),
            kind: row.kind,
            energy: seg.energy,
            item: seg.item.clone(),
            mark: row.mark.trim().to_string(),
            text: row.text,
        })
        .collect()
}

/// The plan flattened for `.tm/last_plan.json`.
fn stored(plan: &DayPlan, priorities: &[Prio]) -> StoredPlan {
    StoredPlan {
        date: Some(plan.date),
        hash: plan.hash(),
        priorities: priority::priorities_for_state(priorities),
        segments: plan
            .segments
            .iter()
            .map(|s| StoredSegment {
                start: hhmm(s.start),
                end: hhmm(s.end),
                kind: render::kind_name(&s.kind).to_string(),
                item: s.item.as_ref().map(|i| i.to_string()),
            })
            .collect(),
    }
}

/// Minutes between two `HH:MM` strings, absolute.
fn minutes_between(a: &str, b: &str) -> u32 {
    let parse = |s: &str| -> i32 {
        let mut it = s.split(':');
        let h: i32 = it.next().and_then(|v| v.parse().ok()).unwrap_or(0);
        let m: i32 = it.next().and_then(|v| v.parse().ok()).unwrap_or(0);
        h * 60 + m
    };
    (parse(a) - parse(b)).unsigned_abs()
}

/// Diff a fresh plan against the stored one (§9, §11's drift).
fn diff(new: &StoredPlan, old: Option<&StoredPlan>) -> PlanDiff {
    let Some(old) = old.filter(|o| o.date == new.date) else {
        return PlanDiff {
            had_previous: false,
            added: new
                .segments
                .iter()
                .filter_map(|s| s.item.clone())
                .collect(),
            ..PlanDiff::default()
        };
    };
    let start_of = |p: &StoredPlan, item: &str| -> Option<String> {
        p.segments
            .iter()
            .find(|s| s.item.as_deref() == Some(item))
            .map(|s| s.start.clone())
    };
    let items = |p: &StoredPlan| -> Vec<String> {
        let mut v: Vec<String> = p.segments.iter().filter_map(|s| s.item.clone()).collect();
        v.dedup();
        v
    };
    let (new_items, old_items) = (items(new), items(old));
    let mut out = PlanDiff {
        had_previous: true,
        ..PlanDiff::default()
    };
    for i in &new_items {
        match start_of(old, i) {
            None => out.added.push(i.clone()),
            Some(was) => {
                let is = start_of(new, i).unwrap_or_default();
                if is != was {
                    out.drift_min += minutes_between(&is, &was);
                    out.moved.push((i.clone(), was, is));
                }
            }
        }
    }
    for i in &old_items {
        if !new_items.contains(i) {
            out.removed.push(i.clone());
        }
    }
    out
}

/// Write one plan: the day file's generated section (§4.3), the day-bar SVG
/// (§12.1), the §10.1 `plan` event (only when the day actually moved) and the
/// state and sidecar §7.4's hysteresis reads tomorrow. Returns the files
/// written.
pub fn write_plan(ctx: &mut Ctx, plan: &DayPlan, prios: &[Prio]) -> Result<Vec<String>, CliError> {
    let new_stored = stored(plan, prios);
    let previous = ctx.last_plan();
    let mut wrote = Vec::new();

    let body = render::timeline(plan, &ctx.tree, &ctx.cfg);
    // §4.3: a day file the CLI creates gets the whole skeleton, not just the
    // front matter — `# Pinned`, `## Log` and `## Notes` are the human half.
    let day_path = super::dayfile::ensure(ctx, plan.date)?;
    let stamp = hhmm(ctx.now_tz);
    ctx.store
        .replace_generated_stamped(&day_path, "plan", Some(&stamp), &body)?;
    wrote.push(day_path);
    let svg_path = format!("day/{}.svg", plan.date);
    ctx.store
        .write_file(&svg_path, &render::svg(plan, &ctx.tree, &ctx.cfg))?;
    wrote.push(svg_path);

    // §10.1: log a `plan` only when the day actually moved.
    let hash = plan.hash();
    let drift = diff(&new_stored, previous.as_ref()).drift_min;
    if ctx.state.last_plan_hash.as_deref() != Some(hash.as_str()) {
        ctx.append_event(Event::Plan {
            hash: hash.clone(),
            replans_today: ctx.plans_today(),
            drift_min: drift,
        })?;
    }
    // §7.4: today's priorities become tomorrow's comparison; the map in
    // `state.json` stays yesterday's for the rest of today.
    let yesterday = ctx.hysteresis_input();
    ctx.state.priorities_yesterday = yesterday;
    ctx.state.last_plan_hash = Some(hash);
    ctx.state.date = Some(plan.date);
    ctx.save_state()?;
    ctx.save_last_plan(&new_stored)?;
    Ok(wrote)
}

/// `tm plan` (§13).
pub fn plan(g: &Globals, args: &super::PlanArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    if args.week {
        return week(&ctx, args.allow_home);
    }
    let (plan, prios) = build(&ctx, args.allow_home);

    let explain = match args.explain.as_deref() {
        Some(arg) => {
            let id = Ctx::key(arg);
            let (cands, _, _) = ctx.priorities(args.allow_home);
            Some(priority::explain(&id, &cands, &prios, &ctx.cfg))
        }
        None => None,
    };

    let new_stored = stored(&plan, &prios);
    let previous = ctx.last_plan();
    let diff_out = args
        .diff
        .then(|| diff(&new_stored, previous.as_ref()));

    let mut wrote = Vec::new();
    if explain.is_none() {
        wrote = write_plan(&mut ctx, &plan, &prios)?;
    }

    let out = PlanOut {
        date: plan.date.to_string(),
        window: [hhmm(plan.window.0), hhmm(plan.window.1)],
        budget_blocks: plan.budget_blocks,
        blocks_done: ctx.replay.blocks_done(ctx.today),
        hash: plan.hash(),
        segments: seg_out(&plan, &ctx),
        diagnostics: plan.diagnostics.clone(),
        priorities: prios.clone(),
        wrote,
        diff: diff_out.clone(),
        explain: explain.clone(),
    };
    emit(
        ctx.json,
        || {
            let mut s = String::new();
            if let Some(e) = &explain {
                return e.clone();
            }
            let body = render::timeline(&plan, &ctx.tree, &ctx.cfg);
            s.push_str(&format!(
                "{} · window {}–{} · budget {} blocks\n",
                plan.date, out.window[0], out.window[1], plan.budget_blocks
            ));
            s.push_str(&body);
            for (id, need, by) in &plan.diagnostics.impossible {
                s.push_str(&format!(
                    "IMPOSSIBLE {}: needs {}m more by {by}\n",
                    id.token(),
                    need
                ));
            }
            if let Some(d) = &diff_out {
                s.push_str(&format!(
                    "diff: +{} −{} moved {} · drift {}m\n",
                    d.added.len(),
                    d.removed.len(),
                    d.moved.len(),
                    d.drift_min
                ));
            }
            s.trim_end().to_string()
        },
        &out,
    )?;
    Ok(0)
}

/// `tm plan --week` (§8.4).
fn week(ctx: &Ctx, allow_home: bool) -> Result<i32, CliError> {
    let days = 7;
    let walls = ctx.walls_by_date(days);
    let slots = ctx.today_slots(allow_home);
    let caps: Vec<DayCapacity> = capacity::lookahead(
        &walls,
        &ctx.cfg,
        &ctx.model,
        &slots,
        ctx.today,
        days,
        ctx.wake_time(),
    );
    let out = WeekOut {
        week: IsoWeek::from_date(ctx.today).to_string(),
        days: caps
            .iter()
            .map(|d| DayOut {
                date: d.date.to_string(),
                minutes_at_level: d.minutes_at_level,
                total: d.total(),
            })
            .collect(),
        grid: capacity::week_grid(&caps),
    };
    emit(ctx.json, || out.grid.clone(), &out)?;
    Ok(0)
}

/// The running block, for `tm now --json`.
#[derive(Clone, Debug, Serialize)]
pub struct ActiveOut {
    /// The item.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// When it started (`HH:MM`).
    pub started: String,
    /// Planned minutes.
    pub est_min: u32,
    /// Minutes elapsed.
    pub elapsed_min: u32,
    /// Timer paused.
    pub paused: bool,
}

/// `tm now --json`.
#[derive(Clone, Debug, Serialize)]
pub struct NowOut {
    /// The instant.
    pub now: String,
    /// The date.
    pub date: String,
    /// Blocks done / budget (§11's status line).
    pub blocks_done: u32,
    /// The budget.
    pub budget_blocks: u32,
    /// The running block, from `state.json`.
    pub active: Option<ActiveOut>,
    /// The segment `now` is inside.
    pub current: Option<SegOut>,
    /// The next three segments (§13).
    pub next: Vec<SegOut>,
}

/// `tm now` (§13).
pub fn now(g: &Globals) -> Result<i32, CliError> {
    let ctx = Ctx::load(g, true)?;
    let (plan, _) = build(&ctx, false);
    let segs = seg_out(&plan, &ctx);
    let current_idx = plan
        .segments
        .iter()
        .position(|s| s.start <= ctx.now_tz && ctx.now_tz < s.end);
    let current = current_idx.map(|i| segs[i].clone());
    let next: Vec<SegOut> = plan
        .segments
        .iter()
        .enumerate()
        .filter(|(_, s)| s.start > ctx.now_tz && !matches!(s.kind, SegKind::Sleep))
        .take(3)
        .map(|(i, _)| segs[i].clone())
        .collect();
    let active = ctx.state.active.as_ref().map(|a| {
        let started = ctx.at(a.started);
        ActiveOut {
            id: a.id.clone(),
            title: ctx
                .tree
                .get(&a.id)
                .map(|i| i.title.clone())
                .unwrap_or_default(),
            started: hhmm(started),
            est_min: a.est_min,
            elapsed_min: (ctx.now_tz - started).num_minutes().max(0) as u32,
            paused: a.paused,
        }
    });
    let out = NowOut {
        now: hhmm(ctx.now_tz),
        date: ctx.today.to_string(),
        blocks_done: ctx.replay.blocks_done(ctx.today),
        budget_blocks: plan.budget_blocks,
        active,
        current,
        next,
    };
    emit(
        ctx.json,
        || {
            let mut s = String::new();
            match &out.active {
                Some(a) => s.push_str(&format!(
                    "▶ {} {} · started {} · {}m of {}m{}\n",
                    a.id.token(),
                    a.title,
                    a.started,
                    a.elapsed_min,
                    a.est_min,
                    if a.paused { " · paused" } else { "" }
                )),
                None => s.push_str("nothing running\n"),
            }
            for seg in &out.next {
                s.push_str(&format!("{} {} {}\n", seg.start, seg.kind, seg.text));
            }
            s.push_str(&format!(
                "{}/{} blocks",
                out.blocks_done, out.budget_blocks
            ));
            s
        },
        &out,
    )?;
    Ok(0)
}
