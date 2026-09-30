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
//!   for one item. Since stage 5 D10 L8 the priorities and the week's
//!   capacity are the kernel's ([`super::kernel_capacity`]): exact units, with
//!   floors only on screen and `…_exact: {num, den}` beside every integer of
//!   capacity on `--json` (the owner's D15).
//! * [`now`] — the running block and the next three segments (§13).
//!
//! The segments come from `tm_core::planner` (§8.2's eight steps); everything
//! around them — the window, the budget, the priorities, the files written,
//! the events logged — belongs to this layer.

use std::collections::BTreeSet;

use serde::Serialize;
use tm_core::capacity::{self, Exact, UnitCapacity};
use tm_core::log::Event;
use tm_core::model::{Id, IsoWeek};
use tm_core::dayplan::{DayPlan, Diagnostics};
use tm_core::planner::{self, PlanInput};
use tm_core::priority::{self, Candidate, Prio};
use tm_core::store::Store;

use super::ctx::{Ctx, Globals, StoredPlan, StoredSegment};
use super::ghost;
use super::kernel_capacity;
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

/// One day of the week grid (the owner's D15: each integer is the floor of its
/// own exact value, and the exact value is beside it).
#[derive(Clone, Debug, Serialize)]
pub struct DayOut {
    /// The date.
    pub date: String,
    /// Minutes at each energy level 0..=5, each the floor of its exact value.
    pub minutes_at_level: [u32; 6],
    /// The exact minutes at each level, `{num, den}` as digit strings.
    pub minutes_at_level_exact: [Exact; 6],
    /// Total minutes: the floor of the exact total, not the sum of the floors
    /// (so it may be up to five more than `minutes_at_level`'s sum).
    pub total: u32,
    /// The exact total.
    pub total_exact: Exact,
}

impl DayOut {
    /// One kernel day, floors beside exact values.
    fn of(day: &UnitCapacity) -> DayOut {
        DayOut {
            date: day.date.to_string(),
            minutes_at_level: day.minutes_at_level_floor(),
            minutes_at_level_exact: day.units.map(Exact::of_units),
            total: day.total_floor(),
            total_exact: Exact::of_units(day.total_units()),
        }
    }
}

/// `HH:MM`.
/// `HH:MM` — `tm_core::dayplan::fmt_clock` under this file's own name (AGENTS
/// §5.3, W-23: a byte-for-byte copy of it stood here).
use tm_core::dayplan::fmt_clock as hhmm;

/// Build the plan for `ctx` (§8), with the priorities it was ordered by.
pub fn build(ctx: &Ctx, allow_home: bool) -> Result<(DayPlan, Vec<Prio>), CliError> {
    let (plan, _, prios) = build_ranked(ctx, allow_home)?;
    Ok((plan, prios))
}

/// [`build`], with the candidates the priorities rank. The planner ranks by the
/// kernel's priorities (stage 5 D10 L8: [`PlanInput::with_ranking`]) and never
/// runs a lookahead or a pass of its own.
pub fn build_ranked(ctx: &Ctx, allow_home: bool) -> Result<(DayPlan, Vec<Candidate>, Vec<Prio>), CliError> {
    let (cands, prios, caps) = ctx.priorities(allow_home)?;
    let input = PlanInput::new(
        &ctx.tree,
        &ctx.replay,
        &ctx.cfg,
        &ctx.model,
        &ctx.state,
        ctx.now_tz,
    )
    .with_caps(&caps)
    .with_ranking(&cands, &prios)
    // §8.2 step 3: `--allow-home` lifts `home_max_ci`; the planner cuts its
    // own slots, so the flag has to reach `PlanInput` too, not only the
    // lookahead `ctx.priorities` sizes.
    .with_allow_home(allow_home);
    let mut plan = planner::plan(&input);
    if plan.priorities.is_empty() {
        plan.priorities = prios
            .iter()
            .map(|p| (p.id.clone(), p.clone()))
            .collect::<Vec<_>>();
    }
    Ok((plan, cands, prios))
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
                // The JSON's word, a replayed pause `pause` (D68; README gap
                // 3433's stored half, the W-38 repair): one span, one reading.
                kind: tm_core::emit::row_kind(s).to_string(),
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
    // One row per item, in the order the plan first mentions it. An item with
    // several blocks (or a routine placed twice) reaches this list once:
    // `moved` compares its *first* start, so a repeat would add the same
    // movement to `drift_min` again (§11: Σ minutes segments moved).
    let items = |p: &StoredPlan| -> Vec<String> {
        let mut seen = BTreeSet::new();
        p.segments
            .iter()
            .filter_map(|s| s.item.clone())
            .filter(|i| seen.insert(i.clone()))
            .collect()
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

    let body = render::timeline(plan, &ctx.tree, &ctx.cfg, ctx.now_tz);
    // §4.3: a day file the CLI creates gets the whole skeleton, not just the
    // front matter — `# Pinned`, `## Log` and `## Notes` are the human half.
    let day_path = super::dayfile::ensure(ctx, plan.date)?;
    let stamp = hhmm(ctx.now_tz);
    ctx.store
        .replace_generated_stamped(&day_path, "plan", Some(&stamp), &body)?;
    wrote.push(day_path);
    // §12.1: the same renderer draws the bar and writes the file, ghost row
    // and all — `.tm/arrival_plan.json` is what the ghost is rebuilt from.
    let blocks = ghost::blocks(ctx);
    let ghost_plan = ghost::plan(&blocks, &ctx.cfg, &ctx.model, &ctx.tree, &ctx.state, plan);
    let svg_path = format!("day/{}.svg", plan.date);
    ctx.store.write_file(
        &svg_path,
        &render::svg(
            plan,
            ghost_plan.as_ref(),
            &ctx.tree,
            &ctx.cfg,
            ctx.wake_dt(),
            ctx.now_tz,
        ),
    )?;
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
    let (plan, cands, prios) = build_ranked(&ctx, args.allow_home)?;

    let explain = match args.explain.as_deref() {
        Some(arg) => {
            let id = Ctx::key(arg);
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
            let body = render::timeline(&plan, &ctx.tree, &ctx.cfg, ctx.now_tz);
            s.push_str(&format!(
                "{} · window {}–{} · budget {} blocks\n",
                plan.date, out.window[0], out.window[1], plan.budget_blocks
            ));
            s.push_str(&body);
            // §8.2 step 8 and §11: what the day cannot say in its rows — the
            // under-used slots, the blocked and waiting items, and the "plan
            // honesty" warning §11 asks `tm plan` for.
            for note in render::diagnostics(&plan, &ctx.tree, &ctx.cfg) {
                s.push_str(&format!("· {note}\n"));
            }
            // §7.3: the banner names the item and the shortfall — "needs 8b,
            // 5b available by Fri" — not raw minutes.
            for banner in tm_core::emit::render_banners(&plan, &ctx.tree, &ctx.cfg) {
                s.push_str(&format!("IMPOSSIBLE {banner}\n"));
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

/// `tm plan --week` (§8.4): the kernel's seven days (stage 5 D10 L8), each cell
/// the floor of its own exact value.
fn week(ctx: &Ctx, allow_home: bool) -> Result<i32, CliError> {
    let caps = kernel_capacity::week(ctx, allow_home)?;
    let out = WeekOut {
        week: IsoWeek::from_date(ctx.today).to_string(),
        days: caps.iter().map(DayOut::of).collect(),
        grid: capacity::week_grid_units(&caps),
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
    /// Minutes WORKED: the wall clock since `started`, net of the pauses,
    /// interruptions and breaks that fell inside the block — the minutes
    /// `tm done` would log (`Replay::active_worked_min`, README gaps 2741 and 2920).
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
    let (plan, _) = build(&ctx, false)?;
    let segs = seg_out(&plan, &ctx);
    // **One selection** (W-23, README gap 1104). `tm now`'s text and
    // `tm now --json` each had their own answer to "the current block and the
    // next three" and the two disagreed: this one took the first segment
    // containing `now` whatever the planner had marked and whether or not it
    // was done, and its `next` used `start > now` and hid Sleep. Hiding a kind
    // is what makes D30 Q5 (a)'s "`tm now`'s rows are a contiguous sub-list of
    // the file's" unsatisfiable, so the rule that survives is the one that
    // filters nothing: `emit::now_window`, and the JSON's positions are the
    // text's positions.
    let (current_idx, next_idx) = tm_core::emit::now_window(&plan, ctx.now_tz);
    let current = current_idx.map(|i| segs[i].clone());
    let next: Vec<SegOut> = next_idx.into_iter().map(|i| segs[i].clone()).collect();
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
            // **One reading of worked minutes** (W-35, README gaps 2741 and
            // 2920). The header used the wall clock since `started`; W-35
            // track E made it the log's open block, which never sees a
            // `break`, so after a five-minute break it said `30m of 30m` while
            // `tm done` logged 25. It is `tm done`'s own reading now —
            // `day::worked_min`, the wall clock net of the day's pauses,
            // interruptions and breaks — and the TUI calls the same rule.
            elapsed_min: super::day::worked_min(&ctx, started),
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
            // §13: the current block and the next three, rendered by the
            // §4.3 renderer so `tm now` and the day file agree.
            s.push_str(&tm_core::emit::render_now_with(
                &plan,
                &ctx.tree,
                &ctx.cfg,
                ctx.now_tz,
            ));
            if !s.ends_with('\n') {
                s.push('\n');
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
