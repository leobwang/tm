//! §12.1's ghost row: the plan as it stood at `tm arrive`.
//!
//! # API overview
//!
//! * [`Block`] — one start of `.tm/arrival_plan.json`, parsed.
//! * [`blocks`] — the record for *today*, or nothing.
//! * [`plan`] — those starts rebuilt into a [`DayPlan`] the day-bar
//!   renderers take as their ghost.
//!
//! The record holds a start and an item per block and nothing else, so the
//! row is **rebuilt** rather than recomputed: a `plan()` re-run at
//! `state.arrival` would use today's runtime state and today's log, so the
//! running block would be reserved at the arrival instant and everything
//! closed since would be missing — which is not "the plan as it stood at
//! arrival" (§12.1).
//!
//! Blocks are sized the way §8.5 sizes one (`est × multiplier`) and clipped
//! at the next recorded start; the minutes between two blocks — breaks,
//! routines and walls the record does not name — stay empty rather than being
//! painted as work.
//!
//! It lives in `cli/` because `.tm/arrival_plan.json` is the CLI's sidecar,
//! and both frontends read it here: `tm plan` writes the ghost into
//! `day/<date>.svg`, the TUI draws it under the day bar (§12.1: "the same
//! renderer writes `day/<date>.svg`").

use chrono::{DateTime, Duration, NaiveTime};
use chrono_tz::Tz;

use tm_core::capacity;
use tm_core::config::Config;
use tm_core::energy::{self, Model};
use tm_core::horizon::MIN_REMAINING_MIN;
use tm_core::model::Id;
use tm_core::planner::{DayPlan, SegFlags, SegKind, Segment};
use tm_core::store::{RuntimeState, Store};
use tm_core::tree::Tree;

use super::ctx::{Ctx, ARRIVAL_PLAN_PATH};
use super::day::ArrivalPlan;

/// One block start of `.tm/arrival_plan.json` — the record `tm arrive`
/// writes of the plan the day started with (§12.1's ghost row, and §11's
/// adherence denominator).
///
/// Defined in [`crate::tui::app`] so that everything under `tui/` stays free
/// of `crate::cli` (§17 M6's snapshot tests pull those modules in by path).
pub use crate::tui::app::ArrivalBlock as Block;

/// `.tm/arrival_plan.json` for **today**. Empty when there is no record, when
/// it is unreadable, or when it is for another day (§10.2: the day rolls).
pub fn blocks(ctx: &Ctx) -> Vec<Block> {
    let Ok(text) = ctx.store.read_text(ARRIVAL_PLAN_PATH) else {
        return Vec::new();
    };
    let Ok(record) = serde_json::from_str::<ArrivalPlan>(&text) else {
        return Vec::new();
    };
    if record.date != ctx.today.to_string() {
        return Vec::new();
    }
    record
        .blocks
        .iter()
        .filter_map(|b| {
            Some(Block {
                start: NaiveTime::parse_from_str(&b.start, "%H:%M").ok()?,
                id: b.id.as_deref().map(Id::new),
            })
        })
        .collect()
}

/// The recorded starts as a [`DayPlan`] — §12.1's ghost row.
///
/// `window` and `budget_blocks` come from the runtime state when it has them
/// (the arrival computed both, §8.1), else from `fallback`. `None` when the
/// day has no record: without an arrival there is no plan the day started
/// with, and the renderers draw the placeholder row instead.
pub fn plan(
    blocks: &[Block],
    cfg: &Config,
    model: &Model,
    tree: &Tree,
    state: &RuntimeState,
    fallback: &DayPlan,
) -> Option<DayPlan> {
    if blocks.is_empty() {
        return None;
    }
    let date = state.date.unwrap_or(fallback.date);
    let local = |t: NaiveTime| capacity::local_dt(cfg.tz, date, t);
    let starts: Vec<DateTime<Tz>> = blocks.iter().map(|b| local(b.start)).collect();
    let mut segments: Vec<Segment> = Vec::new();
    for (i, block) in blocks.iter().enumerate() {
        let start = starts[i];
        let planned = block_minutes(block.id.as_ref(), cfg, model, tree);
        let mut end = start + Duration::minutes(i64::from(planned));
        if let Some(next) = starts.get(i + 1) {
            end = end.min(*next);
        }
        if end <= start {
            continue;
        }
        segments.push(Segment {
            start,
            end,
            kind: SegKind::Block,
            energy: block.id.as_ref().and_then(|id| tree.get(id)).map(|i| i.ci),
            item: block.id.clone(),
            instance: None,
            flags: SegFlags {
                ghost: true,
                planned_min: Some(planned),
                ..SegFlags::default()
            },
        });
    }
    Some(DayPlan {
        date,
        window: match state.window {
            Some((from, to)) => (local(from), local(to)),
            None => fallback.window,
        },
        budget_blocks: state.budget.unwrap_or(fallback.budget_blocks),
        segments,
        diagnostics: Default::default(),
        priorities: Vec::new(),
    })
}

/// How long a ghost block ran for: `est × multiplier`, the way §8.5 sizes a
/// block, falling back to one block.
fn block_minutes(id: Option<&Id>, cfg: &Config, model: &Model, tree: &Tree) -> u32 {
    let block_min = cfg.block_min();
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
    let multiplier = energy::duration_multiplier(model, item.ci, &tree.tags_effective(id));
    energy::planned_minutes(est, multiplier).max(MIN_REMAINING_MIN)
}
