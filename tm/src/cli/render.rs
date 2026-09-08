//! A [`DayPlan`] as the CLI writes it (tm-spec-v1.md §4.3, §12.1).
//!
//! # API overview
//!
//! * [`timeline`] — the body of the `<!-- tm:plan … -->` section of the day
//!   file: §4.3's `HH:MM  ci  pN  mark  title  @parent  est  (actual)  note`
//!   grid, with the `───  window ends HH:MM` divider.
//! * [`svg`] — `day/<date>.svg`: §12.1's day bar, 24 h from wake to wake,
//!   with the ghost row beneath.
//! * [`rows`] — the same rows as data, which `tm plan --json` and `tm now`
//!   reuse.
//! * [`kind_name`] — a [`SegKind`] as the word the JSON and
//!   `.tm/last_plan.json` use.
//!
//! §1.2 puts the renderer itself in `tm-core/src/emit.rs`, and that is where
//! it is: everything here delegates, so `tm plan`, `tm tui` and the M4
//! snapshots print one text for one [`DayPlan`].

use chrono::{DateTime, Timelike};
use chrono_tz::Tz;
use serde::Serialize;
use tm_core::config::Config;
use tm_core::emit;
use tm_core::model::Id;
use tm_core::planner::{DayPlan, SegKind};
use tm_core::tree::Tree;

/// Pixels of `day/<date>.svg` (§12.1's bar is a wide, short strip; the ghost
/// row is drawn inside this height).
const SVG_WIDTH: u32 = 960;
/// Height in pixels.
const SVG_HEIGHT: u32 = 64;
/// Cells the day bar is cut into for the file. One cell is 15 minutes over
/// the 24 h span, which is finer than any segment boundary the planner emits.
const SVG_COLS: usize = 96;

/// One rendered row of the timeline.
#[derive(Clone, Debug, Serialize)]
pub struct Row {
    /// `HH:MM`.
    pub time: String,
    /// Predicted slot energy, when the segment has one.
    pub energy: Option<u8>,
    /// The §4.3 mark (`✓`, `▶`, `⚠`), or empty.
    pub mark: String,
    /// The whole §4.3 row, exactly as the day file has it.
    pub text: String,
    /// The item, when the segment has one.
    pub item: Option<Id>,
    /// The segment kind, lowercased.
    pub kind: String,
}

/// `HH:MM` in `cfg.tz`.
fn hhmm(t: DateTime<Tz>) -> String {
    format!("{:02}:{:02}", t.hour(), t.minute())
}

/// The `SegKind` as a word (`block`, `batch`, `break`, …).
pub fn kind_name(kind: &SegKind) -> &'static str {
    match kind {
        SegKind::Block => "block",
        SegKind::Batch(_) => "batch",
        SegKind::Break => "break",
        SegKind::Routine => "routine",
        SegKind::Wall => "wall",
        SegKind::Rest => "rest",
        SegKind::Optional => "optional",
        SegKind::WindDown => "wind-down",
        SegKind::Sleep => "sleep",
        SegKind::Lost => "lost",
    }
}

/// The rows of a plan, in start order — one per segment, each carrying the
/// §4.3 row `emit` writes into the day file.
pub fn rows(plan: &DayPlan, tree: &Tree, cfg: &Config) -> Vec<Row> {
    plan.segments
        .iter()
        .map(|seg| Row {
            time: hhmm(seg.start),
            energy: seg.energy,
            mark: emit::mark_of(seg).to_string().trim().to_string(),
            text: emit::render_segment_row(seg, plan, tree, cfg),
            item: seg.item.clone(),
            kind: kind_name(&seg.kind).to_string(),
        })
        .collect()
}

/// The body of the day file's `tm:plan` section (§4.3) — the timeline, and
/// only the timeline. §8.2 step 8's diagnostics and §11's warnings go to
/// `tm plan`'s own output ([`diagnostics`]), not into the file.
pub fn timeline(plan: &DayPlan, tree: &Tree, cfg: &Config, now: DateTime<Tz>) -> String {
    emit::render_plan_section(plan, tree, cfg, now).1
}

/// §8.2 step 8's diagnostics and §11's warnings — the "plan honesty {h} —
/// planned above a realistic budget" line among them — as `tm plan` prints
/// them under the timeline.
pub fn diagnostics(plan: &DayPlan, tree: &Tree, cfg: &Config) -> Vec<String> {
    emit::render_diagnostics(&plan.diagnostics, tree, cfg)
}

/// `day/<date>.svg`: §12.1's day bar — 24 h from wake to wake, the log left
/// of the cursor and the plan right of it, the ghost row beneath.
pub fn svg(
    plan: &DayPlan,
    ghost: Option<&DayPlan>,
    tree: &Tree,
    cfg: &Config,
    wake: DateTime<Tz>,
    now: DateTime<Tz>,
) -> String {
    let bar = emit::daybar_cells(plan, ghost, tree, cfg, SVG_COLS, wake, now);
    emit::render_svg(&bar, plan, cfg, SVG_WIDTH, SVG_HEIGHT)
}
