//! A [`DayPlan`] as the CLI writes it (tm-spec-v1.md §4.3, §12.1).
//!
//! # API overview
//!
//! * [`timeline`] — the body of the `<!-- tm:plan … -->` section of the day
//!   file: §4.3's `HH:MM  ci  pN  mark  title  @parent  est  (actual)  note`
//!   grid, with the `───  window ends HH:MM` divider.
//! * [`svg`] — `day/<date>.svg`: §12.1's day bar, 24 h from wake to wake,
//!   with the ghost row beneath.
//! * [`rows`] — the same rows as data, which `tm plan --json` emits. (`tm now`
//!   selects from `emit::plan_rows` directly; this sentence said it "reuses"
//!   [`rows`] and it never did — `tm now` had its own renderer until W-23.)
//! The `SegKind` word the JSON and `.tm/last_plan.json` use is
//! [`tm_core::dayplan::kind_label`]. This module declared a second, byte-for-byte
//! identical kind_name until W-23 (AGENTS §5.3). A deleted name loses its
//! backticks, here as in the README (gap 1313).
//!
//! §1.2 puts the renderer itself in `tm-core/src/emit.rs`, and that is where
//! it is: everything here delegates, so `tm plan`, `tm tui` and the M4
//! snapshots print one text for one [`DayPlan`].

use chrono::DateTime;
use chrono_tz::Tz;
use serde::Serialize;
use tm_core::config::Config;
use tm_core::emit;
use tm_core::model::Id;
use tm_core::dayplan::{self, DayPlan};
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

/// `HH:MM` — `tm_core::dayplan::fmt_clock` under this file's own name (AGENTS
/// §5.3, W-23: a byte-for-byte copy of it stood here).
use tm_core::dayplan::fmt_clock as hhmm;

/// The rows of a plan, in start order — one per segment, each carrying the
/// §4.3 row `emit` writes into the day file.
///
/// **Zipped by position** (README gap **1197**): `emit::plan_rows` answers one
/// row per segment in the same order, and `rows[i].text` is `segments[i]`'s row
/// because it is taken at `i` — not because it was looked up by anything the row
/// says. Two items with one title give byte-identical rows, so a by-value
/// lookup here would have more than one witness. This used to call
/// emit::render_segment_row(seg, …), which rebuilt the priority map once per
/// row and was the by-value form; `plan_rows` replaced it and it is gone.
pub fn rows(plan: &DayPlan, tree: &Tree, cfg: &Config) -> Vec<Row> {
    plan.segments
        .iter()
        .zip(emit::plan_rows(plan, tree, cfg, &emit::Layout::default()))
        .map(|(seg, text)| Row {
            time: hhmm(seg.start),
            energy: seg.energy,
            mark: emit::mark_of(seg).to_string().trim().to_string(),
            text,
            item: seg.item.clone(),
            kind: dayplan::kind_label(&seg.kind).to_string(),
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
