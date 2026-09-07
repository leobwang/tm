//! A [`DayPlan`] as text and as the day bar (tm-spec-v1.md §4.3, §12.1).
//!
//! # API overview
//!
//! * [`timeline`] — the body of the `<!-- tm:plan … -->` section of the day
//!   file: one row per segment, `HH:MM  ci  pN  mark  title  @parent  est
//!   (actual)  note`, with §4.3's marks (`✓ ▶ ↓ ⚠ ⏰ ○ · 🌙`).
//! * [`svg`] — `day/<date>.svg`: one `<rect>` with a `<title>` per segment,
//!   so VS Code's preview shows the tooltip §12.1 describes.
//! * [`rows`] — the same rows as data, which `tm now` and `tm plan --diff`
//!   reuse.
//!
//! **Stand-in.** §1.2 puts this renderer in `tm-core/src/emit.rs`, which is
//! still a stub while another milestone lands; the CLI renders locally so
//! `tm plan` can write its section today. The row shape is §4.3's, so moving
//! the code into `emit.rs` later is a lift, not a rewrite.

use std::fmt::Write as _;

use chrono::{DateTime, Timelike};
use chrono_tz::Tz;
use serde::Serialize;
use tm_core::config::Config;
use tm_core::model::Id;
use tm_core::planner::{DayPlan, SegKind, Segment};
use tm_core::tree::Tree;

use super::out::fmt_dur;

/// One rendered row of the timeline.
#[derive(Clone, Debug, Serialize)]
pub struct Row {
    /// `HH:MM`.
    pub time: String,
    /// Predicted slot energy, when the segment has one.
    pub energy: Option<u8>,
    /// The §4.3 mark (`✓`, `▶`, `⏰`, …).
    pub mark: String,
    /// What the row says.
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

/// §4.3's mark for a segment.
fn mark(seg: &Segment) -> &'static str {
    if seg.flags.done {
        return "✓";
    }
    if seg.flags.current {
        return "▶";
    }
    if seg.flags.hot {
        return "⚠";
    }
    match seg.kind {
        SegKind::Wall => "⏰",
        SegKind::Optional => "○",
        SegKind::Break | SegKind::Routine | SegKind::Sleep => "·",
        SegKind::WindDown => "🌙",
        SegKind::Lost => "×",
        _ => " ",
    }
}

/// The title a segment shows.
fn title_of(seg: &Segment, tree: &Tree) -> String {
    if let Some(id) = &seg.item {
        if let Some(item) = tree.get(id) {
            return item.title.clone();
        }
        return id.to_string();
    }
    match &seg.kind {
        SegKind::Batch(ids) => {
            let titles: Vec<String> = ids
                .iter()
                .map(|i| {
                    tree.get(i)
                        .map(|it| it.title.clone())
                        .unwrap_or_else(|| i.to_string())
                })
                .collect();
            format!("batch: {} ({})", titles.join(" · "), ids.len())
        }
        SegKind::Break => "break".to_string(),
        SegKind::Rest => "rest".to_string(),
        SegKind::WindDown => "wind-down".to_string(),
        SegKind::Sleep => "sleep".to_string(),
        SegKind::Lost => "lost".to_string(),
        other => kind_name(other).to_string(),
    }
}

/// The rows of a plan, in start order.
pub fn rows(plan: &DayPlan, tree: &Tree, cfg: &Config) -> Vec<Row> {
    let block_min = cfg.block_min().max(1);
    plan.segments
        .iter()
        .map(|seg| {
            let mut text = title_of(seg, tree);
            if let Some(id) = &seg.item {
                if let Some(parent) = tree.get(id).and_then(|i| i.parent.clone()) {
                    let _ = write!(text, "  {}", parent.token());
                }
            }
            match (seg.flags.planned_min, seg.flags.multiplier) {
                (Some(min), Some(m)) if (m - 1.0).abs() > 0.005 => {
                    let _ = write!(text, "  {}×{m:.1}", blocks(min, block_min));
                }
                (Some(min), _) => {
                    let _ = write!(text, "  {}", blocks(min, block_min));
                }
                _ => {
                    if matches!(
                        seg.kind,
                        SegKind::Break | SegKind::Routine | SegKind::Wall | SegKind::Optional
                    ) {
                        let _ = write!(text, " {}", fmt_dur(seg.minutes()));
                    }
                }
            }
            if seg.flags.underused {
                text.push_str("     ↓");
            }
            if let Some(note) = &seg.flags.note {
                let _ = write!(text, "    {note}");
            }
            Row {
                time: hhmm(seg.start),
                energy: seg.energy,
                mark: mark(seg).to_string(),
                text,
                item: seg.item.clone(),
                kind: kind_name(&seg.kind).to_string(),
            }
        })
        .collect()
}

/// Minutes as blocks when they divide evenly, else as a duration.
fn blocks(minutes: u32, block_min: u32) -> String {
    if minutes >= block_min && minutes.is_multiple_of(block_min) {
        format!("{}b", minutes / block_min)
    } else {
        fmt_dur(minutes)
    }
}

/// The body of the day file's `tm:plan` section (§4.3).
pub fn timeline(plan: &DayPlan, tree: &Tree, cfg: &Config) -> String {
    let mut out = String::new();
    for row in rows(plan, tree, cfg) {
        let energy = row
            .energy
            .map(|e| e.to_string())
            .unwrap_or_else(|| "·".to_string());
        let _ = writeln!(out, "{}  {} {}  {}", row.time, energy, row.mark, row.text);
    }
    for note in &plan.diagnostics.notes {
        let _ = writeln!(out, "· {note}");
    }
    out
}

/// XML-escape a title for the SVG.
fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// The colour of a segment: the project hue for work, greys for the rest
/// (§12.1).
fn colour(seg: &Segment, tree: &Tree, cfg: &Config) -> String {
    let palette = &cfg.tui.palette;
    match seg.kind {
        SegKind::Block | SegKind::Batch(_) => {
            let root = seg
                .item
                .as_ref()
                .map(|id| tree.root(id))
                .unwrap_or_else(|| Id::new(""));
            if palette.is_empty() {
                return "#4363d8".to_string();
            }
            let h = root
                .as_str()
                .bytes()
                .fold(0u32, |a, b| a.wrapping_mul(31).wrapping_add(u32::from(b)));
            palette[(h as usize) % palette.len()].clone()
        }
        SegKind::Wall => "#333333".to_string(),
        SegKind::Break => "#d9d9d9".to_string(),
        SegKind::Routine | SegKind::Sleep => "#9e9e9e".to_string(),
        SegKind::Optional => "#bfef45".to_string(),
        SegKind::Lost => "#f58231".to_string(),
        SegKind::WindDown => "#6a6a6a".to_string(),
        SegKind::Rest => "#f2f2f2".to_string(),
    }
}

/// `day/<date>.svg`: the day bar of §12.1, one `<rect>` and `<title>` per
/// segment.
pub fn svg(plan: &DayPlan, tree: &Tree, cfg: &Config) -> String {
    const WIDTH: f64 = 960.0;
    const HEIGHT: f64 = 48.0;
    let (from, to) = plan.window;
    let (from, to) = match plan.segments.first() {
        Some(first) => (
            from.min(first.start),
            to.max(plan.segments.iter().map(|s| s.end).max().unwrap_or(to)),
        ),
        None => (from, to),
    };
    let span = (to - from).num_minutes().max(1) as f64;
    let mut out = String::new();
    let _ = writeln!(
        out,
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{WIDTH}\" height=\"{HEIGHT}\" \
         viewBox=\"0 0 {WIDTH} {HEIGHT}\" role=\"img\">"
    );
    let _ = writeln!(
        out,
        "  <title>{} · {}–{}</title>",
        plan.date,
        hhmm(from),
        hhmm(to)
    );
    let _ = writeln!(
        out,
        "  <rect x=\"0\" y=\"0\" width=\"{WIDTH}\" height=\"{HEIGHT}\" fill=\"#ffffff\"/>"
    );
    for seg in &plan.segments {
        let x = ((seg.start - from).num_minutes() as f64 / span * WIDTH).clamp(0.0, WIDTH);
        let w = ((seg.end - seg.start).num_minutes() as f64 / span * WIDTH).max(1.0);
        let label = format!(
            "{}–{} {} {}",
            hhmm(seg.start),
            hhmm(seg.end),
            kind_name(&seg.kind),
            title_of(seg, tree)
        );
        let _ = writeln!(
            out,
            "  <rect x=\"{x:.1}\" y=\"8\" width=\"{w:.1}\" height=\"32\" fill=\"{}\"><title>{}</title></rect>",
            colour(seg, tree, cfg),
            esc(&label)
        );
    }
    let _ = writeln!(out, "</svg>");
    out
}
