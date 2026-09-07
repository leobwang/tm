//! Emit — a [`DayPlan`] rendered for humans: the generated markdown section of
//! the day file (§4.3), the day-bar geometry the TUI widget and the SVG share
//! (§12.1), the hand-written SVG (§17.2), `tm now` (§13), the diagnostics
//! lines (§8.2 step 8, §11) and the day-bar legend (§11 "Energy mix").
//!
//! Everything here is pure: it reads a plan, a [`Tree`] and a [`Config`] and
//! returns `String`s and geometry. No I/O, no clock — `now` and `wake` are
//! parameters (§17.2).
//!
//! # API overview
//!
//! **Timeline (§4.3)**
//! * [`render_plan_section`]`(plan, tree, cfg, now) -> (info, body)` — `info`
//!   is the `10:42` of `<!-- tm:plan start 10:42 -->` (pass it to
//!   `Store::replace_generated_stamped`), `body` is the rows, one per line,
//!   newline-terminated.
//! * [`render_plan_section_with`] — the same with an explicit [`Layout`]
//!   (title width).
//! * [`svg_link`] / [`svg_file_name`] — the `![day](2026-09-07.svg)` line.
//!
//! **Day bar (§12.1)**
//! * [`daybar_cells`]`(plan, ghost, tree, cfg, cols, wake, now) -> DayBar` —
//!   24 h from wake to wake in `cols` cells; [`Cell`] carries the project hue,
//!   the `ci` brightness, a [`CellStyle`], the tooltip and the segment index.
//!   [`Cell::rgb`] turns that into a colour. [`DayBar`] also carries the
//!   geometry (`wake`, `cols`, `span_min`, `cursor_col`) so the terminal
//!   widget and the SVG agree.
//! * [`hue_index`] — FNV-1a of the root id into `cfg.tui.palette`.
//!
//! **SVG (§17.2)**
//! * [`render_svg`]`(bar, plan, cfg, width_px, height_px) -> String` — one
//!   `<rect>` per segment with a `<title>` child, hatched `<pattern>`s for
//!   Lost (orange) and Interrupt (red), a dotted stroke for optionals, hour
//!   ticks, the cursor line and the ghost row beneath.
//!
//! **Text surfaces**
//! * [`render_now`]`(plan, tree, now) -> String` — `tm now`: the current
//!   segment with elapsed/remaining, then the next three.
//! * [`render_diagnostics`]`(diag, tree, cfg) -> Vec<String>` and
//!   [`render_banners`]`(plan, tree, cfg) -> Vec<String>` (§7.3's "needs 8b,
//!   5b available by Fri", which needs the [`Prio`](crate::priority::Prio)
//!   numbers).
//! * [`legend`]`(plan, tree) -> EnergyMix` — §11's energy mix, plus
//!   [`EnergyMix::line`] for the bar legend.
//!
//! # The row format (§4.3)
//!
//! ```text
//! HH:MM  ci  pN  mark  title  @parent  est  (actual)  note
//! 07:00  5 p1 ✓ Read ch.6 §1–2               @m3  1b  (67m)
//! ```
//!
//! Columns are fixed, counted in characters, every field left-aligned and
//! padded to at least its width (a longer value pushes the rest of the row
//! right rather than being truncated — only the title is truncated):
//!
//! | column | offset | width | content |
//! |---|---|---|---|
//! | time | 0 | 5 | `HH:MM` |
//! | ci | 7 | 2 | slot energy (else the item's `ci`) + `↓`; or the row glyph `·` `⏰` `○` `🌙` |
//! | p | 9 | 2 | `p3` — `Block`/`Batch` rows only |
//! | mark | 12 | 1 | `✓` done · `▶` current · `⚠` HOT |
//! | title | 14 | 27 ([`Layout::title_w`]) | truncated with `…` |
//! | @parent | 43 | 3 | the item's written `@parent` |
//! | est | 48 | 2 | `1b`, `2b×1.6`, `20m` |
//! | (actual) | 52 | 1 | `(67m)`, on finished segments |
//! | note | 55 | — | `due today`, `↓ slot 4, item 3` |
//!
//! Gaps are two spaces except around the mark (one on each side); trailing
//! blanks are trimmed. A `───     window ends 16:00` divider row is inserted
//! where the budget runs out (see [`render_plan_section`]).
//!
//! # Differences from the §4.3 example
//!
//! The example in the spec is hand-aligned and internally inconsistent; three
//! of its rows cannot all hold at once. This renderer keeps every column at a
//! fixed offset, which reproduces the fullest rows byte for byte
//! (`07:00`, `08:00`, `09:20`, `21:30`) and differs from the others as follows:
//!
//! 1. **Title offset.** The example starts the title at column 14 on rows with
//!    a mark (`✓ Read ch.6 §1–2`) and on the `⏰`/`🌙` rows, but at column 15
//!    on rows without one (`lunch 30m`, `Claude Code drafts tests`). Column 14
//!    always wins here, so those rows lose one space.
//! 2. **Estimate column.** When an item has no `@parent` the example slides
//!    the estimate left into the parent column (`⏰ … 1h` at 43); this
//!    renderer keeps it at 48 so the column reads down the page.
//! 3. **Actual column.** The `09:00` break's `(24m)` sits at 48 in the example
//!    (the estimate column); here it sits in the actual column at 52.
//!
//! # Conventions this renderer assumes of a [`DayPlan`]
//!
//! * A finished segment (`flags.done`) spans what actually happened — §12.1
//!   asks the bar to draw the log left of the cursor and the plan right of it,
//!   and one `DayPlan` carries both — so `(actual)` is the segment's own
//!   length and `flags.planned_min` is what had been set aside for it.
//! * `flags.planned_min` / `flags.multiplier` are the §8.5 display pair:
//!   `2b×1.6` is `planned_min = 192`, `multiplier = 1.6`.
//! * A `Wall` segment with no `item` is §9's ad-hoc interruption wall (a
//!   synced wall always has an id), so it draws hatched red.

use std::collections::HashMap;
use std::fmt::Write as _;

use chrono::{DateTime, Duration, NaiveDate, Timelike};
use chrono_tz::Tz;
use serde::Serialize;
use thiserror::Error;

use crate::config::Config;
use crate::model::{Dep, Dur, Id};
use crate::planner::{DayPlan, Diagnostics, SegKind, Segment};
use crate::priority::fmt_blocks;
use crate::tree::Tree;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// The one thing that can be malformed in here: a palette entry.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum EmitError {
    /// A `config.tui.palette` entry that is not `#rrggbb`.
    #[error("bad colour `{0}`: expected #rrggbb")]
    BadColour(String),
}

// ---------------------------------------------------------------------------
// Marks and glyphs (§4.3)
// ---------------------------------------------------------------------------

/// `✓` — the segment is finished.
pub const MARK_DONE: char = '✓';
/// `▶` — the segment running at `now`.
pub const MARK_CURRENT: char = '▶';
/// `⚠` — a `p = 0` item (§7.2).
pub const MARK_HOT: char = '⚠';
/// `↓` — the slot is under-used (§8.2 step 5); sits next to the `ci`.
pub const MARK_UNDERUSED: char = '↓';
/// `·` — routines, breaks, rest, sleep and lost time.
pub const GLYPH_ROUTINE: char = '·';
/// `⏰` — an Interval instance (a wall).
pub const GLYPH_WALL: char = '⏰';
/// `○` — an `optional.md` item.
pub const GLYPH_OPTIONAL: char = '○';
/// `🌙` — the wind-down.
pub const GLYPH_WIND_DOWN: char = '🌙';
/// The window-end divider row's glyph.
pub const DIVIDER: &str = "───";

// ---------------------------------------------------------------------------
// Column widths (§4.3)
// ---------------------------------------------------------------------------

/// `HH:MM`.
pub const TIME_W: usize = 5;
/// Slot energy plus the `↓` marker.
pub const CI_W: usize = 2;
/// `p3`.
pub const P_W: usize = 2;
/// One mark character.
pub const MARK_W: usize = 1;
/// `@m3`.
pub const PARENT_W: usize = 3;
/// `1b`.
pub const EST_W: usize = 2;
/// `(67m)` — one, so an empty actual costs a single column.
pub const ACTUAL_W: usize = 1;
/// The default title width; see [`Layout`].
pub const DEFAULT_TITLE_W: usize = 27;
/// The character offset the title starts at.
pub const TITLE_COL: usize = TIME_W + 2 + CI_W + P_W + 1 + MARK_W + 1;

/// How wide the timeline's title column is.
///
/// Everything else is fixed (§4.3 puts `@parent` at column 43, which is
/// [`TITLE_COL`] + [`DEFAULT_TITLE_W`] + 2); a narrower terminal pane can ask
/// for a narrower title.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    /// Characters available to the title; longer titles are cut with `…`.
    pub title_w: usize,
}

impl Default for Layout {
    fn default() -> Self {
        Layout {
            title_w: DEFAULT_TITLE_W,
        }
    }
}

impl Layout {
    /// A layout with the given title width (minimum 4).
    pub fn new(title_w: usize) -> Layout {
        Layout {
            title_w: title_w.max(4),
        }
    }
}

// ---------------------------------------------------------------------------
// Small formatting helpers
// ---------------------------------------------------------------------------

/// Left-align `s` in `w` characters (a longer `s` is returned unchanged).
fn pad(s: &str, w: usize) -> String {
    let n = s.chars().count();
    if n >= w {
        s.to_string()
    } else {
        let mut out = String::with_capacity(s.len() + (w - n));
        out.push_str(s);
        for _ in n..w {
            out.push(' ');
        }
        out
    }
}

/// Truncate `s` to `w` characters, marking the cut with `…`.
fn truncate(s: &str, w: usize) -> String {
    if s.chars().count() <= w {
        return s.to_string();
    }
    let keep = w.saturating_sub(1);
    let mut out: String = s.chars().take(keep).collect();
    out.push('…');
    out
}

/// `HH:MM` in the plan's zone.
fn hhmm(t: &DateTime<Tz>) -> String {
    format!("{:02}:{:02}", t.hour(), t.minute())
}

/// Minutes as the shortest natural unit: `20m`, `1h`, `1h22m`, `8h30m`.
fn fmt_dur(minutes: u32) -> String {
    Dur::canonical(minutes).to_string()
}

/// Minutes between two instants, never negative.
fn minutes_between(from: &DateTime<Tz>, to: &DateTime<Tz>) -> u32 {
    (*to - *from).num_minutes().max(0) as u32
}

// ---------------------------------------------------------------------------
// Per-segment display values
// ---------------------------------------------------------------------------

/// Does this kind print its `ci` and `p`, or a glyph?
fn is_work(kind: &SegKind) -> bool {
    matches!(kind, SegKind::Block | SegKind::Batch(_))
}

/// The glyph a non-work row puts in the `ci` column.
fn glyph_of(kind: &SegKind) -> char {
    match kind {
        SegKind::Wall => GLYPH_WALL,
        SegKind::Optional => GLYPH_OPTIONAL,
        SegKind::WindDown => GLYPH_WIND_DOWN,
        _ => GLYPH_ROUTINE,
    }
}

/// The estimate the row shows, as written where possible (§8.5's `2b×1.6`).
///
/// 1. the item's own estimate (`est:`'s original, else `est:`, else `dur:`),
/// 2. else `planned_min` in blocks,
/// 3. else, for walls and optionals, the segment's own length;
///
/// times `×multiplier` when the planner sized the block with one.
fn est_cell(seg: &Segment, tree: &Tree, cfg: &Config) -> String {
    if !matches!(
        seg.kind,
        SegKind::Block | SegKind::Batch(_) | SegKind::Wall | SegKind::Optional
    ) {
        return String::new();
    }
    let item = seg.item.as_ref().and_then(|id| tree.get(id));
    let written = item.and_then(|i| i.est_original.or(i.est).or(i.dur));
    let base = match (&written, seg.flags.planned_min) {
        (Some(d), _) => d.to_string(),
        (None, Some(p)) => {
            let unscaled = match seg.flags.multiplier {
                Some(m) if m > 0.0 => (f64::from(p) / m).round() as u32,
                _ => p,
            };
            fmt_blocks(unscaled, cfg.block_min())
        }
        (None, None) if matches!(seg.kind, SegKind::Wall | SegKind::Optional) => {
            fmt_dur(seg.minutes())
        }
        (None, None) => String::new(),
    };
    if base.is_empty() {
        return base;
    }
    match seg.flags.multiplier {
        Some(m) if (m - 1.0).abs() >= 0.005 => {
            format!("{base}×{}", crate::energy::fmt_multiplier(m))
        }
        _ => base,
    }
}

/// The title cell: the item's title, or the row's own words for the kinds that
/// carry their duration in the title (`break 20m`, `lunch 30m`).
fn title_cell(seg: &Segment, tree: &Tree, cfg: &Config) -> String {
    let planned = seg.flags.planned_min.unwrap_or_else(|| seg.minutes());
    let name = |fallback: &str| -> String {
        seg.item
            .as_ref()
            .and_then(|id| tree.get(id))
            .map(|i| i.title.clone())
            .filter(|t| !t.is_empty())
            .unwrap_or_else(|| fallback.to_string())
    };
    match &seg.kind {
        SegKind::Batch(ids) => {
            let names: Vec<String> = ids
                .iter()
                .map(|id| {
                    tree.get(id)
                        .map(|i| i.title.clone())
                        .filter(|t| !t.is_empty())
                        .unwrap_or_else(|| id.to_string())
                })
                .collect();
            format!("batch: {} ({})", names.join(" · "), names.len())
        }
        SegKind::Break => format!("break {}", fmt_dur(planned)),
        SegKind::Routine | SegKind::Sleep => {
            format!("{} {}", name("routine"), fmt_dur(planned))
        }
        SegKind::Rest => format!("rest {}", fmt_dur(planned)),
        SegKind::Lost => format!("lost {}", fmt_dur(planned)),
        SegKind::WindDown => format!(
            "wind-down · bed {:02}:{:02}",
            cfg.day.bed.hour(),
            cfg.day.bed.minute()
        ),
        SegKind::Block | SegKind::Optional | SegKind::Wall => name("—"),
    }
}

/// `@m3` — the item's written parent, not its root.
fn parent_cell(seg: &Segment, tree: &Tree) -> String {
    seg.item
        .as_ref()
        .and_then(|id| tree.get(id))
        .and_then(|i| i.parent.as_ref())
        .map(|r| r.token())
        .unwrap_or_default()
}

/// The id a segment is keyed by: its own item, or — for a batch, which has no
/// single item — its first member, the key it was assigned at (§7.5).
fn key_id(seg: &Segment) -> Option<&Id> {
    match &seg.kind {
        SegKind::Batch(ids) => seg.item.as_ref().or_else(|| ids.first()),
        _ => seg.item.as_ref(),
    }
}

/// The mark column: done beats current beats hot.
fn mark_of(seg: &Segment) -> char {
    if seg.flags.done {
        MARK_DONE
    } else if seg.flags.current {
        MARK_CURRENT
    } else if seg.flags.hot {
        MARK_HOT
    } else {
        ' '
    }
}

// ---------------------------------------------------------------------------
// The generated day-file section (§4.3)
// ---------------------------------------------------------------------------

/// Render the `<!-- tm:plan … -->` block of the day file (§4.3).
///
/// Returns `(info, body)`: `info` is `now` as `HH:MM` — the stamp on the start
/// marker, for `Store::replace_generated_stamped` — and `body` is the rows,
/// each newline-terminated.
///
/// A `───     window ends HH:MM` divider is inserted where the day stops being
/// budgeted work: at the end of the `Block`/`Batch` segment whose minutes take
/// the running total to `budget_blocks × block_min`, or at the window end,
/// whichever comes first. The row is placed before the first segment that
/// starts at or after that instant, and carries that instant's time with the
/// window's own end in its text (§4.3 shows `15:10  ───  window ends 16:00`).
pub fn render_plan_section(
    plan: &DayPlan,
    tree: &Tree,
    cfg: &Config,
    now: DateTime<Tz>,
) -> (String, String) {
    render_plan_section_with(plan, tree, cfg, now, &Layout::default())
}

/// [`render_plan_section`] with an explicit title width.
pub fn render_plan_section_with(
    plan: &DayPlan,
    tree: &Tree,
    cfg: &Config,
    now: DateTime<Tz>,
    layout: &Layout,
) -> (String, String) {
    let prios: HashMap<&Id, u8> = plan.priorities.iter().map(|(id, p)| (id, p.p)).collect();
    let divider_at = divider_instant(plan, cfg);
    let mut body = String::new();
    let mut divider_done = divider_at.is_none();
    for seg in &plan.segments {
        if let Some(at) = divider_at {
            if !divider_done && seg.start >= at {
                body.push_str(&divider_row(&at, &plan.window.1));
                body.push('\n');
                divider_done = true;
            }
        }
        body.push_str(&render_row(seg, tree, cfg, &prios, layout));
        body.push('\n');
    }
    if let (false, Some(at)) = (divider_done, divider_at) {
        body.push_str(&divider_row(&at, &plan.window.1));
        body.push('\n');
    }
    (hhmm(&now), body)
}

/// Where the budget runs out, or the window ends — whichever is earlier.
fn divider_instant(plan: &DayPlan, cfg: &Config) -> Option<DateTime<Tz>> {
    let budget_min = plan.budget_blocks.saturating_mul(cfg.block_min());
    let mut used = 0u32;
    let mut spent: Option<DateTime<Tz>> = None;
    for seg in &plan.segments {
        if is_work(&seg.kind) {
            // The minutes the day actually spends, not what was set aside for
            // the item: an overrunning block eats the budget it overran into.
            used = used.saturating_add(seg.minutes());
            if budget_min > 0 && used >= budget_min {
                spent = Some(seg.end);
                break;
            }
        }
    }
    let end = plan.window.1;
    match spent {
        Some(t) if t < end => Some(t),
        _ => {
            // Only worth a row when something is planned past the window.
            if plan.segments.iter().any(|s| s.start >= end) {
                Some(end)
            } else {
                spent
            }
        }
    }
}

/// `15:10  ───     window ends 16:00`.
fn divider_row(at: &DateTime<Tz>, window_end: &DateTime<Tz>) -> String {
    let head = format!("{}  {}", hhmm(at), DIVIDER);
    let mut row = pad(&head, TITLE_COL);
    row.push_str(&format!("window ends {}", hhmm(window_end)));
    row
}

/// One timeline row (§4.3).
fn render_row(
    seg: &Segment,
    tree: &Tree,
    cfg: &Config,
    prios: &HashMap<&Id, u8>,
    layout: &Layout,
) -> String {
    let item = seg.item.as_ref().and_then(|id| tree.get(id));
    let work = is_work(&seg.kind);

    let ci_cell = if work {
        let level = seg
            .energy
            .or_else(|| item.map(|i| i.ci))
            .map(|c| c.to_string())
            .unwrap_or_else(|| " ".to_string());
        let down = if seg.flags.underused {
            MARK_UNDERUSED.to_string()
        } else {
            String::new()
        };
        format!("{level}{down}")
    } else {
        glyph_of(&seg.kind).to_string()
    };

    let p_cell = if work {
        key_id(seg)
            .and_then(|id| prios.get(id))
            .map(|p| format!("p{p}"))
            .unwrap_or_default()
    } else {
        String::new()
    };

    let title = truncate(&title_cell(seg, tree, cfg), layout.title_w);
    let actual = if seg.flags.done && !matches!(seg.kind, SegKind::Rest) {
        format!("({}m)", seg.minutes())
    } else {
        String::new()
    };

    let mut row = String::with_capacity(80);
    row.push_str(&pad(&hhmm(&seg.start), TIME_W));
    row.push_str("  ");
    row.push_str(&pad(&ci_cell, CI_W));
    row.push_str(&pad(&p_cell, P_W));
    row.push(' ');
    row.push(mark_of(seg));
    row.push(' ');
    row.push_str(&pad(&title, layout.title_w));
    row.push_str("  ");
    row.push_str(&pad(&parent_cell(seg, tree), PARENT_W));
    row.push_str("  ");
    row.push_str(&pad(&est_cell(seg, tree, cfg), EST_W));
    row.push_str("  ");
    row.push_str(&pad(&actual, ACTUAL_W));
    row.push_str("  ");
    row.push_str(seg.flags.note.as_deref().unwrap_or(""));
    row.trim_end().to_string()
}

/// The `![day](2026-09-07.svg)` line that heads a day file.
pub fn svg_link(date: NaiveDate) -> String {
    format!("![day]({})", svg_file_name(date))
}

/// `2026-09-07.svg` — the day bar's file name, next to the day file.
pub fn svg_file_name(date: NaiveDate) -> String {
    format!("{date}.svg")
}

// ---------------------------------------------------------------------------
// Day bar geometry (§12.1)
// ---------------------------------------------------------------------------

/// What a day-bar cell is made of (§12.1).
///
/// `Work` is the only style that takes the project hue; the others have a
/// fixed colour (routines grey, breaks light grey, Lost orange, interruptions
/// red, walls dark, sleep near-black) and the TUI adds the pattern (hatching
/// for Lost/Interrupt, dots for Optional).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum CellStyle {
    /// A `Block` or `Batch`.
    Work,
    /// A window instance (§5.2).
    Routine,
    /// A planned break.
    Break,
    /// Lost or leaked time (§11).
    Lost,
    /// §9's ad-hoc interruption wall.
    Interrupt,
    /// An `optional.md` item.
    Optional,
    /// An Interval instance.
    Wall,
    /// A slot no candidate could take.
    Rest,
    /// Sleep or the wind-down.
    Sleep,
    /// Nothing planned here.
    Empty,
}

impl CellStyle {
    /// The style of a segment: `Wall` without an id is §9's interruption.
    pub fn of(seg: &Segment) -> CellStyle {
        match &seg.kind {
            SegKind::Block | SegKind::Batch(_) => CellStyle::Work,
            SegKind::Break => CellStyle::Break,
            SegKind::Routine => CellStyle::Routine,
            SegKind::Wall => {
                if seg.item.is_none() {
                    CellStyle::Interrupt
                } else {
                    CellStyle::Wall
                }
            }
            SegKind::Rest => CellStyle::Rest,
            SegKind::Optional => CellStyle::Optional,
            SegKind::WindDown | SegKind::Sleep => CellStyle::Sleep,
            SegKind::Lost => CellStyle::Lost,
        }
    }

    /// The fixed colour of every style but [`CellStyle::Work`], which is
    /// tinted by the project hue instead.
    pub fn colour(self) -> (u8, u8, u8) {
        match self {
            CellStyle::Work => (0x88, 0x88, 0x88),
            CellStyle::Routine => (0x8a, 0x8a, 0x8a),
            CellStyle::Break => (0xd2, 0xd2, 0xd2),
            CellStyle::Lost => (0xf5, 0x82, 0x31),
            CellStyle::Interrupt => (0xe6, 0x19, 0x4b),
            CellStyle::Optional => (0x7a, 0x8a, 0x99),
            CellStyle::Wall => (0x33, 0x38, 0x44),
            CellStyle::Rest => (0xe8, 0xe8, 0xe8),
            CellStyle::Sleep => (0x1b, 0x1f, 0x2a),
            CellStyle::Empty => (0xf7, 0xf7, 0xf7),
        }
    }

    /// True for the two hatched styles (§12.1).
    pub fn is_hatched(self) -> bool {
        matches!(self, CellStyle::Lost | CellStyle::Interrupt)
    }
}

/// One cell of the day bar (§12.1).
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Cell {
    /// Index into `cfg.tui.palette` — the hash of the item's root id — or
    /// `None` when the cell has no item.
    pub hue: Option<usize>,
    /// `ci` 0..=5: 0 black … 5 the full palette colour.
    pub brightness: u8,
    /// What kind of time this is.
    pub style: CellStyle,
    /// `title · duration · ci · p · @root`, empty for [`CellStyle::Empty`].
    pub tooltip: String,
    /// Index into `DayPlan::segments`, when the cell has one.
    pub segment: Option<usize>,
}

impl Cell {
    /// An empty cell.
    pub fn empty() -> Cell {
        Cell {
            hue: None,
            brightness: 0,
            style: CellStyle::Empty,
            tooltip: String::new(),
            segment: None,
        }
    }

    /// The cell's colour: the palette hue scaled by `brightness / 5` for
    /// [`CellStyle::Work`] (§12.1's "brightness = ci, 0 black … 5 full"), the
    /// style's own colour otherwise.
    pub fn rgb(&self, cfg: &Config) -> (u8, u8, u8) {
        match (self.style, self.hue) {
            (CellStyle::Work, Some(h)) => {
                let (r, g, b) = palette_rgb(cfg, h);
                let f = f64::from(self.brightness.min(5)) / 5.0;
                (
                    (f64::from(r) * f).round() as u8,
                    (f64::from(g) * f).round() as u8,
                    (f64::from(b) * f).round() as u8,
                )
            }
            _ => self.style.colour(),
        }
    }
}

/// The whole bar: the plan row, the arrival ghost row, and the geometry both
/// the terminal widget and [`render_svg`] measure with (§12.1).
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct DayBar {
    /// One cell per column, wake → wake.
    pub cells: Vec<Cell>,
    /// The plan as it stood at arrival; empty when no ghost was given.
    pub ghost: Vec<Cell>,
    /// The column `now` falls in.
    pub cursor_col: usize,
    /// How many columns the bar has.
    pub cols: usize,
    /// The instant column 0 starts at.
    pub wake: DateTime<Tz>,
    /// The instant the cursor sits at.
    pub now: DateTime<Tz>,
    /// The bar's span in minutes — always 24 h (§12.1).
    pub span_min: u32,
}

impl DayBar {
    /// Minutes per cell (`24 h / cols`).
    pub fn cell_minutes(&self) -> f64 {
        f64::from(self.span_min) / self.cols.max(1) as f64
    }
    /// The column an instant falls in, or `None` when it is off the bar.
    pub fn col_of(&self, t: DateTime<Tz>) -> Option<usize> {
        let m = (t - self.wake).num_seconds() as f64 / 60.0;
        if m < 0.0 || m >= f64::from(self.span_min) {
            return None;
        }
        Some(((m / self.cell_minutes()) as usize).min(self.cols.saturating_sub(1)))
    }
    /// Where an instant sits horizontally in a bar `width` units wide, clamped
    /// to the bar.
    pub fn x_of(&self, t: DateTime<Tz>, width: f64) -> f64 {
        let m = (t - self.wake).num_seconds() as f64 / 60.0;
        (m / f64::from(self.span_min) * width).clamp(0.0, width)
    }
    /// The instant a column starts at.
    pub fn start_of(&self, col: usize) -> DateTime<Tz> {
        self.wake + Duration::seconds((col as f64 * self.cell_minutes() * 60.0).round() as i64)
    }
}

/// FNV-1a of a root id, folded into a palette of `palette_len` colours
/// (§12.1's "hash of root id, from a 12-colour palette").
pub fn hue_index(root: &Id, palette_len: usize) -> usize {
    const FNV_OFFSET: u32 = 0x811c_9dc5;
    const FNV_PRIME: u32 = 0x0100_0193;
    let mut h = FNV_OFFSET;
    for b in root.as_str().as_bytes() {
        h ^= u32::from(*b);
        h = h.wrapping_mul(FNV_PRIME);
    }
    (h as usize) % palette_len.max(1)
}

/// `#rrggbb` → `(r, g, b)`.
pub fn parse_hex_colour(s: &str) -> Result<(u8, u8, u8), EmitError> {
    let hex = s.trim().trim_start_matches('#');
    if hex.len() != 6 || !hex.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(EmitError::BadColour(s.to_string()));
    }
    let v = |i: usize| u8::from_str_radix(&hex[i..i + 2], 16).unwrap_or(0);
    Ok((v(0), v(2), v(4)))
}

/// Palette colour `idx`, mid-grey when the palette is empty or malformed.
pub fn palette_rgb(cfg: &Config, idx: usize) -> (u8, u8, u8) {
    let palette = &cfg.tui.palette;
    if palette.is_empty() {
        return (0x88, 0x88, 0x88);
    }
    parse_hex_colour(&palette[idx % palette.len()]).unwrap_or((0x88, 0x88, 0x88))
}

/// Build the day bar (§12.1).
///
/// One row of `cols` cells covering 24 h from `wake` to `wake` (absolute
/// hours, so a DST day is still 24 h of real time). Each cell takes the
/// segment it overlaps most; left of the cursor a finished (`done`) or `Lost`
/// segment wins the tie, right of it a planned one does, which is what makes
/// the left half the log and the right half the plan.
///
/// `ghost` is the plan as it stood at arrival; without one the ghost row is
/// empty.
pub fn daybar_cells(
    plan: &DayPlan,
    ghost: Option<&DayPlan>,
    tree: &Tree,
    cfg: &Config,
    cols: usize,
    wake: DateTime<Tz>,
    now: DateTime<Tz>,
) -> DayBar {
    let cols = cols.max(1);
    let span_min: u32 = 24 * 60;
    let cell_min = f64::from(span_min) / cols as f64;
    let cursor = {
        let m = (now - wake).num_seconds() as f64 / 60.0;
        if m < 0.0 {
            0
        } else {
            ((m / cell_min) as usize).min(cols - 1)
        }
    };
    let row = |p: &DayPlan| -> Vec<Cell> { cells_of(p, tree, cfg, cols, wake, cell_min, cursor) };
    DayBar {
        cells: row(plan),
        ghost: ghost.map(row).unwrap_or_default(),
        cursor_col: cursor,
        cols,
        wake,
        now,
        span_min,
    }
}

/// One row of cells over one plan.
fn cells_of(
    plan: &DayPlan,
    tree: &Tree,
    cfg: &Config,
    cols: usize,
    wake: DateTime<Tz>,
    cell_min: f64,
    cursor: usize,
) -> Vec<Cell> {
    let mut cells = vec![Cell::empty(); cols];
    for (col, cell) in cells.iter_mut().enumerate() {
        let cs = wake + Duration::seconds((col as f64 * cell_min * 60.0).round() as i64);
        let ce = wake + Duration::seconds(((col + 1) as f64 * cell_min * 60.0).round() as i64);
        let past = col <= cursor;
        let mut best: Option<(usize, i64)> = None;
        for (idx, seg) in plan.segments.iter().enumerate() {
            let from = seg.start.max(cs);
            let to = seg.end.min(ce);
            let overlap = (to - from).num_seconds();
            if overlap <= 0 {
                continue;
            }
            let logged = seg.flags.done || matches!(seg.kind, SegKind::Lost);
            let preferred = if past { logged } else { !logged };
            let score = overlap + if preferred { 1_000_000 } else { 0 };
            if best.is_none_or(|(_, s)| score > s) {
                best = Some((idx, score));
            }
        }
        if let Some((idx, _)) = best {
            *cell = cell_of(&plan.segments[idx], idx, tree, cfg, plan);
        }
    }
    cells
}

/// One cell from one segment.
fn cell_of(seg: &Segment, idx: usize, tree: &Tree, cfg: &Config, plan: &DayPlan) -> Cell {
    let item = key_id(seg).and_then(|id| tree.get(id));
    let style = CellStyle::of(seg);
    let hue = key_id(seg).map(|id| hue_index(&tree.root(id), cfg.tui.palette.len()));
    let brightness = item.map(|i| i.ci).or(seg.energy).unwrap_or(0).min(5);
    Cell {
        hue,
        brightness,
        style,
        tooltip: tooltip(seg, tree, cfg, plan),
        segment: Some(idx),
    }
}

/// The name a tooltip leads with: the item's own title (the duration follows
/// it as its own field), or the row's word for the kinds that have no item.
fn tooltip_name(seg: &Segment, tree: &Tree, cfg: &Config) -> String {
    if let Some(title) = seg
        .item
        .as_ref()
        .and_then(|id| tree.get(id))
        .map(|i| i.title.clone())
        .filter(|t| !t.is_empty())
    {
        return title;
    }
    match seg.kind {
        SegKind::Break => "break".to_string(),
        SegKind::Rest => "rest".to_string(),
        SegKind::Lost => "lost".to_string(),
        SegKind::Sleep => "sleep".to_string(),
        SegKind::WindDown => "wind-down".to_string(),
        _ => title_cell(seg, tree, cfg),
    }
}

/// `title · duration · ci · p · @root` (§12.1's hover).
fn tooltip(seg: &Segment, tree: &Tree, cfg: &Config, plan: &DayPlan) -> String {
    let mut parts = vec![tooltip_name(seg, tree, cfg), fmt_dur(seg.minutes())];
    if let Some(item) = key_id(seg).and_then(|id| tree.get(id)) {
        parts.push(format!("ci{}", item.ci));
    } else if let Some(e) = seg.energy {
        parts.push(format!("ci{e}"));
    }
    if let Some(id) = key_id(seg) {
        if let Some((_, prio)) = plan.priorities.iter().find(|(k, _)| k == id) {
            parts.push(format!("p{}", prio.p));
        }
        let root = tree.root(id);
        if &root != id {
            parts.push(format!("@{root}"));
        }
    }
    parts.join(" · ")
}

// ---------------------------------------------------------------------------
// SVG (§17.2)
// ---------------------------------------------------------------------------

/// XML-escape a string for text and attribute content.
fn xml_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&apos;"),
            _ => out.push(c),
        }
    }
    out
}

/// A number with at most two decimals and no trailing zeroes, so snapshots are
/// stable and the file stays small.
fn num(v: f64) -> String {
    let s = format!("{v:.2}");
    let s = s.trim_end_matches('0').trim_end_matches('.');
    if s.is_empty() || s == "-0" {
        "0".to_string()
    } else {
        s.to_string()
    }
}

/// `#rrggbb` for a colour triple.
fn hex(c: (u8, u8, u8)) -> String {
    format!("#{:02x}{:02x}{:02x}", c.0, c.1, c.2)
}

/// Write `day/<date>.svg` (§12.1, §17.2) — hand-written SVG, no crate.
///
/// One `<rect>` per segment (not per cell) with a `<title>` child so VS Code's
/// markdown preview shows the tooltip on hover; `<pattern>` hatching for Lost
/// (orange) and Interrupt (red); a dotted stroke on optionals; hour ticks with
/// labels every three hours; the cursor line at `bar.now`; and, beneath the
/// main row, the ghost row (the plan as it stood at arrival) drawn from
/// `bar.ghost` as runs of equal cells.
pub fn render_svg(
    bar: &DayBar,
    plan: &DayPlan,
    cfg: &Config,
    width_px: u32,
    height_px: u32,
) -> String {
    let w = f64::from(width_px.max(40));
    let h = f64::from(height_px.max(24));
    let label_h = (h * 0.22).clamp(8.0, 14.0);
    let body_h = h - label_h;
    let has_ghost = !bar.ghost.is_empty();
    let gap = if has_ghost { 2.0 } else { 0.0 };
    let ghost_h = if has_ghost {
        (body_h * 0.28).max(3.0)
    } else {
        0.0
    };
    let main_h = (body_h - ghost_h - gap).max(1.0);
    let ghost_y = main_h + gap;

    let mut s = String::with_capacity(4096);
    let _ = writeln!(
        s,
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{w}\" height=\"{h}\" \
         viewBox=\"0 0 {w} {h}\" role=\"img\" aria-label=\"day bar {date}\">",
        w = num(w),
        h = num(h),
        date = plan.date
    );
    s.push_str(&patterns());
    let _ = writeln!(
        s,
        "<rect x=\"0\" y=\"0\" width=\"{}\" height=\"{}\" fill=\"{}\"/>",
        num(w),
        num(h),
        hex(CellStyle::Empty.colour())
    );

    // Main row: one rect per segment.
    s.push_str("<g class=\"plan\">\n");
    for (idx, seg) in plan.segments.iter().enumerate() {
        if let Some(rect) = segment_rect(bar, seg, idx, cfg, 0.0, main_h, w) {
            s.push_str(&rect);
        }
    }
    s.push_str("</g>\n");

    // Ghost row: runs of equal cells.
    if has_ghost {
        s.push_str("<g class=\"ghost\">\n");
        for (from, to, cell) in runs(&bar.ghost) {
            if cell.style == CellStyle::Empty {
                continue;
            }
            let x0 = from as f64 / bar.cols as f64 * w;
            let x1 = to as f64 / bar.cols as f64 * w;
            let _ = write!(
                s,
                "<rect x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\" fill=\"{}\"{}>",
                num(x0),
                num(ghost_y),
                num(x1 - x0),
                num(ghost_h),
                if cell.style.is_hatched() {
                    pattern_ref(cell.style)
                } else {
                    hex(cell.rgb(cfg))
                },
                if cell.style == CellStyle::Optional {
                    " stroke=\"#5b6670\" stroke-width=\"1\" stroke-dasharray=\"2 2\""
                } else {
                    ""
                }
            );
            if !cell.tooltip.is_empty() {
                let _ = write!(s, "<title>{}</title>", xml_escape(&cell.tooltip));
            }
            s.push_str("</rect>\n");
        }
        s.push_str("</g>\n");
    }

    // Hour ticks and labels.
    s.push_str("<g class=\"ticks\" font-family=\"monospace\" font-size=\"9\" fill=\"#666\">\n");
    let mut t = next_hour(bar.wake);
    let end = bar.wake + Duration::minutes(i64::from(bar.span_min));
    while t < end {
        let x = bar.x_of(t, w);
        let _ = writeln!(
            s,
            "<line x1=\"{x}\" y1=\"0\" x2=\"{x}\" y2=\"{y}\" stroke=\"#000\" \
             stroke-opacity=\"0.12\" stroke-width=\"1\"/>",
            x = num(x),
            y = num(main_h)
        );
        if t.hour().is_multiple_of(3) {
            let _ = writeln!(
                s,
                "<text x=\"{}\" y=\"{}\" text-anchor=\"middle\">{:02}</text>",
                num(x),
                num(h - 2.0),
                t.hour()
            );
        }
        t += Duration::hours(1);
    }
    s.push_str("</g>\n");

    // Cursor.
    let cx = bar.x_of(bar.now, w);
    let _ = writeln!(
        s,
        "<line class=\"cursor\" x1=\"{x}\" y1=\"0\" x2=\"{x}\" y2=\"{y}\" stroke=\"#111\" \
         stroke-width=\"1.5\"/>\n<text class=\"cursor-label\" x=\"{lx}\" y=\"{ly}\" \
         font-family=\"monospace\" font-size=\"9\" fill=\"#111\">{now}</text>",
        x = num(cx),
        y = num(ghost_y + ghost_h),
        lx = num((cx + 3.0).min(w - 26.0)),
        ly = num((main_h * 0.5).max(9.0)),
        now = hhmm(&bar.now)
    );
    s.push_str("</svg>\n");
    s
}

/// The two hatch patterns (§12.1).
fn patterns() -> String {
    let mut s = String::new();
    s.push_str("<defs>\n");
    for (id, bg, fg) in [
        ("tm-lost", "#fdecd9", "#f58231"),
        ("tm-interrupt", "#fadfe5", "#e6194b"),
    ] {
        let _ = writeln!(
            s,
            "<pattern id=\"{id}\" width=\"6\" height=\"6\" patternUnits=\"userSpaceOnUse\" \
             patternTransform=\"rotate(45)\">\
             <rect width=\"6\" height=\"6\" fill=\"{bg}\"/>\
             <line x1=\"0\" y1=\"0\" x2=\"0\" y2=\"6\" stroke=\"{fg}\" stroke-width=\"3\"/>\
             </pattern>"
        );
    }
    s.push_str("</defs>\n");
    s
}

/// `url(#tm-lost)` / `url(#tm-interrupt)`.
fn pattern_ref(style: CellStyle) -> String {
    match style {
        CellStyle::Lost => "url(#tm-lost)".to_string(),
        CellStyle::Interrupt => "url(#tm-interrupt)".to_string(),
        _ => hex(style.colour()),
    }
}

/// One `<rect>` for one segment, with its `<title>`.
///
/// The colour and the tooltip come from the bar's own cells (matched by
/// segment index) so the SVG and the terminal never disagree; a segment too
/// short to own a cell falls back to its style's colour and has no tooltip.
fn segment_rect(
    bar: &DayBar,
    seg: &Segment,
    idx: usize,
    cfg: &Config,
    y: f64,
    height: f64,
    width: f64,
) -> Option<String> {
    let end = bar.wake + Duration::minutes(i64::from(bar.span_min));
    if seg.end <= bar.wake || seg.start >= end {
        return None;
    }
    let x0 = bar.x_of(seg.start, width);
    let x1 = bar.x_of(seg.end, width);
    if x1 - x0 <= 0.0 {
        return None;
    }
    let style = CellStyle::of(seg);
    let cell = bar.cells.iter().find(|c| c.segment == Some(idx));
    let fill = match (style.is_hatched(), cell) {
        (true, _) => pattern_ref(style),
        (false, Some(c)) => hex(c.rgb(cfg)),
        (false, None) => hex(style.colour()),
    };
    let dots = if style == CellStyle::Optional {
        " stroke=\"#5b6670\" stroke-width=\"1\" stroke-dasharray=\"2 2\""
    } else {
        ""
    };
    let mut s = String::new();
    let _ = write!(
        s,
        "<rect x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\" fill=\"{}\"{}>",
        num(x0),
        num(y),
        num(x1 - x0),
        num(height),
        fill,
        dots
    );
    let tip = cell.map(|c| c.tooltip.clone()).unwrap_or_default();
    if !tip.is_empty() {
        let _ = write!(s, "<title>{}</title>", xml_escape(&tip));
    }
    s.push_str("</rect>\n");
    Some(s)
}

/// Merge adjacent equal cells into `(from, to, cell)` runs.
fn runs(cells: &[Cell]) -> Vec<(usize, usize, &Cell)> {
    let mut out: Vec<(usize, usize, &Cell)> = Vec::new();
    for (i, c) in cells.iter().enumerate() {
        match out.last_mut() {
            Some((_, to, prev)) if *prev == c && *to == i => *to = i + 1,
            _ => out.push((i, i + 1, c)),
        }
    }
    out
}

/// The first whole hour at or after `t`.
fn next_hour(t: DateTime<Tz>) -> DateTime<Tz> {
    if t.minute() == 0 && t.second() == 0 {
        return t;
    }
    t + Duration::seconds(i64::from(3600 - (t.minute() * 60 + t.second())))
}

// ---------------------------------------------------------------------------
// `tm now` (§13)
// ---------------------------------------------------------------------------

/// `tm now`: the current block with elapsed and remaining time, then the next
/// three segments (§13).
///
/// Uses the default [`Config`] for the two things a row needs from one (the
/// block unit behind `1b` and the `bed` time in the wind-down row); pass your
/// own with [`render_now_with`].
pub fn render_now(plan: &DayPlan, tree: &Tree, now: DateTime<Tz>) -> String {
    render_now_with(plan, tree, &Config::default(), now)
}

/// [`render_now`] with an explicit config.
pub fn render_now_with(plan: &DayPlan, tree: &Tree, cfg: &Config, now: DateTime<Tz>) -> String {
    let prios: HashMap<&Id, u8> = plan.priorities.iter().map(|(id, p)| (id, p.p)).collect();
    let current = plan
        .segments
        .iter()
        .position(|s| s.flags.current && s.start <= now && now < s.end)
        .or_else(|| {
            plan.segments
                .iter()
                .position(|s| s.start <= now && now < s.end && !s.flags.done)
        });
    let mut out = String::new();
    match current.map(|i| &plan.segments[i]) {
        Some(seg) => {
            let mut head = format!(
                "{} {}",
                if seg.flags.done {
                    MARK_DONE
                } else if is_work(&seg.kind) {
                    MARK_CURRENT
                } else {
                    glyph_of(&seg.kind)
                },
                title_cell(seg, tree, cfg)
            );
            let parent = parent_cell(seg, tree);
            if !parent.is_empty() {
                head.push_str(&format!("  {parent}"));
            }
            if let Some(level) = seg.energy.or_else(|| {
                seg.item
                    .as_ref()
                    .and_then(|id| tree.get(id))
                    .map(|i| i.ci)
            }) {
                head.push_str(&format!("  ci{level}"));
            }
            if let Some(p) = seg.item.as_ref().and_then(|id| prios.get(id)) {
                head.push_str(&format!("  p{p}"));
            }
            let est = est_cell(seg, tree, cfg);
            if !est.is_empty() {
                head.push_str(&format!("  {est}"));
            }
            out.push_str(&head);
            out.push('\n');
            out.push_str(&format!(
                "  {}–{} · elapsed {} · left {}\n",
                hhmm(&seg.start),
                hhmm(&seg.end),
                fmt_dur(minutes_between(&seg.start, &now)),
                fmt_dur(minutes_between(&now, &seg.end))
            ));
        }
        None => {
            out.push_str(&format!("— nothing running ({})\n", hhmm(&now)));
        }
    }
    let next: Vec<&Segment> = plan
        .segments
        .iter()
        .enumerate()
        .filter(|(i, s)| s.start >= now && Some(*i) != current)
        .map(|(_, s)| s)
        .take(3)
        .collect();
    if next.is_empty() {
        out.push_str("next   —\n");
        return out;
    }
    out.push_str("next\n");
    for seg in next {
        let mut line = format!("  {}  ", hhmm(&seg.start));
        if !is_work(&seg.kind) {
            line.push(glyph_of(&seg.kind));
            line.push(' ');
        }
        line.push_str(&title_cell(seg, tree, cfg));
        let parent = parent_cell(seg, tree);
        if !parent.is_empty() {
            line.push_str(&format!("  {parent}"));
        }
        let est = est_cell(seg, tree, cfg);
        if !est.is_empty() {
            line.push_str(&format!("  {est}"));
        }
        out.push_str(line.trim_end());
        out.push('\n');
    }
    out
}

// ---------------------------------------------------------------------------
// Diagnostics (§8.2 step 8, §11, §12.1)
// ---------------------------------------------------------------------------

/// The diagnostics pane's lines (§12.1): `1 underused (4→3) · 0 ci-5 lost`,
/// `t5 blocked by t4`, the impossible list, conflicts, deferred and waiting
/// items, plus whatever the planner put in `notes`.
///
/// Takes `cfg` (which the scope's signature omitted) because every duration is
/// printed in blocks, and `block_min` lives in the config.
pub fn render_diagnostics(diag: &Diagnostics, tree: &Tree, cfg: &Config) -> Vec<String> {
    let bm = cfg.block_min();
    let mut out = Vec::new();

    let mut pairs: Vec<String> = Vec::new();
    for (_, slot, ci) in diag.underused.iter().take(3) {
        let p = format!("{slot}→{ci}");
        if !pairs.contains(&p) {
            pairs.push(p);
        }
    }
    let detail = if pairs.is_empty() {
        String::new()
    } else {
        format!(" ({})", pairs.join(", "))
    };
    let lost = if diag.a_capacity_lost == 0 {
        "0".to_string()
    } else {
        format!("{}m", diag.a_capacity_lost)
    };
    out.push(format!(
        "{} underused{} · {} ci-5 lost",
        diag.underused.len(),
        detail,
        lost
    ));

    if let Some(honesty) = diag.plan_honesty {
        if honesty > 1.1 {
            out.push(format!(
                "plan honesty {honesty:.2} — planned above a realistic budget"
            ));
        }
    }
    if diag.rest_debt_min > 0 {
        out.push(format!("rest debt {}m", diag.rest_debt_min));
    }
    for (id, shortfall, due) in &diag.impossible {
        out.push(format!(
            "{} impossible: {} short by {}",
            name_of(tree, id),
            fmt_blocks(*shortfall, bm),
            due
        ));
    }
    if !diag.hot.is_empty() {
        out.push(format!("hot: {}", join_ids(&diag.hot)));
    }
    for (a, b) in &diag.conflicts {
        out.push(format!("{a} conflicts with {b}"));
    }
    for (id, deps) in &diag.blocked {
        let by: Vec<String> = deps
            .iter()
            .map(|d| match d {
                Dep::Item(i) => i.to_string(),
                Dep::Event(n) => format!("event:{n}"),
            })
            .collect();
        out.push(format!("{id} blocked by {}", by.join(", ")));
    }
    if !diag.deferred.is_empty() {
        out.push(format!("deferred: {}", join_ids(&diag.deferred)));
    }
    if !diag.waiting.is_empty() {
        out.push(format!("waiting: {}", join_ids(&diag.waiting)));
    }
    if !diag.dropped_tail.is_empty() {
        out.push(format!("dropped: {}", join_ids(&diag.dropped_tail)));
    }
    out.extend(diag.notes.iter().cloned());
    out
}

/// §7.3's banner for the items that cannot fit: `d1 CS 234 pset 2: needs 8b,
/// 5b available by Fri`.
///
/// Needs the `Prio` numbers (`need_min` / `avail_min`), which live on the plan
/// rather than in [`Diagnostics`], so this is a second function rather than a
/// line of [`render_diagnostics`].
pub fn render_banners(plan: &DayPlan, tree: &Tree, cfg: &Config) -> Vec<String> {
    let bm = cfg.block_min();
    let mut out = Vec::new();
    for (id, _shortfall, due) in &plan.diagnostics.impossible {
        let prio = plan.priorities.iter().find(|(k, _)| k == id).map(|(_, p)| p);
        match prio {
            Some(p) => out.push(format!(
                "{}: needs {}, {} available by {}",
                name_of(tree, id),
                fmt_blocks(p.need_min, bm),
                fmt_blocks(p.avail_min, bm),
                when(*due, plan.date)
            )),
            None => out.push(format!(
                "{}: short by {} at {}",
                name_of(tree, id),
                fmt_blocks(*_shortfall, bm),
                when(*due, plan.date)
            )),
        }
    }
    out
}

/// A deadline within a week reads as a weekday (`Fri`), further out as a date.
fn when(due: NaiveDate, today: NaiveDate) -> String {
    let days = (due - today).num_days();
    if (0..7).contains(&days) {
        due.format("%a").to_string()
    } else {
        due.to_string()
    }
}

/// `d1 CS 234 pset 2`, or just the id when the tree does not know it.
fn name_of(tree: &Tree, id: &Id) -> String {
    match tree.get(id) {
        Some(item) if !item.title.is_empty() => format!("{id} {}", item.title),
        _ => id.to_string(),
    }
}

/// `a3 · d1`.
fn join_ids(ids: &[Id]) -> String {
    ids.iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" · ")
}

// ---------------------------------------------------------------------------
// Legend (§11 "Energy mix")
// ---------------------------------------------------------------------------

/// §11's energy mix — the day bar's legend.
#[derive(Clone, Copy, Debug, Default, PartialEq, Serialize)]
pub struct EnergyMix {
    /// Planned `Block`/`Batch` minutes at each `ci` 0..=5.
    pub minutes_at_ci: [u32; 6],
    /// Σ of `minutes_at_ci`.
    pub total_min: u32,
    /// Share of those minutes spent at `ci ≥ 4`; 0 when nothing is planned.
    pub share_ci4_plus: f64,
    /// How many segments carry the `↓` mark.
    pub underused_count: usize,
    /// Minutes given to `optional.md` items (§11's optional quota).
    pub optional_min: u32,
}

impl EnergyMix {
    /// The legend line: `ci5 120m · ci4 192m · ci3 120m · ci≥4 72% · ↓1`.
    pub fn line(&self) -> String {
        let mut parts: Vec<String> = Vec::new();
        for ci in (0..6).rev() {
            let m = self.minutes_at_ci[ci];
            if m > 0 {
                parts.push(format!("ci{ci} {m}m"));
            }
        }
        parts.push(format!(
            "ci≥4 {}%",
            (self.share_ci4_plus * 100.0).round() as i64
        ));
        parts.push(format!("↓{}", self.underused_count));
        if self.optional_min > 0 {
            parts.push(format!("○ {}m", self.optional_min));
        }
        parts.join(" · ")
    }
}

/// §11's "Energy mix": minutes at each `ci`, the share at `ci ≥ 4`, and the
/// `↓` count.
///
/// Takes the `tree` (which the scope's signature omitted) because a segment
/// carries the *slot's* energy, while the mix is about the *item's* `ci`; the
/// slot energy is the fallback when the tree does not know the item. The share
/// is over the plan's own block minutes, which is defined for any plan — the
/// budget is not always the denominator you want (an over-budget day would
/// score above 100%).
pub fn legend(plan: &DayPlan, tree: &Tree) -> EnergyMix {
    let mut mix = EnergyMix::default();
    for seg in &plan.segments {
        if seg.flags.underused {
            mix.underused_count += 1;
        }
        if matches!(seg.kind, SegKind::Optional) {
            mix.optional_min += seg.minutes();
        }
        if !is_work(&seg.kind) {
            continue;
        }
        let ci = seg
            .item
            .as_ref()
            .and_then(|id| tree.get(id))
            .map(|i| i.ci)
            .or(seg.energy)
            .unwrap_or(0)
            .min(5) as usize;
        let m = seg.minutes();
        mix.minutes_at_ci[ci] += m;
        mix.total_min += m;
    }
    if mix.total_min > 0 {
        let high = mix.minutes_at_ci[4] + mix.minutes_at_ci[5];
        mix.share_ci4_plus = f64::from(high) / f64::from(mix.total_min);
    }
    mix
}
