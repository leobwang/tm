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
//! * [`legend`]`(plan, tree, cfg) -> EnergyMix` — §11's energy mix, plus
//!   [`EnergyMix::line`] for the bar legend.
//!
//! # The row format (§4.3)
//!
//! ```text
//! HH:MM  ci  pN  mark  title  @parent  est  (actual)  note
//! 07:00  5 p1 ✓ Read ch.6 §1–2               @m3  1b  (67m)
//! ```
//!
//! Columns are fixed, counted in *terminal columns* ([`display_width`], so a
//! wide glyph such as `⏰` or a CJK title character costs two), every field
//! left-aligned and padded to at least its width (a longer value pushes the
//! rest of the row right rather than being truncated — only the title is
//! truncated, and a batch row is fitted by [`fit_batch`]):
//!
//! | column | offset | width | content |
//! |---|---|---|---|
//! | time | 0 | 5 | `HH:MM` |
//! | ci | 7 | 2 | slot energy (else the item's `ci`) + `↓`; or the row glyph `·` `⏰` `○` `🌙` |
//! | p | 9 | 2 | `p3` — budgeted work, and the Window *tasks* of §4.3's `1 p0 ⚠ Pick up package` |
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
//! The trailing note is derived when the segment does not carry one: an
//! under-used slot reads `↓ slot 4, item 3` (from `diagnostics.underused`) and
//! a HOT item reads `due today` (from the item's effective due or window) —
//! see [`note_cell`]. An explicit `SegFlags::note` always wins.
//!
//! # Differences from the §4.3 example
//!
//! The example in the spec is hand-aligned and internally inconsistent; three
//! of its rows cannot all hold at once. This renderer keeps every column at a
//! fixed offset, which reproduces the fullest rows byte for byte
//! (`07:00`, `08:00`, `09:20`) and differs from the others as follows:
//!
//! 1. **Title offset.** The example starts the title at column 14 on rows with
//!    a mark (`✓ Read ch.6 §1–2`) but at column 15 on rows without one
//!    (`lunch 30m`, `Claude Code drafts tests`, and — because `⏰` and `🌙`
//!    are two columns wide — the wall and wind-down rows too). Column 14
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
use crate::model::{Dep, Dur, Id, Shape, WindowRange};
use crate::planner::{DayPlan, Diagnostics, SegKind, Segment, fmt_clock};
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

/// East-Asian Wide and Fullwidth code points, plus the emoji that render two
/// columns wide. Sorted, non-overlapping, binary-searched by [`char_width`].
///
/// A compact table rather than the `unicode-width` crate, whose dependency the
/// workspace does not carry; it covers the glyphs this module emits (`⏰`,
/// `🌙`) and the CJK and emoji blocks an item title can contain.
const WIDE_RANGES: &[(u32, u32)] = &[
    (0x1100, 0x115F),
    (0x231A, 0x231B),
    (0x2329, 0x232A),
    (0x23E9, 0x23EC),
    (0x23F0, 0x23F0),
    (0x23F3, 0x23F3),
    (0x25FD, 0x25FE),
    (0x2614, 0x2615),
    (0x2648, 0x2653),
    (0x267F, 0x267F),
    (0x2693, 0x2693),
    (0x26A1, 0x26A1),
    (0x26AA, 0x26AB),
    (0x26BD, 0x26BE),
    (0x26C4, 0x26C5),
    (0x26CE, 0x26CE),
    (0x26D4, 0x26D4),
    (0x26EA, 0x26EA),
    (0x26F2, 0x26F3),
    (0x26F5, 0x26F5),
    (0x26FA, 0x26FA),
    (0x26FD, 0x26FD),
    (0x2705, 0x2705),
    (0x270A, 0x270B),
    (0x2728, 0x2728),
    (0x274C, 0x274C),
    (0x274E, 0x274E),
    (0x2753, 0x2755),
    (0x2757, 0x2757),
    (0x2795, 0x2797),
    (0x27B0, 0x27B0),
    (0x27BF, 0x27BF),
    (0x2B1B, 0x2B1C),
    (0x2B50, 0x2B50),
    (0x2B55, 0x2B55),
    (0x2E80, 0x303E),
    (0x3041, 0x33FF),
    (0x3400, 0x4DBF),
    (0x4E00, 0x9FFF),
    (0xA000, 0xA4CF),
    (0xA960, 0xA97F),
    (0xAC00, 0xD7A3),
    (0xF900, 0xFAFF),
    (0xFE10, 0xFE19),
    (0xFE30, 0xFE6F),
    (0xFF00, 0xFF60),
    (0xFFE0, 0xFFE6),
    (0x1_F004, 0x1_F004),
    (0x1_F0CF, 0x1_F0CF),
    (0x1_F18E, 0x1_F18E),
    (0x1_F191, 0x1_F19A),
    (0x1_F1E6, 0x1_F1FF),
    (0x1_F200, 0x1_F2FF),
    (0x1_F300, 0x1_F9FF),
    (0x1_FA70, 0x1_FAFF),
    (0x2_0000, 0x3_FFFD),
];

/// Code points that take no terminal column: combining marks, the zero-width
/// joiner family and the variation selectors.
const ZERO_RANGES: &[(u32, u32)] = &[
    (0x0300, 0x036F),
    (0x200B, 0x200F),
    (0xFE00, 0xFE0F),
    (0xFEFF, 0xFEFF),
];

/// Is `cp` inside one of the sorted, non-overlapping `ranges`?
fn in_ranges(cp: u32, ranges: &[(u32, u32)]) -> bool {
    ranges
        .binary_search_by(|(lo, hi)| {
            if cp < *lo {
                std::cmp::Ordering::Greater
            } else if cp > *hi {
                std::cmp::Ordering::Less
            } else {
                std::cmp::Ordering::Equal
            }
        })
        .is_ok()
}

/// The terminal columns `c` occupies **on its own**: 0 for a combining mark or
/// a variation selector, 2 for East-Asian Wide/Fullwidth and the emoji that
/// default to an emoji presentation, 1 otherwise.
///
/// **A code point at a time, which is not a glyph at a time.** `👨‍👩‍👧` is three
/// of these and two joiners; a terminal draws one glyph of two columns.
/// [`Walk`] is where that is reconciled, and [`display_width`] is the only
/// thing anybody should be summing — this is the table it reads.
pub fn char_width(c: char) -> usize {
    let cp = c as u32;
    if in_ranges(cp, ZERO_RANGES) {
        0
    } else if in_ranges(cp, WIDE_RANGES) {
        2
    } else {
        1
    }
}

/// U+200D ZERO WIDTH JOINER: the code point that glues two emoji into one
/// glyph. Already 0 columns by `ZERO_RANGES`; what matters here is that it
/// makes the code point **after** it 0 as well.
const ZWJ: char = '\u{200D}';

/// The five emoji modifiers — U+1F3FB..U+1F3FF, FITZPATRICK TYPE-1-2 to
/// TYPE-6. Each re-colours the emoji before it rather than drawing anything of
/// its own, so `👍🏽` is one glyph of two columns and not two of two.
///
/// They sit inside `WIDE_RANGES`'s `(0x1_F300, 0x1_F9FF)` and so measure 2 on
/// their own, which is right for a lone modifier and wrong the moment one
/// follows a base. [`Walk`] is the difference.
const SKIN_TONE: (u32, u32) = (0x1_F3FB, 0x1_F3FF);

/// **The owner's D44: a width walk that knows a glyph from a code point.**
///
/// [`char_width`] is a table lookup and a table cannot see two code points at
/// once, so the sum of it over `👨‍👩‍👧` was **6** and over `👍🏽` was **4** where a
/// terminal draws **2** (README gap 1198). A row carrying one rendered about
/// four columns narrow on screen — and since D43 made this table the TUI's as
/// well, that reached four surfaces at once.
///
/// **This is the whole of the fix, hand-rolled beside the table it reads**: no
/// segmentation crate, because a new external dependency is the one thing six
/// stages of this rebuild have never taken (AGENTS R7). Two rules, and they
/// compose:
///
/// 1. a **ZWJ** with something already drawn before it makes the next code
///    point cost 0 — it joined the cluster rather than starting one;
/// 2. a **skin-tone modifier** with something already drawn before it costs 0
///    — it re-coloured the base rather than drawing beside it.
///
/// "Something already drawn" is `Walk::open`, and it is what keeps a string
/// that *starts* with a joiner or a modifier honest: a lone `🏽` is still the
/// two columns its table entry says, because there is no base for it to
/// modify.
///
/// **One walk, not two** (AGENTS §5.3). [`display_width`] and [`clip`] both
/// drive this, so the count and the cut cannot disagree about where a glyph
/// begins — which is how a cut that fits by the count could still land inside
/// a cluster. A cluster costs its columns at its **base**, and every code
/// point after it costs 0, so `clip` accepts the whole of a cluster whose base
/// it accepted and never emits a dangling joiner.
///
/// **What it still does not do**, declared rather than discovered: a
/// **regional-indicator pair** (`🇯🇵`) is still 4 where a terminal draws 2
/// (README gap 1250); a ZWJ between two ordinary letters swallows the second
/// one; and the general grapheme-cluster rules — Indic conjuncts, emoji tag
/// sequences, U+20E3 keycaps — are not implemented, because D44 names two
/// shapes and this is those two.
#[derive(Clone, Copy, Default)]
struct Walk {
    /// Something with a column of its own has already been counted, so there
    /// is a cluster for a joiner or a modifier to attach to.
    open: bool,
    /// The code point just seen was a `ZWJ` that attached to an open cluster,
    /// so the next one is part of that cluster.
    joined: bool,
}

impl Walk {
    /// The columns `c` adds to the row, given everything before it.
    fn advance(&mut self, c: char) -> usize {
        if c == ZWJ {
            self.joined = self.open;
            return 0;
        }
        if std::mem::take(&mut self.joined) {
            return 0;
        }
        let cp = c as u32;
        if self.open && (SKIN_TONE.0..=SKIN_TONE.1).contains(&cp) {
            return 0;
        }
        let w = char_width(c);
        self.open |= w > 0;
        w
    }
}

/// The terminal columns `s` occupies — what the timeline's fixed columns are
/// counted in, so that `⏰` and `🌙` do not push their rows one column right,
/// and so that `👨‍👩‍👧` does not push its row four columns left (D44, [`Walk`]).
pub fn display_width(s: &str) -> usize {
    let mut walk = Walk::default();
    s.chars().map(|c| walk.advance(c)).sum()
}

/// Left-align `s` in `w` terminal columns (a wider `s` is returned unchanged).
///
/// Private on purpose: a caller that wants a cell of exactly `w` columns wants
/// [`pad_to`], which cuts an over-wide `s` first. See [`pad_to`] for D43.
fn pad(s: &str, w: usize) -> String {
    let n = display_width(s);
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

/// Truncate `s` to `w` terminal columns, marking the cut with `…`.
///
/// **Public since D43.** The TUI had its own copy of this, measuring with
/// ratatui's `unicode-width` instead of [`char_width`]'s table; there is now
/// one truncation in the workspace and this is it.
///
/// The result is never wider than `w`; a cut that would land inside a
/// double-width character drops that character instead of splitting it, and a
/// cut that lands after a space drops the space, so the result can be a column
/// or two narrower.
///
/// **It is [`clip`] plus the trim, and not a second copy of the walk** (AGENTS
/// §5.3, the W-22 repair step). The two used to be the same `for c in
/// s.chars()` written twice, statement for statement, differing only by the
/// `while out.ends_with(' ')` below — so a change to the width walk had to be
/// made in two places, which is README gap 1089's own lesson inside the one
/// file D43 is about. The trim runs **only when a cut happened**: an `s` that
/// already fits comes back untouched even when it ends in `…`.
pub fn truncate(s: &str, w: usize) -> String {
    let out = clip(s, w);
    if display_width(s) <= w || w == 0 {
        return out; // nothing was cut; `s` unchanged, or empty at `w == 0`
    }
    // `clip` put the `…` there; take it off, eat the spaces it was hiding, and
    // put it back.
    let mut out = out;
    out.pop();
    while out.ends_with(' ') {
        out.pop();
    }
    out.push('…');
    out
}

/// Cut `s` to `w` terminal columns for a **viewport**, marking the cut with `…`
/// **at the edge**.
///
/// [`truncate`] and this are two operations, not two implementations of one
/// (AGENTS §5.3): `truncate` fits a *cell*, so it drops the spaces in front of
/// the `…` and the result can be a column or two narrower; `clip` fits a pane,
/// where the row it is given is already padded to its columns and eating that
/// padding would walk the `…` backwards into the middle of the line. Both
/// measure with [`char_width`], which is what D43 is about — the TUI used to
/// clip with ratatui's `unicode-width` instead.
///
/// **That defence was true of the operations and false of the bodies**, and an
/// auditor said so at W-22: they were the same char walk written twice. This is
/// the walk; `truncate` is this plus a trim.
pub fn clip(s: &str, w: usize) -> String {
    if display_width(s) <= w {
        return s.to_string();
    }
    if w == 0 {
        return String::new();
    }
    let mut out = String::with_capacity(s.len());
    let mut used = 0usize;
    // **The same [`Walk`] `display_width` drives** (D44, AGENTS §5.3): a
    // cluster costs its columns at its base and 0 after it, so a cut that
    // accepted a base accepts the rest of its glyph and never leaves a
    // dangling joiner or a base without its skin tone.
    let mut walk = Walk::default();
    for c in s.chars() {
        let cw = walk.advance(c);
        if used + cw > w - 1 {
            break;
        }
        used += cw;
        out.push(c);
    }
    out.push('…');
    out
}

/// A cell of exactly `w` terminal columns: `s` cut to fit, then left-aligned.
///
/// **The owner's D43.** `tui/queue.rs` had its own `pad` — cut-then-pad, the
/// same shape — measuring with ratatui's `unicode-width` where this module
/// measures with [`char_width`]'s East-Asian table. The two disagree on a
/// handful of code points, so a Queue column holding CJK or an emoji can shift
/// by a cell; that is the accepted cost of having one padder, and it is a
/// behaviour row in `kernel/README.md`. Unifying the other way was declined:
/// the day file's bytes are this table's, so the corpus round trip and the
/// frozen-fork comparand would both have moved.
///
/// `tm/tests/one_padder.rs` is the guard that stops a second one appearing.
pub fn pad_to(s: &str, w: usize) -> String {
    pad(&truncate(s, w), w)
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

/// Does this kind spend the day's budget? (`Block`, `Batch` — what the
/// `window ends` divider counts.)
fn is_work(kind: &SegKind) -> bool {
    matches!(kind, SegKind::Block | SegKind::Batch(_))
}

/// Does this row print its `ci` and `pN`, or the kind's glyph?
///
/// Budgeted work always does. So does a Window-shaped *task* placed by §8.2
/// step 2 — §4.3's `15:10  1 p0 ⚠  Pick up package  20m  due today`: it is a
/// `Routine` segment because that is how the planner places a window, but it
/// is on §7's scale. The planner marks it by giving the segment an `energy`;
/// a `routines.md` line (`11:20  ·  lunch 30m`) has none.
fn shows_scale(seg: &Segment) -> bool {
    is_work(&seg.kind) || (matches!(seg.kind, SegKind::Routine) && seg.energy.is_some())
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
    let scheduled_window = matches!(seg.kind, SegKind::Routine) && shows_scale(seg);
    if !scheduled_window
        && !matches!(
            seg.kind,
            SegKind::Block | SegKind::Batch(_) | SegKind::Wall | SegKind::Optional
        )
    {
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
        (None, None) if matches!(seg.kind, SegKind::Wall | SegKind::Optional) || scheduled_window => {
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
///
/// **Public since W-23** (D30 Q5 (a), README gap 1104). `tm/src/tui/today.rs`
/// had a second one — seg_title, which said `break`, `rest`, `interruption`
/// and `batch (3)` where this says `break 20m`, `rest 20m`, the wall's item and
/// `batch: … (3)`. Two implementations of one concept is the bug (AGENTS §5.3),
/// and the one the day file prints is the one that survives, so the Now pane
/// calls this. `Emit.titleCell` is the kernel's statement of the same cell.
pub fn title_cell(seg: &Segment, tree: &Tree, cfg: &Config) -> String {
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
            let names = batch_names(ids, tree);
            format!("batch: {} ({})", names.join(" · "), names.len())
        }
        SegKind::Break => format!("break {}", fmt_dur(planned)),
        // A window *task* puts its length in the est column instead (§4.3).
        SegKind::Routine if shows_scale(seg) => name("—"),
        SegKind::Routine => format!("{} {}", name("routine"), fmt_dur(planned)),
        SegKind::Sleep => format!("{} {}", name("sleep"), fmt_dur(planned)),
        SegKind::Rest => format!("rest {}", fmt_dur(planned)),
        SegKind::Lost => format!("lost {}", fmt_dur(planned)),
        // `crate::model::fmt_time`, not a `{:02}:{:02}` of its own — the kernel's
        // `Emit.titleCell` renders this cell's clock with `Field.renderClock`
        // like every other, and this was a ninth `HH:MM` hiding inside the one
        // renderer (AGENTS §5.3, found by `one_renderer.rs`'s clock guard on its
        // first run, W-23).
        SegKind::WindDown => format!("wind-down · bed {}", crate::model::fmt_time(cfg.day.bed)),
        SegKind::Block | SegKind::Optional | SegKind::Wall => name("—"),
    }
}

/// The titles a batch names, in the order it was assigned (§7.5).
fn batch_names(ids: &[Id], tree: &Tree) -> Vec<String> {
    ids.iter()
        .map(|id| {
            tree.get(id)
                .map(|i| i.title.clone())
                .filter(|t| !t.is_empty())
                .unwrap_or_else(|| id.to_string())
        })
        .collect()
}

/// §7.5's `batch: package · insurance · bank (3)`, fitted into `width`
/// terminal columns.
///
/// The full form is `batch: <title> · <title> · <title> (n)`, which rarely
/// fits the §4.3 title column. Rather than let the plain title truncation eat
/// the member list and the count (the row would then say strictly less than
/// the spec's form), the frame `batch: ` … ` (n)` is kept and the *members* are
/// shortened: the columns left over after the frame and the ` · ` separators
/// are shared out evenly, remainder to the earliest members, and each name is
/// cut with `…`. Only when even one column per member is impossible does the
/// whole string fall back to [`truncate`].
pub fn fit_batch(names: &[String], width: usize) -> String {
    let n = names.len();
    let full = format!("batch: {} ({n})", names.join(" · "));
    if display_width(&full) <= width || n == 0 {
        return full;
    }
    let frame = display_width("batch: ") + display_width(&format!(" ({n})"));
    let seps = 3 * (n - 1);
    let avail = width.saturating_sub(frame + seps);
    if avail < n {
        return truncate(&full, width);
    }
    let share = avail / n;
    let extra = avail % n;
    let parts: Vec<String> = names
        .iter()
        .enumerate()
        .map(|(i, name)| truncate(name, share + usize::from(i < extra)))
        .collect();
    format!("batch: {} ({n})", parts.join(" · "))
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

/// The trailing note column (§4.3's `↓ slot 4, item 3` and `due today`).
///
/// An explicit [`SegFlags::note`](crate::planner::SegFlags::note) wins; without
/// one the note is derived from the mark the row already carries, so a planner
/// that only sets `flags.underused` / `flags.hot` still gets the spec's text:
///
/// * `↓` → `↓ slot <slot energy>, item <item ci>`, taken from
///   `plan.diagnostics.underused` (the planner records the exact pair there)
///   and falling back to the segment's own `energy` and the item's `ci`;
/// * `⚠` → `overdue` / `due today` / `due tomorrow` / `due Fri` / `due
///   2026-11-20`, from the item's effective due (§6.4) or, for a window item
///   such as `win:2026-09-07T09:00/21:00`, the window's last day.
pub fn note_cell(seg: &Segment, tree: &Tree, plan: &DayPlan) -> String {
    if let Some(note) = &seg.flags.note {
        return note.clone();
    }
    if seg.flags.underused {
        if let Some(note) = underused_note(seg, tree, plan) {
            return note;
        }
    }
    if seg.flags.hot {
        if let Some(note) = hot_note(seg, tree, plan) {
            return note;
        }
    }
    String::new()
}

/// `↓ slot 4, item 3` for an under-used slot (§8.2 step 5).
fn underused_note(seg: &Segment, tree: &Tree, plan: &DayPlan) -> Option<String> {
    let id = key_id(seg)?;
    let (slot, ci) = plan
        .diagnostics
        .underused
        .iter()
        .find(|(k, _, _)| k == id)
        .map(|(_, slot, ci)| (*slot, *ci))
        .or_else(|| Some((seg.energy?, tree.get(id)?.ci)))?;
    Some(format!("{MARK_UNDERUSED} slot {slot}, item {ci}"))
}

/// `due today` for a HOT item (§7.2), or the day its deadline falls on.
fn hot_note(seg: &Segment, tree: &Tree, plan: &DayPlan) -> Option<String> {
    let due = due_date(tree, key_id(seg)?, plan.date)?;
    Some(if due < plan.date {
        "overdue".to_string()
    } else if due == plan.date {
        "due today".to_string()
    } else if plan.date.succ_opt() == Some(due) {
        "due tomorrow".to_string()
    } else {
        format!("due {}", when(due, plan.date))
    })
}

/// The day an item is due: its effective due (§6.4), else the last day of its
/// window (a daily window closes on the day being planned).
fn due_date(tree: &Tree, id: &Id, today: NaiveDate) -> Option<NaiveDate> {
    if let Some(dt) = tree.effective_due(id) {
        return Some(dt.date());
    }
    match tree.effective_shape(id) {
        Shape::Window {
            range: WindowRange::Absolute { to, .. },
            ..
        } => Some(to.date()),
        Shape::Window {
            range: WindowRange::Daily { .. },
            ..
        } => Some(today),
        _ => None,
    }
}

/// The mark column: done beats current beats hot.
///
/// `' '` when the row carries none — §4.3's `✓ ▶ ⚠`, and nothing else: the
/// glyphs (`· ⏰ ○ 🌙`) belong to the `ci` column, not here.
pub fn mark_of(seg: &Segment) -> char {
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

/// **The day's rows, one per segment, in the day's order** — the list every
/// surface selects from (D30 Q5 (a), README gap 1104).
///
/// `rows[i]` is the row `plan.segments[i]` gets, byte for byte, wherever it is
/// printed: the day file writes this list with the `window ends` divider spliced
/// in ([`render_plan_section_with`]), `tm plan --json` numbers it
/// (`tm/src/cli/render.rs::rows`), the TUI's Timeline draws it at its own
/// [`Layout`], and `tm now` prints a window of it ([`render_now_with`]).
///
/// **Indexed by position and never by value**: two items with one title give
/// byte-identical rows that differ only in their start time, so `rows` and
/// `plan.segments` are matched by index (README gap **1197**). The list is
/// `Vec<String>` and not an iterator for exactly that reason — a caller holds
/// positions into it.
///
/// It is the kernel's `Emit.rowsOf` on the Rust side of the wire: one row per
/// segment and no other row (`Emit.rowsOf_length`).
pub fn plan_rows(plan: &DayPlan, tree: &Tree, cfg: &Config, layout: &Layout) -> Vec<String> {
    let prios: HashMap<&Id, u8> = plan.priorities.iter().map(|(id, p)| (id, p.p)).collect();
    plan.segments
        .iter()
        .map(|seg| render_row(&row_cells(seg, plan, tree, cfg, &prios), layout))
        .collect()
}

/// **One line of the day section, and the segment it renders.**
///
/// `segment` is a position into `plan.segments`, `None` only for the single
/// `─── window ends HH:MM` divider, which belongs to no segment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DayLine {
    /// The line, byte for byte as the day file holds it.
    pub text: String,
    /// The segment this line renders, by position.
    pub segment: Option<usize>,
}

/// **The whole day section, line by line, each carrying its provenance.**
///
/// [`plan_rows`] with the `window ends` divider spliced in where
/// [`divider_instant`] puts it: at the end of the `Block`/`Batch` segment whose
/// minutes take the running total to `budget_blocks × block_min`, or at the
/// window end, whichever comes first, before the first segment that starts at
/// or after that instant.
///
/// **Every surface that needs to know which segment a line belongs to takes it
/// from here** (README gap **1197**). The TUI used to re-derive the mapping by
/// looking for `───` at a fixed offset in the rendered text and counting
/// around it — a second answer to a question this function settles, and one
/// that a title containing the glyph at the right column could have moved.
pub fn day_lines(plan: &DayPlan, tree: &Tree, cfg: &Config, layout: &Layout) -> Vec<DayLine> {
    let rows = plan_rows(plan, tree, cfg, layout);
    let divider_at = divider_instant(plan, cfg);
    let mut out: Vec<DayLine> = Vec::with_capacity(rows.len() + 1);
    let mut divider_done = divider_at.is_none();
    for (i, (seg, row)) in plan.segments.iter().zip(rows).enumerate() {
        if let Some(at) = divider_at {
            if !divider_done && seg.start >= at {
                out.push(DayLine {
                    text: divider_row(&at, &plan.window.1),
                    segment: None,
                });
                divider_done = true;
            }
        }
        out.push(DayLine {
            text: row,
            segment: Some(i),
        });
    }
    if let (false, Some(at)) = (divider_done, divider_at) {
        out.push(DayLine {
            text: divider_row(&at, &plan.window.1),
            segment: None,
        });
    }
    out
}

/// [`render_plan_section`] with an explicit title width.
pub fn render_plan_section_with(
    plan: &DayPlan,
    tree: &Tree,
    cfg: &Config,
    now: DateTime<Tz>,
    layout: &Layout,
) -> (String, String) {
    let mut body = String::new();
    for line in day_lines(plan, tree, cfg, layout) {
        body.push_str(&line.text);
        body.push('\n');
    }
    (fmt_clock(now), body)
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
    let head = format!("{}  {}", fmt_clock(*at), DIVIDER);
    let mut row = pad(&head, TITLE_COL);
    row.push_str(&format!("window ends {}", fmt_clock(*window_end)));
    row
}

/// **§4.3's nine cells, before anything measures a column** — the Lean
/// kernel's `Emit.Row`, on this side of the wire (D30 Q6 (a): *"the kernel
/// emits cells; one Rust function pads"*).
///
/// The nine are `time ci p mark title parent est actual note`, in that order,
/// and [`cells`](RowCells::cells) is that order as data: a field reordered here
/// breaks it, the way a field reordered in `Emit.Row` breaks
/// `Emit.cells_are_the_nine_in_order`.
///
/// `batch_names` is **not** a tenth cell. It is the member list a batch row's
/// title is built from, which [`fit_batch`] needs and the joined title cannot
/// give back: splitting `title` on ` · ` would come apart on a title that
/// contains the separator. `None` on every other kind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RowCells {
    /// `HH:MM` — the segment's start in `cfg.tz`.
    pub time: String,
    /// The slot energy and `↓`, or the kind's glyph.
    pub ci: String,
    /// `p3`, on a row that is on §7's scale.
    pub p: String,
    /// One of `✓ ▶ ⚠` or a space — and never a glyph.
    pub mark: String,
    /// The item's title, or the row's own words. **Unfitted.**
    pub title: String,
    /// `@m3`.
    pub parent: String,
    /// `2b`, `2b×1.6`, `30m`.
    pub est: String,
    /// `(67m)` on a row the log closed.
    pub actual: String,
    /// The trailing note column.
    pub note: String,
    /// A batch's members, whole; `None` on every other kind.
    pub batch_names: Option<Vec<String>>,
}

impl RowCells {
    /// The nine, in §4.3's order.
    pub fn cells(&self) -> [&str; 9] {
        [
            &self.time,
            &self.ci,
            &self.p,
            &self.mark,
            &self.title,
            &self.parent,
            &self.est,
            &self.actual,
            &self.note,
        ]
    }
}

/// **The cells of one row, measured by nothing.**
///
/// Everything [`render_row`] prints comes from here, and the Lean kernel's
/// `Emit.rowOf` answers the same nine for the same segment —
/// `tm/tests/kernel_row_cells.rs` is the machine that compares them.
pub fn row_cells(
    seg: &Segment,
    plan: &DayPlan,
    tree: &Tree,
    cfg: &Config,
    prios: &HashMap<&Id, u8>,
) -> RowCells {
    let item = seg.item.as_ref().and_then(|id| tree.get(id));
    let work = shows_scale(seg);

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

    let actual = if seg.flags.done && !matches!(seg.kind, SegKind::Rest) {
        format!("({}m)", seg.minutes())
    } else {
        String::new()
    };

    RowCells {
        time: fmt_clock(seg.start),
        ci: ci_cell,
        p: p_cell,
        mark: mark_of(seg).to_string(),
        title: title_cell(seg, tree, cfg),
        parent: parent_cell(seg, tree),
        est: est_cell(seg, tree, cfg),
        actual,
        note: note_cell(seg, tree, plan),
        batch_names: match &seg.kind {
            SegKind::Batch(ids) => Some(batch_names(ids, tree)),
            _ => None,
        },
    }
}

/// **One timeline row (§4.3): the padder, and nothing else.**
///
/// It takes cells and lays them out; it does not know what a segment is. That
/// split is D30 Q6 (a) made structural — the cells can come from
/// [`row_cells`] or from the Lean kernel's `Emit.rowOf` over the wire, and the
/// bytes are the same bytes either way (`tm/tests/kernel_row_cells.rs`).
///
/// It is still the **one padder** (D43): `pad`, [`truncate`] and [`fit_batch`]
/// are here, because this is where the terminal's columns are.
pub fn render_row(cells: &RowCells, layout: &Layout) -> String {
    let title = match &cells.batch_names {
        // A batch keeps its member list and its `(n)` (§7.5): the frame is
        // fitted, not truncated away.
        Some(names) => fit_batch(names, layout.title_w),
        None => truncate(&cells.title, layout.title_w),
    };
    let mut row = String::with_capacity(80);
    row.push_str(&pad(&cells.time, TIME_W));
    row.push_str("  ");
    row.push_str(&pad(&cells.ci, CI_W));
    row.push_str(&pad(&cells.p, P_W));
    row.push(' ');
    row.push_str(&cells.mark);
    row.push(' ');
    row.push_str(&pad(&title, layout.title_w));
    row.push_str("  ");
    row.push_str(&pad(&cells.parent, PARENT_W));
    row.push_str("  ");
    row.push_str(&pad(&cells.est, EST_W));
    row.push_str("  ");
    row.push_str(&pad(&cells.actual, ACTUAL_W));
    row.push_str("  ");
    row.push_str(&cells.note);
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
    /// One cell per *segment* of the plan, in `DayPlan::segments` order — the
    /// segment's own hue, brightness, style and tooltip, whether or not it won
    /// a column. [`render_svg`] draws from this (one `<rect>` per segment,
    /// §17.2); the terminal widget draws from [`DayBar::cells`], and both
    /// therefore agree on colour and hover text.
    pub segments: Vec<Cell>,
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

/// Seconds from wake to the start of column `col` — the one boundary
/// [`DayBar::start_of`], [`DayBar::col_of`] and [`cells_of`] all draw, so that
/// `col_of(start_of(c)) == Some(c)` holds for every `cols`, not only the ones
/// that divide 1440 (`cols = 110`, the config's `min_width`, does not).
fn cell_start_secs(col: usize, cell_min: f64) -> i64 {
    (col as f64 * cell_min * 60.0).round() as i64
}

/// The column `secs` after wake falls in, by [`cell_start_secs`]' boundaries;
/// out-of-range offsets clamp to the first or last column.
fn col_at(secs: i64, cols: usize, cell_min: f64) -> usize {
    let cols = cols.max(1);
    // The float estimate is right to within one column; walk to the boundary
    // the cells were actually cut on.
    let mut col = ((secs.max(0) as f64 / 60.0) / cell_min.max(f64::MIN_POSITIVE)) as usize;
    col = col.min(cols - 1);
    while col > 0 && secs < cell_start_secs(col, cell_min) {
        col -= 1;
    }
    while col + 1 < cols && secs >= cell_start_secs(col + 1, cell_min) {
        col += 1;
    }
    col
}

impl DayBar {
    /// Minutes per cell (`24 h / cols`).
    pub fn cell_minutes(&self) -> f64 {
        f64::from(self.span_min) / self.cols.max(1) as f64
    }
    /// The column an instant falls in, or `None` when it is off the bar.
    ///
    /// The inverse of [`DayBar::start_of`]: `col_of(start_of(c)) == Some(c)`
    /// for every column of every bar.
    pub fn col_of(&self, t: DateTime<Tz>) -> Option<usize> {
        let secs = (t - self.wake).num_seconds();
        if secs < 0 || secs >= i64::from(self.span_min) * 60 {
            return None;
        }
        Some(col_at(secs, self.cols, self.cell_minutes()))
    }
    /// Where an instant sits horizontally in a bar `width` units wide, clamped
    /// to the bar.
    pub fn x_of(&self, t: DateTime<Tz>, width: f64) -> f64 {
        let m = (t - self.wake).num_seconds() as f64 / 60.0;
        (m / f64::from(self.span_min) * width).clamp(0.0, width)
    }
    /// The instant a column starts at.
    pub fn start_of(&self, col: usize) -> DateTime<Tz> {
        self.wake + Duration::seconds(cell_start_secs(col, self.cell_minutes()))
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
///
/// Rendering never fails on a bad config entry — a day bar with one grey
/// project still beats no day bar — so a caller that wants to *report* a
/// malformed `tui.palette` (`tm check`, the TUI at start-up) validates it with
/// [`palette_colours`] first.
pub fn palette_rgb(cfg: &Config, idx: usize) -> (u8, u8, u8) {
    let palette = &cfg.tui.palette;
    if palette.is_empty() {
        return (0x88, 0x88, 0x88);
    }
    parse_hex_colour(&palette[idx % palette.len()]).unwrap_or((0x88, 0x88, 0x88))
}

/// The whole `cfg.tui.palette` as colours, or the first entry that is not
/// `#rrggbb` (§16's `palette`).
///
/// `config.rs` stores the palette as `Vec<String>` without checking it; this
/// is where a typo such as `#ff00` becomes an [`EmitError`] instead of
/// silently rendering as mid-grey.
pub fn palette_colours(cfg: &Config) -> Result<Vec<(u8, u8, u8)>, EmitError> {
    cfg.tui
        .palette
        .iter()
        .map(|s| parse_hex_colour(s))
        .collect()
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
    let cursor = col_at((now - wake).num_seconds(), cols, cell_min);
    let row = |p: &DayPlan| -> Vec<Cell> { cells_of(p, tree, cfg, cols, wake, cell_min, cursor) };
    DayBar {
        cells: row(plan),
        segments: plan
            .segments
            .iter()
            .enumerate()
            .map(|(idx, seg)| cell_of(seg, idx, tree, cfg, plan))
            .collect(),
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
        let cs = wake + Duration::seconds(cell_start_secs(col, cell_min));
        let ce = wake + Duration::seconds(cell_start_secs(col + 1, cell_min));
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
///
/// `plan` must be the plan `bar` was built from: each segment's colour and
/// `<title>` come from `bar.segments[idx]`.
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
        now = fmt_clock(bar.now)
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
/// The colour and the tooltip come from the bar's per-segment cell
/// ([`DayBar::segments`]), which every segment has — a segment that wins no
/// *column* (one shorter than a cell, or one overlapped by a finished segment
/// on the log side) still draws in its project hue and still carries its hover
/// text, which §12.1 and §17.2 both ask for.
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
    let cell = bar.segments.get(idx);
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

/// **The positions `tm now` shows** (§13): the segment `now` is inside — the
/// one the planner marked current, else the first unfinished one containing
/// `now` — and the next three that have not started.
///
/// It answers **positions into `plan.segments`**, not segments, because that is
/// what makes D30 Q5 (a)'s "`tm now`'s rows are a contiguous sub-list of the
/// file's" a checkable claim: two items sharing a title give byte-identical
/// rows, so a sub-list found by value has more than one witness (README gap
/// **1197**). `one_renderer.rs` indexes by these.
///
/// **Contiguity is a property of the day, not of this selector**, and that is
/// declared rather than assumed: `next` takes the first three positions after
/// `current` whose segment has not started, so a segment *after* the current
/// one that started *before* `now` — an overlap — would be skipped and the run
/// would have a hole. The planner does not emit overlapping rows and
/// `one_renderer.rs` asserts the run is whole on the fixture it drives; nothing
/// here forces it.
pub fn now_window(plan: &DayPlan, now: DateTime<Tz>) -> (Option<usize>, Vec<usize>) {
    let current = plan
        .segments
        .iter()
        .position(|s| s.flags.current && s.start <= now && now < s.end)
        .or_else(|| {
            plan.segments
                .iter()
                .position(|s| s.start <= now && now < s.end && !s.flags.done)
        });
    let next: Vec<usize> = plan
        .segments
        .iter()
        .enumerate()
        .filter(|(i, s)| s.start >= now && Some(*i) != current)
        .map(|(i, _)| i)
        .take(3)
        .collect();
    (current, next)
}

/// [`render_now`] with an explicit config.
///
/// **A selection over [`plan_rows`], not a second renderer** (D30 Q5 (a),
/// README gaps **1104** and **1109**). Until W-23 this function had its own
/// format string — `▶ title  @O1  ci4  p5  2b` over two spaces, with no
/// columns and no truncation — so `tm now` and the day file printed different
/// text for the same segment, which is PLAN §4's G1 with one of its three
/// implementations still alive. It now prints *the row*, byte for byte as the
/// day file wrote it, and chooses **which** rows with [`now_window`].
///
/// **This is a behaviour change to `tm now`** and is the one this step takes
/// deliberately: design §5's Q5 (a) says "`render_now_with` stops formatting and
/// starts selecting" and then adds "No user-visible change", which is false of
/// (a) and true only of the day file and the TUI Timeline — `tm now`'s bytes
/// necessarily move, because they were never the file's (README gap 1194
/// measured exactly that). The behaviour row is in the README block.
///
/// The two lines that are **not** rows stay `tm now`'s own: the `elapsed … left
/// …` annotation under the current row (indented two spaces, so it cannot be
/// mistaken for one) and `— nothing running (HH:MM)`.
pub fn render_now_with(plan: &DayPlan, tree: &Tree, cfg: &Config, now: DateTime<Tz>) -> String {
    let rows = plan_rows(plan, tree, cfg, &Layout::default());
    let (current, next) = now_window(plan, now);
    let mut out = String::new();
    match current {
        Some(i) => {
            out.push_str(&rows[i]);
            out.push('\n');
            let seg = &plan.segments[i];
            out.push_str(&format!(
                "  {}–{} · elapsed {} · left {}\n",
                fmt_clock(seg.start),
                fmt_clock(seg.end),
                fmt_dur(minutes_between(&seg.start, &now)),
                fmt_dur(minutes_between(&now, &seg.end))
            ));
        }
        None => {
            out.push_str(&format!("— nothing running ({})\n", fmt_clock(now)));
        }
    }
    if next.is_empty() {
        out.push_str("next   —\n");
        return out;
    }
    out.push_str("next\n");
    for i in next {
        out.push_str(&rows[i]);
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
    /// Σ of `minutes_at_ci` — the minutes the plan actually spends on blocks.
    pub total_min: u32,
    /// The day's budget in minutes (`budget_blocks × block_min`) — §11's
    /// denominator.
    pub budget_min: u32,
    /// §11's "share of budget with `ci ≥ 4`": `(minutes_at_ci[4] +
    /// minutes_at_ci[5]) / budget_min`.
    ///
    /// It is a share *of the budget*, not of what was planned, so a day that
    /// fills its budget with high-energy work reads 100% and one that
    /// overruns it reads above 100%. With no budget (`budget_blocks = 0`) it
    /// falls back to the plan's own block minutes, and with neither it is 0.
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

/// §11's "Energy mix": minutes at each `ci`, the share of the budget at
/// `ci ≥ 4`, and the `↓` count.
///
/// Takes the `tree` and the `cfg` (which the scope's signature omitted)
/// because a segment carries the *slot's* energy while the mix is about the
/// *item's* `ci` (the slot energy is the fallback when the tree does not know
/// the item), and because §11's denominator is the day's budget —
/// `budget_blocks × block_min` — which needs `block_min` from the config.
pub fn legend(plan: &DayPlan, tree: &Tree, cfg: &Config) -> EnergyMix {
    let mut mix = EnergyMix {
        budget_min: plan.budget_blocks.saturating_mul(cfg.block_min()),
        ..EnergyMix::default()
    };
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
    let denominator = if mix.budget_min > 0 {
        mix.budget_min
    } else {
        mix.total_min
    };
    if denominator > 0 {
        let high = mix.minutes_at_ci[4] + mix.minutes_at_ci[5];
        mix.share_ci4_plus = f64::from(high) / f64::from(denominator);
    }
    mix
}
