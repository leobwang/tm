//! Screen 5 — Inbox and capture (tm-spec-v1.md §12.5).
//!
//! # API overview
//!
//! ```text
//! ┌─ Capture ───────────────────────────────────────────────────────────────┐
//! │ > pset2 fri 6b ci4 max 2b/d                                             │
//! │   parsed  - [ ] 4 6b pset2  due:2026-09-11T23:59 max:2b/d  → week/2026-W37.md #Milestones │
//! │   Enter save · Tab change file · Esc cancel                             │
//! └─────────────────────────────────────────────────────────────────────────┘
//!  Inbox (4)   t triage line · C Claude Code triages all · x drop
//! ```
//!
//! The capture line parses as you type. [`capture`] turns free text into the
//! §4.1 line `tm add` would write and names the file it goes to:
//!
//! * [`normalize`] recognises the natural-language shorthands §12.5's example
//!   uses — `fri` → `due:2026-09-11T23:59`, `6b` → the leading estimate,
//!   `ci4` → the min-energy, `max 2b/d` → `max:2b/d` — and leaves every token
//!   that is already §4.1 grammar (`@parent`, `#tag`, `!k`, `key:value`,
//!   flags) untouched.
//! * The result is then round-tripped through [`grammar::parse_line`] +
//!   [`grammar::format_item_line`], so the preview is *by construction* a
//!   canonical §4.1 line — which is exactly what `tm add "<line>"` writes,
//!   plus the `^id` it assigns (M7: "capture preview matches `tm add`").
//! * [`Target`] / [`targets`] — the ring `Tab` cycles: this week's
//!   `# Milestones` and `# Tasks`, `backlog.md`, today's `# Pinned`, and
//!   `inbox.md`. The `inbox.md` target keeps the text verbatim (§2: "capture,
//!   untriaged (bare lines)"), which is what `tm add --to inbox.md` does too —
//!   and it is never the *automatic* target of a line that came from
//!   `inbox.md`, because triage is meant to get the line out of there.
//! * [`Capture::problem`] is what `tm add` would refuse (a line that does not
//!   parse, an `^id` that is taken, and — since the owner's D6 — a `@parent`
//!   that names nothing); [`Capture::warning`] is what `tm check` would then
//!   complain about (an `after:^id` that names nothing). The first blocks
//!   `Enter`, the second only colours the preview — which is exactly what
//!   `tm add` does with the same input.
//!
//! Below the box, [`inbox_lines`] lists `inbox.md` with the same preview per
//! line; `t` loads one into the capture line, `x` drops it, and `C` prints the
//! command that hands the whole file to Claude Code — this screen never shells
//! out itself (see [`CLAUDE_TRIAGE`]).
//!
//! [`CaptureState`], [`render`] and [`on_key`] are the shell-facing surface,
//! as in [`crate::tui::queue`].

use std::fmt;

use chrono::{Datelike, Duration, NaiveDate, Weekday};
use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};
use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, Borders, Paragraph};
use ratatui::Frame;

use tm_core::config::Config;
use tm_core::emit;
use tm_core::grammar::{self, ParseCtx, ParsedFile};
use tm_core::store::{edit, Store, StoreError};
use tm_core::model::{
    self, Dep, Dur, Horizon, Rate, Rule, WindowRange,
};

use super::queue::{Action, Mutation, View};

/// The command `C` prints (§12.5: "C Claude Code triages all"). The screen
/// never runs it; §14 makes Claude Code a peer frontend, not a subprocess of
/// the TUI.
pub const CLAUDE_TRIAGE: &str = "claude \"/triage\"   (reads plan/inbox.md, one `tm add` per line)";

// ---------------------------------------------------------------------------
// Targets
// ---------------------------------------------------------------------------

/// A file (and section) a capture can go to (§6.1: horizon is the file).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Target {
    /// Path relative to the plan root.
    pub file: String,
    /// The heading to insert under, when the file has sections.
    pub section: Option<String>,
}

impl Target {
    /// Build a target.
    pub fn new(file: impl Into<String>, section: Option<&str>) -> Target {
        Target {
            file: file.into(),
            section: section.map(str::to_string),
        }
    }

    /// True for `inbox.md`, `routines.md` and `optional.md` — the files whose
    /// lines carry no checkbox (§4.3).
    pub fn is_bare(&self) -> bool {
        Horizon::from_path(&self.file)
            .map(|h| h.allows_missing_state())
            .unwrap_or(false)
    }
}

impl fmt::Display for Target {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.section {
            Some(s) => write!(f, "{} #{s}", self.file),
            None => write!(f, "{}", self.file),
        }
    }
}

/// The ring `Tab` cycles through (§12.5: "Tab change file").
pub fn targets(view: &View<'_>) -> Vec<Target> {
    let week = Horizon::Week(view.week()).path();
    vec![
        Target::new(week.clone(), Some("Milestones")),
        Target::new(week, Some("Tasks")),
        Target::new("backlog.md", None),
        Target::new(Horizon::Day(view.today).path(), Some("Pinned")),
        Target::new("inbox.md", None),
    ]
}

/// Index of `inbox.md` in [`targets`].
const INBOX_TARGET: usize = 4;
/// Index of `backlog.md` in [`targets`].
const BACKLOG_TARGET: usize = 2;

/// Which target a capture goes to when the user has not pressed `Tab`.
///
/// A dated line is a milestone (§4.3: `^d1` lives in the week file with its
/// `due:`), a line with a `@parent` is a task under it, and anything else is
/// untriaged capture — `inbox.md`.
///
/// `from_inbox` is the `t` (triage a line) path, and there the last case is
/// *not* `inbox.md`: triage is "get this line out of the inbox", so re-adding
/// it to the file it came from would be a drop-and-re-add that leaves the
/// screen exactly as it was. An undated, unparented line's home is
/// `backlog.md` (§2: not scheduled), and `Tab` still reaches every other
/// target.
fn default_target(parsed: &Normalized, from_inbox: bool) -> usize {
    if parsed.tokens.iter().any(|t| {
        t.starts_with("due:") || t.starts_with("at:") || t.starts_with("win:")
    }) {
        0
    } else if parsed.tokens.iter().any(|t| t.starts_with('@')) {
        1
    } else if from_inbox {
        BACKLOG_TARGET
    } else {
        INBOX_TARGET
    }
}

// ---------------------------------------------------------------------------
// Natural language → §4.1
// ---------------------------------------------------------------------------

/// What [`normalize`] recognised in the capture line.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Normalized {
    /// `ci4` / `ci 4` / `ci:4`.
    pub ci: Option<u8>,
    /// The leading estimate (`6b`, `30m`, `1h30m`).
    pub est: Option<String>,
    /// Everything the parser did not claim, in order.
    pub title: String,
    /// The §4.1 tokens, in the order they were written.
    pub tokens: Vec<String>,
    /// Why the line cannot be an item, when it cannot.
    pub problem: Option<String>,
}

/// Recognise §12.5's shorthands in `input`.
///
/// The rules, in the order a word is tested:
///
/// 1. `@ref`, `#tag`, `!k`, `^id`, a `key:value` whose key is in
///    [`grammar::KEYS`], and the [`grammar::FLAGS`] pass through untouched.
/// 2. `ci<N>` and `p<N>` (0..=5, 1..=4) become `ci` and `!k`.
/// 3. A keyword with a value that validates — `due`/`by`, `max`/`cap`, `min`,
///    `every`, `loc`, `at`, `after`, `dur`, `win`, `ci` — becomes `key:value`.
/// 4. A bare duration (`6b`, `30m`, `2h`, `1h30m`) becomes the leading
///    estimate; a second one stays in the title.
/// 5. A day word — `today`, `tomorrow`, a weekday, or an ISO date — becomes
///    `due:`. A relative day gets the end of that day (`T23:59`, as §12.5's
///    example shows); a date the user wrote out stays as written.
/// 6. Anything else is title.
///
/// Rules 4 and 5 are the guesses: a title whose own words are a duration or a
/// weekday ("Sat prep", "buy 2h of parking") loses them to the estimate and the
/// due date. The preview is there to show that immediately, and writing the
/// §4.1 token out (`due:2026-09-12`) always wins over the guess.
///
/// Rule 3 never guesses. Its values must *validate*, and the two keywords whose
/// value space is "any word" are deliberately narrow: `after` takes only an
/// explicit `^id` or `event:<name>` (so "call mom after lunch" stays a title
/// and does not become `after:^lunch`, which §5.5 would make permanently
/// ineligible and `tm check` would call `dangling-dep`), and `loc` only the
/// §4.1 location words. A location of your own is written out — `loc:cafe` —
/// and rule 1 passes it through.
pub fn normalize(input: &str, cfg: &Config, today: NaiveDate) -> Normalized {
    let block_min = cfg.block_min();
    let mut out = Normalized::default();
    let mut title: Vec<String> = Vec::new();
    let words: Vec<&str> = input.split_whitespace().collect();
    // A shape the user wrote out anywhere in the line wins: no guessed `due:`
    // is added next to it (two `due:` tokens would not parse).
    let mut dated = words.iter().any(|w| {
        let lw = w.to_ascii_lowercase();
        lw.starts_with("due:") || lw.starts_with("at:") || lw.starts_with("win:")
    });
    let mut i = 0;
    while i < words.len() {
        let w = words[i];
        let lower = w.to_ascii_lowercase();
        // 1. already grammar.
        if w.starts_with('@') || w.starts_with('#') || w.starts_with('^') {
            out.tokens.push(w.to_string());
            i += 1;
            continue;
        }
        if let Some(rest) = w.strip_prefix('!') {
            if matches!(rest.parse::<u8>(), Ok(k) if (1..=4).contains(&k)) {
                out.tokens.push(w.to_string());
                i += 1;
                continue;
            }
        }
        if let Some((k, v)) = w.split_once(':') {
            if grammar::KEYS.contains(&k) && !v.is_empty() {
                if k == "ci" {
                    out.ci = v.parse::<u8>().ok().filter(|n| *n <= 5);
                } else {
                    out.tokens.push(w.to_string());
                }
                i += 1;
                continue;
            }
        }
        if grammar::FLAGS.contains(&lower.as_str()) {
            out.tokens.push(lower);
            i += 1;
            continue;
        }
        // 2. `ci4`, `p2`.
        if let Some(n) = lower.strip_prefix("ci").and_then(|r| r.parse::<u8>().ok()) {
            if n <= 5 {
                out.ci = Some(n);
                i += 1;
                continue;
            }
        }
        if let Some(n) = lower.strip_prefix('p').and_then(|r| r.parse::<u8>().ok()) {
            if (1..=4).contains(&n) {
                out.tokens.push(format!("!{n}"));
                i += 1;
                continue;
            }
        }
        // 3. keyword + value.
        if let Some(next) = words.get(i + 1) {
            match keyword(&lower, next, cfg, today) {
                Some(Keyword::Ci(n)) => {
                    out.ci = Some(n);
                    i += 2;
                    continue;
                }
                Some(Keyword::Token(t)) if !(dated && shapes(&t)) => {
                    dated |= shapes(&t);
                    out.tokens.push(t);
                    i += 2;
                    continue;
                }
                _ => {}
            }
        }
        // 4. a bare duration.
        if out.est.is_none() && Dur::parse_no_days(w, block_min).is_ok() {
            out.est = Some(w.to_string());
            i += 1;
            continue;
        }
        // 5. a day word.
        if !dated {
            if let Some(v) = day_word(&lower, today) {
                out.tokens.push(format!("due:{v}"));
                dated = true;
                i += 1;
                continue;
            }
        }
        // 6. title.
        title.push(w.to_string());
        i += 1;
    }
    out.title = title.join(" ");
    if out.title.is_empty() {
        out.problem = Some("no title".to_string());
    }
    out
}

/// True for a token that fixes the item's shape (§3.1) — at most one may be
/// written.
fn shapes(token: &str) -> bool {
    token.starts_with("due:") || token.starts_with("at:") || token.starts_with("win:")
}

/// What a `keyword value` pair produced.
enum Keyword {
    /// `ci 4`.
    Ci(u8),
    /// Any other `key:value`.
    Token(String),
}

/// `keyword value` → a §4.1 token, when the value validates.
fn keyword(word: &str, next: &str, cfg: &Config, today: NaiveDate) -> Option<Keyword> {
    let bm = cfg.block_min();
    match word {
        "ci" => next.parse::<u8>().ok().filter(|n| *n <= 5).map(Keyword::Ci),
        "due" | "by" | "deadline" => {
            day_word(&next.to_ascii_lowercase(), today).map(|v| Keyword::Token(format!("due:{v}")))
        }
        "max" | "cap" => Rate::parse(next, bm)
            .ok()
            .map(|_| Keyword::Token(format!("max:{next}"))),
        "min" => Rate::parse(next, bm)
            .ok()
            .map(|_| Keyword::Token(format!("min:{next}"))),
        "every" => Rule::parse(next)
            .ok()
            .map(|_| Keyword::Token(format!("every:{next}"))),
        "dur" => Dur::parse(next, bm)
            .ok()
            .map(|_| Keyword::Token(format!("dur:{next}"))),
        "win" => WindowRange::parse(next)
            .ok()
            .map(|_| Keyword::Token(format!("win:{next}"))),
        "at" => model::parse_interval(next)
            .ok()
            .map(|_| Keyword::Token(format!("at:{next}"))),
        // Only an explicit reference: a bare word after "after" is prose
        // ("call mom after lunch"), and turning it into `after:^lunch` would
        // write a §5.5 dependency on an item that does not exist.
        "after" => Dep::parse_list(next)
            .ok()
            .filter(|d| !d.is_empty())
            .filter(|_| {
                next.split(',')
                    .all(|p| {
                        let p = p.trim();
                        p.starts_with('^') || p.starts_with("event:")
                    })
            })
            .map(|_| Keyword::Token(format!("after:{next}"))),
        // Only §4.1's own location words; `loc:cafe` is written out and rule 1
        // passes it through untouched.
        "loc" => matches!(next.to_ascii_lowercase().as_str(), "any" | "lounge" | "home" | "out")
            .then(|| Keyword::Token(format!("loc:{}", next.to_ascii_lowercase()))),
        _ => None,
    }
}

/// A day word → a `due:` value: `today`, `tomorrow`, `tonight`, a weekday, an
/// ISO date, or an ISO date-time.
fn day_word(word: &str, today: NaiveDate) -> Option<String> {
    let eod = |d: NaiveDate| format!("{d}T23:59");
    match word {
        "today" | "tonight" => return Some(eod(today)),
        "tomorrow" => return Some(eod(today + Duration::days(1))),
        _ => {}
    }
    if let Ok(w) = model::parse_weekday(word) {
        return Some(eod(next_weekday(today, w)));
    }
    if let Some((d, t)) = word.split_once('T') {
        if NaiveDate::parse_from_str(d, "%Y-%m-%d").is_ok() && t.len() == 5 {
            return Some(word.to_string());
        }
    }
    if NaiveDate::parse_from_str(word, "%Y-%m-%d").is_ok() {
        return Some(word.to_string());
    }
    None
}

/// The first date on or after `today` that falls on `w`.
fn next_weekday(today: NaiveDate, w: Weekday) -> NaiveDate {
    let delta = (w.num_days_from_monday() as i64 - today.weekday().num_days_from_monday() as i64
        + 7)
        % 7;
    today + Duration::days(delta)
}

// ---------------------------------------------------------------------------
// The capture
// ---------------------------------------------------------------------------

/// One parse of the capture line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Capture {
    /// The text as typed.
    pub raw: String,
    /// The §4.1 line `tm add` would write — the preview's middle column. Empty
    /// when the line cannot be parsed.
    pub line: String,
    /// Where it goes.
    pub target: Target,
    /// Which entry of [`targets`] that is.
    pub target_index: usize,
    /// Why it cannot be saved, when it cannot — the same refusals `tm add`
    /// makes (a line that does not parse, an `^id` that is already taken).
    pub problem: Option<String>,
    /// A `tm check` problem the line *would* create once saved: a dependency
    /// that names nothing (§5.5). `tm add` writes such a line, so the capture
    /// does too — but it says so instead of showing a clean green parse. (A
    /// `@parent` that names nothing is a [`Capture::problem`] since the
    /// owner's D6: `tm add` refuses it.)
    pub warning: Option<String>,
}

/// Parse the capture line for a target (`None` = the automatic one).
///
/// The returned [`Capture::line`] is what `tm add "<line>" --to <file>` writes,
/// modulo the `^id` the CLI appends.
#[allow(dead_code)] // §17 M7's `tui_queue_capture.rs` drives it directly.
pub fn capture(input: &str, view: &View<'_>, target: Option<usize>) -> Capture {
    capture_from(input, view, target, false)
}

/// The same, saying whether the text came from `inbox.md` (the `t` key).
///
/// A triaged line's automatic target is never `inbox.md` — see
/// [`default_target`].
pub fn capture_from(
    input: &str,
    view: &View<'_>,
    target: Option<usize>,
    from_inbox: bool,
) -> Capture {
    let raw = input.trim().to_string();
    let parsed = normalize(&raw, view.cfg, view.today);
    let ring = targets(view);
    let idx = target.unwrap_or_else(|| default_target(&parsed, from_inbox)) % ring.len();
    let target = ring[idx].clone();
    if raw.is_empty() {
        return Capture {
            raw,
            line: String::new(),
            target,
            target_index: idx,
            problem: Some("type to capture".to_string()),
            warning: None,
        };
    }
    // §2: `inbox.md` holds bare lines, so capture into it keeps the words.
    if target.is_bare() {
        let line = if raw.starts_with("- ") {
            raw.clone()
        } else {
            format!("- {raw}")
        };
        return Capture {
            raw,
            line,
            target,
            target_index: idx,
            problem: None,
            warning: None,
        };
    }
    match build(&parsed, &target, view) {
        Ok((line, warning)) => Capture {
            raw,
            line,
            target,
            target_index: idx,
            problem: None,
            warning,
        },
        Err(e) => Capture {
            raw,
            line: String::new(),
            target,
            target_index: idx,
            problem: Some(e),
            warning: None,
        },
    }
}

/// Assemble and canonicalise the §4.1 line, and check it against the tree.
fn build(
    parsed: &Normalized,
    target: &Target,
    view: &View<'_>,
) -> Result<(String, Option<String>), String> {
    if let Some(p) = &parsed.problem {
        return Err(p.clone());
    }
    let mut parts = vec!["- [ ]".to_string()];
    if let Some(ci) = parsed.ci {
        parts.push(ci.to_string());
    }
    if let Some(e) = &parsed.est {
        parts.push(e.clone());
    }
    parts.push(parsed.title.clone());
    parts.extend(parsed.tokens.iter().cloned());
    let text = parts.join(" ");
    let horizon = Horizon::from_path(&target.file).unwrap_or(Horizon::Backlog);
    let ctx = ParseCtx {
        horizon,
        ..ParseCtx::new(&target.file, view.cfg.block_min())
    };
    let item = grammar::parse_line(&text, &ctx).map_err(|e| e.to_string())?;
    if !item.problems.is_empty() {
        return Err(item.problems.join("; "));
    }
    // The owner's D6: `tm add` refuses a line whose `@parent` names no item
    // (a tree with one refuses every kernel-backed verb), so the preview
    // refuses it too rather than promise a save that cannot happen.
    if let Some(e) = dangling_parent(&item, view) {
        return Err(e);
    }
    // §4.1: ids are global across the tree, and `tm add` refuses a line whose
    // `^id` is taken (exit 1) rather than writing a `tm check` duplicate. The
    // preview has to refuse it too, or it promises a save that cannot happen.
    if item.has_id() && view.files.ids().contains(item.id.as_str()) {
        return Err(format!(
            "{} is already used{} — drop the `^id` and one will be assigned",
            item.id.token(),
            view.files
                .file_of(&item.id)
                .map(|f| format!(" in {f}"))
                .unwrap_or_default()
        ));
    }
    Ok((grammar::format_item_line(&item).map_err(|e| e.to_string())?, dangling(&item, view)))
}

/// A `@parent` that names nothing in the tree (§6.1): refused by `tm add` since
/// the owner's D6 (kernel/README.md gap 22, closed at stage 4 final step 3).
fn dangling_parent(item: &model::Item, view: &View<'_>) -> Option<String> {
    let p = item.parent.as_ref()?;
    (!view.tree.contains(&p.to_id())).then(|| {
        format!("parent {} does not exist — `tm add` refuses a dangling parent", p.token())
    })
}

/// The `tm check` problem the line would create: an `after:^id` that names
/// nothing in the tree (§5.5). `tm add`'s carve-out path writes the line
/// anyway, so this is a warning, not a refusal. (A `@parent` that names nothing
/// is a refusal since the owner's D6 — [`dangling_parent`].)
fn dangling(item: &model::Item, view: &View<'_>) -> Option<String> {
    for dep in &item.after {
        if let Dep::Item(id) = dep {
            if !view.tree.contains(id) {
                return Some(format!("dependency after:{} does not exist", id.token()));
            }
        }
    }
    None
}

/// §12.5's `parsed …  → <file> #<section>` line.
pub fn preview_text(cap: &Capture) -> String {
    match (&cap.problem, &cap.warning) {
        (Some(p), _) if cap.line.is_empty() => format!("parsed  ! {p}"),
        (_, Some(w)) => format!("parsed  {}  → {}  ⚠ {w}", cap.line, cap.target),
        _ => format!("parsed  {}  → {}", cap.line, cap.target),
    }
}

// ---------------------------------------------------------------------------
// The inbox list
// ---------------------------------------------------------------------------

/// One capture line of `inbox.md`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InboxLine {
    /// 1-based line number in `inbox.md`.
    pub line: usize,
    /// The text, without its leading `- `.
    pub raw: String,
    /// The §4.1 line `t` would capture it as.
    pub parsed: String,
    /// Why it does not parse, when it does not.
    pub problem: Option<String>,
    /// Where `t` would send it (§12.5: the target the capture box opens on).
    pub target: Target,
}

/// `inbox.md`'s capture lines with their previews (§12.5, `tm triage`).
///
/// Headings, blank lines and the guidance `tm init` writes inside one HTML
/// comment are skipped, exactly as `tm triage` skips them, and the line numbers
/// are `tm triage`'s. The `parsed` column is *this screen's* preview — what
/// `t` then `Enter` would write, natural-language guesses and all — which is
/// strictly more than `tm triage`'s plain §4.1 re-parse: the two agree on every
/// line [`normalize`] recognises nothing in, and differ exactly where the
/// shorthands of §12.5's own example fire.
pub fn inbox_lines(view: &View<'_>) -> Vec<InboxLine> {
    let Some(file) = view.files.file("inbox.md") else {
        return Vec::new();
    };
    let mut out = Vec::new();
    // `grammar::comment_after` is `Plan.lean`'s automaton and the only one:
    // this pane had its own copy of it until W-24 (D47).
    let mut in_comment = false;
    for line in &file.lines {
        let text = line.text();
        let was_in_comment = in_comment;
        let opener = grammar::opens_comment(&text);
        in_comment = grammar::comment_after(in_comment, &text);
        if was_in_comment || opener {
            continue;
        }
        let trimmed = text.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let raw = trimmed.strip_prefix("- ").unwrap_or(trimmed).to_string();
        let cap = capture_from(&raw, view, None, true);
        out.push(InboxLine {
            line: line.number,
            raw,
            parsed: cap.line,
            problem: cap.problem,
            target: cap.target,
        });
    }
    out
}

/// Remove one raw line from `inbox.md` — [`Mutation::DropInboxLine`] and the
/// tail of a triaged [`Mutation::Capture`] (§12.5: `t` gets the line *out* of
/// the inbox).
///
/// `line` is 1-based, as [`InboxLine::line`] and `tm triage` number them. A
/// line number the file no longer has is a no-op rather than an error: the
/// file may have been edited since the screen was drawn.
pub fn drop_line(store: &dyn Store, line: usize) -> Result<bool, StoreError> {
    let mut removed = false;
    store.modify_file(INBOX_FILE, &mut |parsed: &ParsedFile| {
        removed = false;
        let Some(idx) = parsed.lines.iter().position(|l| l.number == line) else {
            return Ok(None);
        };
        removed = true;
        Ok(Some(edit::remove_line(parsed, idx).0))
    })?;
    Ok(removed)
}

/// The capture file §2 and §12.5 name.
pub const INBOX_FILE: &str = "inbox.md";

// ---------------------------------------------------------------------------
// State and keys
// ---------------------------------------------------------------------------

/// Screen 5's state (§12.5).
#[derive(Debug, Clone, Default)]
pub struct CaptureState {
    /// The capture line's text.
    pub buffer: String,
    /// True while the capture line has focus.
    pub editing: bool,
    /// The target the user chose with `Tab`; `None` = automatic.
    pub target: Option<usize>,
    /// Cursor in the inbox list.
    pub sel: usize,
    /// The `inbox.md` line `t` loaded, to drop once the capture is saved.
    pub triaging: Option<usize>,
    /// The last message (a refusal, or the `C` command).
    pub note: Option<String>,
}

impl CaptureState {
    /// A fresh screen: the inbox list has focus.
    pub fn new() -> CaptureState {
        CaptureState::default()
    }

    /// The current parse of the capture line.
    pub fn capture(&self, view: &View<'_>) -> Capture {
        capture_from(&self.buffer, view, self.target, self.triaging.is_some())
    }
}

/// §12.5's key row while the capture line has focus.
pub const KEYMAP_EDITING: &str = " Enter save · Tab change file · Esc cancel";

/// §12.5's key row for the inbox list.
pub const KEYMAP_LIST: &str = " i capture · t triage line · C Claude Code triages all · x drop";

/// Handle one key press (§12.5).
pub fn on_key(state: &mut CaptureState, view: &View<'_>, key: KeyEvent) -> Action {
    if state.editing {
        return editing_key(state, view, key);
    }
    let lines = inbox_lines(view);
    match key.code {
        KeyCode::Char('j') | KeyCode::Down => {
            if state.sel + 1 < lines.len() {
                state.sel += 1;
            }
            Action::Redraw
        }
        KeyCode::Char('k') | KeyCode::Up => {
            state.sel = state.sel.saturating_sub(1);
            Action::Redraw
        }
        KeyCode::Char('i') | KeyCode::Char('a') => {
            state.editing = true;
            state.triaging = None;
            state.buffer.clear();
            state.target = None;
            state.note = None;
            Action::Redraw
        }
        KeyCode::Char('t') | KeyCode::Enter => match lines.get(state.sel) {
            Some(l) => {
                state.buffer = l.raw.clone();
                state.editing = true;
                state.triaging = Some(l.line);
                state.target = None;
                state.note = None;
                Action::Redraw
            }
            None => Action::Note("inbox is empty".to_string()),
        },
        KeyCode::Char('C') => {
            state.note = Some(CLAUDE_TRIAGE.to_string());
            Action::Note(CLAUDE_TRIAGE.to_string())
        }
        KeyCode::Char('x') => match lines.get(state.sel) {
            Some(l) => Action::Mutate(Mutation::DropInboxLine { line: l.line }),
            None => Action::Note("inbox is empty".to_string()),
        },
        _ => Action::Ignored,
    }
}

/// Keys while the capture line has focus.
fn editing_key(state: &mut CaptureState, view: &View<'_>, key: KeyEvent) -> Action {
    match key.code {
        KeyCode::Esc => {
            state.editing = false;
            state.buffer.clear();
            state.triaging = None;
            state.target = None;
            Action::Redraw
        }
        KeyCode::Tab => {
            let n = targets(view).len();
            let current = state.capture(view).target_index;
            state.target = Some((current + 1) % n);
            Action::Redraw
        }
        KeyCode::BackTab => {
            let n = targets(view).len();
            let current = state.capture(view).target_index;
            state.target = Some((current + n - 1) % n);
            Action::Redraw
        }
        KeyCode::Backspace => {
            state.buffer.pop();
            Action::Redraw
        }
        KeyCode::Enter => {
            let cap = state.capture(view);
            match cap.problem {
                Some(p) => Action::Note(p),
                None => {
                    // `from_inbox` tells the shell to drop that line once the
                    // add lands. It is a line *number*, taken before the add,
                    // so it must not be sent when the add writes to `inbox.md`
                    // itself: the insert would shift it and the drop would
                    // delete a different line.
                    let same_file = cap.target.file == "inbox.md";
                    let m = Mutation::Capture {
                        text: cap.line,
                        file: cap.target.file,
                        section: cap.target.section,
                        from_inbox: state.triaging.filter(|_| !same_file),
                    };
                    state.editing = false;
                    state.buffer.clear();
                    state.triaging = None;
                    state.target = None;
                    Action::Mutate(m)
                }
            }
        }
        KeyCode::Char(c) if !key.modifiers.contains(KeyModifiers::CONTROL) => {
            state.buffer.push(c);
            Action::Redraw
        }
        _ => Action::Ignored,
    }
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

/// Draw Screen 5 into `area` (§12.5).
pub fn render(state: &CaptureState, view: &View<'_>, frame: &mut Frame, area: Rect) {
    if area.height < 3 || area.width == 0 {
        return;
    }
    let rows = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(5),
            Constraint::Length(1),
            Constraint::Min(1),
        ])
        .split(area);
    render_capture(state, view, frame, rows[0]);

    let lines = inbox_lines(view);
    let header = format!(" Inbox ({})   {}", lines.len(), KEYMAP_LIST.trim());
    frame.render_widget(
        Paragraph::new(Line::from(Span::styled(
            emit::clip(&header, rows[1].width as usize),
            Style::default().fg(Color::DarkGray),
        ))),
        rows[1],
    );
    render_list(state, &lines, frame, rows[2]);
}

/// The capture box.
fn render_capture(state: &CaptureState, view: &View<'_>, frame: &mut Frame, area: Rect) {
    let block = Block::default()
        .borders(Borders::ALL)
        .title(" Capture ")
        .border_style(if state.editing {
            Style::default().fg(Color::White)
        } else {
            Style::default().fg(Color::DarkGray)
        });
    let inner = block.inner(area);
    frame.render_widget(block, area);
    if inner.height == 0 {
        return;
    }
    let w = inner.width as usize;
    let cap = state.capture(view);
    let cursor = if state.editing { "_" } else { "" };
    let mut lines = vec![Line::from(vec![
        Span::styled("> ", Style::default().fg(Color::DarkGray)),
        Span::styled(
            emit::clip(&format!("{}{cursor}", state.buffer), w.saturating_sub(2)),
            Style::default().add_modifier(Modifier::BOLD),
        ),
    ])];
    let preview = preview_text(&cap);
    lines.push(Line::from(Span::styled(
        emit::clip(&format!("  {preview}"), w),
        match (&cap.problem, &cap.warning, cap.raw.is_empty()) {
            (_, _, true) => Style::default().fg(Color::DarkGray),
            (Some(_), _, _) => Style::default().fg(Color::Red),
            (None, Some(_), _) => Style::default().fg(Color::Yellow),
            (None, None, _) => Style::default().fg(Color::Green),
        },
    )));
    let hint = state.note.clone().unwrap_or_else(|| {
        if state.editing {
            KEYMAP_EDITING.trim().to_string()
        } else {
            "i capture".to_string()
        }
    });
    lines.push(Line::from(Span::styled(
        emit::clip(&format!("  {hint}"), w),
        Style::default().fg(Color::DarkGray),
    )));
    frame.render_widget(Paragraph::new(lines), inner);
}

/// The inbox list.
fn render_list(state: &CaptureState, lines: &[InboxLine], frame: &mut Frame, area: Rect) {
    if area.height == 0 {
        return;
    }
    let w = area.width as usize;
    let mut out: Vec<Line<'static>> = Vec::new();
    let h = area.height as usize;
    let offset = if state.sel >= h { state.sel + 1 - h } else { 0 };
    for (i, l) in lines.iter().enumerate().skip(offset).take(h) {
        let mark = if l.problem.is_some() { "!" } else { " " };
        let text = emit::clip(&format!(" {mark} {:>3}  {}", l.line, l.raw), w);
        let style = if i == state.sel && !state.editing {
            Style::default().add_modifier(Modifier::REVERSED)
        } else {
            Style::default()
        };
        out.push(Line::from(Span::styled(text, style)));
    }
    if out.is_empty() {
        out.push(Line::from(Span::styled(
            " inbox is empty",
            Style::default().fg(Color::DarkGray),
        )));
    }
    frame.render_widget(Paragraph::new(out), area);
}
