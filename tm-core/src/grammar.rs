//! Grammar — tm-spec-v1.md §4 and §17.2 "Parsing". Hand-written tokenizer,
//! parser and byte-faithful serializer.
//!
//! # API overview
//!
//! * [`parse_file`]`(path, text, &Config) -> `[`ParsedFile`] — every line is
//!   either an [`Item`] or kept verbatim (prose, headings, blank lines, front
//!   matter, generated `<!-- tm:x start -->…<!-- tm:x end -->` ranges,
//!   comments). [`serialize_file`] writes it back byte-identically. A line
//!   inside an `<!-- … -->` comment is prose whatever it looks like — see
//!   [`comment_after`], which is `Plan.lean`'s reading and the only one.
//! * [`parse_line`]`(text, &`[`ParseCtx`]`) -> Result<Item, ParseError>` — one
//!   item line; [`ParseCtx::new`]`(file, block_min)` derives the horizon from
//!   the path.
//! * [`ItemLine`] — the token list kept on `item.src.tokens`. `to_string()` is
//!   the original line. Edit operations change only the token they must:
//!   `set_token` / `remove_token` / `get`, `set_state`, `set_state_with_ci`,
//!   `set_ci`, `remove_ci`, `set_leading_est`, `set_title`, `set_priority`,
//!   `set_parent`, `add_tag`, `remove_tag`, `add_flag`, `remove_flag`,
//!   `append_id`. After an edit, re-parse with [`parse_line`] to get a fresh
//!   `Item`. Edits that touch the positional slots (`set_state`,
//!   `remove_ci`, `set_leading_est`, `set_title`) return
//!   [`EditError::Ambiguous`] instead of producing a line that would re-parse
//!   with a different meaning (a title starting with `5` or `2h` in an empty
//!   ci / estimate slot, or a title word that is a token); the fix is to pin
//!   the slot first (`set_ci`, `set_leading_est`, `set_state_with_ci`) or to
//!   reword the title. Flags are read only after a `@ # ! ^ key:` token, so
//!   `add_flag` and the removals (`remove_token`, `remove_tag`,
//!   `set_parent(None)`, `set_priority(None)`, `set_title`) move a flag that
//!   would end up right after the title to after the `^id`, and fail with
//!   [`EditError::FlagNeedsBoundary`] when there is no id. A refused edit
//!   never changes the line.
//! * [`format_item_line`]`(&Item) -> Result<String, EditError>` — builds a
//!   fresh canonical line (for `tm add` / capture previews) that re-parses to
//!   the same fields, or fails with [`EditError::Ambiguous`] when the title
//!   cannot be written under the grammar.
//! * [`IdGen`] — deterministic id generator (4 chars from `[a-z0-9]` minus
//!   `l o 0 1`, injected seed, uniqueness against a `HashSet`), and
//!   [`append_id_to_text`] for `--fix-ids`.
//!
//! # Parsing rules (as implemented)
//!
//! * An item line starts with `- ` at column 0. Then an optional state
//!   (`[ ]` …), and — only when a state is present — an optional positional
//!   ci (`0`..`5`) and an optional leading estimate (`Nb|Nm|Nh|NhMm`).
//! * The title runs to the first whitespace-separated word that starts with
//!   `@ # ! ^` or matches `[a-z-]+:`. Internal whitespace is preserved.
//! * Every later word is classified: `@parent`, `#tag`, `!k` (1..=4), `^id`,
//!   `key:value`, a flag (`open atomic manual travel-day hot`), or a bare
//!   word. Bare words are appended to the title (joined by single spaces) —
//!   this is what makes `- [ ] 5 !1 Lean: through ch.8 ^O1` work. A malformed
//!   structured token (`!9`, `^%`, `@@`) also stays in the title (§4.1:
//!   tokens the parser cannot classify stay in the title) and is reported as
//!   a problem; a lone `@ # ! ^` is plain punctuation (title, no problem).
//! * Flags are recognised only after the title has ended (after the first
//!   `@ # ! ^ key:` token), per the §4.1 title rule; a title whose last word
//!   is a flag name (`Lean practice open ^l1`) keeps the word and gets a
//!   problem so `tm check` can point at it.
//! * `ci:N` is accepted as a key everywhere (it is the only way to give a ci
//!   on state-less routine/optional lines); it overrides a positional ci.
//!   `cap:` is an alias of `max:`. The first occurrence of a repeated key
//!   wins and a problem is recorded.
//! * A known key whose value does not parse, and any unknown key, is kept
//!   verbatim in `item.extra`; the former also adds to `item.problems`.

use std::collections::HashSet;
use std::fmt;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::config::Config;
use crate::model::{
    parse_date, parse_interval, Budget, Dep, Dur, Horizon, Id, Item, Loc, Moment, OnMiss, Pref,
    Rate, Recur, Ref, Rule, Scope, Shape, SourceLoc, Stamp, Stamps, State, WindowRange,
};

/// The `key:` names the grammar knows, in the §4.1 table order (plus `cap`
/// as an alias of `max`, and `ci`).
pub const KEYS: &[&str] = &[
    "due",
    "at",
    "win",
    "dur",
    "pref",
    "every",
    "after-done",
    "on-event",
    "on-miss",
    "min",
    "max",
    "after",
    "loc",
    "est",
    "demoted",
    "waiting",
    "buffer",
    "cap",
    "ci",
];

/// The flags the grammar knows.
pub const FLAGS: &[&str] = &["open", "atomic", "manual", "travel-day", "hot"];

/// Errors from parsing a single line.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ParseError {
    /// The line does not start with `- ` followed by something.
    #[error("not an item line (must start with \"- \" and have content)")]
    NotAnItemLine,
}

/// Errors from an edit operation on an [`ItemLine`] (and from
/// [`format_item_line`]).
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum EditError {
    /// A positional slot (ci / leading estimate) needs a state on the line.
    #[error("the line has no state, so there is no positional slot")]
    NoState,
    /// The edit would produce a line that re-parses with a different meaning:
    /// `word` in the title would be read as a ci, a leading estimate, or a
    /// token. Pin the slot first (`set_ci`, `set_leading_est`,
    /// `set_state_with_ci`) or reword the title.
    #[error("title word `{word}` would be read as a ci, estimate, or token when re-parsed; pin the positional slots first or reword")]
    Ambiguous {
        /// The offending word.
        word: String,
    },
    /// The text contains a line break, which cannot live in a line.
    #[error("text contains a line break")]
    LineBreak,
    /// A flag would directly follow the title and be absorbed into it on
    /// re-parse (flags count only after a `@ # ! ^ key:` token, §4.1). The
    /// edit could not move it after the `^id` because the line has none.
    #[error("flag `{flag}` would be absorbed into the title: a `@ # ! ^ key:` token or the `^id` must precede it")]
    FlagNeedsBoundary {
        /// The flag.
        flag: String,
    },
}

// ---------------------------------------------------------------------------
// Tokens
// ---------------------------------------------------------------------------

/// What a token is.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TokenKind {
    /// The leading `-`.
    Bullet,
    /// `[ ]` and friends.
    State,
    /// Positional ci digit.
    Ci,
    /// Leading estimate.
    Est,
    /// The title text (may contain whitespace).
    Title,
    /// `@parent`.
    Parent,
    /// `#tag`.
    Tag,
    /// `!k`.
    Priority,
    /// `^id`.
    Id,
    /// `key:value`; the key as written.
    Key(String),
    /// One of [`FLAGS`].
    Flag,
    /// A bare word after the title (appended to the title).
    Word,
    /// A malformed structured token (`!9`, `^%`): appended to the title like
    /// a word, and reported as a problem.
    Unparsed,
}

impl TokenKind {
    /// True for the kinds whose text is part of the item title.
    pub fn is_title_text(&self) -> bool {
        matches!(self, TokenKind::Title | TokenKind::Word | TokenKind::Unparsed)
    }
}

/// One token with the exact whitespace that precedes it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Token {
    /// Whitespace run before the token (empty for the bullet).
    pub lead: String,
    /// The token text.
    pub text: String,
    /// Classification.
    pub kind: TokenKind,
}

impl Token {
    fn new(lead: &str, text: &str, kind: TokenKind) -> Token {
        Token {
            lead: lead.to_string(),
            text: text.to_string(),
            kind,
        }
    }
    /// For `Key` tokens: the value after the first `:`.
    pub fn value(&self) -> Option<&str> {
        match self.kind {
            TokenKind::Key(_) => self.text.split_once(':').map(|(_, v)| v),
            _ => None,
        }
    }
    /// For `Key` tokens: the key as written.
    pub fn key(&self) -> Option<&str> {
        match &self.kind {
            TokenKind::Key(k) => Some(k),
            _ => None,
        }
    }
}

/// An item line as a token list; `to_string()` reproduces the original bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct ItemLine {
    /// Tokens in line order; the first is always the bullet.
    pub tokens: Vec<Token>,
    /// Trailing whitespace after the last token.
    pub trailing: String,
}

impl fmt::Display for ItemLine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for t in &self.tokens {
            f.write_str(&t.lead)?;
            f.write_str(&t.text)?;
        }
        f.write_str(&self.trailing)
    }
}

/// A whitespace-separated word with its preceding whitespace, as byte ranges.
struct Word {
    lead_start: usize,
    start: usize,
    end: usize,
}

fn split_words(text: &str, from: usize) -> (Vec<Word>, usize) {
    let mut words = Vec::new();
    let mut pos = from;
    loop {
        let lead_start = pos;
        let start = skip_ws(text, pos);
        if start >= text.len() {
            return (words, lead_start);
        }
        let end = text[start..]
            .char_indices()
            .find(|(_, c)| c.is_whitespace())
            .map(|(i, _)| start + i)
            .unwrap_or(text.len());
        words.push(Word {
            lead_start,
            start,
            end,
        });
        pos = end;
    }
}

fn skip_ws(text: &str, from: usize) -> usize {
    text[from..]
        .char_indices()
        .find(|(_, c)| !c.is_whitespace())
        .map(|(i, _)| from + i)
        .unwrap_or(text.len())
}

/// Does `text` OPEN with a §4.1 state marker?
///
/// The one answer to "is a `[c]` marker written here", for the writers that
/// have to decide whether to supply one.  `tm add` used to ask the question
/// itself and ask it as `starts_with("- ")` — the HYPHEN, one spelling of a
/// four-spelling class — so a pasted `[ ] write the notes`, which carries the
/// state and not the bullet, fell to the branch that prepends a whole prefix
/// and became `- [ ] [ ] write the notes`, title and all (W-31 repair, README
/// gap 2262).  The marker class is `State::from_glyph`'s and lives here; a
/// caller that spells it again is spelling a subset of it.
pub fn opens_with_state(text: &str) -> bool {
    state_at(text, 0)
}

/// `[c]` at byte offset `i`, followed by whitespace or end of line.
fn state_at(text: &str, i: usize) -> bool {
    let b = text.as_bytes();
    b.len() >= i + 3
        && b[i] == b'['
        && b[i + 2] == b']'
        && State::from_glyph(b[i + 1] as char).is_some()
        && (b.len() == i + 3 || (b[i + 3] as char).is_ascii_whitespace())
}

fn is_ci_digit(w: &str) -> bool {
    w.len() == 1 && matches!(w.as_bytes()[0], b'0'..=b'5')
}

/// **The positional leading-estimate slot, by SHAPE** — `Nb`, `Nm`, `Nh` or
/// `NhMm`, the numerals any run of ASCII digits (README gap 3140, W-37 track T,
/// parity P57). The kernel's `Field.estSlot` reads the slot by this shape over
/// `Nat` numerals, and this reader used to add a magnitude to it
/// (`Dur::parse_no_days(word, 1).is_ok()`, `u32` minutes): so a leading
/// `9999999999999m` was the ESTIMATE to the kernel and a TITLE WORD here, `tm
/// check` said nothing, and the first `tm extend` rewrote the word the kernel
/// read as the slot — taking it out of the title the host had shown. One shape
/// for both readers now: the slot is the slot whatever its size, and a value
/// this reader cannot hold is `est_original: None` and a `bad-value` error, the
/// way a keyed token's unreadable value already is. The fork's own parser, and
/// every other value grammar, are unchanged.
pub fn is_est_slot(w: &str) -> bool {
    let digits = w.bytes().take_while(u8::is_ascii_digit).count();
    if digits == 0 {
        return false;
    }
    match &w[digits..] {
        "b" | "m" | "h" => true,
        rest => rest
            .strip_prefix('h')
            .and_then(|r| r.strip_suffix('m'))
            .is_some_and(|m| !m.is_empty() && m.bytes().all(|b| b.is_ascii_digit())),
    }
}

/// `key` of a `key:value` word when the key matches `[a-z-]+`.
fn key_prefix(w: &str) -> Option<&str> {
    let (k, _) = w.split_once(':')?;
    if !k.is_empty() && k.bytes().all(|b| b.is_ascii_lowercase() || b == b'-') {
        Some(k)
    } else {
        None
    }
}

/// The first character when it is one of the structured sigils `@ # ! ^`.
/// Works on the first *char*, so a word starting with a multi-byte character
/// (`✈`, `§3`, `—`) is never sliced inside a code point.
fn sigil(w: &str) -> Option<char> {
    w.chars().next().filter(|c| matches!(c, '@' | '#' | '!' | '^'))
}

/// True for a word that ends the title: starts with `@ # ! ^` or matches
/// `[a-z-]+:`.
fn starts_token(w: &str) -> bool {
    sigil(w).is_some() || key_prefix(w).is_some()
}

fn classify(w: &str) -> TokenKind {
    match sigil(w) {
        // A lone sigil is punctuation ("Meet Kun @ 7pm"), not a broken token.
        Some(_) if w.len() == 1 => TokenKind::Word,
        Some('@') => TokenKind::Parent,
        Some('#') => TokenKind::Tag,
        Some('!') if matches!(&w[1..], "1" | "2" | "3" | "4") => TokenKind::Priority,
        Some('^') if Id::is_valid(&w[1..]) => TokenKind::Id,
        Some(_) => TokenKind::Unparsed,
        None => match key_prefix(w) {
            Some(k) => TokenKind::Key(k.to_string()),
            None if FLAGS.contains(&w) => TokenKind::Flag,
            None => TokenKind::Word,
        },
    }
}

/// The first word of `title` that a re-parse would not read as title text,
/// simulating the tokenizer: after a state, a ci digit in an empty ci slot
/// or a duration in an empty estimate slot is eaten; from the first word
/// that ends the title segment on, every word is classified and must come
/// out as title text (a lone `@` or a malformed `!5` do; `@m1`, `re:`,
/// `open` do not).
fn title_conflict(title: &str, has_state: bool, has_ci: bool, has_est: bool) -> Option<String> {
    let words: Vec<&str> = title.split_whitespace().collect();
    let first = *words.first()?;
    if has_state {
        let eaten_as_ci = !has_ci && is_ci_digit(first);
        let eaten_as_est = !has_est && is_est_slot(first);
        if eaten_as_ci || eaten_as_est {
            return Some(first.to_string());
        }
    }
    let boundary = words.iter().position(|w| starts_token(w))?;
    words[boundary..]
        .iter()
        .find(|w| !classify(w).is_title_text())
        .map(|w| w.to_string())
}

fn check_text(text: &str) -> Result<(), EditError> {
    if text.contains(['\n', '\r']) {
        return Err(EditError::LineBreak);
    }
    Ok(())
}

/// Whitespace-normalized title text: trimmed, single spaces between words.
fn normalize_title(title: &str) -> String {
    title.split_whitespace().collect::<Vec<_>>().join(" ")
}

impl ItemLine {
    /// Tokenize one line (no trailing newline). Fails only when the line is
    /// not an item line.
    pub fn parse(text: &str) -> Result<ItemLine, ParseError> {
        let rest = text.strip_prefix("- ").ok_or(ParseError::NotAnItemLine)?;
        if rest.trim().is_empty() {
            return Err(ParseError::NotAnItemLine);
        }
        let mut tokens = vec![Token::new("", "-", TokenKind::Bullet)];
        let mut pos = 1;
        let ws_end = skip_ws(text, pos);
        let has_state = state_at(text, ws_end);
        if has_state {
            tokens.push(Token::new(&text[pos..ws_end], &text[ws_end..ws_end + 3], TokenKind::State));
            pos = ws_end + 3;
        }
        let (words, trailing_start) = split_words(text, pos);
        let word_text = |w: &Word| &text[w.start..w.end];
        let lead_of = |w: &Word| &text[w.lead_start..w.start];

        let mut i = 0;
        if has_state {
            if i < words.len() && is_ci_digit(word_text(&words[i])) {
                tokens.push(Token::new(lead_of(&words[i]), word_text(&words[i]), TokenKind::Ci));
                i += 1;
            }
            if i < words.len() && is_est_slot(word_text(&words[i])) {
                tokens.push(Token::new(lead_of(&words[i]), word_text(&words[i]), TokenKind::Est));
                i += 1;
            }
        }
        // Title: up to the first structured token.
        let title_start = i;
        while i < words.len() && !starts_token(word_text(&words[i])) {
            i += 1;
        }
        if i > title_start {
            let first = &words[title_start];
            let last = &words[i - 1];
            tokens.push(Token::new(
                lead_of(first),
                &text[first.start..last.end],
                TokenKind::Title,
            ));
        }
        for w in &words[i..] {
            let t = word_text(w);
            tokens.push(Token::new(lead_of(w), t, classify(t)));
        }
        Ok(ItemLine {
            tokens,
            trailing: text[trailing_start..].to_string(),
        })
    }

    // -- queries ----------------------------------------------------------

    /// Index of the first token of `kind`.
    pub fn index_of(&self, kind: &TokenKind) -> Option<usize> {
        self.tokens.iter().position(|t| &t.kind == kind)
    }
    /// Index of the first `key:` token (treating `cap` and `max` as aliases).
    pub fn key_index(&self, key: &str) -> Option<usize> {
        let alias = match key {
            "max" => Some("cap"),
            "cap" => Some("max"),
            _ => None,
        };
        self.tokens
            .iter()
            .position(|t| matches!(t.key(), Some(k) if k == key || Some(k) == alias))
    }
    /// The value of `key:` if present.
    pub fn get(&self, key: &str) -> Option<&str> {
        self.key_index(key).and_then(|i| self.tokens[i].value())
    }
    /// The `^id` on the line, if any.
    pub fn id(&self) -> Option<Id> {
        self.index_of(&TokenKind::Id)
            .map(|i| Id::new(&self.tokens[i].text[1..]))
    }
    /// True when the line carries the flag.
    pub fn has_flag(&self, flag: &str) -> bool {
        self.tokens
            .iter()
            .any(|t| t.kind == TokenKind::Flag && t.text == flag)
    }
    /// True when the line carries the tag (without `#`).
    pub fn has_tag(&self, tag: &str) -> bool {
        self.tokens
            .iter()
            .any(|t| t.kind == TokenKind::Tag && t.text[1..] == *tag)
    }
    /// The title as an item would see it: the title segment plus any bare
    /// or unparsed words after the tokens, joined by single spaces.
    pub fn title(&self) -> String {
        self.tokens
            .iter()
            .filter(|t| t.kind.is_title_text())
            .map(|t| t.text.as_str())
            .collect::<Vec<_>>()
            .join(" ")
    }
    fn has(&self, kind: &TokenKind) -> bool {
        self.index_of(kind).is_some()
    }
    /// Text of the leading title segment (the `Title` token), if any.
    fn title_segment(&self) -> &str {
        self.index_of(&TokenKind::Title)
            .map(|i| self.tokens[i].text.as_str())
            .unwrap_or("")
    }
    /// Fail when `title` would not survive a re-parse with the given slots.
    fn guard_title(title: &str, has_state: bool, has_ci: bool, has_est: bool) -> Result<(), EditError> {
        match title_conflict(title, has_state, has_ci, has_est) {
            Some(word) => Err(EditError::Ambiguous { word }),
            None => Ok(()),
        }
    }

    // -- generic edits ----------------------------------------------------

    fn insert_at(&mut self, idx: usize, kind: TokenKind, text: &str) {
        self.tokens.insert(idx, Token::new(" ", text, kind));
    }

    /// Insert before the `^id` token if there is one, else append.
    fn insert_before_id_or_end(&mut self, kind: TokenKind, text: &str) {
        let idx = self.index_of(&TokenKind::Id).unwrap_or(self.tokens.len());
        self.insert_at(idx, kind, text);
    }

    fn remove_at(&mut self, idx: usize) {
        self.tokens.remove(idx);
    }

    /// True when a token before `idx` ends the title (starts with `@ # ! ^`
    /// or is a `key:`), so a flag at `idx` is read as a flag rather than as
    /// title text. Bare words do not count: they are absorbed into the title
    /// themselves once nothing structured precedes them.
    fn boundary_before(&self, idx: usize) -> bool {
        self.tokens[..idx]
            .iter()
            .any(|t| t.kind != TokenKind::Title && starts_token(&t.text))
    }

    /// Flags are read only after the title has ended (§4.1), so a flag that
    /// directly follows the title would be absorbed into it on re-parse.
    /// Move such flags after the `^id` (keeping their order); without an id,
    /// fail and leave the line unchanged.
    fn fix_flag_boundaries(&mut self) -> Result<(), EditError> {
        let orphans: Vec<usize> = (0..self.tokens.len())
            .filter(|&i| self.tokens[i].kind == TokenKind::Flag && !self.boundary_before(i))
            .collect();
        let Some(&first) = orphans.first() else {
            return Ok(());
        };
        // `boundary_before` is monotone (a boundary at `i` covers everything
        // after it), so the orphans are exactly the flags before the line's
        // *first* boundary token. Move them, as a group and in order, to
        // just after that boundary: moving them after the `^id` instead
        // reordered them past any flag that already sat between (`A @A
        // atomic due:… open @A ^a` came back `… open … atomic`).
        let Some(boundary) = (0..self.tokens.len())
            .find(|&i| self.tokens[i].kind != TokenKind::Title && starts_token(&self.tokens[i].text))
        else {
            return Err(EditError::FlagNeedsBoundary {
                flag: self.tokens[first].text.clone(),
            });
        };
        let mut moved: Vec<Token> = orphans.iter().rev().map(|&i| self.tokens.remove(i)).collect();
        moved.reverse();
        // Every orphan sat before `boundary`, which is now shifted left by
        // their count; insert right after it.
        let mut at = boundary - orphans.len() + 1;
        for mut t in moved {
            t.lead = " ".to_string();
            self.tokens.insert(at, t);
            at += 1;
        }
        Ok(())
    }

    /// True when the token at `idx` is title text that a re-parse would read
    /// as part of the leading title *segment* rather than as a word of its
    /// own — so the whitespace in front of it is about to become title text.
    /// A token that ends the title itself (a lone `@`, a malformed `!9`) is
    /// not absorbed; neither is the segment, which needs no kind test because
    /// it is the FIRST title-text token and the last conjunct already
    /// excludes it (a `t.kind != Title` conjunct was here and no mutation of
    /// it could fail anything, so it went).
    fn absorbed_into_title(&self, idx: usize) -> bool {
        let t = &self.tokens[idx];
        t.kind.is_title_text()
            && !starts_token(&t.text)
            && !self.boundary_before(idx)
            && self.tokens[..idx].iter().any(|t| t.kind.is_title_text())
    }

    /// [`ItemLine::title`] joins the title-text tokens with ONE space, while
    /// the title segment keeps its whitespace verbatim, so the two agree only
    /// while every absorbed word carries a single-space lead. A freshly
    /// parsed line always satisfies that — the tokenizer merges every word
    /// before the first `@ # ! ^ key:` into one `Title` token, so a `Word`
    /// always has a boundary in front of it. A removal can take that
    /// boundary away, and then the run the word happened to carry becomes
    /// title text (`A ci:0  a` → title `A  a`, a title the line never had;
    /// README gap 1316, owner D46). Give such a word the one space `title()`
    /// already reports. Whitespace *inside* the segment is the author's and
    /// is left alone, as is a word that still has a boundary in front of it.
    fn fix_absorbed_leads(&mut self) {
        for i in 0..self.tokens.len() {
            if self.absorbed_into_title(i) {
                self.tokens[i].lead = " ".to_string();
            }
        }
    }

    /// Run `edit` on a copy and keep it only if the flags still have a
    /// boundary afterwards (moving them after the `^id` when needed), so a
    /// refused edit changes nothing. The same pass re-leads any title word
    /// the edit left with no boundary in front of it, so the line still
    /// renders the title it reports ([`ItemLine::fix_absorbed_leads`]).
    fn edit_keeping_flags<T>(
        &mut self,
        edit: impl FnOnce(&mut ItemLine) -> T,
    ) -> Result<T, EditError> {
        let mut edited = self.clone();
        let out = edit(&mut edited);
        edited.fix_flag_boundaries()?;
        edited.fix_absorbed_leads();
        *self = edited;
        Ok(out)
    }

    /// Set `key:value`: replace in place if present (keeping the key as
    /// written), else insert before `^id`, else append.
    pub fn set_token(&mut self, key: &str, value: &str) {
        match self.key_index(key) {
            Some(i) => {
                let written = self.tokens[i].key().unwrap_or(key).to_string();
                self.tokens[i].text = format!("{written}:{value}");
            }
            None => self.insert_before_id_or_end(
                TokenKind::Key(key.to_string()),
                &format!("{key}:{value}"),
            ),
        }
    }

    /// Remove `key:…`; returns whether it was present. Fails (leaving the
    /// line unchanged) only when the key was the last token keeping a flag
    /// out of the title and there is no `^id` to move the flag after.
    ///
    /// Removes the FIRST occurrence, because [`ItemLine::key_index`] reports
    /// the first match. A line may carry the same key twice — the parser
    /// accepts it and records `duplicate key \`ci:0\`` as a problem — so a
    /// caller that means *the fact*, not *the token*, wants
    /// [`ItemLine::remove_all_tokens`]. README gap **1520**.
    pub fn remove_token(&mut self, key: &str) -> Result<bool, EditError> {
        match self.key_index(key) {
            Some(i) => self.edit_keeping_flags(|l| l.remove_at(i)).map(|_| true),
            None => Ok(false),
        }
    }

    /// Remove EVERY `key:…`, and return how many went; all or nothing, so a
    /// refused removal leaves the line exactly as it was.
    ///
    /// The one definition of "the fact is gone", for the callers whose own
    /// documentation already says *any* (AGENTS §5.3: the second one would be
    /// the bug). [`ItemLine::remove_token`] alone leaves a duplicate standing,
    /// and a surviving `ci:` is not inert — it keeps
    /// [`ItemLine::set_ci`]'s keyed branch alive, so the positional digit is
    /// never inserted and the title's leading word is read as the ci on the
    /// next parse. A seed drew `("- 0 ci:0 ci:0", false)` at W-25's land step
    /// and title `0` came back `""`. README gap **1520**, owner **D46**.
    pub fn remove_all_tokens(&mut self, key: &str) -> Result<usize, EditError> {
        let mut edited = self.clone();
        let mut gone = 0usize;
        while edited.remove_token(key)? {
            gone += 1;
        }
        *self = edited;
        Ok(gone)
    }

    // -- positional edits -------------------------------------------------

    /// Replace the state, or insert one after the bullet. Inserting a state
    /// opens the positional ci / estimate slots, so a state-less line whose
    /// title starts with a ci digit or a duration (`- 5 min stretch …`,
    /// `- 30m walk …`) is refused with [`EditError::Ambiguous`]; use
    /// [`ItemLine::set_state_with_ci`] (and `set_leading_est`) to pin the
    /// slots in the same edit.
    pub fn set_state(&mut self, state: State) -> Result<(), EditError> {
        match self.index_of(&TokenKind::State) {
            Some(i) => self.tokens[i].text = state.as_str().to_string(),
            None => {
                Self::guard_title(self.title_segment(), true, false, self.has(&TokenKind::Est))?;
                self.insert_at(1, TokenKind::State, state.as_str());
            }
        }
        Ok(())
    }

    /// Set the state and a positional ci together (folding EVERY `ci:` key
    /// into the positional slot — a duplicate is representable and one
    /// survivor loses the title, README gap **1520**), so a state can be
    /// added to a line whose
    /// title starts with a digit. Still refused when the title starts with a
    /// duration and the line has no leading estimate (`- 30m walk` cannot
    /// carry a state without one).
    pub fn set_state_with_ci(&mut self, state: State, ci: u8) -> Result<(), EditError> {
        Self::guard_title(self.title_segment(), true, true, self.has(&TokenKind::Est))?;
        self.remove_all_tokens("ci")?;
        match self.index_of(&TokenKind::State) {
            Some(i) => self.tokens[i].text = state.as_str().to_string(),
            None => self.insert_at(1, TokenKind::State, state.as_str()),
        }
        self.set_ci(ci);
        Ok(())
    }

    /// Set the ci. The positional digit and a `ci:` key are both updated when
    /// present (so the fact changes whichever one wins on re-parse); with
    /// neither, a positional ci is inserted after the state, or `ci:N` is
    /// added on a state-less line.
    pub fn set_ci(&mut self, ci: u8) {
        let positional = self.index_of(&TokenKind::Ci);
        let keyed = self.key_index("ci").is_some();
        if let Some(i) = positional {
            self.tokens[i].text = ci.to_string();
        }
        if keyed {
            self.set_token("ci", &ci.to_string());
        }
        if positional.is_none() && !keyed {
            match self.index_of(&TokenKind::State) {
                Some(s) => self.insert_at(s + 1, TokenKind::Ci, &ci.to_string()),
                None => self.set_token("ci", &ci.to_string()),
            }
        }
    }

    /// Remove the positional ci and EVERY `ci:` key (gap **1520**). Refused when the title
    /// would then be read as a ci digit (`- [ ] 3 5 things` → `5` is the ci).
    pub fn remove_ci(&mut self) -> Result<(), EditError> {
        if self.has(&TokenKind::Ci) {
            Self::guard_title(self.title_segment(), true, false, self.has(&TokenKind::Est))?;
        }
        self.remove_all_tokens("ci")?;
        if let Some(i) = self.index_of(&TokenKind::Ci) {
            self.remove_at(i);
        }
        Ok(())
    }

    /// Set (or with `None` remove) the leading estimate. Inserting needs a
    /// state on the line (the slot is positional); removing is refused when
    /// the title would then be read as an estimate (`- [ ] 3 2b 30m run`).
    pub fn set_leading_est(&mut self, est: Option<Dur>) -> Result<(), EditError> {
        match (self.index_of(&TokenKind::Est), est) {
            (Some(i), Some(d)) => self.tokens[i].text = d.to_string(),
            (Some(i), None) => {
                Self::guard_title(self.title_segment(), true, self.has(&TokenKind::Ci), false)?;
                self.remove_at(i);
            }
            (None, None) => {}
            (None, Some(d)) => {
                let after = self
                    .index_of(&TokenKind::Ci)
                    .or_else(|| self.index_of(&TokenKind::State))
                    .ok_or(EditError::NoState)?;
                self.insert_at(after + 1, TokenKind::Est, &d.to_string());
            }
        }
        Ok(())
    }

    /// Replace the title (dropping any bare or unparsed words that were
    /// appended to it). The new title is whitespace-normalized; it is refused
    /// when one of its words would be read as a ci / estimate (in an empty
    /// slot) or as a token (`@x`, `#x`, `!1`, `^x`, `key:`, a flag after a
    /// lone sigil) on re-parse. A flag that the old title's bare words kept
    /// out of the title is moved after the `^id` (see
    /// [`EditError::FlagNeedsBoundary`]).
    pub fn set_title(&mut self, title: &str) -> Result<(), EditError> {
        check_text(title)?;
        let title = normalize_title(title);
        Self::guard_title(
            &title,
            self.has(&TokenKind::State),
            self.has(&TokenKind::Ci),
            self.has(&TokenKind::Est),
        )?;
        self.edit_keeping_flags(|l| {
            l.tokens
                .retain(|t| !matches!(t.kind, TokenKind::Word | TokenKind::Unparsed));
            match l.index_of(&TokenKind::Title) {
                Some(i) if title.is_empty() => l.remove_at(i),
                Some(i) => l.tokens[i].text = title,
                None if title.is_empty() => {}
                None => {
                    let after = l
                        .tokens
                        .iter()
                        .rposition(|t| {
                            matches!(
                                t.kind,
                                TokenKind::Bullet | TokenKind::State | TokenKind::Ci | TokenKind::Est
                            )
                        })
                        .unwrap_or(0);
                    l.insert_at(after + 1, TokenKind::Title, &title);
                }
            }
        })
    }

    // -- trailing-token edits ---------------------------------------------

    /// Set (or with `None` remove) `!k`. Setting replaces the first `!k`
    /// (the one that counts); removing drops every `!k` token. Removing can
    /// fail like [`ItemLine::remove_token`].
    pub fn set_priority(&mut self, k: Option<u8>) -> Result<(), EditError> {
        match (self.index_of(&TokenKind::Priority), k) {
            (Some(i), Some(k)) => self.tokens[i].text = format!("!{k}"),
            (Some(_), None) => {
                self.edit_keeping_flags(|l| l.tokens.retain(|t| t.kind != TokenKind::Priority))?
            }
            (None, Some(k)) => self.insert_before_id_or_end(TokenKind::Priority, &format!("!{k}")),
            (None, None) => {}
        }
        Ok(())
    }

    /// Set (or with `None` remove) `@parent`. Setting replaces the first
    /// `@parent` (the one that counts); removing drops every `@` token.
    /// Removing can fail like [`ItemLine::remove_token`].
    pub fn set_parent(&mut self, parent: Option<&Ref>) -> Result<(), EditError> {
        match (self.index_of(&TokenKind::Parent), parent) {
            (Some(i), Some(p)) => self.tokens[i].text = p.token(),
            (Some(_), None) => {
                self.edit_keeping_flags(|l| l.tokens.retain(|t| t.kind != TokenKind::Parent))?
            }
            (None, Some(p)) => self.insert_before_id_or_end(TokenKind::Parent, &p.token()),
            (None, None) => {}
        }
        Ok(())
    }

    /// Add `#tag` after the last existing tag (no-op if present).
    pub fn add_tag(&mut self, tag: &str) {
        if self.has_tag(tag) {
            return;
        }
        let text = format!("#{tag}");
        match self.tokens.iter().rposition(|t| t.kind == TokenKind::Tag) {
            Some(i) => self.insert_at(i + 1, TokenKind::Tag, &text),
            None => self.insert_before_id_or_end(TokenKind::Tag, &text),
        }
    }

    /// Remove `#tag`; returns whether it was present. Can fail like
    /// [`ItemLine::remove_token`].
    pub fn remove_tag(&mut self, tag: &str) -> Result<bool, EditError> {
        if !self.has_tag(tag) {
            return Ok(false);
        }
        self.edit_keeping_flags(|l| {
            l.tokens
                .retain(|t| !(t.kind == TokenKind::Tag && t.text[1..] == *tag))
        })
        .map(|_| true)
    }

    /// Add a flag (no-op if present): after the last existing flag, else
    /// before the `^id`, else at the end — moved after the `^id` when nothing
    /// else would separate it from the title; fails with
    /// [`EditError::FlagNeedsBoundary`] when that is impossible.
    pub fn add_flag(&mut self, flag: &str) -> Result<(), EditError> {
        if self.has_flag(flag) {
            return Ok(());
        }
        self.edit_keeping_flags(|l| match l.tokens.iter().rposition(|t| t.kind == TokenKind::Flag) {
            Some(i) => l.insert_at(i + 1, TokenKind::Flag, flag),
            None => l.insert_before_id_or_end(TokenKind::Flag, flag),
        })
    }

    /// Remove a flag; returns whether it was present.
    pub fn remove_flag(&mut self, flag: &str) -> bool {
        let before = self.tokens.len();
        self.tokens
            .retain(|t| !(t.kind == TokenKind::Flag && t.text == flag));
        self.tokens.len() != before
    }

    /// Append ` ^id` (or replace an existing id). Used by `--fix-ids`.
    pub fn append_id(&mut self, id: &Id) {
        match self.index_of(&TokenKind::Id) {
            Some(i) => self.tokens[i].text = id.token(),
            None => self.insert_at(self.tokens.len(), TokenKind::Id, &id.token()),
        }
    }
}

/// Append ` ^id` to a raw item line, keeping everything else (including
/// trailing whitespace) as is.
pub fn append_id_to_text(text: &str, id: &Id) -> Result<String, ParseError> {
    let mut line = ItemLine::parse(text)?;
    line.append_id(id);
    Ok(line.to_string())
}

// ---------------------------------------------------------------------------
// Line → Item
// ---------------------------------------------------------------------------

/// Context for parsing one line.
#[derive(Clone, Debug, PartialEq)]
pub struct ParseCtx<'a> {
    /// File path (recorded in `src.file`).
    pub file: &'a str,
    /// Horizon of the file (drives defaults for ci, scope, missing state).
    pub horizon: Horizon,
    /// Minutes per block (`config.day.block_min`).
    pub block_min: u32,
    /// 1-based line number.
    pub line: usize,
    /// Enclosing heading text, if any.
    pub section: Option<&'a str>,
    /// `(series name, 0-based index)` inside a `## series:` section.
    pub series: Option<(&'a str, u32)>,
}

impl<'a> ParseCtx<'a> {
    /// A context for a stand-alone line in `file` (horizon from the path;
    /// unknown paths count as backlog).
    pub fn new(file: &'a str, block_min: u32) -> ParseCtx<'a> {
        ParseCtx {
            file,
            horizon: Horizon::from_path(file).unwrap_or(Horizon::Backlog),
            block_min,
            line: 1,
            section: None,
            series: None,
        }
    }
}

/// Parse one item line.
pub fn parse_line(text: &str, ctx: &ParseCtx) -> Result<Item, ParseError> {
    let line = ItemLine::parse(text)?;
    Ok(build_item(line, ctx))
}

/// Raw `key:value` pairs collected from a line (with their token index so
/// `extra` keeps line order); the first occurrence of a key wins.
struct Collected {
    vals: Vec<(usize, String, String)>,
    extra: Vec<(usize, String, String)>,
    problems: Vec<String>,
}

impl Collected {
    fn has(&self, key: &str) -> bool {
        self.vals.iter().any(|(_, k, _)| k == key)
    }

    fn take(&mut self, key: &str) -> Option<(usize, String)> {
        let i = self.vals.iter().position(|(_, k, _)| k == key)?;
        let (idx, _, v) = self.vals.remove(i);
        Some((idx, v))
    }

    /// Parse the value of `key` with `f`; on failure keep it in `extra` and
    /// note a problem.
    fn parse<T>(&mut self, key: &str, f: impl Fn(&str) -> Result<T, crate::model::ModelError>) -> Option<T> {
        let (idx, v) = self.take(key)?;
        match f(&v) {
            Ok(t) => Some(t),
            Err(e) => {
                self.problems.push(format!("`{key}:{v}`: {e}"));
                self.extra.push((idx, key.to_string(), v));
                None
            }
        }
    }

    /// `extra` in line order, without the indices.
    fn extra_in_order(mut self) -> Vec<(String, String)> {
        self.extra.sort_by_key(|(i, _, _)| *i);
        self.extra.into_iter().map(|(_, k, v)| (k, v)).collect()
    }
}

fn build_item(line: ItemLine, ctx: &ParseCtx) -> Item {
    let bm = ctx.block_min;
    let mut state = State::Todo;
    let mut has_state = false;
    let mut ci_pos: Option<u8> = None;
    let mut est_original = None;
    let mut title_parts: Vec<&str> = Vec::new();
    let mut parent: Option<Ref> = None;
    let mut tags = Vec::new();
    let mut priority = None;
    let mut id = Id::default();
    let mut flags: Vec<String> = Vec::new();
    let mut col = Collected {
        vals: Vec::new(),
        extra: Vec::new(),
        problems: Vec::new(),
    };

    for (idx, t) in line.tokens.iter().enumerate() {
        match &t.kind {
            TokenKind::Bullet => {}
            TokenKind::State => {
                has_state = true;
                state = State::parse(&t.text).unwrap_or(State::Todo);
            }
            TokenKind::Ci => ci_pos = t.text.parse().ok(),
            TokenKind::Est => match Dur::parse_no_days(&t.text, bm) {
                Ok(d) => est_original = Some(d),
                // The slot by shape (`is_est_slot`), a value this reader
                // cannot hold: named, never read as a title word (P57).
                Err(e) => col.problems.push(format!("`{}` (the leading estimate): {e}", t.text)),
            },
            TokenKind::Title | TokenKind::Word => title_parts.push(&t.text),
            TokenKind::Parent => {
                if parent.is_none() {
                    parent = Some(Ref::new(&t.text[1..]));
                } else {
                    col.problems.push(format!("duplicate parent `{}`", t.text));
                }
            }
            TokenKind::Tag => tags.push(t.text[1..].to_string()),
            TokenKind::Priority => {
                if priority.is_some() {
                    col.problems.push(format!("duplicate priority `{}`", t.text));
                } else {
                    priority = t.text[1..].parse::<u8>().ok();
                }
            }
            TokenKind::Id => {
                if id.is_empty() {
                    id = Id::new(&t.text[1..]);
                } else {
                    col.problems.push(format!("duplicate id `{}`", t.text));
                }
            }
            TokenKind::Flag => {
                if !flags.iter().any(|f| f == &t.text) {
                    flags.push(t.text.clone());
                }
            }
            TokenKind::Unparsed => {
                title_parts.push(&t.text);
                col.problems.push(format!("unclassified token `{}` kept in the title", t.text));
            }
            TokenKind::Key(k) => {
                let v = t.value().unwrap_or("").to_string();
                let k = if k == "cap" { "max" } else { k.as_str() };
                if !KEYS.contains(&k) {
                    col.extra.push((idx, k.to_string(), v));
                } else if col.has(k) {
                    col.problems.push(format!("duplicate key `{}`", t.text));
                } else {
                    col.vals.push((idx, k.to_string(), v));
                }
            }
        }
    }

    if !has_state && !ctx.horizon.allows_missing_state() {
        col.problems.push("missing state".to_string());
    }
    // A flag name at the end of the title segment is title text by the §4.1
    // rule; say so, since it was probably meant as a flag.
    if let Some(last) = line.title_segment().split_whitespace().last() {
        if FLAGS.contains(&last) {
            col.problems.push(format!(
                "title ends with `{last}`: flags count only after a `@ # ! ^ key:` token; move it after one if it was meant as a flag"
            ));
        }
    }

    // Known keys.
    let due = col.parse("due", Moment::parse);
    let at = col.parse("at", parse_interval);
    let win = col.parse("win", WindowRange::parse);
    let dur = col.parse("dur", |v| Dur::parse_no_days(v, bm));
    let pref = col.parse("pref", |v| Pref::parse(v, bm));
    let every = col.parse("every", Rule::parse);
    let after_done = col.parse("after-done", |v| Recur::parse_after_done(v, bm));
    let on_event = col.parse("on-event", |v| Recur::parse_on_event(v, bm));
    let on_miss = col.parse("on-miss", OnMiss::parse);
    let floor = col.parse("min", |v| Rate::parse(v, bm));
    let cap = col.parse("max", |v| Rate::parse(v, bm));
    let after = col.parse("after", Dep::parse_list).unwrap_or_default();
    let loc = col.parse("loc", Loc::parse).unwrap_or_default();
    let est = col.parse("est", |v| Dur::parse_no_days(v, bm));
    let demoted = col.parse("demoted", Stamp::parse_list).unwrap_or_default();
    let waiting_since = col.parse("waiting", parse_date);
    let buffer = col.parse("buffer", |v| Dur::parse(v, bm));
    let ci_key = col.parse("ci", |v| match v.parse::<u8>() {
        Ok(n) if n <= 5 => Ok(n),
        _ => Err(crate::model::ModelError::Invalid {
            what: "ci",
            value: v.to_string(),
        }),
    });

    // Shape.
    let shape = if let Some((start, end)) = at {
        if due.is_some() || win.is_some() {
            col.problems.push("conflicting shape keys (at: wins)".to_string());
        }
        Shape::Interval { start, end }
    } else if let Some(range) = win {
        if due.is_some() {
            col.problems.push("conflicting shape keys (win: wins)".to_string());
        }
        match dur {
            Some(d) => Shape::Window { range, dur: d },
            None => {
                col.problems.push("win: without dur:".to_string());
                Shape::None
            }
        }
    } else if let Some(due) = due {
        Shape::Point { due }
    } else {
        Shape::None
    };

    // Recurrence.
    let recur_count = every.is_some() as u8 + after_done.is_some() as u8 + on_event.is_some() as u8;
    if recur_count > 1 {
        col.problems.push("conflicting recurrence keys (every: > after-done: > on-event:)".to_string());
    }
    let recur = every
        .map(Recur::Calendar)
        .or(after_done)
        .or(on_event)
        .unwrap_or_default();

    // ci.
    if ci_pos.is_some() && ci_key.is_some() {
        col.problems.push("ci given twice (ci: wins)".to_string());
    }
    let (ci, ci_explicit) = match ci_key.or(ci_pos) {
        Some(c) => (c, true),
        None => (ctx.horizon.default_ci(), false),
    };

    let scope = if flags.iter().any(|f| f == "open") || ctx.horizon.is_open_file() {
        Scope::Open
    } else {
        Scope::Finite
    };
    let on_miss = on_miss.unwrap_or_else(|| shape.default_on_miss());
    let problems = std::mem::take(&mut col.problems);

    Item {
        id,
        title: title_parts.join(" "),
        state,
        ci,
        ci_explicit,
        est,
        est_original,
        dur,
        priority,
        parent,
        horizon: ctx.horizon,
        scope,
        shape,
        pref,
        recur,
        on_miss,
        budget: Budget { floor, cap },
        splittable: !flags.iter().any(|f| f == "atomic"),
        after,
        loc,
        buffer,
        tags,
        flags,
        series: ctx.series.map(|(n, i)| (n.to_string(), i)),
        stamps: Stamps {
            demoted,
            waiting_since,
        },
        extra: col.extra_in_order(),
        problems,
        src: SourceLoc {
            file: ctx.file.to_string(),
            line: ctx.line,
            section: ctx.section.map(|s| s.to_string()),
            tokens: line,
        },
    }
}

// ---------------------------------------------------------------------------
// Canonical line builder
// ---------------------------------------------------------------------------

/// Build a fresh canonical line from an item's fields (for `tm add` and the
/// capture preview). Order: state, ci, est, title, `@parent`, `#tags`, `!k`,
/// keys in §4.1 table order, extra keys, flags, `^id`. Routine/optional
/// horizons omit the state and write `ci:N` (only when explicit).
///
/// The ci is written only when `ci_explicit` (so parent inheritance is not
/// frozen into the file) — except when the title starts with a ci digit, in
/// which case the item's ci is pinned so the digit stays title text. Fails
/// with [`EditError::Ambiguous`] when the title cannot be written under the
/// grammar (it starts with a duration and there is no leading estimate, or
/// a word would be read as a token) and with [`EditError::LineBreak`] for a
/// title containing a line break.
pub fn format_item_line(item: &Item) -> Result<String, EditError> {
    check_text(&item.title)?;
    let title = normalize_title(&item.title);
    let stateless = item.horizon.is_open_file();
    let first = title.split_whitespace().next().unwrap_or("");
    let write_ci = !stateless && (item.ci_explicit || is_ci_digit(first));
    let write_est = !stateless && item.est_original.is_some();
    if let Some(word) = title_conflict(&title, !stateless, write_ci, write_est) {
        return Err(EditError::Ambiguous { word });
    }

    let mut parts: Vec<String> = Vec::new();
    if !stateless {
        parts.push(item.state.as_str().to_string());
        if write_ci {
            parts.push(item.ci.to_string());
        }
        if let Some(e) = item.est_original {
            parts.push(e.to_string());
        }
    }
    if !title.is_empty() {
        parts.push(title);
    }
    // Everything between the title and the flags; each of these ends the
    // title, so any flag after them is safe.
    let mut mid: Vec<String> = Vec::new();
    if let Some(p) = &item.parent {
        mid.push(p.token());
    }
    for t in &item.tags {
        mid.push(format!("#{t}"));
    }
    if let Some(k) = item.priority {
        mid.push(format!("!{k}"));
    }
    // `dur:` is a field of its own; a window's duration is the same key.
    let dur = item.dur.or(match &item.shape {
        Shape::Window { dur, .. } => Some(*dur),
        _ => None,
    });
    match &item.shape {
        Shape::None => {}
        Shape::Point { due } => mid.push(format!("due:{due}")),
        Shape::Interval { start, end } => {
            mid.push(format!("at:{}", crate::model::fmt_interval(*start, *end)))
        }
        Shape::Window { range, .. } => mid.push(format!("win:{range}")),
    }
    if let Some(d) = dur {
        mid.push(format!("dur:{d}"));
    }
    if let Some(p) = item.pref {
        mid.push(format!("pref:{p}"));
    }
    if let Some(r) = item.recur.token() {
        mid.push(r);
    }
    if item.on_miss != item.shape.default_on_miss() {
        mid.push(format!("on-miss:{}", item.on_miss));
    }
    if let Some(r) = item.budget.floor {
        mid.push(format!("min:{r}"));
    }
    if let Some(r) = item.budget.cap {
        mid.push(format!("max:{r}"));
    }
    if !item.after.is_empty() {
        let deps: Vec<String> = item.after.iter().map(|d| d.to_string()).collect();
        mid.push(format!("after:{}", deps.join(",")));
    }
    if item.loc != Loc::Any {
        mid.push(format!("loc:{}", item.loc));
    }
    if let Some(e) = item.est {
        mid.push(format!("est:{e}"));
    }
    if !item.stamps.demoted.is_empty() {
        mid.push(format!("demoted:{}", item.stamps.demoted_value()));
    }
    if let Some(w) = item.stamps.waiting_since {
        mid.push(format!("waiting:{}", w.format("%Y-%m-%d")));
    }
    if let Some(b) = item.buffer {
        mid.push(format!("buffer:{b}"));
    }
    for (k, v) in &item.extra {
        mid.push(format!("{k}:{v}"));
    }
    if stateless && item.ci_explicit {
        mid.push(format!("ci:{}", item.ci));
    }
    let mut flags: Vec<String> = Vec::new();
    if item.scope == Scope::Open && !stateless && !item.has_flag("open") {
        flags.push("open".to_string());
    }
    if !item.splittable && !item.has_flag("atomic") {
        flags.push("atomic".to_string());
    }
    flags.extend(item.flags.iter().cloned());
    let id = item.has_id().then(|| item.id.token());
    if mid.is_empty() && !flags.is_empty() {
        // A flag directly after the title would be absorbed into it (§4.1);
        // the id supplies the boundary instead.
        let Some(id) = id else {
            return Err(EditError::FlagNeedsBoundary {
                flag: flags[0].clone(),
            });
        };
        parts.push(id);
        parts.extend(flags);
    } else {
        parts.extend(mid);
        parts.extend(flags);
        parts.extend(id);
    }
    Ok(format!("- {}", parts.join(" ")))
}

// ---------------------------------------------------------------------------
// Ids
// ---------------------------------------------------------------------------

/// Alphabet for generated ids: `[a-z0-9]` minus `l o 0 1` (32 symbols).
pub const ID_ALPHABET: &[u8] = b"abcdefghijkmnpqrstuvwxyz23456789";

/// Length of generated ids.
pub const ID_LEN: usize = 4;

/// Deterministic id generator (xorshift64*; inject the seed in tests).
#[derive(Clone, Debug)]
pub struct IdGen {
    state: u64,
}

impl IdGen {
    /// A generator with a fixed seed.
    pub fn new(seed: u64) -> IdGen {
        IdGen {
            state: if seed == 0 { 0x9E37_79B9_7F4A_7C15 } else { seed },
        }
    }

    /// A generator seeded from the clock (for production use).
    pub fn from_entropy() -> IdGen {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0);
        let addr = &nanos as *const u64 as u64;
        IdGen::new(nanos ^ addr.rotate_left(32) ^ std::process::id() as u64)
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.state = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// One random candidate id (not checked for uniqueness).
    pub fn candidate(&mut self) -> String {
        let mut r = self.next_u64();
        (0..ID_LEN)
            .map(|_| {
                let c = ID_ALPHABET[(r % ID_ALPHABET.len() as u64) as usize] as char;
                r /= ID_ALPHABET.len() as u64;
                c
            })
            .collect()
    }

    /// The next id not in `taken`; it is inserted into `taken`.
    pub fn next_id(&mut self, taken: &mut HashSet<String>) -> Id {
        loop {
            let c = self.candidate();
            if taken.insert(c.clone()) {
                return Id(c);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Files
// ---------------------------------------------------------------------------

/// A parse problem with its 1-based line number (0 = whole file).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Problem {
    /// 1-based line, or 0 for file-level problems.
    pub line: usize,
    /// Human-readable description.
    pub message: String,
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.line == 0 {
            f.write_str(&self.message)
        } else {
            write!(f, "line {}: {}", self.line, self.message)
        }
    }
}

/// The line **opens** an HTML comment: `<!--` after leading spaces. Mirrors
/// `Plan.lean`'s `opensComment`, which drops `isIndent` — the space alone, not
/// the kernel's separator `isSp`, which since the owner's D83 (W-42) is
/// `char::is_whitespace` as `split_words` reads it — so a TAB does not indent
/// an opener, and an inline `<!--` in the middle of a line opens nothing, so an
/// item line can never open a comment.
pub fn opens_comment(line: &str) -> bool {
    line.trim_start_matches(' ').starts_with("<!--")
}

/// The line **closes** an HTML comment: `-->` anywhere on it, the opening
/// line included. Mirrors `Plan.lean`'s `closesComment`.
pub fn closes_comment(line: &str) -> bool {
    line.contains("-->")
}

/// Whether a comment is open **after** `line`, given whether one was open
/// before it — `Plan.lean`'s `commentAfter`, which is the whole automaton.
/// CommonMark's HTML block type 2 and nothing wider.
///
/// Every line from the opener to the closer is prose, verbatim: a
/// `- [ ] … ^id` written inside `<!-- … -->` is an example or a line commented
/// out, the Markdown preview the user reads hides it, and every reader of a tm
/// file must agree it is gone (owner **D47**, README gap 1317). This is the one
/// step function on the host side too: [`parse_file`], `tm triage` and the TUI
/// inbox all read comments through it.
pub fn comment_after(open: bool, line: &str) -> bool {
    (open || opens_comment(line)) && !closes_comment(line)
}

/// A `<!-- tm:<name> start … -->` … `<!-- tm:<name> end -->` range.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratedRange {
    /// Section name (`plan`, …).
    pub name: String,
    /// Text after `start` on the marker line (e.g. a timestamp), trimmed.
    pub info: String,
    /// 1-based line of the start marker.
    pub start_line: usize,
    /// 1-based line of the end marker; `None` when unterminated.
    pub end_line: Option<usize>,
}

/// One line of a parsed file.
// Items are much larger than verbatim strings; files are small, and keeping
// `Item` inline keeps `line.item()` a plain borrow, so no boxing.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum LineContent {
    /// An item line.
    Item(Item),
    /// Anything else, byte for byte (without its line ending).
    Verbatim(String),
}

/// A line with its number and line ending (`"\n"`, `"\r\n"`, or `""` at EOF).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Line {
    /// 1-based line number.
    pub number: usize,
    /// Item or verbatim text.
    pub content: LineContent,
    /// The line ending as found.
    pub eol: String,
}

impl Line {
    /// The line text without its ending.
    pub fn text(&self) -> String {
        match &self.content {
            LineContent::Item(i) => i.line_text(),
            LineContent::Verbatim(s) => s.clone(),
        }
    }
    /// The item, if this is an item line.
    pub fn item(&self) -> Option<&Item> {
        match &self.content {
            LineContent::Item(i) => Some(i),
            LineContent::Verbatim(_) => None,
        }
    }
}

/// A parsed plan file.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ParsedFile {
    /// Path as given.
    pub path: String,
    /// Horizon from the path (backlog when unknown; see `problems`).
    pub horizon: Horizon,
    /// `key: value` pairs from the leading `---` block, as written.
    pub front_matter: Vec<(String, String)>,
    /// All lines in order.
    pub lines: Vec<Line>,
    /// Generated ranges.
    pub generated: Vec<GeneratedRange>,
    /// File-level problems (unknown path kind, unterminated blocks).
    pub problems: Vec<Problem>,
}

impl ParsedFile {
    /// All items in line order.
    pub fn items(&self) -> impl Iterator<Item = &Item> {
        self.lines.iter().filter_map(|l| l.item())
    }
    /// All items, mutably.
    pub fn items_mut(&mut self) -> impl Iterator<Item = &mut Item> {
        self.lines.iter_mut().filter_map(|l| match &mut l.content {
            LineContent::Item(i) => Some(i),
            LineContent::Verbatim(_) => None,
        })
    }
    /// The item with `id`.
    pub fn find(&self, id: &Id) -> Option<&Item> {
        self.items().find(|i| &i.id == id)
    }
    /// The line (1-based) carrying `id`.
    pub fn line_of(&self, id: &Id) -> Option<usize> {
        self.find(id).map(|i| i.src.line)
    }
    /// A front-matter value.
    pub fn front(&self, key: &str) -> Option<&str> {
        self.front_matter
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.as_str())
    }
    /// The generated range named `name`.
    pub fn generated(&self, name: &str) -> Option<&GeneratedRange> {
        self.generated.iter().find(|g| g.name == name)
    }
    /// File-level and item-level problems, with line numbers.
    pub fn all_problems(&self) -> Vec<Problem> {
        let mut out = self.problems.clone();
        for it in self.items() {
            for p in &it.problems {
                out.push(Problem {
                    line: it.src.line,
                    message: p.clone(),
                });
            }
        }
        out
    }
    /// True when the line at 1-based `n` is inside a generated range.
    pub fn in_generated(&self, n: usize) -> bool {
        self.generated
            .iter()
            .any(|g| n >= g.start_line && g.end_line.is_none_or(|e| n <= e))
    }
    /// Serialize back to text (byte-identical when unmodified).
    pub fn to_text(&self) -> String {
        serialize_file(self)
    }
}

/// Split into `(text, eol)` pairs, keeping `\n` / `\r\n` and a final
/// unterminated line.
fn split_lines(text: &str) -> Vec<(&str, &str)> {
    let mut out = Vec::new();
    let mut rest = text;
    while !rest.is_empty() {
        match rest.find('\n') {
            Some(i) => {
                let (line, eol) = if i > 0 && rest.as_bytes()[i - 1] == b'\r' {
                    (&rest[..i - 1], &rest[i - 1..=i])
                } else {
                    (&rest[..i], &rest[i..=i])
                };
                out.push((line, eol));
                rest = &rest[i + 1..];
            }
            None => {
                out.push((rest, ""));
                break;
            }
        }
    }
    out
}

/// `(name, "start", info)` or `(name, "end", "")` for a tm marker line.
fn generated_marker(line: &str) -> Option<(String, bool, String)> {
    let t = line.trim();
    let inner = t.strip_prefix("<!--")?.strip_suffix("-->")?.trim();
    let rest = inner.strip_prefix("tm:")?;
    let mut words = rest.splitn(3, char::is_whitespace);
    let name = words.next()?.to_string();
    match words.next()? {
        "start" => Some((name, true, words.next().unwrap_or("").trim().to_string())),
        "end" => Some((name, false, String::new())),
        _ => None,
    }
}

/// Heading text for `# Heading` / `## series:x` lines.
fn heading(line: &str) -> Option<&str> {
    let hashes = line.bytes().take_while(|b| *b == b'#').count();
    if hashes == 0 {
        return None;
    }
    let rest = &line[hashes..];
    if rest.is_empty() || rest.starts_with(' ') || rest.starts_with('\t') {
        Some(rest.trim())
    } else {
        None
    }
}

/// Parse a whole file.
pub fn parse_file(path: &str, text: &str, cfg: &Config) -> ParsedFile {
    let mut problems = Vec::new();
    let horizon = match Horizon::from_path(path) {
        Some(h) => h,
        None => {
            problems.push(Problem {
                line: 0,
                message: format!("unknown file kind `{path}`; treated as backlog"),
            });
            Horizon::Backlog
        }
    };
    let raw = split_lines(text);
    let mut lines = Vec::with_capacity(raw.len());
    let mut front_matter = Vec::new();
    let mut generated: Vec<GeneratedRange> = Vec::new();

    // Front matter: `---` on line 1 … next `---`.
    let mut i = 0;
    if raw.first().is_some_and(|(l, _)| l.trim_end() == "---") {
        match raw[1..].iter().position(|(l, _)| l.trim_end() == "---") {
            Some(rel) => {
                let close = rel + 1;
                for (l, _) in &raw[1..close] {
                    if let Some((k, v)) = l.split_once(':') {
                        front_matter.push((k.trim().to_string(), v.trim().to_string()));
                    }
                }
                for (n, (l, eol)) in raw[..=close].iter().enumerate() {
                    lines.push(Line {
                        number: n + 1,
                        content: LineContent::Verbatim(l.to_string()),
                        eol: eol.to_string(),
                    });
                }
                i = close + 1;
            }
            None => problems.push(Problem {
                line: 1,
                message: "unterminated front matter".to_string(),
            }),
        }
    }

    let mut section: Option<String> = None;
    let mut series: Option<(String, u32)> = None;
    let mut in_generated = false;
    // The HTML-comment automaton, run over every line after the front
    // matter, exactly as `Plan.lean`'s is (D47). `comment` is the state
    // BEFORE the line about to be read, so the opener itself is an ordinary
    // prose line — which is what keeps `<!-- tm:plan start -->`, an opener
    // that closes on its own line, a generated marker.
    let mut comment = false;
    let mut comment_opened_at = 0usize;

    while i < raw.len() {
        let (l, eol) = raw[i];
        let number = i + 1;
        i += 1;
        let verbatim = |s: &str| LineContent::Verbatim(s.to_string());

        let was_in_comment = comment;
        if !comment && opens_comment(l) {
            comment_opened_at = number;
        }
        comment = comment_after(comment, l);
        if was_in_comment {
            // Inside a comment nothing is an item, a heading or a marker.
            lines.push(Line {
                number,
                content: verbatim(l),
                eol: eol.to_string(),
            });
            continue;
        }

        if let Some((name, start, info)) = generated_marker(l) {
            if start {
                if in_generated {
                    problems.push(Problem {
                        line: number,
                        message: format!("nested generated section `{name}`"),
                    });
                }
                generated.push(GeneratedRange {
                    name,
                    info,
                    start_line: number,
                    end_line: None,
                });
                in_generated = true;
            } else {
                match generated.iter_mut().rev().find(|g| g.name == name && g.end_line.is_none()) {
                    Some(g) => g.end_line = Some(number),
                    None => problems.push(Problem {
                        line: number,
                        message: format!("end marker without start: `{name}`"),
                    }),
                }
                in_generated = false;
            }
            lines.push(Line {
                number,
                content: verbatim(l),
                eol: eol.to_string(),
            });
            continue;
        }
        if in_generated {
            lines.push(Line {
                number,
                content: verbatim(l),
                eol: eol.to_string(),
            });
            continue;
        }
        if let Some(h) = heading(l) {
            section = Some(h.to_string());
            series = h
                .strip_prefix("series:")
                .map(|n| (n.trim().to_string(), 0));
            lines.push(Line {
                number,
                content: verbatim(l),
                eol: eol.to_string(),
            });
            continue;
        }
        let ctx = ParseCtx {
            file: path,
            horizon,
            block_min: cfg.day.block_min,
            line: number,
            section: section.as_deref(),
            series: series.as_ref().map(|(n, i)| (n.as_str(), *i)),
        };
        let content = match parse_line(l, &ctx) {
            Ok(item) => {
                if let Some((_, idx)) = series.as_mut() {
                    *idx += 1;
                }
                LineContent::Item(item)
            }
            Err(ParseError::NotAnItemLine) => verbatim(l),
        };
        lines.push(Line {
            number,
            content,
            eol: eol.to_string(),
        });
    }

    if comment {
        // The kernel's loader refuses the file by name
        // (`LErr.unterminatedComment`, naming the opener); the host reports it
        // the way it reports the other two unterminated things, so the two
        // readers agree about where the comment stopped instead of guessing.
        problems.push(Problem {
            line: comment_opened_at,
            message: "unterminated comment".to_string(),
        });
    }

    for g in &generated {
        if g.end_line.is_none() {
            problems.push(Problem {
                line: g.start_line,
                message: format!("unterminated generated section `{}`", g.name),
            });
        }
    }

    ParsedFile {
        path: path.to_string(),
        horizon,
        front_matter,
        lines,
        generated,
        problems,
    }
}

/// Write a parsed file back; byte-identical when nothing was edited.
pub fn serialize_file(file: &ParsedFile) -> String {
    let mut out = String::new();
    for l in &file.lines {
        match &l.content {
            LineContent::Item(i) => out.push_str(&i.line_text()),
            LineContent::Verbatim(s) => out.push_str(s),
        }
        out.push_str(&l.eol);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{DurUnit, IsoWeek, Period, YearMonth};
    use chrono::{NaiveDate, NaiveTime, Weekday};

    fn ctx(file: &str) -> ParseCtx<'_> {
        ParseCtx::new(file, 60)
    }

    fn week(text: &str) -> Item {
        parse_line(text, &ctx("week/2026-W37.md")).unwrap()
    }

    fn routine(text: &str) -> Item {
        parse_line(text, &ctx("routines.md")).unwrap()
    }

    fn dt(s: &str) -> chrono::NaiveDateTime {
        crate::model::parse_datetime(s).unwrap()
    }

    fn t(s: &str) -> NaiveTime {
        crate::model::parse_time(s).unwrap()
    }

    #[test]
    fn spec_header_example() {
        let s = "- [ ] 4 2b Exercises 5.3–5.5  @m1 #lean due:2026-09-11T23:59 max:2b/d est:1b ^t3";
        let it = week(s);
        assert_eq!(it.state, State::Todo);
        assert_eq!(it.ci, 4);
        assert!(it.ci_explicit);
        assert_eq!(it.est_original, Some(Dur::blocks(2, 60)));
        assert_eq!(it.est, Some(Dur::blocks(1, 60)));
        assert_eq!(it.title, "Exercises 5.3–5.5");
        assert_eq!(it.parent, Some(Ref::new("m1")));
        assert_eq!(it.tags, vec!["lean"]);
        assert_eq!(
            it.shape,
            Shape::Point {
                due: Moment::DateTime(dt("2026-09-11T23:59"))
            }
        );
        assert_eq!(it.budget.cap.unwrap().to_string(), "2b/d");
        assert_eq!(it.budget.cap.unwrap().per, Period::Day);
        assert_eq!(it.id, Id::new("t3"));
        assert_eq!(it.on_miss, OnMiss::Persist);
        assert_eq!(it.horizon, Horizon::Week(IsoWeek::new(2026, 37)));
        assert!(it.problems.is_empty(), "{:?}", it.problems);
        assert_eq!(it.line_text(), s);
    }

    #[test]
    fn month_priority_before_title() {
        let s = "- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1";
        let it = parse_line(s, &ctx("month/2026-09.md")).unwrap();
        assert_eq!(it.priority, Some(1));
        assert_eq!(it.title, "Lean: through ch.8 of the tutorial");
        assert_eq!(it.id, Id::new("O1"));
        assert_eq!(it.horizon, Horizon::Month(YearMonth::new(2026, 9)));
        assert!(it.problems.is_empty());
        assert_eq!(it.line_text(), s);
        let it = parse_line(
            "- [ ] 2 !3 Winter course selection + admin done        ^O3",
            &ctx("month/2026-09-a.md"),
        )
        .unwrap();
        assert_eq!(it.title, "Winter course selection + admin done");
    }

    #[test]
    fn at_interval_forms() {
        let it = week("- [ ] 5 2h Midterm                      @O3 at:2026-10-20T10:00/12:00 loc:JCL ^x1");
        assert_eq!(
            it.shape,
            Shape::Interval {
                start: dt("2026-10-20T10:00"),
                end: dt("2026-10-20T12:00")
            }
        );
        assert_eq!(it.loc, Loc::Named("JCL".into()));
        assert_eq!(it.est_original, Some(Dur::hours(2)));
        let it = parse_line(
            "- [ ] 1 ✈ ORD→SFO UA 1234    at:2026-09-12T08:15/10:40 buffer:2h travel-day ^g3",
            &ctx("calendar/2026-W37.md"),
        )
        .unwrap();
        assert_eq!(it.title, "✈ ORD→SFO UA 1234");
        assert_eq!(
            it.shape,
            Shape::Interval {
                start: dt("2026-09-12T08:15"),
                end: dt("2026-09-12T10:40")
            }
        );
        assert_eq!(it.buffer, Some(Dur::hours(2)));
        assert!(it.is_travel_day());
        assert_eq!(it.horizon, Horizon::Calendar(IsoWeek::new(2026, 37)));
        let it = week("- [ ] 3 Trip at:2026-09-12T08:15/2026-09-13T10:40 ^z1");
        assert_eq!(
            it.shape,
            Shape::Interval {
                start: dt("2026-09-12T08:15"),
                end: dt("2026-09-13T10:40")
            }
        );
    }

    #[test]
    fn routine_windows() {
        let it = routine("- sleep      win:22:00-08:00 dur:8h30m every:day ci:0");
        assert_eq!(it.title, "sleep");
        assert_eq!(it.state, State::Todo);
        assert_eq!(it.ci, 0);
        assert!(it.ci_explicit);
        assert_eq!(it.scope, Scope::Open);
        assert_eq!(it.horizon, Horizon::Routine);
        assert_eq!(
            it.shape,
            Shape::Window {
                range: WindowRange::Daily {
                    from: t("22:00"),
                    to: t("08:00")
                },
                dur: Dur::hours_minutes(8, 30)
            }
        );
        assert_eq!(it.dur, Some(Dur::hours_minutes(8, 30)));
        assert_eq!(it.recur, Recur::Calendar(Rule::Daily));
        assert_eq!(it.on_miss, OnMiss::Expire);
        assert!(it.problems.is_empty(), "{:?}", it.problems);

        let it = routine("- breakfast  win:06:00-09:00 dur:30m  every:day pref:wake+10m");
        assert_eq!(it.ci, 1);
        assert!(!it.ci_explicit);
        assert_eq!(it.pref, Some(Pref::WakePlus(Dur::from_minutes(10))));

        let it = routine("- workout    win:16:00-19:00 dur:1h   every:Mon,Wed,Fri");
        assert_eq!(
            it.recur,
            Recur::Calendar(Rule::Weekly(vec![Weekday::Mon, Weekday::Wed, Weekday::Fri]))
        );

        let it = routine("- shower     win:07:00-23:00 dur:20m  after-done:2d~1d");
        assert_eq!(
            it.recur,
            Recur::AfterDone {
                offset: Dur::days(2),
                window: Some(Dur::days(1))
            }
        );
        let it = routine("- laundry    win:09:00-21:00 dur:30m  every:week on-miss:persist");
        assert_eq!(it.recur, Recur::Calendar(Rule::Weeks(1)));
        assert_eq!(it.on_miss, OnMiss::Persist);
        let it = routine("- groceries  win:10:00-20:00 dur:45m  every:week loc:out");
        assert_eq!(it.loc, Loc::Out);
        let it = routine("- pay rent   every:month:1 dur:10m win:09:00-17:00");
        assert_eq!(it.recur, Recur::Calendar(Rule::Monthly(1)));
        let it = routine("- review     every:2w:Sun dur:1h win:10:00-18:00");
        assert_eq!(it.recur, Recur::Calendar(Rule::EveryNWeeks(2, Weekday::Sun)));
        let it = routine("- water plants every:3d dur:5m win:08:00-22:00");
        assert_eq!(it.recur, Recur::Calendar(Rule::EveryNDays(3)));
        let it = routine("- standup every:weekday win:09:00-09:30 dur:15m");
        assert_eq!(it.recur, Recur::Calendar(Rule::Weekdays));
    }

    #[test]
    fn optional_and_backlog_examples() {
        let it = parse_line("- Factorio        dur:2h max:4h/w", &ctx("optional.md")).unwrap();
        assert_eq!(it.ci, 0);
        assert_eq!(it.scope, Scope::Open);
        assert_eq!(it.shape, Shape::None);
        assert_eq!(it.dur, Some(Dur::hours(2)));
        assert_eq!(it.budget.cap, Some(Rate::parse("4h/w", 60).unwrap()));
        assert!(it.problems.is_empty());

        let it = parse_line(
            "- [ ] 1 Pick up package  win:2026-09-07T09:00/21:00 dur:20m ^a3",
            &ctx("backlog.md"),
        )
        .unwrap();
        assert_eq!(it.title, "Pick up package");
        assert_eq!(it.ci, 1);
        assert_eq!(it.est_original, None);
        assert_eq!(
            it.shape,
            Shape::Window {
                range: WindowRange::Absolute {
                    from: dt("2026-09-07T09:00"),
                    to: dt("2026-09-07T21:00")
                },
                dur: Dur::from_minutes(20)
            }
        );
        assert_eq!(it.scope, Scope::Finite);

        let it = parse_line(
            "- [?] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4",
            &ctx("backlog.md"),
        )
        .unwrap();
        assert_eq!(it.state, State::Waiting);
        assert_eq!(it.title, "Ask Prof. Lee about the reading group");
        assert_eq!(
            it.recur,
            Recur::OnEvent {
                name: "reply".into(),
                timeout: Some(Dur::days(7))
            }
        );
        assert_eq!(
            it.stamps.waiting_since,
            Some(NaiveDate::from_ymd_opt(2026, 9, 5).unwrap())
        );

        let it = parse_line(
            "- [ ] 5 10b Workshop paper draft  @O2 due:2026-11-20 #soundcode ^d2",
            &ctx("backlog.md"),
        )
        .unwrap();
        assert_eq!(
            it.shape,
            Shape::Point {
                due: Moment::Date(NaiveDate::from_ymd_opt(2026, 11, 20).unwrap())
            }
        );
        assert_eq!(it.tags, vec!["soundcode"]);

        let it = week("- [ ] 3 1b Review the drafts            @m2 after:^t4 ^t5");
        assert_eq!(it.after, vec![Dep::Item(Id::new("t4"))]);
        let it = week("- [ ] 3 1b X after:^k7q2,^m2,event:visa ^t6");
        assert_eq!(
            it.after,
            vec![
                Dep::Item(Id::new("k7q2")),
                Dep::Item(Id::new("m2")),
                Dep::Event("visa".into())
            ]
        );
        let it = parse_line(
            "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2",
            &ctx("month/2026-09.md"),
        )
        .unwrap();
        assert_eq!(it.state, State::Demoted);
        assert_eq!(it.stamps.demoted, vec![Stamp::Week(37)]);
        let it = week("- [ ] 3 X demoted:W36,W37 ^q");
        assert_eq!(it.stamps.demoted, vec![Stamp::Week(36), Stamp::Week(37)]);
        let it = week("- [ ] 3 X demoted:D07 ^q");
        assert_eq!(it.stamps.demoted, vec![Stamp::Day(7)]);
    }

    #[test]
    fn budgets_flags_misc() {
        let it = week("- [ ] 4 Lean practice min:6b/w open ^l1");
        assert_eq!(it.budget.floor, Some(Rate::parse("6b/w", 60).unwrap()));
        assert_eq!(it.scope, Scope::Open);
        assert!(it.has_flag("open"));
        let it = week("- [ ] 4 X cap:30m/d atomic hot manual ^l2");
        assert_eq!(it.budget.cap.unwrap().amount, Dur::from_minutes(30));
        assert!(!it.splittable);
        assert!(it.is_hot());
        assert!(it.is_manual());
        assert_eq!(it.flags, vec!["atomic", "hot", "manual"]);
        let it = week("- [ ] 4 X on-miss:next ^l3 pref:12:00 due:2026-09-11");
        assert_eq!(it.on_miss, OnMiss::Next);
        assert_eq!(it.pref, Some(Pref::At(t("12:00"))));
        let it = week("- [x] 2 X ^l4 every:2w:Sun");
        assert_eq!(it.state, State::Done);
        assert_eq!(it.recur, Recur::Calendar(Rule::EveryNWeeks(2, Weekday::Sun)));
        let it = week("- [ ] 3 8h30m Long thing ^l5");
        assert_eq!(it.est_original.unwrap().unit, DurUnit::HoursMinutes);
        assert_eq!(it.est_original.unwrap().minutes, 510);
        let it = week("- [ ] 2d printing ^l6");
        assert_eq!(it.est_original, None);
        assert_eq!(it.title, "2d printing");
        assert_eq!(it.ci, 3);
        assert!(!it.ci_explicit);
    }

    #[test]
    fn problems_and_extra() {
        let it = week("- [ ] 3 X due:2026-13-01 foo:bar !9 ^ ^t1 ^t2");
        assert_eq!(it.extra, vec![("due".to_string(), "2026-13-01".to_string()), ("foo".to_string(), "bar".to_string())]);
        assert_eq!(it.shape, Shape::None);
        assert_eq!(it.id, Id::new("t1"));
        assert_eq!(it.title, "X !9 ^", "unclassified tokens stay in the title");
        assert!(it.problems.iter().any(|p| p.contains("due:2026-13-01")));
        assert!(it.problems.iter().any(|p| p.contains("`!9`")));
        assert!(!it.problems.iter().any(|p| p.contains("`^`")), "a lone sigil is punctuation");
        assert!(it.problems.iter().any(|p| p.contains("duplicate id")));
        assert_eq!(it.line_text(), "- [ ] 3 X due:2026-13-01 foo:bar !9 ^ ^t1 ^t2");

        let it = week("- [ ] 3 X win:09:00-17:00 ^t1");
        assert_eq!(it.shape, Shape::None);
        assert!(it.problems.iter().any(|p| p.contains("win: without dur:")));

        let it = week("- [ ] 3 X due:2026-09-11 at:2026-09-11T10:00/11:00 ^t1");
        assert!(matches!(it.shape, Shape::Interval { .. }));
        assert!(it.problems.iter().any(|p| p.contains("conflicting shape")));

        let it = week("- [ ] 3 X every:day after-done:2d ^t1");
        assert_eq!(it.recur, Recur::Calendar(Rule::Daily));
        assert!(it.problems.iter().any(|p| p.contains("conflicting recurrence")));

        let it = week("- [ ] 3 X ci:7 ^t1");
        assert_eq!(it.ci, 3);
        assert!(it.problems.iter().any(|p| p.contains("ci:7")));

        let it = week("- [ ] 3 X ci:5 ^t1");
        assert_eq!(it.ci, 5);
        assert!(it.problems.iter().any(|p| p.contains("ci given twice")));

        let it = week("- No state here ^t1");
        assert!(it.problems.iter().any(|p| p == "missing state"));
        let it = parse_line("- No state here", &ctx("inbox.md")).unwrap();
        assert!(it.problems.is_empty());
        assert_eq!(it.horizon, Horizon::Inbox);

        let it = week("- [ ] 3 X due:2026-09-11 due:2026-09-12 ^t1");
        assert_eq!(
            it.shape,
            Shape::Point {
                due: Moment::Date(NaiveDate::from_ymd_opt(2026, 9, 11).unwrap())
            }
        );
        assert!(it.problems.iter().any(|p| p.contains("duplicate key")));

        assert_eq!(
            parse_line("not an item", &ctx("backlog.md")),
            Err(ParseError::NotAnItemLine)
        );
        assert_eq!(parse_line("- ", &ctx("backlog.md")), Err(ParseError::NotAnItemLine));
        assert_eq!(parse_line("  - [ ] x", &ctx("backlog.md")), Err(ParseError::NotAnItemLine));
    }

    #[test]
    fn title_edge_cases() {
        let it = week("- [ ]");
        assert_eq!(it.title, "");
        assert_eq!(it.line_text(), "- [ ]");
        let it = week("- [ ] 3");
        assert_eq!(it.ci, 3);
        assert_eq!(it.title, "");
        let it = week("- [ ] 3 things");
        assert_eq!(it.ci, 3);
        assert_eq!(it.title, "things");
        let it = week("- [ ] 42 things");
        assert_eq!(it.ci, 3);
        assert_eq!(it.title, "42 things");
        let it = week("- [ ]\t3\t2b\tTabbed  title\t@m1\t^t1");
        assert_eq!(it.title, "Tabbed  title");
        assert_eq!(it.parent, Some(Ref::new("m1")));
        assert_eq!(it.line_text(), "- [ ]\t3\t2b\tTabbed  title\t@m1\t^t1");
        // Bare words after tokens join the title with single spaces.
        let it = week("- [ ] 3 Read @m1 the   book ^t1");
        assert_eq!(it.title, "Read the book");
        // `Note:` (uppercase) does not end the title; `re:` does.
        let it = week("- [ ] 3 Note: call bank ^t1");
        assert_eq!(it.title, "Note: call bank");
        let it = week("- [ ] 3 Call re: bank ^t1");
        assert_eq!(it.title, "Call bank");
        assert_eq!(it.extra, vec![("re".to_string(), String::new())]);
    }

    #[test]
    fn edit_ops_minimal_diffs() {
        let s = "- [>] 4 2b Exercises 5.3–5.5            @m1 ^t3";
        let mut l = ItemLine::parse(s).unwrap();
        l.set_token("est", "1b");
        assert_eq!(l.to_string(), "- [>] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3");
        l.set_token("est", "2b");
        assert_eq!(l.to_string(), "- [>] 4 2b Exercises 5.3–5.5            @m1 est:2b ^t3");
        assert_eq!(l.get("est"), Some("2b"));
        assert_eq!(l.remove_token("est"), Ok(true));
        assert_eq!(l.remove_token("est"), Ok(false));
        assert_eq!(l.to_string(), s);

        let s = "- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1";
        let mut l = ItemLine::parse(s).unwrap();
        l.set_token("due", "2026-09-12T23:59");
        assert_eq!(
            l.to_string(),
            "- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-12T23:59 max:2b/d ^d1"
        );
        l.set_state(State::Active).unwrap();
        assert_eq!(
            l.to_string(),
            "- [>] 4 6b CS 234 pset 2                @O3 due:2026-09-12T23:59 max:2b/d ^d1"
        );
        l.set_ci(5);
        l.set_leading_est(Some(Dur::blocks(8, 60))).unwrap();
        assert_eq!(
            l.to_string(),
            "- [>] 5 8b CS 234 pset 2                @O3 due:2026-09-12T23:59 max:2b/d ^d1"
        );
        l.set_leading_est(None).unwrap();
        assert_eq!(
            l.to_string(),
            "- [>] 5 CS 234 pset 2                @O3 due:2026-09-12T23:59 max:2b/d ^d1"
        );
        l.set_leading_est(Some(Dur::hours(2))).unwrap();
        assert_eq!(
            l.to_string(),
            "- [>] 5 2h CS 234 pset 2                @O3 due:2026-09-12T23:59 max:2b/d ^d1"
        );
        l.set_title("pset 2").unwrap();
        l.set_priority(Some(2)).unwrap();
        l.add_flag("hot").unwrap();
        l.add_tag("cs234");
        l.add_tag("cs234");
        assert_eq!(
            l.to_string(),
            "- [>] 5 2h pset 2                @O3 due:2026-09-12T23:59 max:2b/d !2 hot #cs234 ^d1"
        );
        l.add_tag("school");
        assert_eq!(
            l.to_string(),
            "- [>] 5 2h pset 2                @O3 due:2026-09-12T23:59 max:2b/d !2 hot #cs234 #school ^d1"
        );
        assert_eq!(l.remove_tag("cs234"), Ok(true));
        assert_eq!(l.remove_tag("cs234"), Ok(false));
        assert!(l.remove_flag("hot"));
        assert!(!l.remove_flag("hot"));
        l.set_priority(None).unwrap();
        l.set_parent(Some(&Ref::new("O2"))).unwrap();
        assert_eq!(
            l.to_string(),
            "- [>] 5 2h pset 2                @O2 due:2026-09-12T23:59 max:2b/d #school ^d1"
        );
        // Removing a token removes the whitespace that preceded it.
        l.set_parent(None).unwrap();
        assert_eq!(
            l.to_string(),
            "- [>] 5 2h pset 2 due:2026-09-12T23:59 max:2b/d #school ^d1"
        );
        // cap: is an alias of max:
        l.set_token("cap", "1b/d");
        assert_eq!(l.get("max"), Some("1b/d"));
        assert_eq!(
            l.to_string(),
            "- [>] 5 2h pset 2 due:2026-09-12T23:59 max:1b/d #school ^d1"
        );
    }

    #[test]
    fn edit_ops_without_id_or_state() {
        let mut l = ItemLine::parse("- [ ] 3 Call the bank  ").unwrap();
        l.set_token("due", "2026-09-11");
        assert_eq!(l.to_string(), "- [ ] 3 Call the bank due:2026-09-11  ");
        l.append_id(&Id::new("p1"));
        assert_eq!(l.to_string(), "- [ ] 3 Call the bank due:2026-09-11 ^p1  ");
        l.append_id(&Id::new("p2"));
        assert_eq!(l.to_string(), "- [ ] 3 Call the bank due:2026-09-11 ^p2  ");
        assert_eq!(l.id(), Some(Id::new("p2")));
        assert_eq!(
            append_id_to_text("- [ ] 2 20m Call the bank about the card", &Id::new("p1")).unwrap(),
            "- [ ] 2 20m Call the bank about the card ^p1"
        );

        let mut l = ItemLine::parse("- lunch      win:11:30-13:30 dur:30m  every:day").unwrap();
        l.set_ci(2);
        assert_eq!(
            l.to_string(),
            "- lunch      win:11:30-13:30 dur:30m  every:day ci:2"
        );
        l.set_ci(1);
        assert_eq!(
            l.to_string(),
            "- lunch      win:11:30-13:30 dur:30m  every:day ci:1"
        );
        assert_eq!(l.set_leading_est(Some(Dur::hours(1))), Err(EditError::NoState));
        l.set_state(State::Todo).unwrap();
        assert_eq!(
            l.to_string(),
            "- [ ] lunch      win:11:30-13:30 dur:30m  every:day ci:1"
        );
        l.remove_ci().unwrap();
        l.set_ci(3);
        assert_eq!(
            l.to_string(),
            "- [ ] 3 lunch      win:11:30-13:30 dur:30m  every:day"
        );

        // set_title on a line whose title was made of bare words after `!1`.
        let mut l = ItemLine::parse("- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1").unwrap();
        l.set_title("Lean: ch.9").unwrap();
        assert_eq!(l.to_string(), "- [ ] 5 Lean: ch.9 !1          ^O1");
        assert_eq!(l.title(), "Lean: ch.9");
        // Unparsed words are part of the title and are replaced with it.
        let mut l = ItemLine::parse("- [ ] 3 Top !5 task ^t1").unwrap();
        assert_eq!(l.title(), "Top !5 task");
        l.set_title("  Top task  ").unwrap();
        assert_eq!(l.to_string(), "- [ ] 3 Top task ^t1");
    }

    #[test]
    fn set_ci_updates_positional_and_key() {
        // Regression: only the positional digit was edited, but `ci:` wins on
        // re-parse, so the edit had no effect.
        let mut l = ItemLine::parse("- [ ] 3 Title ci:5 ^t1").unwrap();
        l.set_ci(4);
        assert_eq!(l.to_string(), "- [ ] 4 Title ci:4 ^t1");
        assert_eq!(week(&l.to_string()).ci, 4);
        let mut l = ItemLine::parse("- [ ] Title ci:5 ^t1").unwrap();
        l.set_ci(2);
        assert_eq!(l.to_string(), "- [ ] Title ci:2 ^t1");
        assert_eq!(week(&l.to_string()).ci, 2);
        let mut l = ItemLine::parse("- [ ] Title ^t1").unwrap();
        l.set_ci(2);
        assert_eq!(l.to_string(), "- [ ] 2 Title ^t1");
    }

    #[test]
    fn positional_edits_guard_the_title() {
        // Regression: set_title wrote `2h nap` into the positional slot and
        // the re-parse read `2h` as the estimate.
        let mut l = ItemLine::parse("- [ ] 3 Call ^p1").unwrap();
        assert_eq!(
            l.set_title("2h nap"),
            Err(EditError::Ambiguous { word: "2h".to_string() })
        );
        assert_eq!(l.to_string(), "- [ ] 3 Call ^p1", "a refused edit changes nothing");
        l.set_leading_est(Some(Dur::hours(1))).unwrap();
        l.set_title("2h nap").unwrap();
        assert_eq!(l.to_string(), "- [ ] 3 1h 2h nap ^p1");
        let it = week(&l.to_string());
        assert_eq!((it.title.as_str(), it.est_original), ("2h nap", Some(Dur::hours(1))));

        let mut l = ItemLine::parse("- [ ] Call ^p1").unwrap();
        assert_eq!(l.set_title("5 things"), Err(EditError::Ambiguous { word: "5".to_string() }));
        l.set_ci(3);
        l.set_title("5 things").unwrap();
        assert_eq!(week(&l.to_string()).title, "5 things");
        // With both slots filled any digit/duration title is fine; words that
        // start a token never are.
        let mut l = ItemLine::parse("- [ ] 3 2b Call ^p1").unwrap();
        l.set_title("2h 5 things").unwrap();
        assert_eq!(week(&l.to_string()).title, "2h 5 things");
        assert_eq!(l.set_title("Call @m1"), Err(EditError::Ambiguous { word: "@m1".to_string() }));
        assert_eq!(l.set_title("re: bank"), Err(EditError::Ambiguous { word: "re:".to_string() }));
        assert_eq!(l.set_title("Note: bank"), Ok(()));
        assert_eq!(l.set_title("Meet  Kun @ 7pm"), Ok(()), "a lone sigil is title text");
        assert_eq!(l.to_string(), "- [ ] 3 2b Meet Kun @ 7pm ^p1", "whitespace is normalized");
        assert_eq!(week(&l.to_string()).title, "Meet Kun @ 7pm");
        assert_eq!(l.set_title("Top !5 task"), Ok(()), "unparsed words stay title text");
        assert_eq!(week(&l.to_string()).title, "Top !5 task");
        // After a lone sigil every word is classified, so a flag is a flag.
        assert_eq!(l.set_title("Keep @ open"), Err(EditError::Ambiguous { word: "open".to_string() }));
        assert_eq!(l.set_title("Keep it open"), Ok(()));
        assert_eq!(l.set_title("a\nb"), Err(EditError::LineBreak));
        // Stateless lines have no positional slots.
        let mut l = ItemLine::parse("- lunch win:11:30-13:30 dur:30m").unwrap();
        l.set_title("5 min stretch").unwrap();
        assert_eq!(routine(&l.to_string()).title, "5 min stretch");

        // Removing a slot can expose the title the same way.
        let mut l = ItemLine::parse("- [ ] 3 5 things ^p1").unwrap();
        assert_eq!(week(&l.to_string()).title, "5 things");
        assert_eq!(l.remove_ci(), Err(EditError::Ambiguous { word: "5".to_string() }));
        let mut l = ItemLine::parse("- [ ] 3 2b 30m run ^p1").unwrap();
        assert_eq!(week(&l.to_string()).title, "30m run");
        assert_eq!(l.set_leading_est(None), Err(EditError::Ambiguous { word: "30m".to_string() }));
        l.set_leading_est(Some(Dur::blocks(1, 60))).unwrap();
        assert_eq!(l.to_string(), "- [ ] 3 1b 30m run ^p1");
    }

    #[test]
    fn set_state_on_stateless_line_guards_the_title() {
        // Regression: inserting `[ ]` before `5 min stretch` made `5` the ci.
        let ctx = ctx("routines.md");
        let it = parse_line("- 5 min stretch win:09:00-17:00 dur:5m", &ctx).unwrap();
        assert_eq!((it.title.as_str(), it.ci), ("5 min stretch", 1));
        let mut l = it.line().clone();
        assert_eq!(l.set_state(State::Todo), Err(EditError::Ambiguous { word: "5".to_string() }));
        assert_eq!(l.to_string(), "- 5 min stretch win:09:00-17:00 dur:5m");
        l.set_state_with_ci(State::Todo, it.ci).unwrap();
        assert_eq!(l.to_string(), "- [ ] 1 5 min stretch win:09:00-17:00 dur:5m");
        let again = parse_line(&l.to_string(), &ctx).unwrap();
        assert_eq!((again.title.as_str(), again.ci, again.state), ("5 min stretch", 1, State::Todo));
        // `ci:` keys are folded into the positional slot.
        let mut l = ItemLine::parse("- 5 min stretch win:09:00-17:00 dur:5m ci:2").unwrap();
        l.set_state_with_ci(State::Todo, 2).unwrap();
        assert_eq!(l.to_string(), "- [ ] 2 5 min stretch win:09:00-17:00 dur:5m");
        // A duration-leading title has no representation with a state.
        let mut l = ItemLine::parse("- 2h nap dur:2h").unwrap();
        assert_eq!(l.set_state(State::Todo), Err(EditError::Ambiguous { word: "2h".to_string() }));
        assert_eq!(l.set_state_with_ci(State::Todo, 1), Err(EditError::Ambiguous { word: "2h".to_string() }));
        // Ordinary titles are unaffected; a present state is simply replaced.
        let mut l = ItemLine::parse("- lunch win:11:30-13:30 dur:30m").unwrap();
        l.set_state(State::Todo).unwrap();
        assert_eq!(l.to_string(), "- [ ] lunch win:11:30-13:30 dur:30m");
        l.set_state(State::Done).unwrap();
        assert_eq!(l.to_string(), "- [x] lunch win:11:30-13:30 dur:30m");
        let mut l = ItemLine::parse("- [ ] 5 things").unwrap();
        l.set_state(State::Done).unwrap();
        assert_eq!(l.to_string(), "- [x] 5 things");
    }

    #[test]
    fn removing_a_token_does_not_widen_the_title() {
        // A bare word after a `@ # ! ^ key:` token is a token of its own, and
        // `title()` joins those with ONE space; the leading title segment
        // keeps its whitespace verbatim. Remove the token that separated
        // them and the word is absorbed into the segment, so whichever
        // whitespace run it happened to carry becomes title text: the line
        // below has title `0 A A a` and came back `0 A A  a`. Found by a
        // proptest seed (README gap 1316, owner D46); `set_parent(None)`,
        // `remove_tag` and `set_priority(None)` reach the same shape, and
        // `add_flag_and_remove_parent_keep_flags`'s pinned seed
        // `- [ ] a @A  a zz:0 @A` is the second case below.
        let rctx = ctx("routines.md");
        let it = parse_line("- 0 A A ci:0  a @A @a", &rctx).unwrap();
        assert_eq!(it.title, "0 A A a");
        let mut l = it.line().clone();
        l.set_state_with_ci(State::Done, it.ci).unwrap();
        assert_eq!(l.to_string(), "- [x] 0 0 A A a @A @a");
        assert_eq!(parse_line(&l.to_string(), &rctx).unwrap().title, "0 A A a");

        let wctx = ctx("week/2026-W37.md");
        let it = parse_line("- [ ] a @A  a zz:0 @A", &wctx).unwrap();
        assert_eq!(it.title, "a a");
        let mut l = it.line().clone();
        l.set_parent(None).unwrap();
        assert_eq!(l.to_string(), "- [ ] a a zz:0");
        assert_eq!(parse_line(&l.to_string(), &wctx).unwrap().title, "a a");

        let mut l = ItemLine::parse("- [ ] A #t  b ^x").unwrap();
        assert_eq!(l.title(), "A b");
        l.remove_tag("t").unwrap();
        assert_eq!(l.to_string(), "- [ ] A b ^x");

        let mut l = ItemLine::parse("- [ ] A !1  b ^x").unwrap();
        l.set_priority(None).unwrap();
        assert_eq!(l.to_string(), "- [ ] A b ^x");

        // A flag with no boundary left is moved after the `^id` first, and
        // the word behind it is still absorbed.
        let mut l = ItemLine::parse("- [ ] A ci:0 open  b ^x").unwrap();
        assert_eq!(l.title(), "A b");
        l.remove_token("ci").unwrap();
        assert_eq!(l.to_string(), "- [ ] A b ^x open");

        // And the shapes it must NOT touch. Whitespace INSIDE the title
        // segment is the author's and is preserved.
        let mut l = ItemLine::parse("- [ ] A  B #t ^x").unwrap();
        assert_eq!(l.title(), "A  B");
        l.remove_tag("t").unwrap();
        assert_eq!(l.to_string(), "- [ ] A  B ^x");
        // A word that keeps a boundary in front of it stays a word.
        let mut l = ItemLine::parse("- [ ] A #t @p  b ^x").unwrap();
        l.remove_tag("t").unwrap();
        assert_eq!(l.to_string(), "- [ ] A @p  b ^x");
        // A lone sigil and a malformed token END the title segment
        // themselves, so nothing behind them is absorbed and their own lead
        // is not the title's.
        let mut l = ItemLine::parse("- [ ] A #t @  b ^x").unwrap();
        assert_eq!(l.title(), "A @ b");
        l.remove_tag("t").unwrap();
        assert_eq!(l.to_string(), "- [ ] A @  b ^x");
        assert_eq!(l.title(), "A @ b");
        let mut l = ItemLine::parse("- [ ] A #t  !9 ^x").unwrap();
        assert_eq!(l.title(), "A !9");
        l.remove_tag("t").unwrap();
        assert_eq!(l.to_string(), "- [ ] A  !9 ^x");
        assert_eq!(l.title(), "A !9");
        // With no title text in front of it the word is the whole title, so
        // its lead is not internal whitespace and nothing needs re-leading:
        // the edit moves the bytes it must and no others.
        let mut l = ItemLine::parse("- [ ] ci:0  a").unwrap();
        assert_eq!(l.title(), "a");
        l.remove_token("ci").unwrap();
        assert_eq!(l.to_string(), "- [ ]  a");
        assert_eq!(l.title(), "a");
    }

    /// A key is representable TWICE — the parser accepts it and records
    /// `duplicate key` as a problem — and an edit that means *the fact* must
    /// take every occurrence. `remove_token` takes the first, which is the
    /// whole of the defect a W-25 seed drew: with a `ci:` left standing,
    /// `set_ci`'s keyed branch fires, the positional digit is never inserted,
    /// and the title's leading word is read as the ci on the next parse.
    /// README gap **1520**, owner **D46**.
    #[test]
    fn a_duplicated_key_is_removed_in_full_and_the_count_is_reported() {
        // The count is the fact's multiplicity, not "it was there".
        let mut l = ItemLine::parse("- [ ] hi est:1b est:2b est:3b").unwrap();
        assert_eq!(l.remove_all_tokens("est"), Ok(3));
        assert_eq!(l.to_string(), "- [ ] hi");
        let mut l = ItemLine::parse("- [ ] hi est:1b").unwrap();
        assert_eq!(l.remove_all_tokens("est"), Ok(1));
        assert_eq!(l.to_string(), "- [ ] hi");
        let mut l = ItemLine::parse("- [ ] hi").unwrap();
        assert_eq!(l.remove_all_tokens("est"), Ok(0));
        assert_eq!(l.to_string(), "- [ ] hi");

        // `remove_ci` promises "the positional ci and EVERY `ci:` key". One
        // survivor means the ci is still 0 after a clear.
        let mut l = ItemLine::parse("- [ ] 3 ci:0 ci:0").unwrap();
        l.remove_ci().unwrap();
        assert_eq!(l.to_string(), "- [ ]");
        assert_eq!(l.get("ci"), None);
        let mut l = ItemLine::parse("- [ ] 3 hi ci:0 ci:1").unwrap();
        l.remove_ci().unwrap();
        assert_eq!(l.to_string(), "- [ ] hi");
        assert_eq!(l.get("ci"), None);
        // The single-key case is unchanged, which is what says the fix is a
        // widening and not a different edit.
        let mut l = ItemLine::parse("- [ ] 3 hi ci:0").unwrap();
        l.remove_ci().unwrap();
        assert_eq!(l.to_string(), "- [ ] hi");

        // And the seed itself, as a named case rather than only as a pinned
        // proptest regression.
        let mut l = ItemLine::parse("- 0 ci:0 ci:0").unwrap();
        l.set_state_with_ci(State::Done, 0).unwrap();
        assert_eq!(l.to_string(), "- [x] 0 0");
        let again = ItemLine::parse(&l.to_string()).unwrap();
        assert_eq!(again.title(), "0");
    }

    #[test]
    fn multibyte_words_after_tokens_do_not_panic() {
        // Regression: `classify` sliced `&w[1..]` before checking the first
        // byte, so any non-ASCII bare word after a token panicked.
        let cases = [
            ("- [ ] 3 Read @m1 §3 ^t1", "Read §3"),
            ("- [ ] 3 Call mom @o1 🎂", "Call mom 🎂"),
            ("- [ ] 5 !1 Trip ✈ Tokyo ^O1", "Trip ✈ Tokyo"),
            ("- [ ] 4 !1 Soundcode: demo — runs ^O2", "Soundcode: demo — runs"),
            ("- [ ] 5 !1 Été prep ^O1", "Été prep"),
            ("- [ ] 3 Call @m1 über ^t1", "Call über"),
            ("- [ ] 1 at:2026-09-12T08:15/10:40 ✈ ORD→SFO UA 1234 buffer:2h travel-day ^g3", "✈ ORD→SFO UA 1234"),
            ("- [ ] 3 X @m1 ^é ^t1", "X ^é"),
            ("- [ ] 3 X @é #ü ^t1", "X"),
        ];
        for (line, title) in cases {
            let it = week(line);
            assert_eq!(it.title, title, "{line}");
            assert_eq!(it.line_text(), line);
        }
        let it = week("- [ ] 3 X @é #ü ^t1");
        assert_eq!(it.parent, Some(Ref::new("é")));
        assert_eq!(it.tags, vec!["ü"]);
        let it = week("- [ ] 3 X @m1 ^é ^t1");
        assert!(it.problems.iter().any(|p| p.contains("`^é`")));
        assert_eq!(it.id, Id::new("t1"));
        let f = parse_file("week/2026-W37.md", "- [ ] 3 Read @m1 §3 ^t1\n- [ ] 4 !1 Demo — runs ^O2\n", &Config::default());
        assert_eq!(f.items().count(), 2);
        assert_eq!(f.items().nth(1).unwrap().title, "Demo — runs");
        assert!(f.all_problems().is_empty(), "{:?}", f.all_problems());
    }

    #[test]
    fn unparsed_tokens_stay_in_title() {
        // Regression: malformed structured tokens were dropped from the title.
        let it = week("- [ ] 3 Meet Kun @ 7pm ^t1");
        assert_eq!(it.title, "Meet Kun @ 7pm");
        assert!(it.problems.is_empty(), "{:?}", it.problems);
        let it = week("- [ ] 3 Top !5 task ^t1");
        assert_eq!(it.title, "Top !5 task");
        assert!(it.problems.iter().any(|p| p.contains("`!5`") && p.contains("kept in the title")));
        let it = week("- [ ] 3 Issue # 42 ! ^ ^t1");
        assert_eq!(it.title, "Issue # 42 ! ^");
        assert!(it.problems.is_empty(), "{:?}", it.problems);
        assert_eq!(it.id, Id::new("t1"));
        let it = week("- [ ] 3 Call mom @ 5pm !!! ^a1");
        assert_eq!(it.title, "Call mom @ 5pm !!!");
        assert_eq!(it.line_text(), "- [ ] 3 Call mom @ 5pm !!! ^a1");
    }

    #[test]
    fn trailing_flag_word_in_title_is_reported() {
        // Flags are read only after the title ends (§4.1 title rule); a title
        // ending in a flag word keeps the word and gets a problem.
        let it = week("- [ ] 4 Lean practice open ^l1");
        assert_eq!(it.title, "Lean practice open");
        assert_eq!(it.scope, Scope::Finite);
        assert!(it.flags.is_empty());
        assert!(it.problems.iter().any(|p| p.contains("title ends with `open`")), "{:?}", it.problems);
        let it = week("- [ ] 3 X open atomic manual travel-day hot ^a");
        assert!(it.problems.iter().any(|p| p.contains("title ends with `hot`")));
        // After any token the flag is a flag.
        let it = week("- [ ] 4 Lean practice ^l1 open");
        assert_eq!(it.scope, Scope::Open);
        assert!(it.problems.is_empty());
        let it = week("- [ ] 4 Lean practice min:6b/w open ^l1");
        assert!(it.problems.is_empty());
        let it = week("- [ ] 3 Read the manual, then ^t1");
        assert!(it.problems.is_empty(), "only an exact flag word counts");
    }

    #[test]
    fn bad_values_are_problems_not_panics() {
        // Regression: `demoted:Ж37` panicked in Stamp::parse.
        let it = week("- [ ] 4 X demoted:Ж37 ^q1");
        assert_eq!(it.extra, vec![("demoted".to_string(), "Ж37".to_string())]);
        assert!(it.problems.iter().any(|p| p.contains("demoted:Ж37")));
        assert!(it.stamps.demoted.is_empty());
        // Regression: an `at:` end before the start produced a negative interval.
        let it = week("- [ ] 3 X at:2026-09-12T10:00/2026-09-11T09:00 ^z");
        assert_eq!(it.shape, Shape::None);
        assert!(it.problems.iter().any(|p| p.contains("end before start")), "{:?}", it.problems);
        let it = week("- [ ] 3 X win:2026-09-12T10:00/2026-09-11T09:00 dur:1h ^z");
        assert_eq!(it.shape, Shape::None);
        assert!(it.problems.iter().any(|p| p.contains("win:2026-09-12T10:00/2026-09-11T09:00")));
        assert_eq!(it.dur, Some(Dur::hours(1)));
    }

    #[test]
    fn own_remaining_falls_back_to_dur() {
        let it = parse_line("- Severance S3E4  dur:1h", &ctx("optional.md")).unwrap();
        assert_eq!(it.own_remaining(), Some(Dur::hours(1)));
        let it = routine("- lunch win:11:30-13:30 dur:30m every:day");
        assert_eq!(it.own_remaining(), Some(Dur::from_minutes(30)));
        let it = week("- [ ] 3 2b X est:1b dur:30m ^t1");
        assert_eq!(it.own_remaining(), Some(Dur::blocks(1, 60)));
        let it = week("- [ ] 3 2b X dur:30m ^t1");
        assert_eq!(it.own_remaining(), Some(Dur::blocks(2, 60)));
        let it = week("- [ ] 3 X ^t1");
        assert_eq!(it.own_remaining(), None);
    }

    #[test]
    fn format_canonical_line() {
        let fmt = |it: &Item| format_item_line(it).unwrap();
        let it = week("- [ ] 4 6b CS 234 pset 2  @O3 #cs due:2026-09-11T23:59 max:2b/d ^d1");
        assert_eq!(
            fmt(&it),
            "- [ ] 4 6b CS 234 pset 2 @O3 #cs due:2026-09-11T23:59 max:2b/d ^d1"
        );
        let it = routine("- sleep      win:22:00-08:00 dur:8h30m every:day ci:0");
        assert_eq!(fmt(&it), "- sleep win:22:00-08:00 dur:8h30m every:day ci:0");
        let it = routine("- laundry    win:09:00-21:00 dur:30m  every:week on-miss:persist");
        assert_eq!(fmt(&it), "- laundry win:09:00-21:00 dur:30m every:week on-miss:persist");
        let it = parse_line("- Factorio        dur:2h max:4h/w", &ctx("optional.md")).unwrap();
        assert_eq!(fmt(&it), "- Factorio dur:2h max:4h/w");
        let it = week("- [>] 4 2b Exercises 5.3–5.5 !2 @m1 est:1b atomic hot after:^t4,event:visa loc:zoom foo:bar ^t3");
        assert_eq!(
            fmt(&it),
            "- [>] 4 2b Exercises 5.3–5.5 @m1 !2 after:^t4,event:visa loc:zoom est:1b foo:bar atomic hot ^t3"
        );
        let it = week("- [ ] 2 Sit at:2026-09-12T23:30/05:45 buffer:1h");
        assert_eq!(fmt(&it), "- [ ] 2 Sit at:2026-09-12T23:30/2026-09-13T05:45 buffer:1h");
        // A canonical line re-parses to the same fields.
        let again = week(&fmt(&it));
        assert_eq!(again.shape, it.shape);
        assert_eq!(again.buffer, it.buffer);
    }

    /// Every field the grammar can express survives `format_item_line` and a
    /// re-parse (source location aside).
    fn assert_canonical_round_trip(line: &str, file: &str) -> String {
        let c = ctx(file);
        let it = parse_line(line, &c).unwrap();
        let out = format_item_line(&it).unwrap();
        let again = parse_line(&out, &c).unwrap();
        let strip = |mut i: Item| {
            i.src = SourceLoc::default();
            i
        };
        assert_eq!(strip(again), strip(it), "{line} -> {out}");
        out
    }

    #[test]
    fn format_keeps_ci_inheritance_and_dur() {
        // Regression: a stateful line without a ci was written with the file
        // default, freezing it and defeating parent inheritance.
        let out = assert_canonical_round_trip("- [ ] Read ch.7 @m1 ^t9", "week/2026-W37.md");
        assert_eq!(out, "- [ ] Read ch.7 @m1 ^t9");
        let out = assert_canonical_round_trip("- [ ] 2b Read ch.7 @m1 ^t9", "week/2026-W37.md");
        assert_eq!(out, "- [ ] 2b Read ch.7 @m1 ^t9");
        let out = assert_canonical_round_trip("- [ ] Read ch.7 ci:4 ^t9", "week/2026-W37.md");
        assert_eq!(out, "- [ ] 4 Read ch.7 ^t9");
        // Regression: `dur:` was dropped for Point and Interval shapes.
        let out = assert_canonical_round_trip("- [ ] 3 X due:2026-09-11 dur:30m ^t1", "week/2026-W37.md");
        assert_eq!(out, "- [ ] 3 X due:2026-09-11 dur:30m ^t1");
        let out = assert_canonical_round_trip("- [ ] 3 X at:2026-09-11T10:00/11:00 dur:30m ^t1", "week/2026-W37.md");
        assert_eq!(out, "- [ ] 3 X at:2026-09-11T10:00/11:00 dur:30m ^t1");
        let out = assert_canonical_round_trip("- [ ] 1 Pick up package  win:2026-09-07T09:00/21:00 dur:20m ^a3", "backlog.md");
        assert_eq!(out, "- [ ] 1 Pick up package win:2026-09-07T09:00/21:00 dur:20m ^a3");
        // A title starting with a ci digit pins the ci so the digit stays text.
        let out = assert_canonical_round_trip("- [ ] 3 5 things ^t1", "week/2026-W37.md");
        assert_eq!(out, "- [ ] 3 5 things ^t1");
        let mut it = week("- [ ] 3 5 things ^t1");
        it.ci_explicit = false;
        assert_eq!(format_item_line(&it).unwrap(), "- [ ] 3 5 things ^t1");
        // A title starting with a duration and no leading estimate cannot be
        // written; nor can a title word that is a token.
        let mut it = week("- [ ] 3 30m run ^p1");
        assert_eq!(it.title, "run");
        it.title = "30m run".to_string();
        it.est_original = None;
        assert_eq!(format_item_line(&it), Err(EditError::Ambiguous { word: "30m".to_string() }));
        it.est_original = Some(Dur::from_minutes(30));
        assert_eq!(format_item_line(&it).unwrap(), "- [ ] 3 30m 30m run ^p1");
        it.title = "run @m1".to_string();
        assert_eq!(format_item_line(&it), Err(EditError::Ambiguous { word: "@m1".to_string() }));
        it.title = "run\nfast".to_string();
        assert_eq!(format_item_line(&it), Err(EditError::LineBreak));
        // Stateless files have no slots, so a digit-leading title is fine.
        let out = assert_canonical_round_trip("- 5 min stretch win:09:00-17:00 dur:5m", "routines.md");
        assert_eq!(out, "- 5 min stretch win:09:00-17:00 dur:5m");
        for line in [
            "- [ ] 5 6b Finish ch.5 exercises        @O1 ^m1",
            "- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1",
            "- [ ] 5 2h Midterm                      @O3 at:2026-10-20T10:00/12:00 loc:JCL ^x1",
            "- [?] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4",
            "- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2",
            "- [ ] 1 ✈ ORD→SFO UA 1234    at:2026-09-12T08:15/10:40 buffer:2h travel-day ^g3",
            "- [ ] 4 Lean practice min:6b/w open pref:wake+10m ^l1",
            "- [ ] 3 Meet Kun @ 7pm ^t1",
        ] {
            assert_canonical_round_trip(line, "week/2026-W37.md");
        }
        assert_canonical_round_trip("- shower     win:07:00-23:00 dur:20m  after-done:2d~1d", "routines.md");
    }

    #[test]
    fn flags_keep_a_boundary_before_them() {
        // A flag right after the title is title text on re-parse, so edits
        // that would leave one there move it after the `^id`.
        let mut l = ItemLine::parse("- [ ] 3 Foo ^t1").unwrap();
        l.add_flag("open").unwrap();
        assert_eq!(l.to_string(), "- [ ] 3 Foo ^t1 open");
        let it = week(&l.to_string());
        assert_eq!((it.title.as_str(), it.scope), ("Foo", Scope::Open));
        l.add_flag("hot").unwrap();
        assert_eq!(l.to_string(), "- [ ] 3 Foo ^t1 open hot");
        let mut l = ItemLine::parse("- [ ] 3 Foo @m1 ^t1").unwrap();
        l.add_flag("open").unwrap();
        assert_eq!(l.to_string(), "- [ ] 3 Foo @m1 open ^t1");
        let mut l = ItemLine::parse("- [ ] 3 Foo").unwrap();
        assert_eq!(l.add_flag("open"), Err(EditError::FlagNeedsBoundary { flag: "open".to_string() }));
        assert_eq!(l.to_string(), "- [ ] 3 Foo");

        // Removing the only boundary token.
        let mut l = ItemLine::parse("- [ ] 3 Foo @m1 open hot ^t1").unwrap();
        l.set_parent(None).unwrap();
        assert_eq!(l.to_string(), "- [ ] 3 Foo ^t1 open hot");
        assert_eq!(week(&l.to_string()).flags, vec!["open", "hot"]);
        let mut l = ItemLine::parse("- [ ] 3 Foo due:2026-09-11 open ^t1").unwrap();
        assert_eq!(l.remove_token("due"), Ok(true));
        assert_eq!(l.to_string(), "- [ ] 3 Foo ^t1 open");
        let mut l = ItemLine::parse("- [ ] 3 Foo #x open ^t1").unwrap();
        assert_eq!(l.remove_tag("x"), Ok(true));
        assert_eq!(l.to_string(), "- [ ] 3 Foo ^t1 open");
        let mut l = ItemLine::parse("- [ ] 3 Foo !2 open ^t1").unwrap();
        l.set_priority(None).unwrap();
        assert_eq!(l.to_string(), "- [ ] 3 Foo ^t1 open");
        let mut l = ItemLine::parse("- [ ] 3 Foo !2 open").unwrap();
        assert_eq!(l.set_priority(None), Err(EditError::FlagNeedsBoundary { flag: "open".to_string() }));
        assert_eq!(l.to_string(), "- [ ] 3 Foo !2 open", "a refused edit changes nothing");
        // Duplicated tokens (a reported problem) are all removed by `None`.
        let mut l = ItemLine::parse("- [ ] 3 Foo @a @b !1 !2 ^t1").unwrap();
        l.set_parent(None).unwrap();
        l.set_priority(None).unwrap();
        assert_eq!(l.to_string(), "- [ ] 3 Foo ^t1");
        // A bare word is not a boundary either: `Foo bar open` is all title.
        let mut l = ItemLine::parse("- [ ] 3 Foo @m1 bar open ^t1").unwrap();
        l.set_parent(None).unwrap();
        assert_eq!(l.to_string(), "- [ ] 3 Foo bar ^t1 open");
        assert_eq!(week(&l.to_string()).title, "Foo bar");
        // set_title drops the bare words that kept the flag out of the title.
        let mut l = ItemLine::parse("- [ ] A @ open ^t1").unwrap();
        assert_eq!(week(&l.to_string()).flags, vec!["open"]);
        l.set_title("a").unwrap();
        assert_eq!(l.to_string(), "- [ ] a ^t1 open");
        let mut l = ItemLine::parse("- [ ] A @ open").unwrap();
        assert_eq!(l.set_title("a"), Err(EditError::FlagNeedsBoundary { flag: "open".to_string() }));
        assert_eq!(l.to_string(), "- [ ] A @ open");
        // The canonical builder does the same.
        let it = week("- [ ] 4 Lean practice ^l1 open");
        assert_eq!(format_item_line(&it).unwrap(), "- [ ] 4 Lean practice ^l1 open");
        let mut it = week("- [ ] 4 Lean practice open ^l1");
        it.flags = vec!["open".to_string()];
        it.title = "Lean practice".to_string();
        assert_eq!(format_item_line(&it).unwrap(), "- [ ] 4 Lean practice ^l1 open");
        it.id = Id::default();
        assert_eq!(format_item_line(&it), Err(EditError::FlagNeedsBoundary { flag: "open".to_string() }));
        it.tags = vec!["lean".to_string()];
        assert_eq!(format_item_line(&it).unwrap(), "- [ ] 4 Lean practice #lean open");
    }

    #[test]
    fn id_generator() {
        let mut g = IdGen::new(42);
        let mut taken = HashSet::new();
        let a = g.next_id(&mut taken);
        let b = g.next_id(&mut taken);
        assert_ne!(a, b);
        assert_eq!(a.as_str().len(), 4);
        for c in a.as_str().chars().chain(b.as_str().chars()) {
            assert!(ID_ALPHABET.contains(&(c as u8)), "{c}");
            assert!(!"lo01".contains(c));
        }
        // Deterministic for the same seed.
        let mut g2 = IdGen::new(42);
        let mut taken2 = HashSet::new();
        assert_eq!(g2.next_id(&mut taken2), a);
        // Uniqueness: a taken candidate is skipped.
        let mut g3 = IdGen::new(42);
        let mut taken3: HashSet<String> = [a.as_str().to_string()].into_iter().collect();
        assert_eq!(g3.next_id(&mut taken3), b);
        assert!(IdGen::from_entropy().candidate().len() == 4);
    }

    #[test]
    fn file_structure() {
        let text = "---\nweek: 2026-W37\nwindow: 2026-09-07..2026-09-13\n---\n# Milestones\n- [ ] 5 6b Finish ch.5 exercises        @O1 ^m1\n\n<!-- tm:plan start 10:42 -->\n- [ ] not an item here\n<!-- tm:plan end -->\n## series:cell-bio\n- [x] 4 4b Cell Biology vol. 1 ^c1\n- [ ] 4 4b Cell Biology vol. 2 ^c2\n# Other\n- [ ] 3 X ^c3\nprose\n- \n";
        let cfg = Config::default();
        let f = parse_file("plan/week/2026-W37.md", text, &cfg);
        assert_eq!(f.horizon, Horizon::Week(IsoWeek::new(2026, 37)));
        assert_eq!(
            f.front_matter,
            vec![
                ("week".to_string(), "2026-W37".to_string()),
                ("window".to_string(), "2026-09-07..2026-09-13".to_string())
            ]
        );
        assert_eq!(f.front("week"), Some("2026-W37"));
        let items: Vec<&Item> = f.items().collect();
        assert_eq!(items.len(), 4);
        assert_eq!(items[0].src.section.as_deref(), Some("Milestones"));
        assert_eq!(items[0].src.line, 6);
        assert_eq!(items[1].series, Some(("cell-bio".to_string(), 0)));
        assert_eq!(items[2].series, Some(("cell-bio".to_string(), 1)));
        assert_eq!(items[2].src.section.as_deref(), Some("series:cell-bio"));
        assert_eq!(items[3].series, None);
        assert_eq!(items[3].src.section.as_deref(), Some("Other"));
        let g = f.generated("plan").unwrap();
        assert_eq!((g.start_line, g.end_line, g.info.as_str()), (8, Some(10), "10:42"));
        assert!(f.in_generated(9));
        assert!(!f.in_generated(11));
        assert_eq!(f.line_of(&Id::new("c2")), Some(13));
        assert!(f.problems.is_empty(), "{:?}", f.problems);
        assert_eq!(serialize_file(&f), text);
        assert_eq!(f.to_text(), text);
    }

    #[test]
    fn file_problems_and_crlf() {
        let cfg = Config::default();
        let text = "---\r\nx: 1\r\n- [ ] 3 X ^a\r\n<!-- tm:plan start -->\r\nfoo";
        let f = parse_file("notes.md", text, &cfg);
        assert_eq!(f.horizon, Horizon::Backlog);
        assert!(f.problems.iter().any(|p| p.message.contains("unknown file kind")));
        assert!(f.problems.iter().any(|p| p.message.contains("unterminated front matter")));
        assert!(f.problems.iter().any(|p| p.message.contains("unterminated generated")));
        assert_eq!(f.items().count(), 1);
        assert_eq!(serialize_file(&f), text);
        let f = parse_file("backlog.md", "<!-- tm:plan end -->\n", &cfg);
        assert!(f.problems.iter().any(|p| p.message.contains("end marker without start")));
        let f = parse_file("backlog.md", "", &cfg);
        assert!(f.lines.is_empty());
        assert_eq!(serialize_file(&f), "");
    }
}
