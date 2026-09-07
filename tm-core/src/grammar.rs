//! Grammar — tm-spec-v1.md §4 and §17.2 "Parsing". Hand-written tokenizer,
//! parser and byte-faithful serializer.
//!
//! # API overview
//!
//! * [`parse_file`]`(path, text, &Config) -> `[`ParsedFile`] — every line is
//!   either an [`Item`] or kept verbatim (prose, headings, blank lines, front
//!   matter, generated `<!-- tm:x start -->…<!-- tm:x end -->` ranges,
//!   comments). [`serialize_file`] writes it back byte-identically.
//! * [`parse_line`]`(text, &`[`ParseCtx`]`) -> Result<Item, ParseError>` — one
//!   item line; [`ParseCtx::new`]`(file, block_min)` derives the horizon from
//!   the path.
//! * [`ItemLine`] — the token list kept on `item.src.tokens`. `to_string()` is
//!   the original line. Edit operations change only the token they must:
//!   `set_token` / `remove_token` / `get`, `set_state`, `set_ci`,
//!   `set_leading_est`, `set_title`, `set_priority`, `set_parent`, `add_tag`,
//!   `remove_tag`, `add_flag`, `remove_flag`, `append_id`. After an edit,
//!   re-parse with [`parse_line`] to get a fresh `Item`.
//! * [`format_item_line`]`(&Item) -> String` — builds a fresh canonical line
//!   (for `tm add` / capture previews).
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
//!   structured token (`!9`, `^`, `@`) is kept verbatim and reported as a
//!   problem, not added to the title.
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

/// Errors from an edit operation on an [`ItemLine`].
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum EditError {
    /// A positional slot (ci / leading estimate) needs a state on the line.
    #[error("the line has no state, so there is no positional slot")]
    NoState,
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
    /// A malformed structured token, kept verbatim and reported.
    Unparsed,
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

/// `key` of a `key:value` word when the key matches `[a-z-]+`.
fn key_prefix(w: &str) -> Option<&str> {
    let (k, _) = w.split_once(':')?;
    if !k.is_empty() && k.bytes().all(|b| b.is_ascii_lowercase() || b == b'-') {
        Some(k)
    } else {
        None
    }
}

fn starts_token(w: &str) -> bool {
    matches!(w.as_bytes()[0], b'@' | b'#' | b'!' | b'^') || key_prefix(w).is_some()
}

fn classify(w: &str) -> TokenKind {
    let rest = &w[1..];
    match w.as_bytes()[0] {
        b'@' if !rest.is_empty() => TokenKind::Parent,
        b'#' if !rest.is_empty() => TokenKind::Tag,
        b'!' if rest.len() == 1 && matches!(rest.as_bytes()[0], b'1'..=b'4') => {
            TokenKind::Priority
        }
        b'^' if Id::is_valid(rest) => TokenKind::Id,
        b'@' | b'#' | b'!' | b'^' => TokenKind::Unparsed,
        _ => match key_prefix(w) {
            Some(k) => TokenKind::Key(k.to_string()),
            None if FLAGS.contains(&w) => TokenKind::Flag,
            None => TokenKind::Word,
        },
    }
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
            if i < words.len() && Dur::parse_no_days(word_text(&words[i]), 1).is_ok() {
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

    /// Remove `key:…`; returns whether it was present.
    pub fn remove_token(&mut self, key: &str) -> bool {
        match self.key_index(key) {
            Some(i) => {
                self.remove_at(i);
                true
            }
            None => false,
        }
    }

    // -- positional edits -------------------------------------------------

    /// Replace the state, or insert one after the bullet.
    pub fn set_state(&mut self, state: State) {
        match self.index_of(&TokenKind::State) {
            Some(i) => self.tokens[i].text = state.as_str().to_string(),
            None => self.insert_at(1, TokenKind::State, state.as_str()),
        }
    }

    /// Set the ci: replace the positional digit or the `ci:` key, else insert
    /// a positional ci after the state, else (no state) add `ci:N`.
    pub fn set_ci(&mut self, ci: u8) {
        if let Some(i) = self.index_of(&TokenKind::Ci) {
            self.tokens[i].text = ci.to_string();
        } else if self.key_index("ci").is_some() {
            self.set_token("ci", &ci.to_string());
        } else if let Some(s) = self.index_of(&TokenKind::State) {
            self.insert_at(s + 1, TokenKind::Ci, &ci.to_string());
        } else {
            self.set_token("ci", &ci.to_string());
        }
    }

    /// Remove the positional ci and any `ci:` key.
    pub fn remove_ci(&mut self) {
        if let Some(i) = self.index_of(&TokenKind::Ci) {
            self.remove_at(i);
        }
        self.remove_token("ci");
    }

    /// Set (or with `None` remove) the leading estimate. Inserting needs a
    /// state on the line (the slot is positional).
    pub fn set_leading_est(&mut self, est: Option<Dur>) -> Result<(), EditError> {
        match (self.index_of(&TokenKind::Est), est) {
            (Some(i), Some(d)) => self.tokens[i].text = d.to_string(),
            (Some(i), None) => self.remove_at(i),
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

    /// Replace the title (and drop any bare words that were appended to it).
    pub fn set_title(&mut self, title: &str) {
        self.tokens.retain(|t| t.kind != TokenKind::Word);
        match self.index_of(&TokenKind::Title) {
            Some(i) if title.is_empty() => self.remove_at(i),
            Some(i) => self.tokens[i].text = title.to_string(),
            None if title.is_empty() => {}
            None => {
                let after = self
                    .tokens
                    .iter()
                    .rposition(|t| {
                        matches!(
                            t.kind,
                            TokenKind::Bullet | TokenKind::State | TokenKind::Ci | TokenKind::Est
                        )
                    })
                    .unwrap_or(0);
                self.insert_at(after + 1, TokenKind::Title, title);
            }
        }
    }

    // -- trailing-token edits ---------------------------------------------

    /// Set (or with `None` remove) `!k`.
    pub fn set_priority(&mut self, k: Option<u8>) {
        match (self.index_of(&TokenKind::Priority), k) {
            (Some(i), Some(k)) => self.tokens[i].text = format!("!{k}"),
            (Some(i), None) => self.remove_at(i),
            (None, Some(k)) => self.insert_before_id_or_end(TokenKind::Priority, &format!("!{k}")),
            (None, None) => {}
        }
    }

    /// Set (or with `None` remove) `@parent`.
    pub fn set_parent(&mut self, parent: Option<&Ref>) {
        match (self.index_of(&TokenKind::Parent), parent) {
            (Some(i), Some(p)) => self.tokens[i].text = p.token(),
            (Some(i), None) => self.remove_at(i),
            (None, Some(p)) => self.insert_before_id_or_end(TokenKind::Parent, &p.token()),
            (None, None) => {}
        }
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

    /// Remove `#tag`; returns whether it was present.
    pub fn remove_tag(&mut self, tag: &str) -> bool {
        let before = self.tokens.len();
        self.tokens
            .retain(|t| !(t.kind == TokenKind::Tag && t.text[1..] == *tag));
        self.tokens.len() != before
    }

    /// Add a flag (no-op if present).
    pub fn add_flag(&mut self, flag: &str) {
        if !self.has_flag(flag) {
            self.insert_before_id_or_end(TokenKind::Flag, flag);
        }
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
            TokenKind::Est => est_original = Dur::parse_no_days(&t.text, bm).ok(),
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
            TokenKind::Unparsed => col.problems.push(format!("cannot parse token `{}`", t.text)),
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
pub fn format_item_line(item: &Item) -> String {
    let mut parts: Vec<String> = Vec::new();
    let stateless = item.horizon.is_open_file();
    if !stateless {
        parts.push(item.state.as_str().to_string());
        parts.push(item.ci.to_string());
        if let Some(e) = item.est_original {
            parts.push(e.to_string());
        }
    }
    if !item.title.is_empty() {
        parts.push(item.title.clone());
    }
    if let Some(p) = &item.parent {
        parts.push(p.token());
    }
    for t in &item.tags {
        parts.push(format!("#{t}"));
    }
    if let Some(k) = item.priority {
        parts.push(format!("!{k}"));
    }
    match &item.shape {
        Shape::None => {
            if let Some(d) = item.dur {
                parts.push(format!("dur:{d}"));
            }
        }
        Shape::Point { due } => parts.push(format!("due:{due}")),
        Shape::Interval { start, end } => {
            parts.push(format!("at:{}", crate::model::fmt_interval(*start, *end)))
        }
        Shape::Window { range, dur } => {
            parts.push(format!("win:{range}"));
            parts.push(format!("dur:{dur}"));
        }
    }
    if let Some(p) = item.pref {
        parts.push(format!("pref:{p}"));
    }
    if let Some(r) = item.recur.token() {
        parts.push(r);
    }
    if item.on_miss != item.shape.default_on_miss() {
        parts.push(format!("on-miss:{}", item.on_miss));
    }
    if let Some(r) = item.budget.floor {
        parts.push(format!("min:{r}"));
    }
    if let Some(r) = item.budget.cap {
        parts.push(format!("max:{r}"));
    }
    if !item.after.is_empty() {
        let deps: Vec<String> = item.after.iter().map(|d| d.to_string()).collect();
        parts.push(format!("after:{}", deps.join(",")));
    }
    if item.loc != Loc::Any {
        parts.push(format!("loc:{}", item.loc));
    }
    if let Some(e) = item.est {
        parts.push(format!("est:{e}"));
    }
    if !item.stamps.demoted.is_empty() {
        parts.push(format!("demoted:{}", item.stamps.demoted_value()));
    }
    if let Some(w) = item.stamps.waiting_since {
        parts.push(format!("waiting:{}", w.format("%Y-%m-%d")));
    }
    if let Some(b) = item.buffer {
        parts.push(format!("buffer:{b}"));
    }
    for (k, v) in &item.extra {
        parts.push(format!("{k}:{v}"));
    }
    if item.scope == Scope::Open && !stateless && !item.has_flag("open") {
        parts.push("open".to_string());
    }
    if !item.splittable && !item.has_flag("atomic") {
        parts.push("atomic".to_string());
    }
    for f in &item.flags {
        parts.push(f.clone());
    }
    if stateless && item.ci_explicit {
        parts.push(format!("ci:{}", item.ci));
    }
    if item.has_id() {
        parts.push(item.id.token());
    }
    format!("- {}", parts.join(" "))
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

    while i < raw.len() {
        let (l, eol) = raw[i];
        let number = i + 1;
        i += 1;
        let verbatim = |s: &str| LineContent::Verbatim(s.to_string());

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
        assert!(it.problems.iter().any(|p| p.contains("due:2026-13-01")));
        assert!(it.problems.iter().any(|p| p.contains("`!9`")));
        assert!(it.problems.iter().any(|p| p.contains("`^`")));
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
        assert!(l.remove_token("est"));
        assert!(!l.remove_token("est"));
        assert_eq!(l.to_string(), s);

        let s = "- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1";
        let mut l = ItemLine::parse(s).unwrap();
        l.set_token("due", "2026-09-12T23:59");
        assert_eq!(
            l.to_string(),
            "- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-12T23:59 max:2b/d ^d1"
        );
        l.set_state(State::Active);
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
        l.set_title("pset 2");
        l.set_priority(Some(2));
        l.add_flag("hot");
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
        assert!(l.remove_tag("cs234"));
        assert!(l.remove_flag("hot"));
        assert!(!l.remove_flag("hot"));
        l.set_priority(None);
        l.set_parent(Some(&Ref::new("O2")));
        assert_eq!(
            l.to_string(),
            "- [>] 5 2h pset 2                @O2 due:2026-09-12T23:59 max:2b/d #school ^d1"
        );
        // Removing a token removes the whitespace that preceded it.
        l.set_parent(None);
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
        l.set_state(State::Todo);
        assert_eq!(
            l.to_string(),
            "- [ ] lunch      win:11:30-13:30 dur:30m  every:day ci:1"
        );
        l.remove_ci();
        l.set_ci(3);
        assert_eq!(
            l.to_string(),
            "- [ ] 3 lunch      win:11:30-13:30 dur:30m  every:day"
        );

        // set_title on a line whose title was made of bare words after `!1`.
        let mut l = ItemLine::parse("- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1").unwrap();
        l.set_title("Lean: ch.9");
        assert_eq!(l.to_string(), "- [ ] 5 Lean: ch.9 !1          ^O1");
    }

    #[test]
    fn format_canonical_line() {
        let it = week("- [ ] 4 6b CS 234 pset 2  @O3 #cs due:2026-09-11T23:59 max:2b/d ^d1");
        assert_eq!(
            format_item_line(&it),
            "- [ ] 4 6b CS 234 pset 2 @O3 #cs due:2026-09-11T23:59 max:2b/d ^d1"
        );
        let it = routine("- sleep      win:22:00-08:00 dur:8h30m every:day ci:0");
        assert_eq!(
            format_item_line(&it),
            "- sleep win:22:00-08:00 dur:8h30m every:day ci:0"
        );
        let it = routine("- laundry    win:09:00-21:00 dur:30m  every:week on-miss:persist");
        assert_eq!(
            format_item_line(&it),
            "- laundry win:09:00-21:00 dur:30m every:week on-miss:persist"
        );
        let it = parse_line("- Factorio        dur:2h max:4h/w", &ctx("optional.md")).unwrap();
        assert_eq!(format_item_line(&it), "- Factorio dur:2h max:4h/w");
        let it = week("- [>] 4 2b Exercises 5.3–5.5 !2 @m1 est:1b atomic hot after:^t4,event:visa loc:zoom foo:bar ^t3");
        assert_eq!(
            format_item_line(&it),
            "- [>] 4 2b Exercises 5.3–5.5 @m1 !2 after:^t4,event:visa loc:zoom est:1b foo:bar atomic hot ^t3"
        );
        let it = week("- [ ] 2 Sit at:2026-09-12T23:30/05:45 buffer:1h");
        assert_eq!(
            format_item_line(&it),
            "- [ ] 2 Sit at:2026-09-12T23:30/2026-09-13T05:45 buffer:1h"
        );
        // A canonical line re-parses to the same fields.
        let again = week(&format_item_line(&it));
        assert_eq!(again.shape, it.shape);
        assert_eq!(again.buffer, it.buffer);
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
