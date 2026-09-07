//! Check — tree validation (§1.2 `check.rs`, §1.3 "`tm check` validates the
//! tree", §4.1 parsing rules, §5.4 series, §5.5 cycles, §6.2 outcomes with an
//! estimate, §13 `tm check [--fix-ids]`, §17 M1, §17.2 ids).
//!
//! # API overview
//!
//! * [`check`]`(&[ParsedFile], &`[`Tree`]`, &Config) -> Vec<`[`CheckProblem`]`>`
//!   — every problem in the tree, sorted by `(file, line)`. Pure: no I/O, no
//!   clock, no randomness. The `Tree` must be the one built from the same
//!   `files` ([`Tree::build`]), because the structural checks read it and the
//!   per-line checks read the files.
//! * [`CheckProblem`] `{ severity, code, file, line, id, message }` —
//!   `Display` is `file:line: error[code]: message` (`warning[…]` for a
//!   warning), and it derives `Serialize` for `tm check --json`. [`CODES`]
//!   lists every code the module emits and [`Severity`] the two levels.
//! * [`has_errors`], [`exit_code`] (0 or 2, §13) and [`summary`] turn the
//!   list into what the CLI prints and returns.
//! * [`fix_ids`]`(&dyn Store, &mut [ParsedFile], &mut IdGen)` — the
//!   `--fix-ids` pass: append a fresh `^id` to every line that needs one
//!   (§17.2 "assign on first parse by appending ` ^id` to the line"), write
//!   the changed files back through the [`Store`], and return
//!   `(file, line, id)` for each. [`assign_ids_in_text`] is the same
//!   operation on a single buffer, pure, for the TUI's first load.
//!   [`needs_id`] is the predicate both use.
//!
//! # What is checked
//!
//! Structural (from the [`Tree`]):
//!
//! | code | severity | meaning |
//! |---|---|---|
//! | `dup-id` | error | one `^id` on several lines (beyond the §6.3 archive copy), reported once per line |
//! | `dangling-parent` | error | `@parent` names nothing |
//! | `parent-cycle` | error | `@parent` links form a cycle |
//! | `dep-cycle` | error | `after:` links form a cycle (§5.5) |
//! | `dangling-dep` | error | `after:^x` names nothing |
//! | `outcome-with-est` | warning | month item with an estimate and no children (§6.2) |
//! | `series-order` | warning | a non-head member of a `## series:` section is `[>]` (§5.4) |
//! | `wall-conflict` | warning | two open Intervals overlap (§8.2 step 1) |
//!
//! Per line (from the parsed files):
//!
//! | code | severity | meaning |
//! |---|---|---|
//! | `bad-value` | error | a `key:` whose value does not parse, a missing state, an unreadable file |
//! | `bad-value` | warning | a duplicate or conflicting token the parser resolved by rule |
//! | `bad-ci` | error | `ci:` outside `0..=5`, or a `!k` outside `1..=4` |
//! | `unknown-key` | warning | a `key:value` the grammar does not know (kept in `extra`, §4.1) |
//! | `unclassified-token` | warning | a malformed token kept in the title (§4.1) |
//! | `missing-id` | warning | a line with no `^id` outside routines/optional/inbox (fixable) |
//! | `priority-on-child` | warning | `!k` on a non-root, which §7.1 ignores |
//! | `routine-shape` | error | a `routines.md` line with neither a window nor `after-done:` |
//! | `optional-shape` | warning | an `optional.md` line without `dur:` |
//! | `calendar-shape` | error | a `calendar/` line that is not an Interval |
//! | `day-section` | warning | an item in a `day/` file outside `# Pinned` (§6.2) |
//! | `waiting-state` | warning | `waiting:` without `[?]`, or `[?]` without `waiting:` |
//!
//! Only errors set the exit code; warnings are advice.

use std::collections::HashSet;
use std::fmt;

use serde::Serialize;
use thiserror::Error;

use crate::config::Config;
use crate::grammar::{parse_file, IdGen, ParseCtx, ParsedFile, Problem, TokenKind, KEYS};
use crate::model::{Horizon, Id, Item, Recur, Shape, State};
use crate::store::{Store, StoreError};
use crate::tree::Tree;

// ---------------------------------------------------------------------------
// Codes
// ---------------------------------------------------------------------------

/// One `^id` on several lines.
pub const DUP_ID: &str = "dup-id";
/// `@parent` names nothing in the tree.
pub const DANGLING_PARENT: &str = "dangling-parent";
/// A cycle in the `@parent` graph.
pub const PARENT_CYCLE: &str = "parent-cycle";
/// A cycle in the `after:` graph (§5.5).
pub const DEP_CYCLE: &str = "dep-cycle";
/// `after:^x` names nothing in the tree.
pub const DANGLING_DEP: &str = "dangling-dep";
/// A value that does not parse, or another line-level parse problem.
pub const BAD_VALUE: &str = "bad-value";
/// A `key:value` the grammar does not know (§4.1).
pub const UNKNOWN_KEY: &str = "unknown-key";
/// A line with no `^id` where one is required (§17.2); `--fix-ids` fixes it.
pub const MISSING_ID: &str = "missing-id";
/// A month item with an estimate and no children (§6.2).
pub const OUTCOME_WITH_EST: &str = "outcome-with-est";
/// A `routines.md` line with neither a window nor `after-done:` (§4.3).
pub const ROUTINE_SHAPE: &str = "routine-shape";
/// An `optional.md` line without `dur:` (§4.3).
pub const OPTIONAL_SHAPE: &str = "optional-shape";
/// A `calendar/` line that is not an Interval (§4.3).
pub const CALENDAR_SHAPE: &str = "calendar-shape";
/// `ci:` outside `0..=5`, or `!k` outside `1..=4`.
pub const BAD_CI: &str = "bad-ci";
/// `!k` on an item that is not a root (§7.1 ignores it).
pub const PRIORITY_ON_CHILD: &str = "priority-on-child";
/// A non-head series member that is `[>]` (§5.4).
pub const SERIES_ORDER: &str = "series-order";
/// Two open Intervals overlap (§8.2 step 1).
pub const WALL_CONFLICT: &str = "wall-conflict";
/// A malformed token kept in the title (§4.1).
pub const UNCLASSIFIED_TOKEN: &str = "unclassified-token";
/// An item in a `day/` file outside `# Pinned` (§6.2).
pub const DAY_SECTION: &str = "day-section";
/// `waiting:` without state `[?]`, or `[?]` without `waiting:`.
pub const WAITING_STATE: &str = "waiting-state";

/// Every code [`check`] can produce.
pub const CODES: &[&str] = &[
    DUP_ID,
    DANGLING_PARENT,
    PARENT_CYCLE,
    DEP_CYCLE,
    DANGLING_DEP,
    BAD_VALUE,
    UNKNOWN_KEY,
    MISSING_ID,
    OUTCOME_WITH_EST,
    ROUTINE_SHAPE,
    OPTIONAL_SHAPE,
    CALENDAR_SHAPE,
    BAD_CI,
    PRIORITY_ON_CHILD,
    SERIES_ORDER,
    WALL_CONFLICT,
    UNCLASSIFIED_TOKEN,
    DAY_SECTION,
    WAITING_STATE,
];

// ---------------------------------------------------------------------------
// Problems
// ---------------------------------------------------------------------------

/// How bad a [`CheckProblem`] is: only an `Error` fails `tm check` (§13 exit
/// code 2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// The tree is wrong; `tm check` exits 2.
    Error,
    /// The tree is suspicious but usable.
    Warning,
}

impl Severity {
    /// `"error"` / `"warning"`.
    pub fn as_str(&self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
        }
    }
    /// True for [`Severity::Error`].
    pub fn is_error(&self) -> bool {
        matches!(self, Severity::Error)
    }
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One validation problem. `Display` is the line `tm check` prints:
/// `file:line: error[code]: message`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CheckProblem {
    /// Error or warning.
    pub severity: Severity,
    /// Stable machine-readable code; one of [`CODES`].
    pub code: &'static str,
    /// File the problem is in, as the parser saw it (`week/2026-W37.md`).
    pub file: String,
    /// 1-based line, or 0 for a whole-file problem.
    pub line: usize,
    /// The item's key (`^id`, or the title for an id-less routine line), when
    /// the problem is about one item.
    pub id: Option<Id>,
    /// Human-readable description.
    pub message: String,
}

impl CheckProblem {
    /// An error at `file:line`.
    pub fn error(code: &'static str, file: &str, line: usize, id: Option<Id>, message: impl Into<String>) -> CheckProblem {
        CheckProblem {
            severity: Severity::Error,
            code,
            file: file.to_string(),
            line,
            id,
            message: message.into(),
        }
    }

    /// A warning at `file:line`.
    pub fn warning(code: &'static str, file: &str, line: usize, id: Option<Id>, message: impl Into<String>) -> CheckProblem {
        CheckProblem {
            severity: Severity::Warning,
            code,
            file: file.to_string(),
            line,
            id,
            message: message.into(),
        }
    }

    /// True for [`Severity::Error`].
    pub fn is_error(&self) -> bool {
        self.severity.is_error()
    }

    /// The `(file, line, code, message)` order `check` sorts by.
    fn sort_key(&self) -> (&str, usize, &str, &str) {
        (&self.file, self.line, self.code, &self.message)
    }
}

impl fmt::Display for CheckProblem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.file.is_empty() {
            f.write_str(&self.file)?;
            if self.line > 0 {
                write!(f, ":{}", self.line)?;
            }
            f.write_str(": ")?;
        }
        write!(f, "{}[{}]: {}", self.severity, self.code, self.message)
    }
}

/// Errors from the writing half of the module ([`fix_ids`]).
#[derive(Debug, Error)]
pub enum CheckError {
    /// The store could not read or write a file.
    #[error(transparent)]
    Store(#[from] StoreError),
}

// ---------------------------------------------------------------------------
// Reporting helpers
// ---------------------------------------------------------------------------

/// True when the item's line must carry an `^id` (§17.2: ids are global; only
/// `routines.md`, `optional.md` and `inbox.md` lines may omit them).
pub fn needs_id(item: &Item) -> bool {
    needs_id_in(item, item.horizon)
}

fn needs_id_in(item: &Item, horizon: Horizon) -> bool {
    !item.has_id() && !horizon.allows_missing_state()
}

/// True when at least one problem is an error.
pub fn has_errors(problems: &[CheckProblem]) -> bool {
    problems.iter().any(CheckProblem::is_error)
}

/// The process exit code for a run of `tm check`: 2 when anything is an
/// error, 0 otherwise (§13).
pub fn exit_code(problems: &[CheckProblem]) -> i32 {
    if has_errors(problems) {
        2
    } else {
        0
    }
}

/// One line naming how many errors and warnings there are.
pub fn summary(problems: &[CheckProblem]) -> String {
    let errors = problems.iter().filter(|p| p.is_error()).count();
    let warnings = problems.len() - errors;
    if problems.is_empty() {
        return "no problems".to_string();
    }
    format!(
        "{errors} error{}, {warnings} warning{}",
        plural(errors),
        plural(warnings)
    )
}

fn plural(n: usize) -> &'static str {
    if n == 1 {
        ""
    } else {
        "s"
    }
}

/// The key an item is addressed by, for the `id` field of a problem.
fn key_of(item: &Item) -> Option<Id> {
    let key = Tree::key_of(item);
    if key.is_empty() {
        None
    } else {
        Some(key)
    }
}

/// `(file, line)` of the primary item with `id`.
fn loc_of(tree: &Tree, id: &Id) -> (String, usize) {
    match tree.get(id) {
        Some(it) => (it.src.file.clone(), it.src.line),
        None => (String::new(), 0),
    }
}

fn fmt_ids(ids: &[Id]) -> String {
    ids.iter()
        .map(|i| i.token())
        .collect::<Vec<_>>()
        .join(" -> ")
}

fn fmt_locations(locs: &[(String, usize)]) -> String {
    locs.iter()
        .map(|(f, l)| format!("{f}:{l}"))
        .collect::<Vec<_>>()
        .join(", ")
}

// ---------------------------------------------------------------------------
// check
// ---------------------------------------------------------------------------

/// Validate the tree (§1.3). `files` are the parsed plan files and `tree` the
/// index built from exactly those files; the result is sorted by
/// `(file, line)` and is stable for a given input.
pub fn check(files: &[ParsedFile], tree: &Tree, cfg: &Config) -> Vec<CheckProblem> {
    let mut out = Vec::new();
    for file in files {
        check_file(file, tree, &mut out);
    }
    check_structure(tree, cfg, &mut out);
    check_walls(tree, &mut out);
    out.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
    out
}

// -- per file ---------------------------------------------------------------

fn check_file(file: &ParsedFile, tree: &Tree, out: &mut Vec<CheckProblem>) {
    for p in &file.problems {
        let (severity, code) = classify_file_problem(p);
        out.push(CheckProblem {
            severity,
            code,
            file: file.path.clone(),
            line: p.line,
            id: None,
            message: p.message.clone(),
        });
    }
    for item in file.items() {
        check_item(file, item, tree, out);
    }
}

/// A whole-file problem from the parser. An unknown file kind is only a
/// warning: a stray note in `plan/` should not fail a commit hook.
fn classify_file_problem(p: &Problem) -> (Severity, &'static str) {
    if p.message.starts_with("unknown file kind") {
        (Severity::Warning, BAD_VALUE)
    } else {
        (Severity::Error, BAD_VALUE)
    }
}

fn check_item(file: &ParsedFile, item: &Item, tree: &Tree, out: &mut Vec<CheckProblem>) {
    let path = file.path.as_str();
    let line = item.src.line;
    let key = key_of(item);
    let at = |code: &'static str, msg: String, severity: Severity| CheckProblem {
        severity,
        code,
        file: path.to_string(),
        line,
        id: key.clone(),
        message: msg,
    };

    // Malformed tokens the parser kept in the title (§4.1). A `!k` outside
    // 1..=4 is the one case with a better name than "unclassified".
    for t in &item.src.tokens.tokens {
        if t.kind != TokenKind::Unparsed {
            continue;
        }
        if t.text.starts_with('!') {
            out.push(at(
                BAD_CI,
                format!("`{}`: priority must be `!1`..`!4` (§4.1)", t.text),
                Severity::Error,
            ));
        } else {
            out.push(at(
                UNCLASSIFIED_TOKEN,
                format!("`{}` is not a token; it stays in the title (§4.1)", t.text),
                Severity::Warning,
            ));
        }
    }

    // Everything else the parser noticed on the line.
    for msg in &item.problems {
        if msg.starts_with("unclassified token") {
            continue; // reported from the token above, with its own code
        }
        let (severity, code) = classify_item_problem(msg);
        out.push(at(code, msg.clone(), severity));
    }

    // Unknown `key:value` tokens (§4.1: preserved in `extra`, reported here).
    for (k, v) in &item.extra {
        if !KEYS.contains(&k.as_str()) {
            out.push(at(
                UNKNOWN_KEY,
                format!("unknown key `{k}:{v}`; it is preserved but ignored"),
                Severity::Warning,
            ));
        }
    }

    // Ids (§17.2).
    if needs_id_in(item, file.horizon) {
        out.push(CheckProblem {
            severity: Severity::Warning,
            code: MISSING_ID,
            file: path.to_string(),
            line,
            id: None,
            message: format!("no `^id` on `{}`; run `tm check --fix-ids`", item.title),
        });
    }

    // `!k` counts on roots only (§7.1).
    if item.priority.is_some() {
        if let Some(k) = &key {
            if let Some(parent) = tree.parent(k) {
                out.push(at(
                    PRIORITY_ON_CHILD,
                    format!("priority on a non-root is ignored; ^{parent} carries the priority of this branch"),
                    Severity::Warning,
                ));
            }
        }
    }

    // `waiting:` and `[?]` go together (§4.1, §5.1).
    match (item.state, item.stamps.waiting_since) {
        (State::Waiting, None) => out.push(at(
            WAITING_STATE,
            "state `[?]` without `waiting:<date>`".to_string(),
            Severity::Warning,
        )),
        (s, Some(d)) if s != State::Waiting => out.push(at(
            WAITING_STATE,
            format!("`waiting:{d}` without state `[?]`"),
            Severity::Warning,
        )),
        _ => {}
    }

    // File conventions (§4.3).
    match file.horizon {
        Horizon::Routine => {
            // §4.3: "every line is `open`, has a window or `after-done`".
            // The `open` half is structural — the grammar makes every line of
            // an open file `Scope::Open` — so only the shape can be wrong.
            let windowed = matches!(item.shape, Shape::Window { .. });
            let after_done = matches!(item.recur, Recur::AfterDone { .. });
            if !windowed && !after_done {
                out.push(at(
                    ROUTINE_SHAPE,
                    "a routine needs a window (`win:` + `dur:`) or `after-done:`".to_string(),
                    Severity::Error,
                ));
            }
        }
        Horizon::Optional => {
            if item.dur.is_none() {
                out.push(at(
                    OPTIONAL_SHAPE,
                    "an optional item needs `dur:` so it can be time-boxed".to_string(),
                    Severity::Warning,
                ));
            }
        }
        Horizon::Calendar(_) => {
            if !matches!(item.shape, Shape::Interval { .. }) {
                out.push(at(
                    CALENDAR_SHAPE,
                    "a calendar line must be an interval (`at:<start>/<end>`)".to_string(),
                    Severity::Error,
                ));
            }
        }
        Horizon::Day(_) => {
            if item.src.section.as_deref() != Some("Pinned") {
                let where_ = match &item.src.section {
                    Some(s) => format!("section `# {s}`"),
                    None => "no section".to_string(),
                };
                out.push(at(
                    DAY_SECTION,
                    format!("items in a day file belong under `# Pinned` ({where_})"),
                    Severity::Warning,
                ));
            }
        }
        _ => {}
    }
}

/// Map a parser problem to a severity and a code. A value that failed to
/// parse is an error (the field is simply not there); a token the parser
/// resolved by rule (a duplicate key, a conflicting shape) is a warning.
fn classify_item_problem(msg: &str) -> (Severity, &'static str) {
    if let Some(rest) = msg.strip_prefix('`') {
        if rest.starts_with("ci:") {
            return (Severity::Error, BAD_CI);
        }
        return (Severity::Error, BAD_VALUE);
    }
    if msg.starts_with("missing state") {
        return (Severity::Error, BAD_VALUE);
    }
    (Severity::Warning, BAD_VALUE)
}

// -- structural -------------------------------------------------------------

fn check_structure(tree: &Tree, cfg: &Config, out: &mut Vec<CheckProblem>) {
    // Duplicate ids: one problem per line, each naming the others (§17.2).
    for (id, locations) in tree.duplicate_ids() {
        for (i, (file, line)) in locations.iter().enumerate() {
            let others: Vec<(String, usize)> = locations
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, l)| l.clone())
                .collect();
            out.push(CheckProblem::error(
                DUP_ID,
                file,
                *line,
                Some(id.clone()),
                format!("duplicate id ^{id}; also at {}", fmt_locations(&others)),
            ));
        }
    }

    // Dangling parents (§6.1).
    for (id, parent) in tree.dangling_parents() {
        let (file, line) = loc_of(tree, id);
        out.push(CheckProblem::error(
            DANGLING_PARENT,
            &file,
            line,
            Some(id.clone()),
            format!("parent {} does not exist", parent.token()),
        ));
    }

    // Dangling dependencies (§5.5).
    for (id, dep) in tree.dangling_deps() {
        let (file, line) = loc_of(tree, &id);
        out.push(CheckProblem::error(
            DANGLING_DEP,
            &file,
            line,
            Some(id.clone()),
            format!("dependency after:{} does not exist", dep.token()),
        ));
    }

    // Cycles (§5.5: "cycles are a `tm check` error"). Reported once, at the
    // line of the first member (cycles start at the smallest id).
    for ids in tree.parent_cycles() {
        let anchor = ids.first().cloned().unwrap_or_default();
        let (file, line) = loc_of(tree, &anchor);
        out.push(CheckProblem::error(
            PARENT_CYCLE,
            &file,
            line,
            Some(anchor.clone()),
            format!("parent cycle: {} -> {}", fmt_ids(&ids), anchor.token()),
        ));
    }
    for ids in tree.dep_cycles() {
        let anchor = ids.first().cloned().unwrap_or_default();
        let (file, line) = loc_of(tree, &anchor);
        out.push(CheckProblem::error(
            DEP_CYCLE,
            &file,
            line,
            Some(anchor.clone()),
            format!("dependency cycle: {} -> {}", fmt_ids(&ids), anchor.token()),
        ));
    }

    // Outcomes that are really milestones (§6.2).
    for id in tree.month_items_with_est_and_no_children() {
        let Some(item) = tree.get(&id) else { continue };
        let blocks = item
            .own_remaining()
            .map(|d| d.as_blocks(cfg.block_min()))
            .unwrap_or(0.0);
        out.push(CheckProblem::warning(
            OUTCOME_WITH_EST,
            &item.src.file,
            item.src.line,
            Some(id.clone()),
            format!("outcome with an estimate ({blocks:.1}b) and no children — did you mean a milestone in `week/`?"),
        ));
    }

    // Series: only the head is active (§5.4).
    let names: Vec<String> = tree.series_names().map(|s| s.to_string()).collect();
    for name in names {
        let head = tree.series_head(&name);
        for id in tree.series_members(&name) {
            if Some(id) == head.as_ref() {
                continue;
            }
            let Some(item) = tree.get(id) else { continue };
            if item.state == State::Active {
                let head_txt = match &head {
                    Some(h) => format!("the head is ^{h}"),
                    None => "the series has no open head".to_string(),
                };
                out.push(CheckProblem::warning(
                    SERIES_ORDER,
                    &item.src.file,
                    item.src.line,
                    Some(id.clone()),
                    format!("`[>]` on a non-head member of series `{name}`; only the head is active ({head_txt})"),
                ));
            }
        }
    }
}

/// Overlapping walls (§8.2 step 1: "overlapping walls → diagnostics; the
/// planner places nothing in the overlap"). Every open Interval counts, not
/// only the synced `calendar/` ones, since the planner treats them alike;
/// `buffer:` is not included (it is placement, not a booking).
fn check_walls(tree: &Tree, out: &mut Vec<CheckProblem>) {
    let mut walls: Vec<(&Id, &Item, chrono::NaiveDateTime, chrono::NaiveDateTime)> = Vec::new();
    for node in tree.nodes() {
        if !node.primary || !node.item.state.is_open() {
            continue;
        }
        if let Shape::Interval { start, end } = node.item.shape {
            walls.push((&node.key, &node.item, start, end));
        }
    }
    walls.sort_by(|a, b| {
        (a.2, a.3, a.1.src.file.as_str(), a.1.src.line).cmp(&(b.2, b.3, b.1.src.file.as_str(), b.1.src.line))
    });
    for i in 0..walls.len() {
        for j in i + 1..walls.len() {
            if walls[j].2 >= walls[i].3 {
                break; // sorted by start: nothing later can overlap either
            }
            let (key, item, start, end) = walls[j];
            let (okey, oitem, ostart, oend) = walls[i];
            out.push(CheckProblem::warning(
                WALL_CONFLICT,
                &item.src.file,
                item.src.line,
                Some(key.clone()),
                format!(
                    "wall ^{key} {} overlaps ^{okey} {} ({}:{})",
                    fmt_span(start, end),
                    fmt_span(ostart, oend),
                    oitem.src.file,
                    oitem.src.line
                ),
            ));
        }
    }
}

fn fmt_span(start: chrono::NaiveDateTime, end: chrono::NaiveDateTime) -> String {
    if start.date() == end.date() {
        format!("{}–{}", start.format("%Y-%m-%dT%H:%M"), end.format("%H:%M"))
    } else {
        format!("{}–{}", start.format("%Y-%m-%dT%H:%M"), end.format("%Y-%m-%dT%H:%M"))
    }
}

// ---------------------------------------------------------------------------
// --fix-ids (§13, §17.2)
// ---------------------------------------------------------------------------

/// Append an `^id` to every line that needs one and write the changed files
/// back through `store`; returns `(file, line, id)` for each id assigned, in
/// file order.
///
/// `files` must be the whole tree (`store.read_tree()`): the ids already in
/// it are what the new ones are checked against. Each changed file goes
/// through [`Store::modify_file`], so a concurrent save is merged rather than
/// clobbered (§1.3), and the entry in `files` is replaced by the re-read
/// version. Files that need no id are not touched at all — the rest of every
/// line stays byte-identical, because only the `^id` token is appended.
pub fn fix_ids(
    store: &dyn Store,
    files: &mut [ParsedFile],
    gen: &mut IdGen,
) -> Result<Vec<(String, usize, Id)>, CheckError> {
    let mut taken: HashSet<String> = files
        .iter()
        .flat_map(|f| f.items())
        .filter(|i| i.has_id())
        .map(|i| i.id.as_str().to_string())
        .collect();
    let mut assigned = Vec::new();

    for idx in 0..files.len() {
        if !files[idx].items().any(needs_id) {
            continue;
        }
        let path = files[idx].path.clone();
        let horizon = files[idx].horizon;
        let mut here: Vec<(usize, Id)> = Vec::new();
        {
            let gen = &mut *gen;
            let taken = &mut taken;
            let here = &mut here;
            let mut edit = move |current: &ParsedFile| -> Result<Option<String>, StoreError> {
                let mut next = current.clone();
                *here = assign_ids_in_parsed(&mut next, horizon, gen, taken);
                if here.is_empty() {
                    Ok(None)
                } else {
                    Ok(Some(next.to_text()))
                }
            };
            store.modify_file(&path, &mut edit)?;
        }
        if here.is_empty() {
            continue;
        }
        files[idx] = store.read_file(&path)?;
        for (line, id) in here {
            assigned.push((path.clone(), line, id));
        }
    }
    Ok(assigned)
}

/// Append an `^id` to every line of `text` that needs one — the pure half of
/// [`fix_ids`], for the TUI's first load of a buffer and for previews.
///
/// `ctx` supplies the file name, the horizon (which decides whether ids are
/// required at all) and `block_min`; `existing` is the set of ids already in
/// use anywhere in the tree and gains every id found in `text` as well as
/// every id assigned. Returns the new text (byte-identical when nothing was
/// assigned, and otherwise changed only by the appended tokens) and the ids
/// in line order.
pub fn assign_ids_in_text(
    text: &str,
    ctx: &ParseCtx<'_>,
    gen: &mut IdGen,
    existing: &mut HashSet<String>,
) -> (String, Vec<Id>) {
    if ctx.horizon.allows_missing_state() {
        return (text.to_string(), Vec::new());
    }
    let cfg = block_min_config(ctx.block_min);
    let mut parsed = parse_file(ctx.file, text, &cfg);
    let assigned = assign_ids_in_parsed(&mut parsed, ctx.horizon, gen, existing);
    if assigned.is_empty() {
        return (text.to_string(), Vec::new());
    }
    let ids = assigned.into_iter().map(|(_, id)| id).collect();
    (parsed.to_text(), ids)
}

/// A config that differs from the defaults only in `block_min`, which is all
/// [`parse_file`] reads.
fn block_min_config(block_min: u32) -> Config {
    let mut cfg = Config::default();
    cfg.day.block_min = block_min;
    cfg
}

/// Assign ids in a parsed file; returns `(line, id)` in line order.
fn assign_ids_in_parsed(
    parsed: &mut ParsedFile,
    horizon: Horizon,
    gen: &mut IdGen,
    taken: &mut HashSet<String>,
) -> Vec<(usize, Id)> {
    let present: Vec<String> = parsed
        .items()
        .filter(|i| i.has_id())
        .map(|i| i.id.as_str().to_string())
        .collect();
    taken.extend(present);

    let mut out = Vec::new();
    for item in parsed.items_mut() {
        if !needs_id_in(item, horizon) {
            continue;
        }
        let id = gen.next_id(taken);
        item.src.tokens.append_id(&id);
        item.id = id.clone();
        out.push((item.src.line, id));
    }
    out
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::MemStore;

    fn cfg() -> Config {
        Config::default()
    }

    fn problems(files: &[(&str, &str)]) -> Vec<CheckProblem> {
        let c = cfg();
        let parsed: Vec<ParsedFile> = files.iter().map(|(p, t)| parse_file(p, t, &c)).collect();
        let tree = Tree::build(&parsed, &c);
        check(&parsed, &tree, &c)
    }

    fn codes(problems: &[CheckProblem]) -> Vec<&'static str> {
        problems.iter().map(|p| p.code).collect()
    }

    #[test]
    fn clean_tree_has_no_problems() {
        let p = problems(&[(
            "week/2026-W37.md",
            "# Milestones\n- [ ] 5 6b Finish ch.5 exercises ^m1\n- [ ] 4 1b Sub task @m1 ^t1\n",
        )]);
        assert!(p.is_empty(), "{p:?}");
        assert_eq!(exit_code(&p), 0);
        assert_eq!(summary(&p), "no problems");
    }

    #[test]
    fn display_form() {
        let p = CheckProblem::error(DUP_ID, "week/2026-W37.md", 4, Some(Id::new("m1")), "duplicate id ^m1");
        assert_eq!(p.to_string(), "week/2026-W37.md:4: error[dup-id]: duplicate id ^m1");
        let w = CheckProblem::warning(MISSING_ID, "backlog.md", 2, None, "no `^id`");
        assert_eq!(w.to_string(), "backlog.md:2: warning[missing-id]: no `^id`");
        let f = CheckProblem::error(BAD_VALUE, "notes.md", 0, None, "unterminated front matter");
        assert_eq!(f.to_string(), "notes.md: error[bad-value]: unterminated front matter");
    }

    #[test]
    fn exit_code_and_summary() {
        let ps = vec![
            CheckProblem::error(DUP_ID, "a.md", 1, None, "x"),
            CheckProblem::warning(MISSING_ID, "a.md", 2, None, "y"),
        ];
        assert!(has_errors(&ps));
        assert_eq!(exit_code(&ps), 2);
        assert_eq!(summary(&ps), "1 error, 1 warning");
        let only_warnings = vec![CheckProblem::warning(MISSING_ID, "a.md", 2, None, "y")];
        assert!(!has_errors(&only_warnings));
        assert_eq!(exit_code(&only_warnings), 0);
        assert_eq!(summary(&only_warnings), "0 errors, 1 warning");
    }

    #[test]
    fn structural_problems() {
        let p = problems(&[(
            "week/2026-W37.md",
            "- [ ] 3 1b A @nope ^aa11\n\
             - [ ] 3 1b B after:^gone ^bb22\n\
             - [ ] 3 1b C @dd44 ^cc33\n\
             - [ ] 3 1b D @cc33 ^dd44\n\
             - [ ] 3 1b E after:^ff66 ^ee55\n\
             - [ ] 3 1b F after:^ee55 ^ff66\n",
        )]);
        assert_eq!(
            codes(&p),
            vec![
                DANGLING_PARENT,
                DANGLING_DEP,
                PARENT_CYCLE,
                DEP_CYCLE,
            ]
        );
        assert!(has_errors(&p));
    }

    #[test]
    fn line_level_problems() {
        let p = problems(&[(
            "week/2026-W37.md",
            "- [ ] 3 1b Bad due:tomorrow ^aa11\n\
             - [ ] 3 1b Unknown foo:bar ^bb22\n\
             - [ ] 3 1b Ci ci:7 ^cc33\n\
             - [ ] 3 1b Priority !9 ^dd44\n\
             - [ ] 3 1b Junk ^% ^ee55\n\
             - [ ] 3 1b No id here\n\
             - [?] 3 1b Waiting ^ff66\n",
        )]);
        assert_eq!(
            codes(&p),
            vec![
                BAD_VALUE,
                UNKNOWN_KEY,
                BAD_CI,
                BAD_CI,
                UNCLASSIFIED_TOKEN,
                MISSING_ID,
                WAITING_STATE,
            ]
        );
    }

    #[test]
    fn file_conventions() {
        let p = problems(&[
            ("routines.md", "- meditate every:day\n- lunch win:11:30-13:30 dur:30m every:day\n"),
            ("optional.md", "- Doomscrolling\n- Factorio dur:2h\n"),
            ("calendar/2026-W37.md", "- [ ] 3 No shape ^gg11\n"),
            ("day/2026-09-07.md", "# Scratch\n- [ ] 2 20m Loose ^hh22\n"),
        ]);
        assert_eq!(
            codes(&p),
            vec![CALENDAR_SHAPE, DAY_SECTION, OPTIONAL_SHAPE, ROUTINE_SHAPE]
        );
    }

    #[test]
    fn wall_conflicts_are_pairwise() {
        let p = problems(&[(
            "calendar/2026-W37.md",
            "- [ ] 3 One at:2026-09-08T10:00/11:00 ^aa11\n\
             - [ ] 3 Two at:2026-09-08T10:30/11:30 ^bb22\n\
             - [ ] 3 Three at:2026-09-08T12:00/13:00 ^cc33\n",
        )]);
        assert_eq!(codes(&p), vec![WALL_CONFLICT]);
        assert_eq!(p[0].line, 2);
        assert!(!has_errors(&p));
    }

    #[test]
    fn assign_ids_appends_only_where_needed() {
        let text = "# Tasks\n- [ ] 3 1b Has one ^aa11\n- [ ] 3 1b Needs one\nprose\n";
        let ctx = ParseCtx::new("week/2026-W37.md", 60);
        let mut gen = IdGen::new(7);
        let mut existing: HashSet<String> = HashSet::new();
        let (out, ids) = assign_ids_in_text(text, &ctx, &mut gen, &mut existing);
        assert_eq!(ids.len(), 1);
        let expected = format!("# Tasks\n- [ ] 3 1b Has one ^aa11\n- [ ] 3 1b Needs one {}\nprose\n", ids[0].token());
        assert_eq!(out, expected);
        assert!(existing.contains("aa11"));
        assert!(existing.contains(ids[0].as_str()));
    }

    #[test]
    fn assign_ids_skips_id_less_files() {
        let text = "- lunch win:11:30-13:30 dur:30m every:day\n";
        let ctx = ParseCtx::new("routines.md", 60);
        let mut gen = IdGen::new(7);
        let mut existing = HashSet::new();
        let (out, ids) = assign_ids_in_text(text, &ctx, &mut gen, &mut existing);
        assert_eq!(out, text);
        assert!(ids.is_empty());
    }

    #[test]
    fn fix_ids_writes_through_the_store() {
        let store = MemStore::new()
            .with_file("week/2026-W37.md", "- [ ] 3 1b One\n- [ ] 3 1b Two ^aa11\n")
            .with_file("routines.md", "- lunch win:11:30-13:30 dur:30m every:day\n");
        let mut files = store.read_tree().unwrap().files;
        let mut gen = IdGen::new(11);
        let assigned = fix_ids(&store, &mut files, &mut gen).unwrap();
        assert_eq!(assigned.len(), 1);
        assert_eq!(assigned[0].0, "week/2026-W37.md");
        assert_eq!(assigned[0].1, 1);
        let text = store.read_text("week/2026-W37.md").unwrap();
        assert_eq!(
            text,
            format!("- [ ] 3 1b One {}\n- [ ] 3 1b Two ^aa11\n", assigned[0].2.token())
        );
        assert_eq!(store.read_text("routines.md").unwrap(), "- lunch win:11:30-13:30 dur:30m every:day\n");
        // The in-memory copies were refreshed, so a re-check is clean.
        let cfg = store.read_config().unwrap();
        let tree = Tree::build(&files, &cfg);
        let p = check(&files, &tree, &cfg);
        assert!(p.iter().all(|p| p.code != MISSING_ID), "{p:?}");
    }
}
