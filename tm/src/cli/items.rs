//! The file verbs of tm-spec-v1.md §13: `add`, `edit`, `move`, `rank`,
//! `demote`, `readopt`, `drop`, `event`, `skip`, `routine done`, `triage`.
//!
//! # API overview
//!
//! Every one of these changes one line of one Markdown file — byte-faithfully
//! (§1.3: through [`tm_core::grammar::ItemLine`] and
//! [`tm_core::store::Store::write_line`]) — and appends the §10.1 event that
//! records it. The horizon moves (`move`, `demote`, `readopt`, `drop`, `rank`)
//! are `horizon.rs`'s (§6.3); this module resolves the arguments, records the
//! undo entry and prints the result.
//!
//! * [`add`] — a new line, with an id assigned when the file wants one
//!   ([`id_gen`] seeds the generator from `now`, so `--now` makes it
//!   reproducible; an `^id` the text already carries must be free, §4.1).
//!   §10.1 has no `add` event; the line is logged as `edit{field:"add"}`.
//! * [`edit`] — `k=v` pairs (typed: `ci`, `est` — the item's *remaining*
//!   estimate, so the `est:` token when the line carries one and the leading
//!   estimate otherwise, §4.1 — `title`, `p`, `state`) plus `--set` (a raw
//!   `key:value` token) and `--unset` (the `key:` token, or the positional
//!   `p`/`ci`), one `edit` event per field. The result is re-parsed before it
//!   is written, so the CLI never produces a line its own `tm check` rejects
//!   ([`reject_new_problems`]).
//! * [`event`] — §5.1: logs `event{name,id}` and flips every `[?]` item the
//!   name resolves back to `[ ]` with its estimate reset.
//! * [`skip`] / [`routine`] — today's instance of a routine (§5.1, §5.3).
//! * [`triage`] — `inbox.md` with a parse preview per line (§12.5).

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use serde::Serialize;

use tm_core::check as validate;
use tm_core::grammar::{self, IdGen, ItemLine, ParseCtx};
use tm_core::horizon;
use tm_core::log::Event;
use tm_core::model::{Dur, Horizon, Id, IsoWeek, State, YearMonth};
use tm_core::recur;
use tm_core::store::{edit as text_edit, Store};
use tm_core::tree::Tree;

use super::ctx::{Ctx, Globals};
use super::kernel_bridge::{self, Cmd as KCmd};
use super::out::{emit, CliError};
use super::undo::Recorder;

/// An id generator seeded from the instant and a salt, so `--now` makes new
/// ids reproducible (§17.2: no randomness that a test cannot pin).
pub fn id_gen(ctx: &Ctx, salt: &str) -> IdGen {
    let mut h = DefaultHasher::new();
    ctx.now.timestamp_millis().hash(&mut h);
    salt.hash(&mut h);
    IdGen::new(h.finish())
}

/// The file a `--to` argument names.
fn target_path(ctx: &Ctx, to: Option<&str>) -> Result<String, CliError> {
    let Some(to) = to else {
        return Ok("inbox.md".to_string());
    };
    if to.ends_with(".md") {
        return Ok(to.to_string());
    }
    Ok(horizon_arg(ctx, to)?.path())
}

/// The horizon a word or path names (§6.1: horizon = file).
fn horizon_arg(ctx: &Ctx, s: &str) -> Result<Horizon, CliError> {
    let week = IsoWeek::from_date(ctx.today);
    Ok(match s {
        "backlog" | "none" => Horizon::Backlog,
        "week" => Horizon::Week(week),
        "month" => Horizon::Month(YearMonth::from_date(ctx.today)),
        "day" => Horizon::Day(ctx.today),
        "inbox" => Horizon::Inbox,
        "routines" | "routine" => Horizon::Routine,
        "optional" => Horizon::Optional,
        "calendar" => Horizon::Calendar(week),
        other => Horizon::from_path(other).ok_or_else(|| {
            CliError::msg(format!(
                "unknown horizon {other:?} (backlog, month, week, day, inbox, routines, optional, \
                 or a path like week/2026-W37.md)"
            ))
        })?,
    })
}

/// `tm add --json`.
#[derive(Debug, Serialize)]
pub struct AddOut {
    /// The id the line carries (empty in `routines.md` / `optional.md` /
    /// `inbox.md`, where lines have none).
    pub id: Id,
    /// The file it went into.
    pub file: String,
    /// The section it landed in.
    pub section: Option<String>,
    /// The line as written.
    pub line: String,
}

/// True for a `## series:<name>` heading (§5.4).
fn is_series(heading: &str) -> bool {
    heading.trim_start().starts_with("series:")
}

/// Insert `text` into `path`, and say which section it landed in.
///
/// Without an explicit `--section` the line goes at the end of the file —
/// except that §4.3's `backlog.md` (and the tree `tm init` writes) *ends*
/// with a `## series:<name>` section, where a new item would be a silent
/// non-head and therefore invisible to the planner (§5.4: "only the head is
/// active; the rest are invisible"). So a trailing series section is skipped:
/// the line goes under the last ordinary heading, or above the first series
/// heading when there is none.
fn insert(
    ctx: &Ctx,
    path: &str,
    section: Option<&str>,
    text: &str,
) -> Result<Option<String>, CliError> {
    if let Some(s) = section {
        ctx.store.insert_line(path, Some(s), text)?;
        return Ok(Some(s.to_string()));
    }
    if !ctx.store.exists(path) {
        ctx.store.insert_line(path, None, text)?;
        return Ok(None);
    }
    let parsed = ctx.store.read_file(path)?;
    let headings = text_edit::headings(&parsed);
    if !headings.last().is_some_and(|h| is_series(&h.text)) {
        ctx.store.insert_line(path, None, text)?;
        return Ok(headings.last().map(|h| h.text.clone()));
    }
    match headings.iter().rev().find(|h| !is_series(&h.text)) {
        Some(h) => {
            let name = h.text.clone();
            ctx.store.insert_line(path, Some(&name), text)?;
            Ok(Some(name))
        }
        None => {
            // Every section is a series: the line belongs above them all.
            let first = headings
                .first()
                .map(|h| h.index)
                .unwrap_or(parsed.lines.len());
            let line = text.to_string();
            ctx.store
                .modify_file(path, &mut |parsed: &tm_core::grammar::ParsedFile| {
                    let mut lines: Vec<String> =
                        parsed.lines.iter().map(|l| l.text()).collect();
                    let at = first.min(lines.len());
                    lines.insert(at, line.clone());
                    Ok(Some(format!("{}\n", lines.join("\n"))))
                })?;
            Ok(None)
        }
    }
}

/// True when a kernel-backed `tm add` can express this request on the wire
/// (kernel/README.md, 2026-09-12 "rank, add and the keyed edit" block). The
/// wire carries a plain title only — the kernel renders `- [ ] <title> ^id`
/// at the end of the file — so everything else stays on the old Rust path,
/// each carve-out by name:
///
/// * a `--section` (the kernel places the line itself; no section on the
///   wire — the same rule as `tm move --section`),
/// * an id-less destination (`routines.md`/`optional.md`/`inbox.md` — the
///   kernel renders a box and an id, gap 5's mirror image),
/// * an explicit `^id` in the text (the kernel's ids are `freshId`'s own;
///   `parseCmd` refuses a `^` in a title),
/// * a state other than `[ ]` (the wire has no box parameter),
/// * a destination whose **last** heading is a `## series:` section — §5.4:
///   the kernel appends at the end of the file, where the line would become
///   a silent, invisible non-head of the series; the old path's series-skip
///   is host placement logic the wire does not carry.
fn kernel_addable(ctx: &Ctx, path: &str, horizon: Horizon, text: &str) -> bool {
    if horizon.allows_missing_state() {
        return false;
    }
    let Some(title) = text.strip_prefix("- [ ] ") else {
        return false;
    };
    if title.is_empty()
        || title.contains(['^', '\t', '\n'])
        || title.starts_with(' ')
        || title.ends_with(' ')
    {
        return false;
    }
    if ctx.store.exists(path) {
        if let Ok(parsed) = ctx.store.read_file(path) {
            if text_edit::headings(&parsed)
                .last()
                .is_some_and(|h| is_series(&h.text))
            {
                return false;
            }
        }
    }
    true
}

/// **The errors `tm check` would name about the tree as it stands**, as a
/// fingerprint per problem (`file`, `code`, `message` — never the line, which
/// an insertion above moves).
///
/// This is `tm check`'s own host-side pass, [`tm_core::check::check`], asked of
/// the `Ctx` already loaded: one reader of "what is wrong with this tree"
/// (AGENTS §5.3), not a second list of field rules. Warnings are left out on
/// purpose — a warning is the tree being *suspicious*, which is not a reason to
/// refuse a write.
fn check_errors(ctx: &Ctx) -> Vec<String> {
    validate::check(&ctx.files.files, &ctx.tree, &ctx.cfg)
        .into_iter()
        .filter(|p| p.severity.is_error())
        .map(|p| format!("{}\u{1}{}\u{1}{}", p.file, p.code, p.message))
        .collect()
}

/// **The errors this write ADDED**, as the first one's own `tm check` line.
///
/// `before` is [`check_errors`] of the tree the verb loaded and `ctx` is the
/// tree it has just written. A problem already in `before` is consumed rather
/// than reported, so a user inside an already-broken tree is not trapped by a
/// fault that was there before they typed — the same reason `tm undo` and
/// `tm check --fix-ids` are not gated on the tree they start from.
///
/// **THE BLIND SPOT, DECLARED.** The comparison is a MULTISET of
/// `(file, code, message)`, so a write that adds a SECOND error identical in
/// all three to one already present is not seen. That is the quiet direction
/// and it is the price of not trapping the user; the loud direction — refusing
/// every write into a tree that already has an error — is the trap.
fn added_error(before: &[String], ctx: &Ctx) -> Option<String> {
    let mut pool: Vec<String> = before.to_vec();
    for p in validate::check(&ctx.files.files, &ctx.tree, &ctx.cfg) {
        if !p.severity.is_error() {
            continue;
        }
        let key = format!("{}\u{1}{}\u{1}{}", p.file, p.code, p.message);
        match pool.iter().position(|q| *q == key) {
            Some(k) => {
                pool.swap_remove(k);
            }
            None => return Some(p.to_string()),
        }
    }
    None
}

/// **The sentence a write refused for a line `tm check` calls an error takes**
/// (W-32 repair, kernel/README.md gap 2415).
///
/// The kernel's own refusal has one spelling
/// ([`kernel_bridge::gate`]); this is the host half's, and it says the same
/// three things — what is wrong, where, and that nothing was written.
fn bad_line_refusal(verb: &str, problem: &str) -> CliError {
    CliError::msg(format!(
        "{problem} — nothing was written: `tm {verb}` wrote a line `tm check` calls an error, and \
         every verb that reads the field would ignore it in silence (the tree still loads, so no \
         other gate would have said so)"
    ))
}

/// The kernel-backed `tm add`: one `{"op":"add","seed":…,"doc":…,"title":…}`
/// through the choke point. The seed comes from the same entropy source the
/// old id generator used ([`id_gen`]'s hasher over `--now` and the text), so
/// `--now` still pins the id (§17.2) and nothing new is stored; the id
/// itself is the kernel's — `freshId` renders the seed as digits and bumps
/// past every taken id, freshness by theorem (L21), so the id shape is
/// digits now, not the old four-character base-32 (gap 13's recorded
/// resolution: digits are a subset of `[a-z0-9]`).
fn add_kernel(
    ctx: &mut Ctx,
    path: &str,
    title: &str,
    raw: &str,
    before: &[String],
) -> Result<i32, CliError> {
    let mut h = DefaultHasher::new();
    ctx.now.timestamp_millis().hash(&mut h);
    raw.hash(&mut h);
    // Four digits to start with, the old id length; freshId may walk past.
    let seed = 1000 + (h.finish() % 9000);
    let existed = ctx.store.exists(path);
    let prior = ctx.store.read_text(path).ok();
    let rec = Recorder::start(ctx, "add")?;
    let applied = kernel_bridge::apply(
        ctx,
        "add",
        &[KCmd::Add {
            seed,
            to: path.to_string(),
            title: title.to_string(),
        }],
    )?;
    // The added line is the one the destination gained; the kernel returns
    // the id on the rendered line (a trailing `^<digits>` token).
    let doc = applied
        .doc(path)
        .ok_or_else(|| CliError::msg(format!("{path}: not in the kernel response")))?;
    let sent: Vec<&str> = doc.sent.lines().collect();
    let line = doc
        .returned
        .lines()
        .find(|l| !sent.contains(l))
        .unwrap_or_default()
        .to_string();
    let id = Id::new(
        line.split_whitespace()
            .rev()
            .find_map(|w| w.strip_prefix('^'))
            .unwrap_or_default(),
    );
    // **AND A WRITE THAT LEAVES A LINE `tm check` CALLS AN ERROR IS NOT A
    // SUCCESS EITHER** (W-32 repair, kernel/README.md gap 2415). Gap 2263 put
    // `kernel_bridge::gate` on the other side of the write, and that gate asks
    // whether the tree LOADS — a REFERENCE question. A malformed field VALUE
    // leaves a tree that loads perfectly, so it walked straight through on both
    // add paths. DRIVEN on the binary built from 9d7fad2, each on its own fresh
    // `tm init` tree whose `tm check` first said `no problems`: `tm add --to
    // week "- [ ] 3 90m audit block max:60m"` exited **0**, `tm check` then
    // exited 2 with ``week/2026-W39.md:22: error[bad-value]: `max:60m`: invalid
    // rate: "60m"``, and `tm plan` exited 0 having dropped the field without a
    // word. Six spellings did it — `max:60m`, `min:xyz`, `est:90`, `dur:7`,
    // `due:notadate` and a bare `9` in the ci slot — while `after:^nosuch` was
    // refused, because THAT one breaks the load. §5.13's failure class: a
    // plausible keystroke that neither works nor says so.
    //
    // The question is asked of the tree this add produced, by `tm check`'s own
    // pass, and only about what this add ADDED. Nothing has reached the log
    // yet and the recorder has pushed nothing, so putting the one file back
    // restores the tree exactly — the same rollback gap 2263 wrote.
    ctx.reload()?;
    if let Some(problem) = added_error(before, ctx) {
        match (existed, &prior) {
            (true, Some(text)) => ctx.store.write_file(path, text)?,
            _ => ctx.store.delete_file(path)?,
        }
        ctx.reload()?;
        return Err(bad_line_refusal("add", &problem));
    }
    ctx.append_event(Event::Edit {
        id: id.to_string(),
        field: "add".to_string(),
        from: String::new(),
        to: line.clone(),
    })?;
    ctx.reload()?;
    rec.finish(ctx, format!("add {path}"))?;

    let out = AddOut {
        section: ctx
            .tree
            .get(&id)
            .and_then(|i| i.src.section.clone()),
        id,
        file: path.to_string(),
        line,
    };
    emit(ctx.json, || format!("{} → {}", out.line, out.file), &out)?;
    Ok(0)
}

/// `tm add "<line>" [--to <file>] [--section <name>]`.
pub fn add(g: &Globals, args: &super::AddArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let path = target_path(&ctx, args.to.as_deref())?;
    let horizon = Horizon::from_path(&path).unwrap_or(Horizon::Backlog);

    // **THE PREFIX THIS SUPPLIES IS THE PART THAT IS MISSING** (W-31 repair,
    // README gap 2262).  `mod.rs` documents a CLASS — "the `- [ ] ` prefix is
    // optional" — and this read one spelling of it, `starts_with("- ")`.  A
    // line that carries the STATE and not the bullet has no hyphen and fell to
    // the last branch, so `tm add --to week "[ ] write the notes"` wrote `- [ ]
    // [ ] write the notes`, whose §4.1 TITLE is literally `[ ] write the
    // notes`; `tm check` then said "no problems" and `tm plan` rendered the
    // doubled checkbox in the shipped output beside a clean row.  DRIVEN over
    // four spellings and four horizons before the repair: the two carrying a
    // bare marker DOUBLED on week, backlog and month, and `inbox` was right
    // only by accident, because `allows_missing_state` took the other branch.
    //
    // The two prefix parts are now asked for separately, and the marker
    // question is `grammar::opens_with_state` — the grammar's own answer, the
    // one `ItemLine::parse` uses — rather than a second spelling of `[ ]`.
    let raw = args.line.trim();
    let (bullet, body) = match raw.strip_prefix("- ") {
        Some(rest) => (true, rest.trim_start()),
        None => (false, raw),
    };
    let mut text = if bullet {
        raw.to_string()
    } else if grammar::opens_with_state(body) {
        format!("- {body}")
    } else if horizon.allows_missing_state() {
        format!("- {raw}")
    } else {
        format!("- [ ] {raw}")
    };
    let pctx = ParseCtx {
        horizon,
        ..ParseCtx::new(&path, ctx.block_min())
    };
    let parsed = grammar::parse_line(&text, &pctx)
        .map_err(|e| CliError::msg(format!("{e}: {text:?}")))?;

    // The owner's D6 (kernel/README.md gap 22, closed at stage 4 final step
    // 3): a parent is read off its line, and a tree whose `@parent` names no
    // item refuses every kernel-backed verb by name (`danglingParent`). The
    // kernel's own `add` refuses such a title (`badItem`, its post-state
    // check); the carve-outs below write without the kernel, so without this
    // they would write the one line that then refuses every later verb. So
    // both paths refuse it here, first, by the kernel's name.
    if let Some(parent) = &parsed.parent {
        if !ctx.tree.contains(&parent.to_id()) {
            return Err(CliError::msg(format!(
                "danglingParent — {} names no item in the tree, and the kernel refuses a tree whose parent link dangles; nothing was written: {text:?}",
                parent.token()
            )));
        }
    }

    // The errors `tm check` already names about this tree, taken BEFORE either
    // write path runs, so the two paths compare against one reading (gap 2415).
    let before = check_errors(&ctx);

    // Kernel-backed when the wire can carry it (kernel/README.md, 2026-09-12
    // "rank, add and the keyed edit" block); the carve-outs stay on the old
    // Rust path, each named on [`kernel_addable`].
    if args.section.is_none() && kernel_addable(&ctx, &path, horizon, &text) {
        let title = text.strip_prefix("- [ ] ").expect("checked").to_string();
        return add_kernel(&mut ctx, &path, &title, raw, &before);
    }

    kernel_bridge::gate(&ctx, "add")?;
    let rec = Recorder::start(&ctx, "add")?;
    let mut line = ItemLine::parse(&text).map_err(|e| CliError::msg(e.to_string()))?;
    let mut id = line.id().unwrap_or_default();
    let mut taken = ctx.taken_ids();
    // **AN ID IS OWED BY THE LINE, NOT BY THE FILE** (W-30 repair, README gap
    // 2132). This read `!horizon.allows_missing_state()`, which is §17.2's rule
    // about the STATE — `routines.md`, `optional.md` and `inbox.md` lines may be
    // bare — and used it as the rule about the ID. They are different rules, and
    // the kernel enforces the second one everywhere: a line that carries a state
    // BOX must carry an `^id` or the whole tree refuses to load (`Tm.PErr.noId`).
    // DRIVEN on the binary built from 0e5d1da, in a fresh `tm init` tree: `tm add
    // "- [ ] write the audit report est:2b ci:3"` wrote that text verbatim to
    // `inbox.md:11` at **rc=0**, and every following verb then refused the whole
    // tree — `tm add` and `tm plan` at rc=1 with `badLine — inbox.md:11 looks
    // like an item but does not parse (Tm.PErr.noId)`, `tm check` at rc=2. That
    // is §5.13's stated failure class: a plausible keystroke that neither works
    // nor says so at the time. (`tm undo` did restore it exactly, and the refusal
    // named that recovery, so nothing was ever lost — but the tree was bricked
    // until the operator read the next verb's output.) So the test is the LINE's
    // own state token: a bare inbox capture still gets no id, and a boxed one
    // gets the id the kernel demands, from the same generator as every other
    // target. `tm add --to week` had always assigned one; this makes the inbox
    // agree with it instead of writing a line the kernel cannot read.
    let boxed = line.index_of(&grammar::TokenKind::State).is_some();
    if id.is_empty() && (!horizon.allows_missing_state() || boxed) {
        let mut gen = id_gen(&ctx, raw);
        id = gen.next_id(&mut taken);
        line.append_id(&id);
        text = line.to_string();
    } else if !id.is_empty() && taken.contains(id.as_str()) {
        // §4.1: ids are global across the tree. The capture path must not be
        // the thing that creates a `tm check` duplicate.
        return Err(CliError::msg(format!(
            "{} is already used{} — drop the `^id` and one will be assigned",
            id.token(),
            ctx.files
                .file_of(&id)
                .map(|f| format!(" in {f}"))
                .unwrap_or_default()
        )));
    }
    // **A WRITE THAT LEAVES THE TREE UNLOADABLE IS NOT A SUCCESS** (W-31
    // repair, kernel/README.md gap 2263).  §5.7 was honoured on the READ side
    // and not on the write side: `tm add` validated the LINE against the §4.1
    // grammar, wrote it, and returned 0, and every reading verb then refused
    // the whole tree by name.  DRIVEN on the binary built from 74771aa, in a
    // fresh `tm init` tree: `tm add --to routines "[ ] 0700 stretch est:15m
    // every:day"` printed the line and exited **0**, after which `tm review
    // day`, `tm sync-cal` and `tm close week` all exited 1 with `itemCheck —
    // the tree fails the kernel's item invariant (fileKindShape)` and `tm
    // check` exited 2 naming `routines.md:15: a routine needs a window (`win:`
    // + `dur:`) or `after-done:``.  Reproduced a second time on `optional`,
    // three consecutive adds each leaving the tree refusing.
    //
    // The line parses and the tree does not, so the question has to be asked of
    // the TREE — which is `kernel_bridge::gate`, the same door every writing
    // verb already goes through BEFORE it writes, asked again AFTER.  The write
    // is put back exactly: the file's own bytes, or the file removed when this
    // add is what created it (`Store::delete_file`, added for this).  Nothing
    // has reached the log at this point and the recorder has pushed nothing, so
    // restoring the one file restores the tree.
    let existed = ctx.store.exists(&path);
    let prior = ctx.store.read_text(&path).ok();
    let section = insert(&ctx, &path, args.section.as_deref(), &text)?;
    ctx.reload()?;
    // The tree must LOAD (gap 2263) **and** the line must not be one `tm check`
    // calls an error (gap 2415) — two questions, one rollback. The second is
    // the one a malformed field VALUE trips: `max:60m` leaves a tree the kernel
    // loads and `tm plan` renders, with the field dropped in silence.
    let verdict = kernel_bridge::gate(&ctx, "add")
        .err()
        .or_else(|| added_error(&before, &ctx).map(|p| bad_line_refusal("add", &p)));
    if let Some(refusal) = verdict {
        match (existed, &prior) {
            (true, Some(t)) => ctx.store.write_file(&path, t)?,
            _ => ctx.store.delete_file(&path)?,
        }
        ctx.reload()?;
        return Err(refusal);
    }
    let key = if id.is_empty() {
        Id::new(
            grammar::parse_line(&text, &pctx)
                .map(|i| Tree::key_of(&i).to_string())
                .unwrap_or_default(),
        )
    } else {
        id.clone()
    };
    // §10.1 has no `add`; the line is recorded as an `edit` of the file.
    ctx.append_event(Event::Edit {
        id: key.to_string(),
        field: "add".to_string(),
        from: String::new(),
        to: text.clone(),
    })?;
    ctx.reload()?;
    rec.finish(&ctx, format!("add {path}"))?;

    let out = AddOut {
        id: key,
        file: path,
        section,
        line: text,
    };
    emit(
        ctx.json,
        || format!("{} → {}", out.line, out.file),
        &out,
    )?;
    Ok(0)
}

/// One field an edit changed.
#[derive(Debug, Serialize)]
pub struct FieldChange {
    /// The field name (`ci`, `est`, `due`, `title`, `p`, or any key).
    pub field: String,
    /// The old value (empty when it was unset).
    pub from: String,
    /// The new value (empty when unset).
    pub to: String,
}

/// `tm edit --json`.
#[derive(Debug, Serialize)]
pub struct EditOut {
    /// The item.
    pub id: Id,
    /// What changed.
    pub changes: Vec<FieldChange>,
    /// The line afterwards.
    pub line: String,
    /// **The `^id` this edit wrote onto a title-keyed line** (D33, gap 477),
    /// when `state=` put the first box on it. `None` otherwise — including for
    /// every edit that boxes nothing, which is why the field is skipped when it
    /// is absent and no existing `--json` answer moves.
    ///
    /// The twin of [`DropOut::assigned`], and for the same reason: D33's
    /// accepted cost is a token the user did not type, and *visibly* is half
    /// the decision.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assigned: Option<Id>,
}

/// Split `k=v`.
fn split_pair(pair: &str) -> Result<(&str, &str), CliError> {
    pair.split_once('=')
        .ok_or_else(|| CliError::msg(format!("expected key=value, got {pair:?}")))
}

/// Apply one `k=v` to a line, returning the change it made. `raw` is `--set`:
/// the flag documented as writing a `key:value` token verbatim, so it skips
/// the typed handling of `ci`, `est`, `title`, `p` and `state`.
fn apply_pair(
    line: &mut ItemLine,
    item: &tm_core::model::Item,
    key: &str,
    value: &str,
    block_min: u32,
    raw: bool,
) -> Result<FieldChange, CliError> {
    let from = match key {
        _ if raw => line.get(key).unwrap_or_default().to_string(),
        "ci" => item.ci.to_string(),
        "title" => item.title.clone(),
        "p" | "priority" => item.priority.map(|p| p.to_string()).unwrap_or_default(),
        "state" => item.state.as_str().to_string(),
        // §4.1: `est:` is the remaining estimate and it overrides the leading
        // one, so the value `est=` replaces is whichever of the two the item's
        // remaining (§6.4) actually reads.
        "est" => match line.get("est") {
            Some(v) => v.to_string(),
            None => item
                .est_original
                .as_ref()
                .map(|d| d.to_string())
                .unwrap_or_default(),
        },
        other => line.get(other).unwrap_or_default().to_string(),
    };
    if raw {
        line.set_token(key, value);
        return Ok(FieldChange {
            field: key.to_string(),
            from,
            to: value.to_string(),
        });
    }
    match key {
        "ci" => {
            let v: u8 = value
                .parse()
                .map_err(|_| CliError::msg(format!("ci must be 0–5, got {value:?}")))?;
            if v > 5 {
                return Err(CliError::msg("ci must be 0–5"));
            }
            line.set_ci(v);
        }
        "title" => line.set_title(value)?,
        "p" | "priority" => {
            // §4.1's EBNF: `"!" ("1".."4")`.
            let v: u8 = value
                .parse()
                .map_err(|_| CliError::msg(format!("priority must be 1–4, got {value:?}")))?;
            if !(1..=4).contains(&v) {
                return Err(CliError::msg(format!(
                    "priority must be 1–4, got {value:?}"
                )));
            }
            line.set_priority(Some(v))?;
        }
        "state" => line.set_state(State::parse(value)?)?,
        "est" => {
            let d = Dur::parse_no_days(value, block_min)?;
            // §4.1: `est:` is the remaining estimate and "overrides the
            // leading estimate", which is §3.1's `est_original` — "the leading
            // estimate as written", the historical number §11 calibrates
            // actual/est against. So on a line that already carries `est:` the
            // value has to land there: writing the leading one instead would
            // leave `remaining` (§6.4) untouched *and* rewrite the history.
            // `tm edit ^id --unset est` drops the remainder and puts the
            // leading estimate back in charge of `remaining`, which is how the
            // leading one is changed on such a line.
            if line.get("est").is_some() {
                line.set_token("est", &d.to_string());
            } else {
                match line.set_leading_est(Some(d.clone())) {
                    // §4.3: a `routines.md` / `optional.md` line has no state,
                    // so it has no positional estimate slot either — the
                    // `est:` key is the only place the value can go.
                    Err(grammar::EditError::NoState) => line.set_token("est", &d.to_string()),
                    other => other?,
                }
            }
        }
        other => line.set_token(other, value),
    }
    Ok(FieldChange {
        field: key.to_string(),
        from,
        to: value.to_string(),
    })
}

/// A [`ParseCtx`] for the file an item lives in.
fn parse_ctx<'a>(item: &'a tm_core::model::Item, block_min: u32) -> ParseCtx<'a> {
    ParseCtx {
        horizon: item.horizon.clone(),
        section: item.src.section.as_deref(),
        ..ParseCtx::new(&item.src.file, block_min)
    }
}

/// Refuse an edit that would write a line the §4.1 grammar does not accept —
/// `due:notadate`, `max:nonsense`, an unknown value shape. §14 makes the CLI
/// the sanctioned writer, so it must never produce a tree its own `tm check`
/// rejects (§1.3). Only problems the line did *not* already have are raised.
fn reject_new_problems(
    item: &tm_core::model::Item,
    line: &ItemLine,
    block_min: u32,
) -> Result<(), CliError> {
    let pctx = parse_ctx(item, block_min);
    let before: Vec<String> = grammar::parse_line(&item.line().to_string(), &pctx)
        .map(|i| i.problems)
        .unwrap_or_default();
    let after = grammar::parse_line(&line.to_string(), &pctx)
        .map_err(|e| CliError::msg(format!("{e}: {line}")))?;
    if let Some(p) = after.problems.iter().find(|p| !before.contains(p)) {
        return Err(CliError::msg(format!("{p} (§4.1)")));
    }
    Ok(())
}

/// `tm edit ^id [k=v …] [--set k=v] [--unset k]`.
pub fn edit(g: &Globals, args: &super::EditArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    let item = ctx.item(&id)?.clone();
    if args.pairs.is_empty() && args.set.is_empty() && args.unset.is_empty() {
        return Err(CliError::msg("nothing to change (try `tm edit ^id ci=4`)"));
    }
    // The keyed edit — kernel-backed for **every** key the kernel wires
    // (kernel/README.md, 2026-09-12 "rank, add and the keyed edit" block,
    // superseding the est-only routing of "the five lifecycle verbs"): the
    // kernel parses the value with the key's own field grammar, writes it
    // through the one proven setter, and refuses by name (`badValue`,
    // `keyAbsent`; a tabbed line was refused too until the owner's D83 made a
    // tab the kernel's separator, W-42). **README gap 48's eight — `due at win
    // every on-event after loc waiting` — joined at W-27 under the owner's
    // D49**; the host's remaining half is closed and the kernel is the one
    // writer of every KEYED edit the wire carries. (`--set` still writes a
    // raw token under any spelling at all, by its own contract — it is in
    // the list below, not an exception to this sentence.)
    //
    // What stays on the old Rust path, by name — each one a key or a form
    // the WIRE does not carry, not a spelling this host declined to route:
    // id-less lines (gap 5: the wire addresses an `^id`), `--set`
    // (documented as a raw verbatim token, which the kernel would
    // canonicalize), the typed non-key edits (`title`, `p`, `state` — three
    // positional slots of §4.1's line grammar, and no `Field.Key` at all),
    // `--unset ci`/`--unset p` (positional-slot surgery the wire does not
    // carry — gap 41), `demoted` (excluded from the wire by the kernel's own
    // policy, gap 40 and CHEAT 45), and a `ci=` on a line whose ci is the
    // positional digit (gap 41 again — see [`unwired_reason`]).
    //
    // **AND A COMMAND MIXING ONE OF THOSE WITH A WIRED PAIR IS REFUSED** —
    // README gap 1700, closed at the W-27 repair step. It used to take the old
    // path WHOLE, which is precisely how the host stayed a second writer of a
    // key the kernel owns: `tm edit ^a1 cap=3h/d` wrote `max:3h/d` and
    // `tm edit ^a1 cap=3h/d ci=4` wrote `cap:3h/d`, and `est=2b ci=4` rewrote
    // §3.1's LEADING estimate instead of adding §4.1's `est:` key. Routing
    // gap 48's eight keys made that harder to reach and could not make it
    // unreachable, because `ci=`, `--set`, `title=` and an unknown spelling
    // are all one keystroke away. [`edit_route`] answers three ways now.
    if item.has_id() {
        match edit_route(&ctx, &id, args)? {
            EditRoute::Kernel(cmds) => return edit_kernel(&mut ctx, &id, &item, args, cmds),
            EditRoute::Mixed {
                wired,
                unwired,
                why,
            } => {
                return Err(CliError::msg(format!(
                    "one edit has one writer: `{wired}` is written by the kernel and `{unwired}` \
                     is not ({why}), so this command would write `{wired}` twice over. \
                     Run them as separate edits."
                )));
            }
            EditRoute::Host => {}
        }
    }
    kernel_bridge::gate(&ctx, "edit")?;
    let rec = Recorder::start(&ctx, "edit")?;
    // **D33, gap 477, the half `c4726e2` left behind** (W-16 repair, gap 575):
    // `tm edit <title> state=[ ]` boxes a box-less, id-less line exactly as
    // `tm drop <title>` does — `ItemLine::set_state` inserts the box after the
    // bullet — and D33's rule is about *boxing*, not about `drop`. All six
    // state values reach it, and before this the line went out boxed and
    // id-less, which `Plan.itemsWf` refuses by name (`PErr.noId`): `tm check`
    // exited 2 and `tm plan`, `tm now` and `tm review day` exited 1 on a tree
    // the previous command had just written and exited 0 on.
    //
    // Only the typed `state=` pair boxes. `--set state=…` writes a verbatim
    // `state:…` token (a key, not a box) and `--unset` removes; both leave the
    // positional slot alone, so neither is a boxing path.
    let boxing = !item.has_id()
        && item.line().index_of(&grammar::TokenKind::State).is_none()
        && args
            .pairs
            .iter()
            .any(|p| matches!(split_pair(p), Ok((k, _)) if k == "state"));
    let was = id.clone();
    let boxed_in = item.src.file.clone();
    let (id, item, assigned) = if boxing {
        let assigned = write_id_for_boxing(&mut ctx, &id, "edit")?;
        let item = ctx.item(&assigned)?.clone();
        (assigned.clone(), item, Some(assigned))
    } else {
        (id, item, None)
    };
    let block_min = ctx.block_min();
    let mut line = ctx.line(&id)?;
    let mut changes = Vec::new();
    for (pair, raw) in args
        .pairs
        .iter()
        .map(|p| (p, false))
        .chain(args.set.iter().map(|p| (p, true)))
    {
        let (k, v) = split_pair(pair)?;
        changes.push(apply_pair(&mut line, &item, k, v, block_min, raw)?);
    }
    for key in &args.unset {
        let from = match key.as_str() {
            "p" | "priority" => {
                let was = item.priority.map(|p| p.to_string()).unwrap_or_default();
                line.set_priority(None)?;
                was
            }
            // §4.1 writes the ci in the positional slot after the state, so
            // `remove_token` never finds it there; only the state-less
            // `routines.md` / `optional.md` lines spell it `ci:`.
            // [`ItemLine::remove_ci`] clears whichever the line carries (§3.1:
            // the item then inherits its parent's ci again).
            "ci" => {
                let was = match (line.get("ci"), line.index_of(&grammar::TokenKind::Ci)) {
                    (Some(v), _) => v.to_string(),
                    (None, Some(_)) => item.ci.to_string(),
                    (None, None) => String::new(),
                };
                line.remove_ci()?;
                was
            }
            other => {
                let was = line.get(other).unwrap_or_default().to_string();
                line.remove_token(other)?;
                was
            }
        };
        changes.push(FieldChange {
            field: key.clone(),
            from,
            to: String::new(),
        });
    }
    reject_new_problems(&item, &line, block_min)?;
    ctx.write_line(&id, &line)?;
    for c in &changes {
        ctx.append_event(Event::Edit {
            id: id.to_string(),
            field: c.field.clone(),
            from: c.from.clone(),
            to: c.to.clone(),
        })?;
    }
    ctx.reload()?;
    rec.finish(&ctx, format!("edit {}", id.token()))?;

    let note = assigned
        .as_ref()
        .map(|id| boxed_note(&was, id, &boxed_in));
    let out = EditOut {
        id: id.clone(),
        changes,
        line: line.to_string(),
        assigned,
    };
    emit(
        ctx.json,
        || match &note {
            None => out.line.clone(),
            Some(note) => format!("{}\n({note})", out.line),
        },
        &out,
    )?;
    Ok(0)
}

/// The keys the kernel's edit path is wired for (kernel/README.md,
/// edit-widening block: `Field.Key.ofName?` spellings, `cap` and `max` one
/// key). `ci` sets ride the wire; `--unset ci` does not — the wire clears
/// the `ci:` key slot only, and a complete unset has to clear the positional
/// digit too (gap 41), which stays the old path's line surgery.
///
/// **The eight of README gap 48 joined at W-27 — the owner's D49, `tm edit`
/// has ONE writer and it is the kernel's.** `Cmd.keyEditable` has carried
/// `due at win every on-event after loc waiting` since gap 40's bridges
/// (`bf7cc63`) while this list carried nine, so `tm edit ^id due=…` went down
/// the old Rust path — and, because [`edit_route`] routes only when
/// **every** pair is wired, so did every command that merely *mentioned* one
/// of them. That is the mechanism that made `tm edit ^a1 cap=3h/d` and
/// `tm edit ^a1 cap=3h/d due=2026-10-01` write different bytes for the same
/// pair: the alias (`max:` against `cap:`), the rendering (`est:120m` against
/// `2b`) and the slot (the `est:` key against the leading estimate).
///
/// **Seventeen of the kernel's eighteen keys, plus the `cap` alias.**
/// `demoted` is out by the *kernel's* policy (`keyNotWired demoted`,
/// `Negative.lean` CHEAT 45), not by this list, and
/// [`tests::the_host_routes_every_key_the_kernel_wires`] asserts exactly that
/// — in both directions, against `tm_core::grammar::KEYS` and the kernel's
/// own answer, so this stays a derived table and not a second name list
/// (§5.3). Its blind spots are written out beside it.
const KERNEL_EDIT_KEYS: &[&str] = &[
    "est", "dur", "buffer", "pref", "on-miss", "after-done", "min", "max", "cap", "ci", "due",
    "at", "win", "every", "on-event", "after", "loc", "waiting",
];

/// How one `tm edit` invocation is routed -- and it is a THREE-way answer,
/// not a two-way one, which is the W-27 repair step's correction to D49.
///
/// It used to be `Option<Vec<KCmd>>`: every change wired, or the whole edit on
/// the old Rust path. The second branch is what kept a SECOND WRITER alive.
/// DRIVEN on the merged binary, against a copy of `plan-basic` whose line is
/// `- [ ] 2 30m Insurance claim for the bike  ^a1` (a leading estimate, no
/// `est:` key):
///
/// ```text
/// tm edit ^a1 cap=3h/d        ->  .. bike max:3h/d  ^a1      (kernel)
/// tm edit ^a1 cap=3h/d ci=4   ->  .. bike cap:3h/d  ^a1      (host: the ALIAS)
/// tm edit ^a1 est=2b          ->  .. bike est:120m  ^a1      (kernel)
/// tm edit ^a1 est=2b ci=4     ->  - [ ] 4 2b Insurance ..    (host: the SLOT
///                                  and the RENDERING -- §3.1's leading
///                                  `est_original`, which §11 calibrates
///                                  actual/est against, rewritten in place)
/// ```
///
/// Those are verbatim the three axes D49 names, on one keystroke, and `due=`
/// reproduced them the same way before W-27 routed it. Routing gap 48's eight
/// keys shortened the list of second keys that do it; it could not empty the
/// list, because some forms are genuinely NOT on the wire and are named below.
///
/// So a MIXED command is refused. One invocation now has one writer by
/// construction rather than by which keys happen to be routed: the kernel's
/// bytes, the host's bytes, or a refusal that names the form that is not on
/// the wire. Nothing silently writes the other one's answer.
enum EditRoute {
    /// Every change is on the kernel's wire: the one proven setter writes.
    Kernel(Vec<KCmd>),
    /// No change is: the old Rust path writes, and no wired key rides along.
    Host,
    /// Some are and some are not.
    Mixed {
        /// A wired change, by the spelling the user typed.
        wired: String,
        /// An unwired one.
        unwired: String,
        /// Why it is not on the wire -- a property of the WIRE or of the
        /// LINE, never "this host declined to route it".
        why: &'static str,
    },
}

/// Why `key` is not on the kernel's edit wire for `line`, or `None` if it is.
///
/// Every arm is a form the wire does not CARRY. That is the whole difference
/// between this function and the list it replaces: `due at win every on-event
/// after loc waiting` were unrouted for eight steps because a second name list
/// had not been updated, and that is the defect D49 closed. What is left is
/// structural, and each one says which README gap records the stance.
fn unwired_reason(line: &ItemLine, key: &str, unset: bool) -> Option<&'static str> {
    if !KERNEL_EDIT_KEYS.contains(&key) {
        return Some(match key {
            "title" | "p" | "state" => {
                "a positional slot of §4.1's line grammar, and no `Field.Key` at all"
            }
            "demoted" => "kept off the wire by the kernel's own policy (`keyNotWired demoted`, \
                          Negative.lean CHEAT 45, gap 40)",
            _ => "not a key the kernel's field grammar spells (the kernel refuses it by name, \
                  `unknownKey`; `--set` is the documented way to write a raw token)",
        });
    }
    if key == "ci" {
        if unset {
            return Some("a complete unset clears the positional digit too, which is §4.1 line \
                         surgery the wire does not carry (gap 41)");
        }
        if line.get("ci").is_none() {
            return Some("this line's ci is the positional digit, and the wire writes the `ci:` \
                         key slot, which would leave `tm check` saying `ci given twice` (gap 41)");
        }
    }
    None
}

/// The wire commands for a `tm edit` invocation, when **every** requested
/// change is one the kernel path carries -- else [`EditRoute::Mixed`] if any
/// change is wired and any is not, and [`EditRoute::Host`] if none is. An
/// `est=` pair is sent as the `est` op with the value AS WRITTEN and the block
/// length, and the kernel's reader is the only one on this path (W-36 track T
/// deleted the host's `Dur` pre-parse, so `est=zzz` is `kernel refusal:
/// badValue est`; an id-less line never reaches this route and its `est=`
/// still runs the host's reader and writer in `apply_pair`, README gap 3135):
/// since W-35 (the owner's D56) the kernel writes a leading
/// estimate that is the slot in place, as written — `30b` becomes `20b`, one
/// estimate on the line — and an `est:` token in canonical minutes, the bytes
/// the minutes form always wrote. Every other wired pair rides raw -- the
/// kernel's field grammar is the one reader -- and an empty value (or
/// `--unset <key>`) is the wire's unset form.
///
/// `--set` is counted as unwired here rather than gating the whole call, for
/// the same reason: `tm edit ^a1 cap=3h/d --set zz=1` wrote the host's `cap:`
/// alias before this, and now refuses.
fn edit_route(ctx: &Ctx, id: &Id, args: &super::EditArgs) -> Result<EditRoute, CliError> {
    let line = ctx.line(id)?;
    let mut wired: Vec<String> = Vec::new();
    let mut unwired: Option<(String, &'static str)> = None;
    let mut note = |w: Option<(String, &'static str)>, spelling: String| match w {
        Some((_, why)) => {
            if unwired.is_none() {
                unwired = Some((spelling, why));
            }
        }
        None => wired.push(spelling),
    };
    for pair in &args.pairs {
        let (k, v) = split_pair(pair)?;
        let why = unwired_reason(&line, k, v.is_empty());
        note(why.map(|w| (pair.clone(), w)), pair.clone());
    }
    for k in &args.unset {
        let why = unwired_reason(&line, k, true);
        note(why.map(|w| (format!("--unset {k}"), w)), format!("--unset {k}"));
    }
    for pair in &args.set {
        note(
            Some((
                format!("--set {pair}"),
                "a raw verbatim `key:value` token by its own contract, which the kernel would \
                 canonicalize",
            )),
            format!("--set {pair}"),
        );
    }
    if let Some((unwired, why)) = unwired {
        return Ok(match wired.first() {
            Some(w) => EditRoute::Mixed {
                wired: w.clone(),
                unwired,
                why,
            },
            None => EditRoute::Host,
        });
    }
    let mut cmds = Vec::new();
    for pair in &args.pairs {
        let (k, v) = split_pair(pair)?;
        cmds.push(if k == "est" && !v.is_empty() {
            // The value rides AS WRITTEN beside the block length its `b`
            // means, and the kernel — the one writer (D49) and, since W-36,
            // the ONE READER (README gap 2929) — reads it with its own grammar,
            // bounded by the host's `u32` (`Look.maxPlanMinutes`), and writes
            // the slot the view reads (D56, README gap 2572). The host used to
            // run its own `Dur::parse_no_days` first: a second reader of one
            // value, and the one whose `u32` width was the only thing standing
            // between `est=4294967296m` and a line the host cannot read back.
            // A value the kernel refuses is `badValue est`, and
            // [`edit_kernel`] puts the value typed into the document beside it.
            KCmd::Est {
                id: id.to_string(),
                value: v.to_string(),
                block_min: ctx.block_min(),
            }
        } else {
            KCmd::EditKey {
                id: id.to_string(),
                key: k.to_string(),
                value: v.to_string(),
            }
        });
    }
    for k in &args.unset {
        cmds.push(KCmd::EditKey {
            id: id.to_string(),
            key: k.clone(),
            value: String::new(),
        });
    }
    Ok(EditRoute::Kernel(cmds))
}

/// **The value a `badValue <k>` refusal refused, put back beside it** (W-36
/// track T, README gap 2929). The kernel's refusal names the key it read
/// (`detail.key`, the spelling the host sent); the host knows the text it sent
/// for that key, so the `--json` document keeps carrying both things a caller
/// wants to fix — which field and which text — as the host's own `invalid`
/// document did while the host still pre-parsed `est=`. Nothing is re-read:
/// the value is the pair exactly as typed.
fn with_the_value_typed(e: CliError, pairs: &[String]) -> CliError {
    let CliError::Kernel(mut issue) = e else {
        return e;
    };
    if issue.name == "badValue" {
        let key = issue
            .detail
            .get("key")
            .and_then(serde_json::Value::as_str)
            .map(str::to_string);
        let typed = key.and_then(|k| {
            pairs
                .iter()
                .filter_map(|p| split_pair(p).ok())
                .find(|(pk, _)| *pk == k)
                .map(|(_, v)| v.to_string())
        });
        if let Some(v) = typed {
            issue.message = format!("{} (the value was {v:?})", issue.message);
            issue
                .detail
                .insert("value".to_string(), serde_json::Value::String(v));
        }
    }
    CliError::Kernel(issue)
}

/// The kernel-backed keyed edit: every wired `k=v` and `--unset k` of one
/// `tm edit` invocation in one request through the choke point.
///
/// Observable changes from the old Rust path, recorded in kernel/README.md's
/// 2026-09-12 blocks: the accepted value lands as the field's **canonical
/// rendering** (`est=045m` → `est:45m`, `cap=2b/d` → `max:…`); `ci=` writes
/// the `ci:` key token — which both readers give precedence — instead of
/// rewriting the positional digit; `est=` writes the slot the view reads —
/// since W-35 (D56) a leading estimate with no `est:` token beside it is
/// rewritten in place as written (`30b` → `20b`), a line with no estimate
/// gains an `est:` token, and the leading estimate is never invented; a bad value and an
/// unset of an absent key are refused **by name** (`badValue <k>`, `keyAbsent`) where the
/// old path wrote silently or raised its own free text.  A line carrying a tab was refused
/// by name as well until W-42, when the owner's D83 made a tab the kernel's separator as it
/// is this host's, and the line is edited as the host would edit it.
fn edit_kernel(
    ctx: &mut Ctx,
    id: &Id,
    item: &tm_core::model::Item,
    args: &super::EditArgs,
    cmds: Vec<KCmd>,
) -> Result<i32, CliError> {
    let line_before = item.line();
    // What each change replaces: `est` reads whichever of the two slots
    // `remaining` reads (the `est:` token, else the leading estimate —
    // §4.1); `ci` reads the item's effective ci; every other key its token.
    let from_of = |k: &str| -> String {
        match k {
            "est" => match line_before.get("est") {
                Some(v) => v.to_string(),
                None => item
                    .est_original
                    .as_ref()
                    .map(|x| x.to_string())
                    .unwrap_or_default(),
            },
            "ci" => item.ci.to_string(),
            other => line_before.get(other).unwrap_or_default().to_string(),
        }
    };
    let mut changes = Vec::new();
    for pair in &args.pairs {
        let (k, v) = split_pair(pair)?;
        changes.push(FieldChange {
            field: k.to_string(),
            from: from_of(k),
            to: v.to_string(),
        });
    }
    for k in &args.unset {
        changes.push(FieldChange {
            field: k.clone(),
            from: from_of(k),
            to: String::new(),
        });
    }
    let rec = Recorder::start(ctx, "edit")?;
    let applied = kernel_bridge::apply(ctx, "edit", &cmds)
        .map_err(|e| with_the_value_typed(e, &args.pairs))?;
    for c in &changes {
        ctx.append_event(Event::Edit {
            id: id.to_string(),
            field: c.field.clone(),
            from: c.from.clone(),
            to: c.to.clone(),
        })?;
    }
    let line = applied
        .line_of(id.as_str())
        .map(|(_, l)| l)
        .unwrap_or_else(|| line_before.to_string());
    ctx.reload()?;
    rec.finish(ctx, format!("edit {}", id.token()))?;

    let out = EditOut {
        id: id.clone(),
        changes,
        line,
        // The kernel edit path is reached only when the item already carries an
        // `^id` (`item.has_id()` above), so there is never a box to pay for.
        assigned: None,
    };
    emit(ctx.json, || out.line.clone(), &out)?;
    Ok(0)
}

/// `tm move --json` / `tm readopt --json`.
#[derive(Debug, Serialize)]
pub struct MoveOut {
    /// The item.
    pub id: Id,
    /// The file it left.
    pub from: String,
    /// The file it landed in.
    pub to: String,
}

/// `tm move ^id <backlog|month|week|day>`.
///
/// Kernel-backed (kernel/README.md, 2026-09-12 "the five lifecycle verbs"):
/// the whole tree goes through [`kernel_bridge::apply`], and a destination
/// file that already holds a line with this id — a standing `[-]` tombstone
/// included — is refused by name (`occupied`) instead of silently gaining a
/// second copy. That refusal is A6 closed in the shipped binary: the
/// pre-stage-0 `move_to` appended without ever asking.
///
/// An id-less routine/optional line is invisible to the kernel (gap 5), so
/// those stay on the old Rust path, by name in the README block.
pub fn move_item(g: &Globals, args: &super::MoveArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    let item = ctx.item(&id)?.clone();
    let to = horizon_arg(&ctx, &args.to)?;
    if !item.has_id() {
        // Old path: the kernel cannot address a line without a `^id`.
        let section = args.section.clone().or_else(|| match to {
            Horizon::Day(_) => Some(horizon::PINNED_SECTION.to_string()),
            _ => None,
        });
        kernel_bridge::gate(&ctx, "move")?;
        let rec = Recorder::start(&ctx, "move")?;
        let moved = horizon::move_item(&ctx.hz(), &id, &to, section.as_deref())?;
        ctx.reload()?;
        rec.finish(&ctx, format!("move {} → {}", id.token(), moved.to))?;
        let out = MoveOut {
            id: moved.id,
            from: moved.from,
            to: moved.to,
        };
        emit(
            ctx.json,
            || format!("{} {} → {}", out.id.token(), out.from, out.to),
            &out,
        )?;
        return Ok(0);
    }
    // The kernel places a moved line itself (at a fresh rank in the
    // destination); it has no section parameter, so `--section` cannot be
    // honoured on the kernel path and is refused rather than ignored
    // (kernel/README.md, 2026-09-12 block).
    if args.section.is_some() {
        return Err(CliError::msg(
            "--section is not supported by the kernel-backed move: the kernel places the \
             line itself (kernel/README.md, stage-3 wiring block)",
        ));
    }
    let to_path = to.path();
    let from = item.src.file.clone();
    let rec = Recorder::start(&ctx, "move")?;
    kernel_bridge::apply(
        &ctx,
        "move",
        &[KCmd::Move {
            id: id.to_string(),
            to: to_path.clone(),
        }],
    )?;
    ctx.append_event(Event::Move {
        id: id.to_string(),
        from: from.clone(),
        to: to_path.clone(),
    })?;
    ctx.reload()?;
    rec.finish(&ctx, format!("move {} → {}", id.token(), to_path))?;

    let out = MoveOut {
        id: id.clone(),
        from,
        to: to_path,
    };
    emit(
        ctx.json,
        || format!("{} {} → {}", out.id.token(), out.from, out.to),
        &out,
    )?;
    Ok(0)
}

/// `tm rank --json`.
#[derive(Debug, Serialize)]
pub struct RankOut {
    /// The item.
    pub id: Id,
    /// The 1-based position asked for.
    pub n: usize,
    /// Whether the line actually moved.
    pub moved: bool,
}

/// The rotation a kernel-backed `tm rank ^id n` compiles to: a sequence of
/// `rank{id,rank}` wire ops (kernel ranks are line indices; the kernel
/// refuses a taken one, `badHorizon`). `None` when a line in the rotation
/// carries no `^id` the kernel can address (gap 5 — the old path takes the
/// whole reorder); `Some((vec![], false))` when the item already sits at the
/// clamped position (the old path's `moved: false`), and `Some((vec![], true))`
/// when only `[-]` records stand between it and that position, which keep their
/// lines (P91), so no line moves.
fn rank_cmds(
    ctx: &Ctx,
    id: &Id,
    path: &str,
    n: usize,
) -> Result<Option<(Vec<KCmd>, bool)>, CliError> {
    let parsed = ctx.store.read_file(path)?;
    let idx = text_edit::find_line(&parsed, id)
        .ok_or_else(|| CliError::NotFound(id.clone()))?;
    let (start, end) = text_edit::section_range(&parsed, idx);
    // The section's item slots, as kernel ranks: a parsed line's index *is*
    // its rank (the loader assigns rank = line index; front matter and
    // prose included).
    let slots: Vec<usize> = (start..end)
        .filter(|&i| parsed.lines[i].item().is_some())
        .collect();
    let pos = slots
        .iter()
        .position(|&i| i == idx)
        .ok_or_else(|| CliError::NotFound(id.clone()))?;
    let target = n.max(1).min(slots.len()) - 1;
    if target == pos {
        return Ok(Some((Vec::new(), false)));
    }
    let id_at = |i: usize| -> Option<String> {
        parsed.lines[i]
            .item()
            .filter(|it| it.has_id())
            .map(|it| it.id.to_string())
    };
    // **A tombstone keeps its line** (README gap 4502, the W-43 repair, parity
    // **P91**). A `[-]` line whose item lives in ANOTHER file is the archive
    // half of a demotion pair (§6.3): the kernel's `rank{id}` moves an item's
    // LIVE line, so a rotation that sent this line's id a rank in this file
    // moved the other file's live line instead, and the kernel refused the
    // whole reorder `badHorizon` — driven: `tm demote ^t4` then `tm rank ^t5 1`
    // on a fresh example tree, exit 1, nothing written. The position `n` still
    // counts every item line of the section, as fork 4748911's `horizon::rank`
    // counts them; the live lines take the live slots in the fork's resulting
    // order, and a tombstone stays where it stood, as interleaved prose does.
    let tombstone = |i: usize| -> bool {
        parsed.lines[i]
            .item()
            .filter(|it| it.has_id())
            .and_then(|it| ctx.tree.get(&it.id))
            .is_some_and(|live| live.src.file != path)
    };
    // The fork's order: the moved line taken out and put back at `target`.
    let mut order: Vec<usize> = slots.clone();
    let moved = order.remove(pos);
    order.insert(target, moved);
    let live_slots: Vec<usize> = slots.iter().copied().filter(|&i| !tombstone(i)).collect();
    let live_order: Vec<usize> = order.into_iter().filter(|&i| !tombstone(i)).collect();
    // Where each live line goes: the k-th live line of the new order takes the
    // k-th live slot. A line that stays needs no command.
    let to: std::collections::BTreeMap<usize, usize> = live_order
        .iter()
        .zip(&live_slots)
        .filter(|(from, dest)| from != dest)
        .map(|(&from, &dest)| (from, dest))
        .collect();
    if to.is_empty() {
        return Ok(Some((Vec::new(), true)));
    }
    let mut ids = std::collections::BTreeMap::new();
    for &from in to.keys() {
        match id_at(from) {
            Some(i) => {
                ids.insert(from, i);
            }
            None => return Ok(None),
        }
    }
    // Past every possible rank: a file of L parsed lines splits into at
    // most L+1 kernel lines (the trailing newline's empty segment), so
    // ranks 0..=L can be taken and L+2 never is.
    let temp = (parsed.lines.len() + 2) as u64;
    // Each cycle of the permutation in turn: its first line steps out to the
    // free rank, each line whose destination is the slot just vacated steps in,
    // and the first line takes the last slot freed — every step onto a free
    // rank, which is all the kernel asks.
    let from_of: std::collections::BTreeMap<usize, usize> = to.iter().map(|(&f, &d)| (d, f)).collect();
    let mut done = std::collections::BTreeSet::new();
    let mut cmds = Vec::new();
    for &first in to.keys() {
        if done.contains(&first) {
            continue;
        }
        cmds.push(KCmd::Rank {
            id: ids[&first].clone(),
            rank: temp,
        });
        done.insert(first);
        let mut cur = first;
        loop {
            let next = from_of[&cur];
            if next == first {
                cmds.push(KCmd::Rank {
                    id: ids[&first].clone(),
                    rank: cur as u64,
                });
                break;
            }
            cmds.push(KCmd::Rank {
                id: ids[&next].clone(),
                rank: cur as u64,
            });
            done.insert(next);
            cur = next;
        }
    }
    Ok(Some((cmds, false)))
}

/// `tm rank ^id <n>` — rank is line order (§7.4).
///
/// Kernel-backed (kernel/README.md, 2026-09-12 "rank, add and the keyed
/// edit" block). The wire op is `rank{id,rank}` with a **raw document
/// rank** (a line index), and the kernel refuses a taken rank
/// (`badHorizon`) rather than renumbering the file — so the host rotates:
/// the moved line goes to the one always-free rank past the end of the
/// file, the items between old and new position each step into the rank
/// their neighbour just vacated, and the moved line takes the freed target
/// rank, all in one atomic request. Observable changes from the old Rust
/// path, recorded in that README block: items rotate through the section's
/// *item* slots while interleaved prose keeps its own line (the old path
/// reinserted the line and shifted the prose); and a file whose sections
/// refuse an item at the end of the file (a day file whose `# Pinned` is
/// not last) refuses the whole reorder `badHorizon`, because the rotation's
/// temporary rank sits there. Id-less lines — the moved one or any line it
/// must rotate through — stay on the old path (gap 5).
pub fn rank(g: &Globals, args: &super::RankArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    let item = ctx.item(&id)?.clone();
    if item.has_id() {
        if let Some((cmds, records_only)) = rank_cmds(&ctx, &id, &item.src.file, args.n)? {
            if cmds.is_empty() {
                // Already at the requested position — the old path's
                // `moved: false`: no kernel call, nothing written, but the
                // undo entry still recorded, exactly as before. Gated anyway
                // (D35): this arm reports success, and a verb must not report
                // success on a tree every reading verb refuses.
                kernel_bridge::gate(&ctx, "rank")?;
                let rec = Recorder::start(&ctx, "rank")?;
                ctx.reload()?;
                rec.finish(&ctx, format!("rank {} {}", id.token(), args.n))?;
                let out = RankOut {
                    id: id.clone(),
                    n: args.n,
                    moved: false,
                };
                emit(
                    ctx.json,
                    || {
                        if records_only {
                            format!(
                                "{} stays: only `[-]` records stand between it and position {}, and a record keeps its line",
                                out.id.token(),
                                out.n
                            )
                        } else {
                            format!("{} already at position {}", out.id.token(), out.n)
                        }
                    },
                    &out,
                )?;
                return Ok(0);
            }
            let rec = Recorder::start(&ctx, "rank")?;
            kernel_bridge::apply(&ctx, "rank", &cmds)?;
            ctx.reload()?;
            rec.finish(&ctx, format!("rank {} {}", id.token(), args.n))?;
            let out = RankOut {
                id: id.clone(),
                n: args.n,
                moved: true,
            };
            emit(
                ctx.json,
                || format!("{} → position {}", out.id.token(), out.n),
                &out,
            )?;
            return Ok(0);
        }
    }
    kernel_bridge::gate(&ctx, "rank")?;
    let rec = Recorder::start(&ctx, "rank")?;
    let moved = horizon::rank(&ctx.hz(), &id, args.n)?;
    ctx.reload()?;
    rec.finish(&ctx, format!("rank {} {}", id.token(), args.n))?;

    let out = RankOut {
        id: id.clone(),
        n: args.n,
        moved,
    };
    emit(
        ctx.json,
        || {
            if moved {
                format!("{} → position {}", out.id.token(), out.n)
            } else {
                format!("{} already at position {}", out.id.token(), out.n)
            }
        },
        &out,
    )?;
    Ok(0)
}

/// `tm demote --json`.
#[derive(Debug, Serialize)]
pub struct DemoteOut {
    /// The item.
    pub id: Id,
    /// The remaining estimate carried (§6.3).
    pub est_min: u32,
    /// Its stamps afterwards.
    pub stamps: Vec<String>,
}

/// `tm demote ^id` (§6.3).
///
/// Kernel-backed (kernel/README.md, 2026-09-12 "the five lifecycle verbs").
/// The host resolves the destination — `month/<current>` — and the stamp
/// period (the item's week number); the kernel writes the tombstone and the
/// stamped copy. An item that already has a standing `# Demoted` record is
/// merged into it — stamps merged, the record's `est:` kept as a floor under a
/// line with no estimate of its own — as fork-point `demote_one` did
/// (kernel/README.md gap 53). It refuses by name: `alreadyDemoted` for a `[-]`
/// record demoted again or an item whose other line is a `[-]` outside a
/// month's `# Demoted`, `badHorizon` when the copy cannot land where the
/// month file's sections allow.
pub fn demote(g: &Globals, args: &super::IdArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    let item = ctx.item(&id)?.clone();
    let Horizon::Week(week) = item.horizon else {
        // The same refusal the old path raised: only week items demote.
        return Err(CliError::Horizon(horizon::HorizonError::Horizon {
            id: id.clone(),
            horizon: item.horizon.to_string(),
            message: "only week items are demoted (use `tm move`)".to_string(),
        }));
    };
    let month = YearMonth::from_date(ctx.today);
    let month_path = Horizon::Month(month).path();
    let rec = Recorder::start(&ctx, "demote")?;
    let applied = kernel_bridge::apply(
        &ctx,
        "demote",
        &[KCmd::Demote {
            id: id.to_string(),
            to: month_path.clone(),
            period: week.week,
        }],
    )?;
    // The copy the kernel wrote carries the record: its `est:` (or, when it
    // has none, its leading estimate) is the remaining the demotion
    // carries, and its `demoted:` value is the stamp list.
    let copy = applied.line_in(&month_path, id.as_str()).unwrap_or_default();
    let (est_min, stamps) = demote_record(&ctx, &copy);
    ctx.append_event(Event::Demote {
        id: id.to_string(),
        from: week.to_string(),
        to: month.to_string(),
        est_min,
    })?;
    ctx.reload()?;
    rec.finish(&ctx, format!("demote {}", id.token()))?;

    let out = DemoteOut {
        id: id.clone(),
        est_min,
        stamps,
    };
    emit(
        ctx.json,
        || {
            format!(
                "demoted {} · est {}m · {}",
                out.id.token(),
                out.est_min,
                out.stamps.join(",")
            )
        },
        &out,
    )?;
    Ok(0)
}

/// What the archive copy the kernel wrote records: the remaining estimate
/// it carries (`est:`, else the leading estimate — `est:` overrides the
/// leading one, §4.1) in minutes, and its `demoted:` stamps. Read through
/// the same §4.1 parser the tree uses, so there is one reader.
fn demote_record(ctx: &Ctx, copy: &str) -> (u32, Vec<String>) {
    let pctx = ParseCtx {
        horizon: Horizon::Month(YearMonth::from_date(ctx.today)),
        ..ParseCtx::new("month", ctx.block_min())
    };
    match grammar::parse_line(copy, &pctx) {
        Ok(item) => (
            item.est
                .as_ref()
                .or(item.est_original.as_ref())
                .map(|d| d.as_minutes())
                .unwrap_or(0),
            item.stamps.demoted.iter().map(|s| s.to_string()).collect(),
        ),
        Err(_) => (0, Vec::new()),
    }
}

/// Remove the `[-]` line a `tm demote` left behind when the readopt has just
/// brought the stamped archive copy back into the *same* file.
///
/// `tm demote ^id` marks the week line `[-]` and copies it to
/// `month/…# Demoted`; `tm readopt ^id` moves that copy into the current
/// week. Within one week that is the file the `[-]` line is still in, and
/// `tm_core::horizon::readopt` does not remove it — the id would then be on
/// two lines and `tm check` would exit 2 (§17 M9: the tree must pass
/// `tm check`). §6.3 makes the stamped copy the record, so the stale `[-]`
/// line is the one that goes. Upstream fix: `horizon::readopt`.
fn drop_stale_demotion(ctx: &Ctx, id: &Id, path: &str) -> Result<(), CliError> {
    let parsed = ctx.store.read_file(path)?;
    let stale: Vec<usize> = parsed
        .lines
        .iter()
        .enumerate()
        .filter(|(i, l)| {
            l.item()
                .is_some_and(|it| Tree::key_of(it) == *id && it.state == State::Demoted)
                && !text_edit::is_demoted(&parsed, *i)
        })
        .map(|(i, _)| i)
        .collect();
    // Only when the readopted line is really a second copy in this file.
    let live = parsed
        .items()
        .filter(|it| Tree::key_of(it) == *id)
        .count();
    if stale.is_empty() || live < 2 {
        return Ok(());
    }
    let idx = stale[0];
    ctx.store
        .modify_file(path, &mut |parsed: &grammar::ParsedFile| {
            if parsed.lines.len() <= idx {
                return Ok(None);
            }
            Ok(Some(text_edit::remove_line(parsed, idx).0))
        })?;
    Ok(())
}

/// `tm readopt ^id [--to week]` (§6.3).
///
/// Kernel-backed (kernel/README.md, 2026-09-12 "the five lifecycle verbs"):
/// the kernel takes the demoted record into `to`, flips `[-]` back to `[ ]`
/// keeping its stamps, and removes the tombstone — so the same-week readopt
/// leaves one line without the old path's stale-copy cleanup. An id whose
/// live line is not demoted — including §4.3's shipped `[ ]`-beside-`[-]`
/// pair, which the old path *absorbed* — is refused by name (`notDemoted`),
/// and nothing is written.
pub fn readopt(g: &Globals, args: &super::ReadoptArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    let item = ctx.item(&id)?.clone();
    let to = match &args.to {
        Some(s) => horizon_arg(&ctx, s)?,
        None => Horizon::Week(IsoWeek::from_date(ctx.today)),
    };
    if !item.has_id() {
        // Old path: the kernel cannot address a line without a `^id`.
        kernel_bridge::gate(&ctx, "readopt")?;
        let rec = Recorder::start(&ctx, "readopt")?;
        let moved = horizon::readopt(&ctx.hz(), &id, Some(&to))?;
        ctx.reload()?;
        drop_stale_demotion(&ctx, &id, &moved.to)?;
        ctx.reload()?;
        rec.finish(&ctx, format!("readopt {}", id.token()))?;
        let out = MoveOut {
            id: moved.id,
            from: moved.from,
            to: moved.to,
        };
        emit(
            ctx.json,
            || format!("readopted {} → {}", out.id.token(), out.to),
            &out,
        )?;
        return Ok(0);
    }
    let to_path = to.path();
    let rec = Recorder::start(&ctx, "readopt")?;
    let applied = kernel_bridge::apply(
        &ctx,
        "readopt",
        &[KCmd::Readopt {
            id: id.to_string(),
            to: to_path.clone(),
        }],
    )?;
    // The file the record left: the changed document that lost the id (the
    // dest may lose the tombstone and gain the live line, so it still
    // carries the id and is skipped).
    let from = applied
        .lost_id(id.as_str(), &to_path)
        .unwrap_or_else(|| item.src.file.clone());
    ctx.append_event(Event::Readopt { id: id.to_string() })?;
    ctx.reload()?;
    rec.finish(&ctx, format!("readopt {}", id.token()))?;

    let out = MoveOut {
        id: id.clone(),
        from,
        to: to_path,
    };
    emit(
        ctx.json,
        || format!("readopted {} → {}", out.id.token(), out.to),
        &out,
    )?;
    Ok(0)
}

/// `tm drop --json`.
#[derive(Debug, Serialize)]
pub struct DropOut {
    /// The item.
    pub id: Id,
    /// The line afterwards.
    pub line: String,
    /// **The `^id` this drop wrote onto a title-keyed line** (D33, gap 477),
    /// when it wrote one. `None` for a line that already carried an id.
    ///
    /// D33's accepted cost is a token in the user's Markdown that they did not
    /// type, and "deliberately and **visibly**" is half the decision — so the
    /// token is named in the answer rather than found later in a diff.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assigned: Option<Id>,
}

/// **A verb that puts a state box on a title-keyed line writes its `^id`
/// first** — the owner's **D33**, gap 477.
///
/// Since D31 a box-less, id-less line is a real entity keyed by its **title**.
/// Putting a box on it makes it a *tracked* item, and a tracked item needs an
/// id that survives the user editing its title: without one, `tm drop lunch`
/// wrote `- [~] lunch …`, which the kernel's own grammar then refuses
/// (`PErr.noId`, `Negative.lean` cheat 174), so one documented one-word command
/// bricked every kernel-backed verb on the tree.
///
/// **Cheat 174 stays, and D33 follows D31 rather than bending it**: the kernel
/// still never invents an id for a line the user marked as tracked. The *host*
/// writes it, deliberately and visibly — and the accepted cost is a token in
/// the user's Markdown that they did not type.
///
/// The id is generated the way `--fix-ids` generates one ([`id_gen`] +
/// [`IdGen::next_id`] against every id in the tree) and written the way
/// `--fix-ids` writes one ([`ItemLine::append_id`], through
/// [`Store::modify_file`] so a concurrent save is merged rather than
/// clobbered). There is no second answer to "how is an id put on a line"
/// (AGENTS §5.3). Only **this** line is touched: `check::fix_ids` deliberately
/// assigns nothing in `routines.md`, `optional.md` or `inbox.md`
/// (`needs_id_in`'s `allows_missing_state`), and that stays true — those files
/// gain an id only for the one line a verb is about to box.
///
/// Call it **after** `Recorder::start`, so `tm undo` takes the token back off
/// with the box it was written for.
///
/// Returns the id the line now carries, and leaves `ctx` reloaded — so the
/// caller's `Item` is stale and the line is addressed by the returned id.
fn write_id_for_boxing(ctx: &mut Ctx, key: &Id, salt: &str) -> Result<Id, CliError> {
    let item = ctx.item(key)?;
    let (path, line) = (item.src.file.clone(), item.src.line);
    let mut taken: std::collections::HashSet<String> = ctx
        .files
        .files
        .iter()
        .flat_map(grammar::ParsedFile::items)
        .filter(|i| i.has_id())
        .map(|i| i.id.as_str().to_string())
        .collect();
    let id = id_gen(ctx, salt).next_id(&mut taken);
    let key = key.clone();
    let assign = id.clone();
    ctx.store.modify_file(&path.clone(), &mut |parsed: &grammar::ParsedFile| {
        let mut next = parsed.clone();
        let Some(target) = next
            .items_mut()
            .find(|i| i.src.line == line && Tree::key_of(i) == key)
        else {
            // The file moved under us between the load and the write; the
            // caller's own read is what then fails, by name.
            return Ok(None);
        };
        target.src.tokens.append_id(&assign);
        target.id = assign.clone();
        Ok(Some(next.to_text()))
    })?;
    ctx.reload()?;
    Ok(id)
}

/// **One spelling of "this line just gained an `^id`"** (AGENTS §5.3, README
/// gap 991).
///
/// `tm drop <title>` and `tm edit <title> state=…` are the two verbs D33 lets
/// box a box-less, id-less line, and each spelled the consequence its own way
/// — `dropped ^x — a state box makes it…` and `(a state box makes it…)`. Two
/// sentences for one concept, and neither was pinned by a test.
///
/// It now says the two things a user is about to need and neither spelling
/// said. **The title stops being an address**: D31 keys a line by its title
/// only while it carries no `^id`, so after the box `tm drop laundry`, `tm
/// edit laundry ci=3`, `tm routine done laundry` and `tm skip laundry` all
/// refuse the title — driven, all four, and *both* boxing verbs leave exactly
/// that state, which is why gap 991's "two verbs disagree" is refuted rather
/// than repaired. And **a boxed routine stops recurring**: on one tree at one
/// instant, `tm plan` scheduled `laundry 30m` at 09:20 before the box and
/// nothing at all after it.
///
/// The recurrence clause is keyed on `routines.md` and not on the boxing,
/// because recurrence is that file's: an `optional.md` or week line gains an
/// id and loses a title, and that is the whole of what happened to it.
fn boxed_note(was: &Id, assigned: &Id, file: &str) -> String {
    let mut note = format!(
        "a state box makes it a tracked item, so {} was written on the line, and `{}` addressed \
         it only while it carried no `^id` (D31)",
        assigned.token(),
        was.as_str()
    );
    if matches!(Horizon::from_path(file), Some(Horizon::Routine)) {
        note.push_str(
            "; a routine line with a box does not recur, so `tm routine done`, `tm skip` and \
             `tm plan` no longer see an instance of it — `tm undo` puts the line back",
        );
    }
    note
}

/// `tm drop ^id`, or `tm drop <title>` for a line D31 keys by its title.
///
/// Kernel-backed (kernel/README.md, 2026-09-12 "the five lifecycle verbs"):
/// the kernel rewrites the item's live line to `[~]` and refuses an
/// unloadable tree by name.
///
/// **D33, gap 477**: a title-keyed line gets its `^id` written first
/// ([`write_id_for_boxing`]), because the drop is about to box it. The box
/// itself still goes on through `horizon::drop_item`, because the kernel does
/// not add a box to a line that has none — `Plan.boxesWf` refuses the result
/// and the request comes back `badHorizon` (driven: a `routines.md` line
/// carrying an `^id` and no box is refused on the kernel path today, which is
/// **gap 531**). What D33 changes is that the line the host writes is one the
/// kernel can read back.
pub fn drop_item(g: &Globals, args: &super::IdArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let key = Ctx::key(&args.id);
    let item = ctx.item(&key)?.clone();
    let rec = Recorder::start(&ctx, "drop")?;
    let boxed_in = item.src.file.clone();
    let (id, line, assigned) = if item.has_id() {
        let applied = kernel_bridge::apply(&ctx, "drop", &[KCmd::Drop { id: key.to_string() }])?;
        ctx.append_event(Event::Drop { id: key.to_string() })?;
        let line = applied
            .line_of(key.as_str())
            .map(|(_, l)| l)
            .unwrap_or_else(|| item.line().to_string());
        (key, line, None)
    } else {
        // D33: the box and the id land together, in that order — and the gate
        // goes ahead of both, because this branch never reaches the kernel.
        kernel_bridge::gate(&ctx, "drop")?;
        let was = key.clone();
        let id = write_id_for_boxing(&mut ctx, &key, "drop")?;
        let line = horizon::drop_item(&ctx.hz(), &id)?;
        (id.clone(), line, Some((was, id)))
    };
    ctx.reload()?;
    rec.finish(&ctx, format!("drop {}", id.token()))?;

    let note = assigned
        .as_ref()
        .map(|(was, id)| boxed_note(was, id, &boxed_in));
    let out = DropOut {
        id: id.clone(),
        line,
        assigned: assigned.map(|(_, id)| id),
    };
    emit(
        ctx.json,
        || match &note {
            None => format!("dropped {}", out.id.token()),
            Some(note) => format!("dropped {} — {note}", out.id.token()),
        },
        &out,
    )?;
    Ok(0)
}

/// `tm event --json`.
#[derive(Debug, Serialize)]
pub struct EventOut {
    /// The event name.
    pub name: String,
    /// The item it was restricted to, if any.
    pub id: Option<String>,
    /// The `[?]` items it resolved (§5.1).
    pub resolved: Vec<Id>,
}

/// `tm event <name> [^id]` (§5.1, §5.5).
pub fn event(g: &Globals, args: &super::EventArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let only = args.id.as_deref().map(Ctx::key);
    if let Some(id) = &only {
        ctx.item(id)?;
    }
    kernel_bridge::gate(&ctx, "event")?;
    let rec = Recorder::start(&ctx, "event")?;
    ctx.append_event(Event::Named {
        name: args.name.clone(),
        id: only.as_ref().map(|i| i.to_string()),
    })?;

    let mut resolved = Vec::new();
    let targets: Vec<Id> = match &only {
        Some(id) => vec![id.clone()],
        None => ctx.tree.waiting_ids(),
    };
    for id in targets {
        let Some(item) = ctx.tree.get(&id) else {
            continue;
        };
        if item.state != State::Waiting || !recur::event_resolves(item, &args.name) {
            continue;
        }
        let mut line = item.line().clone();
        recur::on_event_arrived(item).apply(&mut line)?;
        ctx.store.write_line(&id, &line.to_string())?;
        resolved.push(id);
    }
    ctx.reload()?;
    rec.finish(&ctx, format!("event {}", args.name))?;

    let out = EventOut {
        name: args.name.clone(),
        id: only.map(|i| i.to_string()),
        resolved,
    };
    emit(
        ctx.json,
        || {
            if out.resolved.is_empty() {
                format!("event {} logged", out.name)
            } else {
                format!(
                    "event {} · resolved {}",
                    out.name,
                    out.resolved
                        .iter()
                        .map(|i| i.token())
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
        },
        &out,
    )?;
    Ok(0)
}

/// `tm skip --json` / `tm routine done --json`.
#[derive(Debug, Serialize)]
pub struct InstanceOut {
    /// The routine (its title, or an `^id`).
    pub item: String,
    /// The instance key (`2026-09-07` or `#3`).
    pub inst: String,
    /// `skipped` or `done`.
    pub status: String,
    /// Minutes it took, for a done.
    pub actual_min: Option<u32>,
}

/// The item and today's instance behind a routine argument.
fn instance_of(
    ctx: &Ctx,
    name: &str,
) -> Result<(tm_core::model::Item, tm_core::model::Instance), CliError> {
    let id = Ctx::key(name);
    // A routine is addressed by its title, so this is the path an ambiguous
    // title reaches first (W-16 repair, gap 576).
    ctx.refuse_ambiguous_title(&id)?;
    let item = ctx
        .tree
        .get(&id)
        .cloned()
        .ok_or_else(|| CliError::msg(format!("no such routine: {name}")))?;
    let insts = recur::today_instances(
        [&item],
        ctx.today,
        ctx.now_tz.naive_local(),
        &ctx.replay,
        &ctx.cfg,
    );
    let inst = insts
        .into_iter()
        .map(|(i, _)| i)
        .next()
        .ok_or_else(|| CliError::msg(format!("{name} has no instance today")))?;
    Ok((item, inst))
}

/// `tm skip <routine>` (§5.3).
pub fn skip(g: &Globals, args: &super::SkipArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let (item, inst) = instance_of(&ctx, &args.name)?;
    kernel_bridge::gate(&ctx, "skip")?;
    let rec = Recorder::start(&ctx, "skip")?;
    let entry = recur::skip_instance(&item, &inst, ctx.now);
    ctx.append_entry(&entry)?;
    ctx.reload()?;
    rec.finish(&ctx, format!("skip {}", args.name))?;

    let out = InstanceOut {
        item: Tree::key_of(&item).to_string(),
        inst: inst.key.to_string(),
        status: "skipped".to_string(),
        actual_min: None,
    };
    emit(
        ctx.json,
        || format!("skipped {} {}", out.item, out.inst),
        &out,
    )?;
    Ok(0)
}

/// `tm routine done <name> [--min 18]`.
pub fn routine(g: &Globals, args: &super::RoutineArgs) -> Result<i32, CliError> {
    let super::RoutineCmd::Done { name, min } = &args.cmd;
    let mut ctx = Ctx::load(g, true)?;
    let (item, inst) = instance_of(&ctx, name)?;
    kernel_bridge::gate(&ctx, "routine done")?;
    let rec = Recorder::start(&ctx, "routine")?;
    let entry = recur::done_instance(&item, &inst, ctx.now, *min);
    ctx.append_entry(&entry)?;
    ctx.reload()?;
    rec.finish(&ctx, format!("routine done {name}"))?;

    let out = InstanceOut {
        item: Tree::key_of(&item).to_string(),
        inst: inst.key.to_string(),
        status: "done".to_string(),
        actual_min: *min,
    };
    emit(
        ctx.json,
        || {
            format!(
                "{} {} done{}",
                out.item,
                out.inst,
                out.actual_min
                    .map(|m| format!(" ({m}m)"))
                    .unwrap_or_default()
            )
        },
        &out,
    )?;
    Ok(0)
}

/// One inbox line with its preview.
#[derive(Debug, Serialize)]
pub struct TriageLine {
    /// The line number in `inbox.md` (1-based).
    pub line: usize,
    /// The raw text.
    pub raw: String,
    /// The §4.1 line it would become.
    pub parsed: Option<String>,
    /// Why it does not parse, when it does not.
    pub problem: Option<String>,
}

/// `tm triage --json`.
#[derive(Debug, Serialize)]
pub struct TriageOut {
    /// The file read.
    pub file: String,
    /// One entry per capture line.
    pub lines: Vec<TriageLine>,
}

/// `tm triage` — the inbox with parse previews (§12.5, §14).
pub fn triage(g: &Globals) -> Result<i32, CliError> {
    let ctx = Ctx::load(g, true)?;
    let text = if ctx.store.exists("inbox.md") {
        ctx.store.read_text("inbox.md")?
    } else {
        String::new()
    };
    let pctx = ParseCtx::new("inbox.md", ctx.block_min());
    let mut lines = Vec::new();
    // §14: `tm init` fills `inbox.md` with its guidance inside one HTML
    // comment. Everything between `<!--` and `-->` is commentary, not
    // capture — previewing it would have `/triage` `tm add` the guidance.
    // The automaton is `grammar::comment_after`, which is `Plan.lean`'s, so
    // this screen, the TUI inbox and the parser cannot disagree about where a
    // comment ends (D47). This loop had its own copy until W-24.
    let mut in_comment = false;
    for (i, raw) in text.lines().enumerate() {
        let was_in_comment = in_comment;
        let opener = grammar::opens_comment(raw);
        in_comment = grammar::comment_after(in_comment, raw);
        if was_in_comment || opener {
            continue;
        }
        let trimmed = raw.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let candidate = if trimmed.starts_with("- ") {
            trimmed.to_string()
        } else {
            format!("- [ ] {trimmed}")
        };
        let (parsed, problem) = match grammar::parse_line(&candidate, &pctx) {
            Ok(item) => match grammar::format_item_line(&item) {
                Ok(text) => (Some(text), None),
                Err(e) => (Some(candidate.clone()), Some(e.to_string())),
            },
            Err(e) => (None, Some(e.to_string())),
        };
        lines.push(TriageLine {
            line: i + 1,
            raw: trimmed.to_string(),
            parsed,
            problem,
        });
    }
    let out = TriageOut {
        file: "inbox.md".to_string(),
        lines,
    };
    emit(
        ctx.json,
        || {
            if out.lines.is_empty() {
                return "inbox is empty".to_string();
            }
            out.lines
                .iter()
                .map(|l| match (&l.parsed, &l.problem) {
                    (Some(p), _) => format!("{:>3}  {}\n     {}", l.line, l.raw, p),
                    (None, Some(e)) => format!("{:>3}  {}\n     ! {}", l.line, l.raw, e),
                    _ => format!("{:>3}  {}", l.line, l.raw),
                })
                .collect::<Vec<_>>()
                .join("\n")
        },
        &out,
    )?;
    Ok(0)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::KERNEL_EDIT_KEYS;

    /// The kernel's own verdict on one `k:` spelling, asked through the FFI:
    /// `true` when the wire's `edit` op carries the key at all.
    ///
    /// `Boundary.lean`'s `edit` arm answers `unknownKey <k>` for a spelling
    /// `Field.Key.ofName?` does not know and `keyNotWired <k>` for a key the
    /// edit path excludes (`demoted` alone since gap 40's bridges); every
    /// other answer — `ok`, or a `badValue <k>` from the key's own field
    /// grammar — means the key IS carried. So the probe value need not be a
    /// legal value for the key, and deliberately is not: one value for all
    /// eighteen keeps this a question about ROUTING and not about grammars.
    fn kernel_carries_key(key: &str) -> bool {
        let req = json!({
            "docs": [{"path": "inbox.md", "lines": ["- [ ] 1 30m probe ^p1"]}],
            "cmds": [{"op": "edit", "id": "p1", "key": key, "value": "probe"}],
        });
        let raw = tm_kernel_ffi::call(&req.to_string()).expect("the kernel answered nothing");
        let resp: serde_json::Value =
            serde_json::from_str(&raw).unwrap_or_else(|e| panic!("not JSON ({e}): {raw}"));
        // **The refusal's two shapes, and the probe must read both.** A
        // request the kernel cannot DECODE answers with a bare string
        // (`{"err":"keyNotWired demoted"}`) — the edit arm of `parseCmd` runs
        // before any document is loaded — while a refusal from the loaded
        // plan answers with the object form (`{"err":{"kernel":…}}`). Reading
        // only the object form reported `demoted` as CARRIED, which is how
        // this comment came to exist.
        let err = match resp.get("err") {
            Some(serde_json::Value::String(s)) => s.clone(),
            Some(e) => e.get("kernel").and_then(|k| k.as_str()).unwrap_or_default().to_string(),
            None => String::new(),
        };
        !(err.starts_with("unknownKey") || err.starts_with("keyNotWired"))
    }

    /// **The routing table is derived, in both directions** (the owner's
    /// **D49**; README gap 48 was open from stage 3 to W-27).
    ///
    /// For every `key:` spelling the *loader* knows — `tm_core::grammar::KEYS`,
    /// the same list `parse_line` uses to decide a key is a key and not an
    /// `extra` — the host routes it to the kernel exactly when the kernel
    /// carries it. A key the kernel gains and this host does not route turns
    /// this red, which is the half that stayed silent for nineteen weeks: the
    /// kernel wired eight keys at `bf7cc63` and `KERNEL_EDIT_KEYS` was a name
    /// list nothing compared against.
    ///
    /// **Three things it cannot see**, and they are the reason this comment is
    /// longer than the test:
    ///
    /// 1. `grammar::KEYS` is itself a hand-written vocabulary (AGENTS §5.2).
    ///    A nineteenth spelling the KERNEL learns and the loader does not is
    ///    invisible here — the host could not read such a token back anyway,
    ///    so it is unroutable rather than unrouted, but this test does not
    ///    say so and cannot.
    /// 2. It asks whether the key is on the WIRE, not whether
    ///    [`edit_route`] routes a given *invocation*: `ci` is on the
    ///    list and is deliberately held back on a line whose ci is the
    ///    positional digit, and `--unset ci` is never routed (gap 41). The
    ///    list and the predicate are different facts and only the first is
    ///    checked here.
    /// 3. It drives one `inbox.md` line. A key whose acceptance depends on
    ///    the file kind or the item's shape — `due`/`at`/`win` on a month
    ///    outcome answer `badHorizon` (gap 50) — is counted as CARRIED, which
    ///    is the right answer for routing and says nothing about the refusal
    ///    the user meets.
    #[test]
    fn the_host_routes_every_key_the_kernel_wires() {
        let mut wrong = Vec::new();
        for key in tm_core::grammar::KEYS {
            let kernel = kernel_carries_key(key);
            let host = KERNEL_EDIT_KEYS.contains(key);
            if kernel != host {
                wrong.push(format!(
                    "{key}: the kernel {} it, KERNEL_EDIT_KEYS {} it",
                    if kernel { "carries" } else { "refuses" },
                    if host { "routes" } else { "does not route" },
                ));
            }
        }
        assert!(
            wrong.is_empty(),
            "the host's routing table and the kernel's wire disagree (D49, README gap 48):\n  {}",
            wrong.join("\n  ")
        );
    }

    /// The one key on neither side, named so the count above cannot drift into
    /// agreeing about nothing: `demoted` is excluded by the **kernel** and the
    /// host follows, and `tm_core::grammar::KEYS` does carry it, so the loop
    /// above really does visit a key it expects both to refuse.
    #[test]
    fn demoted_is_refused_by_the_kernel_and_unrouted_by_the_host() {
        assert!(tm_core::grammar::KEYS.contains(&"demoted"));
        assert!(!kernel_carries_key("demoted"));
        assert!(!KERNEL_EDIT_KEYS.contains(&"demoted"));
    }
}
