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
//!   reproducible). §10.1 has no `add` event; the line is logged as
//!   `edit{field:"add"}`.
//! * [`edit`] — `k=v` pairs plus `--set` / `--unset`, one `edit` event per
//!   field.
//! * [`event`] — §5.1: logs `event{name,id}` and flips every `[?]` item the
//!   name resolves back to `[ ]` with its estimate reset.
//! * [`skip`] / [`routine`] — today's instance of a routine (§5.1, §5.3).
//! * [`triage`] — `inbox.md` with a parse preview per line (§12.5).

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use serde::Serialize;

use tm_core::grammar::{self, IdGen, ItemLine, ParseCtx};
use tm_core::horizon;
use tm_core::log::Event;
use tm_core::model::{Dur, Horizon, Id, IsoWeek, State, YearMonth};
use tm_core::recur;
use tm_core::store::Store;
use tm_core::tree::Tree;

use super::ctx::{Ctx, Globals};
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
    /// The section, when one was given.
    pub section: Option<String>,
    /// The line as written.
    pub line: String,
}

/// `tm add "<line>" [--to <file>] [--section <name>]`.
pub fn add(g: &Globals, args: &super::AddArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let rec = Recorder::start(&ctx, "add")?;
    let path = target_path(&ctx, args.to.as_deref())?;
    let horizon = Horizon::from_path(&path).unwrap_or(Horizon::Backlog);

    let raw = args.line.trim();
    let mut text = if raw.starts_with("- ") {
        raw.to_string()
    } else if horizon.allows_missing_state() {
        format!("- {raw}")
    } else {
        format!("- [ ] {raw}")
    };
    let pctx = ParseCtx {
        horizon,
        ..ParseCtx::new(&path, ctx.block_min())
    };
    grammar::parse_line(&text, &pctx)
        .map_err(|e| CliError::msg(format!("{e}: {text:?}")))?;

    let mut line = ItemLine::parse(&text).map_err(|e| CliError::msg(e.to_string()))?;
    let mut id = line.id().unwrap_or_default();
    if id.is_empty() && !horizon.allows_missing_state() {
        let mut taken = ctx.taken_ids();
        let mut gen = id_gen(&ctx, raw);
        id = gen.next_id(&mut taken);
        line.append_id(&id);
        text = line.to_string();
    }
    ctx.store.insert_line(&path, args.section.as_deref(), &text)?;
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
        section: args.section.clone(),
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
}

/// Split `k=v`.
fn split_pair(pair: &str) -> Result<(&str, &str), CliError> {
    pair.split_once('=')
        .ok_or_else(|| CliError::msg(format!("expected key=value, got {pair:?}")))
}

/// Apply one `k=v` to a line, returning the change it made.
fn apply_pair(
    line: &mut ItemLine,
    item: &tm_core::model::Item,
    key: &str,
    value: &str,
    block_min: u32,
) -> Result<FieldChange, CliError> {
    let from = match key {
        "ci" => item.ci.to_string(),
        "title" => item.title.clone(),
        "p" | "priority" => item.priority.map(|p| p.to_string()).unwrap_or_default(),
        "state" => item.state.as_str().to_string(),
        other => line.get(other).unwrap_or_default().to_string(),
    };
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
            let v: u8 = value
                .parse()
                .map_err(|_| CliError::msg(format!("priority must be 1–4, got {value:?}")))?;
            line.set_priority(Some(v))?;
        }
        "state" => line.set_state(State::parse(value)?)?,
        "est" => {
            let d = Dur::parse(value, block_min)?;
            line.set_token("est", &d.to_string());
        }
        other => line.set_token(other, value),
    }
    Ok(FieldChange {
        field: key.to_string(),
        from,
        to: value.to_string(),
    })
}

/// `tm edit ^id [k=v …] [--set k=v] [--unset k]`.
pub fn edit(g: &Globals, args: &super::EditArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    let item = ctx.item(&id)?.clone();
    if args.pairs.is_empty() && args.set.is_empty() && args.unset.is_empty() {
        return Err(CliError::msg("nothing to change (try `tm edit ^id ci=4`)"));
    }
    let rec = Recorder::start(&ctx, "edit")?;
    let block_min = ctx.block_min();
    let mut line = ctx.line(&id)?;
    let mut changes = Vec::new();
    for pair in args.pairs.iter().chain(args.set.iter()) {
        let (k, v) = split_pair(pair)?;
        changes.push(apply_pair(&mut line, &item, k, v, block_min)?);
    }
    for key in &args.unset {
        let from = match key.as_str() {
            "p" | "priority" => {
                let was = item.priority.map(|p| p.to_string()).unwrap_or_default();
                line.set_priority(None)?;
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

    let out = EditOut {
        id: id.clone(),
        changes,
        line: line.to_string(),
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
pub fn move_item(g: &Globals, args: &super::MoveArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    ctx.item(&id)?;
    let to = horizon_arg(&ctx, &args.to)?;
    let section = args.section.clone().or_else(|| match to {
        // §6.2: a day file's items live under `# Pinned`.
        Horizon::Day(_) => Some(horizon::PINNED_SECTION.to_string()),
        _ => None,
    });
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

/// `tm rank ^id <n>` — rank is line order (§7.4).
pub fn rank(g: &Globals, args: &super::RankArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    ctx.item(&id)?;
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
pub fn demote(g: &Globals, args: &super::IdArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    ctx.item(&id)?;
    let rec = Recorder::start(&ctx, "demote")?;
    let d = horizon::demote(&ctx.hz(), &id)?;
    ctx.reload()?;
    rec.finish(&ctx, format!("demote {}", id.token()))?;

    let out = DemoteOut {
        id: d.id,
        est_min: d.est_min,
        stamps: d.stamps.iter().map(|s| s.to_string()).collect(),
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

/// `tm readopt ^id [--to week]` (§6.3).
pub fn readopt(g: &Globals, args: &super::ReadoptArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    let to = match &args.to {
        Some(s) => Some(horizon_arg(&ctx, s)?),
        None => None,
    };
    let rec = Recorder::start(&ctx, "readopt")?;
    let moved = horizon::readopt(&ctx.hz(), &id, to.as_ref())?;
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
    Ok(0)
}

/// `tm drop --json`.
#[derive(Debug, Serialize)]
pub struct DropOut {
    /// The item.
    pub id: Id,
    /// The line afterwards.
    pub line: String,
}

/// `tm drop ^id`.
pub fn drop_item(g: &Globals, args: &super::IdArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    ctx.item(&id)?;
    let rec = Recorder::start(&ctx, "drop")?;
    let line = horizon::drop_item(&ctx.hz(), &id)?;
    ctx.reload()?;
    rec.finish(&ctx, format!("drop {}", id.token()))?;

    let out = DropOut {
        id: id.clone(),
        line,
    };
    emit(ctx.json, || format!("dropped {}", out.id.token()), &out)?;
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
    for (i, raw) in text.lines().enumerate() {
        let trimmed = raw.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') || trimmed.starts_with("<!--") {
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
