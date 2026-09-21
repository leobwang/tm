//! The clock verbs of tm-spec-v1.md §9: `wake`, `arrive`, `start`, `done`,
//! `extend`, `stop`, `break`, `interrupt`, `resume`, `pause`, `energy`,
//! `idle`.
//!
//! # API overview
//!
//! One keystroke changes one fact (§9): each verb makes the byte-faithful
//! line edit §4.1 allows, updates the matching `state.json` field (§10.2) and
//! appends the matching §10.1 event — in that order, all inside a
//! [`super::undo::Recorder`] so `tm undo` can put every part of it back.
//!
//! * [`wake`] — `wake{slept_min,onset_min}`, stamped at the wake time; starts
//!   a new day in `state.json`.
//! * [`arrive`] — §8.1's window and budget (calendar sync first when
//!   `sync_on_arrive`), `arrive{loc,window,budget}`, then a replan; the block
//!   starts are kept in `.tm/arrival_plan.json` for §12.1's ghost row.
//! * [`start`] / [`done`] / [`extend`] / [`stop`] — the block machine; the
//!   energy report is `--energy N`, or asked on a terminal.
//! * [`take_break`] — starts a break, or ends the running one and logs it
//!   with its actual length (so does the next `start`, `done` or `stop`).
//! * [`interrupt`] / [`resume`] / [`pause`] / [`energy`] / [`idle`] — §9's
//!   remaining rows. A non-zero energy δ replans (§8.5).
//!
//! Every one of them also writes §4.3's human trace: one `HH:MM …` line in
//! the day file's `## Log`, and — for `wake` and `arrive` — the runtime front
//! matter (see [`super::dayfile`]).

use std::collections::BTreeSet;
use std::io::{self, BufRead, IsTerminal, Write};

use chrono::{DateTime, NaiveTime};
use serde::Serialize;

use tm_core::energy::{self, Features};
use tm_core::horizon::MIN_REMAINING_MIN;
use tm_core::log::{self, Event};
use tm_core::model::{parse_time, Dur, Horizon, Id, Recur, State};
use tm_core::recur;
use tm_core::store::{ActiveBlock, BreakState, InterruptState, Store};

use super::ctx::{Ctx, Globals, ARRIVAL_PLAN_PATH};
use super::out::{emit, fmt_time, CliError};
use super::planning;
use super::undo::Recorder;

/// `HH:MM` — `tm_core::planner::fmt_clock` under this file's own name (AGENTS
/// §5.3, W-23: a byte-for-byte copy of it stood here).
use tm_core::planner::fmt_clock as hhmm;

/// The unit a tool-written `est:` uses: whole blocks when the minutes divide
/// evenly (§9's "est: += 1b"), else the compact `Nm`/`Nh`/`NhMm` form. Mirrors
/// the private `est_dur` of `horizon.rs`, so a `tm stop` and a day close write
/// the same text.
fn est_dur(minutes: u32, block_min: u32) -> Dur {
    if block_min > 0 && minutes > 0 && minutes.is_multiple_of(block_min) {
        Dur::blocks(minutes / block_min, block_min)
    } else {
        Dur::canonical(minutes)
    }
}

/// Parse a duration argument (`20m`, `1b`, `1h30m`).
fn dur(arg: &str, block_min: u32) -> Result<Dur, CliError> {
    Ok(Dur::parse(arg, block_min)?)
}

/// Ask for an energy report on a terminal; `None` when stdin is not one.
fn ask_energy(pred: u8) -> Option<u8> {
    if !io::stdin().is_terminal() {
        return None;
    }
    print!("energy 0-5 (predicted {pred}, Enter to skip): ");
    let _ = io::stdout().flush();
    let mut line = String::new();
    io::stdin().lock().read_line(&mut line).ok()?;
    line.trim().parse::<u8>().ok().filter(|v| *v <= 5)
}

/// Minutes of working time since the last break *ended* (§8.5's
/// `since_break` feature, §10.1's `start{since_break_min}`).
///
/// `break.t` is when the break *began* — the entry is appended when it ends,
/// with `actual_min` set (log.rs's convention) — so the end is `t +
/// actual_min`. With no break yet today the gap is measured from the day's
/// first `start` instead: zero would read as "a break has just ended" after
/// five hours of unbroken work.
fn since_break_min(ctx: &Ctx) -> u32 {
    let since = ctx.replay.seam(ctx.today).and_then(|s| s.since_break);
    // A break that is still running (started, not yet ended) is itself the
    // most recent boundary: nothing has been worked since it began.
    if let Some(br) = &ctx.state.break_ {
        if let Some(started) = br.started {
            return (ctx.now_tz - ctx.at(started)).num_minutes().clamp(0, 24 * 60) as u32;
        }
    }
    match since {
        Some(t) => (ctx.now - t).num_minutes().clamp(0, 24 * 60) as u32,
        None => 0,
    }
}

/// "no such item", the error every id argument shares.
fn missing(id: &Id) -> CliError {
    CliError::NotFound(id.clone())
}

/// Append one line to the day file's `## Log` at `now` (§4.3) — the human
/// half of the §10.1 event the verb has just written.
fn day_note(ctx: &Ctx, text: impl Into<String>) -> Result<(), CliError> {
    super::dayfile::note(ctx, ctx.today, ctx.now_tz.time(), &text.into())
}

/// True for a line that carries no state and is never rewritten: §4.3's
/// `routines.md` and `optional.md`, whose occurrences live in the log as
/// §10.1 `routine`/`skip` events. Writing `[x]` into one would end the
/// recurrence for good (§5.1: "a recurring item never changes its line").
fn is_stateless(item: &tm_core::model::Item) -> bool {
    matches!(item.horizon, Horizon::Routine | Horizon::Optional)
}

/// Today's instance key for a stateless line, for §10.1's `routine{inst}`.
fn instance_key(ctx: &Ctx, item: &tm_core::model::Item) -> String {
    recur::today_instances(
        [item],
        ctx.today,
        ctx.now_tz.naive_local(),
        &ctx.replay,
        &ctx.cfg,
    )
    .first()
    .map(|(i, _)| i.key.to_string())
    .unwrap_or_else(|| ctx.today.to_string())
}

/// The features of the current instant (§8.5).
fn features(ctx: &Ctx, at: DateTime<chrono_tz::Tz>) -> Features {
    Features::at(at, ctx.wake_dt(), ctx.loc())
        .with_slept(ctx.slept_min())
        .with_progress(ctx.replay.blocks_done(ctx.today), since_break_min(ctx))
}

/// End the running break, appending its §10.1 `break` event with the actual
/// length and un-pausing the block the break paused (§10.2's
/// `active.paused`). Returns the minutes it lasted.
fn end_break(ctx: &mut Ctx) -> Result<Option<u32>, CliError> {
    let Some(br) = ctx.state.break_.take() else {
        return Ok(None);
    };
    let started = br.started.unwrap_or_else(|| ctx.now_tz.time());
    let start_dt = ctx.at(started);
    let actual = (ctx.now_tz - start_dt).num_minutes().max(0) as u32;
    // The break paused the block (§9); ending it un-pauses, unless an
    // interruption is also running and owns the pause.
    if ctx.state.interrupt.is_none() {
        if let Some(a) = ctx.state.active.as_mut() {
            a.paused = false;
        }
    }
    let entry = log::LogEntry::new(
        start_dt.fixed_offset(),
        Event::Break {
            planned_min: br.planned_min,
            actual_min: Some(actual),
            r#where: br.place.clone(),
        },
    );
    ctx.append_entry(&entry)?;
    Ok(Some(actual))
}

/// The minutes of the running block that were *not* worked: §9 pauses
/// (`pause`…`unpause`), interruptions (`interrupt`…`resume`) and breaks
/// (`break`…) that fell inside it. log.rs's own convention for a block's
/// worked minutes is "elapsed since `start` minus paused and interrupted
/// time"; §8.5's duration multiplier and §11's ledgers both double-count
/// without it (the same minutes are already `resume{lost_min}`).
fn idle_min_since(ctx: &Ctx, started: DateTime<chrono_tz::Tz>) -> u32 {
    let mut total = 0i64;
    let mut open: Option<DateTime<chrono::FixedOffset>> = None;
    let from = started.fixed_offset();
    let mut add = |a: DateTime<chrono::FixedOffset>, b: DateTime<chrono::FixedOffset>| {
        let a = a.max(from);
        let b = b.min(ctx.now);
        if b > a {
            total += (b - a).num_minutes();
        }
    };
    let marks = ctx.replay.seam(ctx.today).map_or(&[][..], |s| s.idle_marks.as_slice());
    for mark in marks {
        match *mark {
            log::IdleMark::Pause(t) | log::IdleMark::Interrupt(t) => {
                if open.is_none() {
                    open = Some(t);
                }
            }
            log::IdleMark::Unpause(t) | log::IdleMark::Resume(t) => {
                if let Some(a) = open.take() {
                    add(a, t);
                }
            }
            // `break.t` is the break's start; the entry is written when it
            // ends, so the pair is one entry.
            log::IdleMark::Break {
                t,
                actual_min: Some(m),
            } => add(t, t + chrono::Duration::minutes(i64::from(m))),
            log::IdleMark::Break { actual_min: None, .. } => {}
        }
    }
    // Anything still open at `now` (a pause or interruption that has not been
    // lifted) counts up to now.
    if let Some(a) = open {
        add(a, ctx.now);
    }
    // …and a break the caller is about to close, which is not in the log yet.
    if let Some(br) = &ctx.state.break_ {
        if let Some(s) = br.started {
            add(ctx.at(s).fixed_offset(), ctx.now);
        }
    }
    total.clamp(0, 24 * 60) as u32
}

/// Minutes actually worked on the running block: wall clock since `started`,
/// net of [`idle_min_since`].
fn worked_min(ctx: &Ctx, started: DateTime<chrono_tz::Tz>) -> u32 {
    let elapsed = (ctx.now_tz - started).num_minutes().max(0) as u32;
    elapsed.saturating_sub(idle_min_since(ctx, started))
}

/// `tm wake --json`.
#[derive(Debug, Serialize)]
pub struct WakeOut {
    /// The date the day belongs to.
    pub date: String,
    /// `HH:MM`.
    pub wake: String,
    /// Minutes slept.
    pub slept_min: u32,
    /// Minutes to fall asleep.
    pub onset_min: Option<u32>,
}

/// `tm wake [HH:MM] [--slept 8h10m] [--onset 25m]`.
pub fn wake(g: &Globals, args: &super::WakeArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    super::kernel_bridge::gate(&ctx, "wake")?;
    let rec = Recorder::start(&ctx, "wake")?;
    let time = match &args.time {
        Some(t) => parse_time(t)?,
        None => ctx.now_tz.time(),
    };
    let block_min = ctx.block_min();
    let slept_min = match &args.slept {
        Some(s) => dur(s, block_min)?.as_minutes(),
        None => 0,
    };
    let onset_min = match &args.onset {
        Some(s) => Some(dur(s, block_min)?.as_minutes()),
        None => None,
    };

    // A new day: the window, the budget and everything running are gone.
    ctx.state.date = Some(ctx.today);
    ctx.state.wake = Some(time);
    ctx.state.arrival = None;
    ctx.state.window = None;
    ctx.state.budget = None;
    ctx.state.active = None;
    ctx.state.break_ = None;
    ctx.state.interrupt = None;
    ctx.save_state()?;

    let entry = log::LogEntry::new(
        ctx.at(time).fixed_offset(),
        Event::Wake {
            slept_min,
            onset_min,
        },
    );
    ctx.append_entry(&entry)?;
    ctx.reload()?;

    // §4.3: the day file's front matter carries the wake time and the sleep,
    // and `## Log` its first line.
    let slept = super::out::fmt_dur(slept_min);
    let mut front = vec![("wake", fmt_time(time))];
    if slept_min > 0 {
        front.push(("slept", slept.clone()));
    }
    super::dayfile::front(&ctx, ctx.today, &front)?;
    super::dayfile::note(
        &ctx,
        ctx.today,
        time,
        &format!(
            "wake slept={slept}{}",
            onset_min.map(|o| format!(" onset={o}m")).unwrap_or_default()
        ),
    )?;
    rec.finish(&ctx, format!("wake {}", fmt_time(time)))?;

    let out = WakeOut {
        date: ctx.today.to_string(),
        wake: fmt_time(time),
        slept_min,
        onset_min,
    };
    emit(
        ctx.json,
        || {
            format!(
                "wake {} · slept {}m{}",
                out.wake,
                out.slept_min,
                out.onset_min
                    .map(|o| format!(" · onset {o}m"))
                    .unwrap_or_default()
            )
        },
        &out,
    )?;
    Ok(0)
}

/// `tm arrive --json`.
#[derive(Debug, Serialize)]
pub struct ArriveOut {
    /// The date.
    pub date: String,
    /// Where you are.
    pub loc: String,
    /// `HH:MM`.
    pub arrival: String,
    /// `[start, end]` (§8.1).
    pub window: [String; 2],
    /// Block budget (§8.1).
    pub budget: u32,
    /// Calendar files the sync wrote (§15).
    pub synced: Vec<String>,
    /// Anything that went wrong without failing the verb.
    pub warnings: Vec<String>,
    /// The plan the arrival produced.
    pub plan_hash: String,
    /// The block starts recorded for §12.1's ghost row.
    pub plan_at_arrival: Vec<ArrivalBlock>,
}

/// One block start as it stood at arrival.
#[derive(Clone, Debug, Serialize, serde::Deserialize)]
pub struct ArrivalBlock {
    /// `HH:MM`.
    pub start: String,
    /// The item.
    pub id: Option<String>,
}

/// `.tm/arrival_plan.json`.
#[derive(Clone, Debug, Serialize, serde::Deserialize)]
pub struct ArrivalPlan {
    /// The day.
    pub date: String,
    /// The plan hash at arrival.
    pub hash: String,
    /// The planned block starts.
    pub blocks: Vec<ArrivalBlock>,
}

/// **The pre-flight the three verbs that write before they plan owe** (gap
/// 115). `arrive`, `resume` and `energy` write `state.json` and the log
/// *before* the planning call that sends the tree to the kernel, so until this
/// a tree the kernel refuses was found only *after* the write. Driven at
/// `89ead46` on a `plan-basic` copy whose `^m1` carries a typo'd `@parent`:
/// `arrive` exited 1 having appended its `arrive` line *and* written
/// `state.json`; `energy 3` exited 1 having appended its `energy` line; and
/// `resume` exited 1 having cleared the interruption out of `state.json` —
/// losing it outright, since no log line recorded it either.
///
/// [`super::kernel_capacity::check_plan`] covers the *configured* values
/// (parity P26). This adds the **tree**, through
/// [`super::kernel_bridge::gate`] — the one shared write gate the owner's D35
/// makes every host-only write path ask (gap 584). It used to ask
/// `kernel_bridge::apply(ctx, &[])`, which is the same question through the
/// machine that ends in a write step: a request with no commands changes
/// nothing, but a document the kernel *renormalises* differs from the one sent
/// and would have been written back by a pre-flight. The gate goes to
/// `kernel_bridge::call` directly and cannot write at all.
fn preflight(ctx: &Ctx, verb: &str) -> Result<(), CliError> {
    super::kernel_capacity::check_plan(ctx)?;
    super::kernel_bridge::gate(ctx, verb)?;
    Ok(())
}

/// `tm arrive [lounge|home|<name>]`.
pub fn arrive(g: &Globals, args: &super::ArriveArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    preflight(&ctx, "arrive")?;
    let rec = Recorder::start(&ctx, "arrive")?;
    let loc = args
        .loc
        .clone()
        .or_else(|| ctx.state.loc.clone())
        .unwrap_or_else(|| "lounge".to_string());
    let at = match &args.at {
        Some(t) => parse_time(t)?,
        None => ctx.now_tz.time(),
    };

    // §15: sync the calendar first, so the walls are in the window.
    let mut warnings = Vec::new();
    let mut synced = Vec::new();
    if ctx.cfg.calendar.sync_on_arrive && !ctx.cfg.calendar.ics_urls.is_empty() {
        match super::lifecycle::sync_calendar(&ctx) {
            Ok(r) => {
                synced = r.files;
                warnings.extend(r.warnings);
                ctx.reload()?;
            }
            Err(e) => warnings.push(format!("calendar sync failed: {e}")),
        }
    }

    // **One definition of §8.1's window, shared with D42's rebuild** (the
    // owner's **D45**, AGENTS §5.3): `Ctx::arrival_window` is what writes the
    // cache here and what derives it back from the log when the cache is
    // gone, so the two cannot disagree about a day with two arrivals.
    let (window, budget) = ctx.arrival_window(at);
    ctx.state.date = Some(ctx.today);
    ctx.state.arrival = Some(at);
    ctx.state.loc = Some(loc.clone());
    ctx.state.window = Some(window);
    ctx.state.budget = Some(budget);
    ctx.save_state()?;

    // **`arrive.t` IS the arrival** — `tm_core::log`'s own event convention
    // ("`wake.t` is the wake time; `arrive.t` the arrival; `start.t` the block
    // start"), which `tm wake` above has always honoured and this verb did not:
    // it stamped [`Ctx::now`], so a retro `tm arrive --at 07:00` run at 13:00
    // wrote a header reading 13:00 and left the arrival only inside
    // `window[0]`. Two readings of one fact (AGENTS §5.3), and the one that
    // moved was the reader's: D42's rebuild takes the header for the arrival,
    // so deleting `.tm/state.json` moved `arrival` and `window` to an instant
    // in neither the cache nor the payload (README gap 1305).
    //
    // Without `--at` this is the same instant to the second — `at` is
    // `ctx.now_tz.time()` and `Ctx::at` puts it back on today's date in the
    // same zone — so the only bytes that move are a retro or future `--at`'s,
    // which move to what the convention says they must be.
    let entry = log::LogEntry::new(
        ctx.at(at).fixed_offset(),
        Event::Arrive {
            loc: loc.clone(),
            window: [fmt_time(window.0), fmt_time(window.1)],
            budget,
        },
    );
    ctx.append_entry(&entry)?;
    ctx.reload()?;

    // The plan, and the ghost row §12.1 draws from it.
    let (plan, prios) = planning::build(&ctx, false)?;
    planning::write_plan(&mut ctx, &plan, &prios)?;
    let blocks: Vec<ArrivalBlock> = plan
        .segments
        .iter()
        .filter(|s| {
            matches!(
                s.kind,
                tm_core::planner::SegKind::Block | tm_core::planner::SegKind::Batch(_)
            )
        })
        .map(|s| ArrivalBlock {
            start: hhmm(s.start),
            id: s.item.as_ref().map(|i| i.to_string()),
        })
        .collect();
    let arrival_plan = ArrivalPlan {
        date: ctx.today.to_string(),
        hash: plan.hash(),
        blocks: blocks.clone(),
    };
    ctx.store
        .write_file(ARRIVAL_PLAN_PATH, &serde_json::to_string_pretty(&arrival_plan)?)?;
    ctx.reload()?;

    // §4.3's runtime front matter, and the arrival in `## Log`.
    super::dayfile::front(
        &ctx,
        ctx.today,
        &[
            ("loc", loc.clone()),
            ("window", format!("{}..{}", fmt_time(window.0), fmt_time(window.1))),
            ("budget", budget.to_string()),
        ],
    )?;
    super::dayfile::note(&ctx, ctx.today, at, &format!("arrive {loc}"))?;
    rec.finish(&ctx, format!("arrive {loc} {}", fmt_time(at)))?;

    let out = ArriveOut {
        date: ctx.today.to_string(),
        loc,
        arrival: fmt_time(at),
        window: [fmt_time(window.0), fmt_time(window.1)],
        budget,
        synced,
        warnings,
        plan_hash: plan.hash(),
        plan_at_arrival: blocks,
    };
    emit(
        ctx.json,
        || {
            let mut s = format!(
                "arrive {} {} · window {}–{} · budget {} blocks",
                out.loc, out.arrival, out.window[0], out.window[1], out.budget
            );
            for w in &out.warnings {
                s.push_str(&format!("\n! {w}"));
            }
            s
        },
        &out,
    )?;
    Ok(0)
}

/// `tm start --json`.
#[derive(Debug, Serialize)]
pub struct StartOut {
    /// The item.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// `HH:MM`.
    pub started: String,
    /// Predicted energy (§8.5).
    pub pred: u8,
    /// Reported energy, if given.
    pub rep: Option<u8>,
    /// Planned minutes (`est × multiplier`).
    pub est_min: u32,
    /// The duration multiplier used.
    pub multiplier: f64,
    /// Hours since wake.
    pub hsw: f64,
}

/// `tm start ^id`.
pub fn start(g: &Globals, args: &super::StartArgs) -> Result<i32, CliError> {
    // `--energy` is §8.5's reported level, the same 0–5 scale `tm energy`
    // takes — and `tm energy 9` says so. Filtering an out-of-range value away
    // here instead asked for the energy again on a terminal and recorded
    // nothing off one, which is the report the user typed thrown away without
    // a word. Checked before the tree is loaded: nothing else runs.
    if let Some(level) = args.energy.filter(|v| *v > 5) {
        return Err(CliError::msg(format!("--energy is 0–5, not {level}")));
    }
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    let item = ctx.item(&id)?.clone();
    if let Some(a) = &ctx.state.active {
        if a.id != id {
            return Err(CliError::msg(format!(
                "{} is running — `tm done`, `tm stop` or `tm extend` first",
                a.id.token()
            )));
        }
    }
    super::kernel_bridge::gate(&ctx, "start")?;
    let rec = Recorder::start(&ctx, "start")?;
    let ended_break = end_break(&mut ctx)?;

    let mut f = features(&ctx, ctx.now_tz);
    if ended_break.is_some() {
        // The break this very command closed is not in `ctx.replay` yet.
        f.since_break_min = 0;
    }
    let pred = energy::predict(&ctx.model, &ctx.cfg, &f);
    let rep = args.energy.or_else(|| ask_energy(pred));
    // §8.5's planned minutes, through the ONE function that computes them:
    // D42's rebuild of `.tm/state.json` puts the same number back when the
    // cache is gone, and a second copy of this arithmetic here would be the
    // AGENTS §5.3 defect that rebuild exists to stop having an instance of.
    let (est_min, multiplier) = ctx.planned_block(&id);

    // §5.1/§4.3: a routine or optional line has no state and never changes —
    // its occurrences live in the log, not in the file.
    if !is_stateless(&item) {
        let mut line = ctx.line(&id)?;
        line.set_state(State::Active)?;
        ctx.write_line(&id, &line)?;
    }

    ctx.state.active = Some(ActiveBlock {
        id: id.clone(),
        started: ctx.now_tz.time(),
        est_min,
        paused: false,
    });
    ctx.state.date = Some(ctx.today);
    ctx.save_state()?;

    ctx.append_event(Event::Start {
        id: id.to_string(),
        pred,
        rep,
        hsw: f.hsw,
        slept_min: ctx.slept_min().unwrap_or(0),
        loc: ctx.state.loc.clone().unwrap_or_else(|| "lounge".to_string()),
        blocks_done: ctx.replay.blocks_done(ctx.today),
        since_break_min: f.since_break_min,
    })?;
    ctx.reload()?;
    day_note(
        &ctx,
        format!(
            "start {} pred={pred}{}",
            id.token(),
            rep.map(|r| format!(" rep={r}")).unwrap_or_default()
        ),
    )?;
    rec.finish(&ctx, format!("start {}", id.token()))?;

    let out = StartOut {
        id: id.clone(),
        title: item.title.clone(),
        started: hhmm(ctx.now_tz),
        pred,
        rep,
        est_min,
        multiplier,
        hsw: f.hsw,
    };
    emit(
        ctx.json,
        || {
            format!(
                "▶ {} {} · {} · pred {}{}",
                out.id.token(),
                out.title,
                out.started,
                out.pred,
                out.rep.map(|r| format!(" rep {r}")).unwrap_or_default()
            )
        },
        &out,
    )?;
    Ok(0)
}

/// `tm done --json`.
#[derive(Debug, Serialize)]
pub struct DoneOut {
    /// The item.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// Planned minutes.
    pub est_min: u32,
    /// Minutes worked (0 for a retro done).
    pub actual_min: u32,
    /// The block is done, the item is not.
    pub partial: bool,
    /// The state the line now carries.
    pub state: String,
    /// The remaining estimate written back, when partial.
    pub remaining_min: Option<u32>,
}

/// `tm done [--partial] [^id]`.
pub fn done(g: &Globals, args: &super::DoneArgs) -> Result<i32, CliError> {
    // §10.1's `went` is 1, 2 or 3 (§8.5). Filtering anything else away left
    // the two records of one `done` disagreeing: the `## Log` note in the day
    // file printed `went=7` while `.tm/log.jsonl` recorded no `went` at all,
    // and §8.5 never saw the report. Checked before the tree is loaded.
    if let Some(went) = args.went.filter(|w| !(1..=3).contains(w)) {
        return Err(CliError::msg(format!(
            "--went is 1 fine, 2 hard or 3 collapsed (§8.5), not {went}"
        )));
    }
    let mut ctx = Ctx::load(g, true)?;
    let active = ctx.state.active.clone();
    let (id, retro) = match (&args.id, &active) {
        (Some(arg), Some(a)) => {
            let id = Ctx::key(arg);
            let retro = id != a.id;
            (id, retro)
        }
        (Some(arg), None) => (Ctx::key(arg), true),
        (None, Some(a)) => (a.id.clone(), false),
        (None, None) => return Err(CliError::msg("nothing is running (`tm done ^id` for a retro done)")),
    };
    // An ambiguous title is refused before anything is logged (W-16 repair,
    // gap 576): this verb looks the argument up in the tree directly rather
    // than through `Ctx::item`, so it needs the refusal by name.
    ctx.refuse_ambiguous_title(&id)?;
    // §1.3: the other two writers may have removed the line while the block
    // ran. That must not wedge the block machine, so a missing item only
    // costs the line edit, not the event and not the state change.
    let item = match ctx.tree.get(&id) {
        Some(i) => Some(i.clone()),
        None if retro => return Err(missing(&id)),
        None => None,
    };
    super::kernel_bridge::gate(&ctx, "done")?;
    let rec = Recorder::start(&ctx, "done")?;

    let (est_min, actual_min) = if retro {
        (ctx.tree.remaining(&id).unwrap_or(0), 0)
    } else {
        let a = active.as_ref().expect("an active block");
        (a.est_min, worked_min(&ctx, ctx.at(a.started)))
    };
    end_break(&mut ctx)?;

    let stateless = item.as_ref().is_some_and(is_stateless);
    let mut remaining_min = None;
    if let Some(item) = item.as_ref().filter(|_| !stateless) {
        let mut line = ctx.line(&id)?;
        if args.partial {
            let left = ctx
                .tree
                .remaining(&id)
                .unwrap_or(est_min)
                .saturating_sub(actual_min)
                .max(MIN_REMAINING_MIN);
            line.set_state(State::Todo)?;
            line.set_token("est", &est_dur(left, ctx.block_min()).to_string());
            remaining_min = Some(left);
        } else if matches!(item.recur, Recur::OnEvent { .. }) {
            // §5.1: an on-event item goes to `[?]` with `waiting:<today>`.
            recur::on_done_waiting(item, ctx.today).apply(&mut line)?;
        } else {
            line.set_state(State::Done)?;
        }
        ctx.write_line(&id, &line)?;
    }

    if !retro {
        ctx.state.active = None;
    }
    ctx.save_state()?;

    // §10.1: a routine or optional occurrence is a `routine` event, not a
    // `done` — a `done{id}` would mark the recurring item finished for good.
    match item.as_ref().filter(|_| stateless) {
        Some(item) => ctx.append_event(Event::Routine {
            item: id.to_string(),
            inst: instance_key(&ctx, item),
            status: "done".to_string(),
            actual_min: Some(actual_min),
        })?,
        None => ctx.append_event(Event::Done {
            id: id.to_string(),
            est_min,
            actual_min,
            went: args.went,
            tags: ctx.tree.tags_effective(&id),
            // §3.1's default when the line itself is gone.
            ci: item.as_ref().map(|i| i.ci).unwrap_or(3),
            partial: args.partial,
        })?,
    }
    ctx.reload()?;
    day_note(
        &ctx,
        format!(
            "done {} {}m/{}m{}",
            id.token(),
            actual_min,
            est_min,
            args.went.map(|w| format!(" went={w}")).unwrap_or_default()
        ),
    )?;
    rec.finish(&ctx, format!("done {}", id.token()))?;

    let state = ctx
        .tree
        .get(&id)
        .map(|i| i.state.as_str().to_string())
        .unwrap_or_else(|| State::Done.as_str().to_string());
    let out = DoneOut {
        id: id.clone(),
        title: item.map(|i| i.title).unwrap_or_default(),
        est_min,
        actual_min,
        partial: args.partial,
        state,
        remaining_min,
    };
    emit(
        ctx.json,
        || {
            format!(
                "✓ {} {} · {}m/{}m{}",
                out.id.token(),
                out.title,
                out.actual_min,
                out.est_min,
                out.remaining_min
                    .map(|r| format!(" · {r}m left"))
                    .unwrap_or_default()
            )
        },
        &out,
    )?;
    Ok(0)
}

/// `tm extend --json`.
#[derive(Debug, Serialize)]
pub struct ExtendOut {
    /// The item.
    pub id: Id,
    /// Minutes added.
    pub by_min: u32,
    /// The block's new planned length.
    pub est_min: u32,
}

/// `tm extend [1b]`.
pub fn extend(g: &Globals, args: &super::ExtendArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let Some(active) = ctx.state.active.clone() else {
        return Err(CliError::msg("nothing is running"));
    };
    super::kernel_bridge::gate(&ctx, "extend")?;
    let rec = Recorder::start(&ctx, "extend")?;
    let block_min = ctx.block_min();
    let by = match &args.by {
        Some(s) => dur(s, block_min)?.as_minutes(),
        None => block_min,
    };
    let id = active.id.clone();
    // §1.3: a line the other writers removed costs the `est:` rewrite, not
    // the block.
    if let Some(item) = ctx.tree.get(&id).filter(|i| !is_stateless(i)) {
        let remaining = ctx.tree.remaining(&id).unwrap_or(0);
        let mut line = item.line().clone();
        line.set_token("est", &est_dur(remaining + by, block_min).to_string());
        ctx.write_line(&id, &line)?;
    }

    let est_min = active.est_min + by;
    ctx.state.active = Some(ActiveBlock { est_min, ..active });
    ctx.save_state()?;
    ctx.append_event(Event::Extend {
        id: id.to_string(),
        by_min: by,
    })?;
    ctx.reload()?;
    day_note(&ctx, format!("extend {} +{by}m", id.token()))?;
    rec.finish(&ctx, format!("extend {} +{by}m", id.token()))?;

    let out = ExtendOut {
        id: id.clone(),
        by_min: by,
        est_min,
    };
    emit(
        ctx.json,
        || format!("+{}m on {} · now {}m", out.by_min, out.id.token(), out.est_min),
        &out,
    )?;
    Ok(0)
}

/// `tm stop --json`.
#[derive(Debug, Serialize)]
pub struct StopOut {
    /// The item.
    pub id: Id,
    /// Minutes worked.
    pub worked_min: u32,
    /// The remaining estimate written back.
    pub remaining_min: u32,
}

/// `tm stop`.
pub fn stop(g: &Globals) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let Some(active) = ctx.state.active.clone() else {
        return Err(CliError::msg("nothing is running"));
    };
    super::kernel_bridge::gate(&ctx, "stop")?;
    let rec = Recorder::start(&ctx, "stop")?;
    let id = active.id.clone();
    let started = ctx.at(active.started);
    let worked = worked_min(&ctx, started);
    // §11's break integrity: a break still running when the block stops is
    // over too, and its `break` event has to reach the log.
    end_break(&mut ctx)?;
    let remaining = ctx
        .tree
        .remaining(&id)
        .unwrap_or(active.est_min)
        .saturating_sub(worked)
        .max(MIN_REMAINING_MIN);

    if let Some(item) = ctx.tree.get(&id).filter(|i| !is_stateless(i)) {
        let mut line = item.line().clone();
        line.set_state(State::Todo)?;
        line.set_token("est", &est_dur(remaining, ctx.block_min()).to_string());
        ctx.write_line(&id, &line)?;
    }

    ctx.state.active = None;
    ctx.save_state()?;
    ctx.append_event(Event::Stop {
        id: id.to_string(),
        remaining_min: remaining,
    })?;
    ctx.reload()?;
    day_note(
        &ctx,
        format!("stop {} {worked}m · {remaining}m left", id.token()),
    )?;
    rec.finish(&ctx, format!("stop {}", id.token()))?;

    let out = StopOut {
        id: id.clone(),
        worked_min: worked,
        remaining_min: remaining,
    };
    emit(
        ctx.json,
        || {
            format!(
                "stopped {} after {}m · {}m left",
                out.id.token(),
                out.worked_min,
                out.remaining_min
            )
        },
        &out,
    )?;
    Ok(0)
}

/// `tm break --json`.
#[derive(Debug, Serialize)]
pub struct BreakOut {
    /// `started` or `ended`.
    pub action: String,
    /// Planned minutes.
    pub planned_min: u32,
    /// Minutes it actually lasted (when ending).
    pub actual_min: Option<u32>,
    /// Where.
    pub place: Option<String>,
}

/// `tm break [20m] [--where walk]` — starts a break, or ends the running one.
pub fn take_break(g: &Globals, args: &super::BreakArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    // **The arguments are read in both arms** (the owner's D20, gap 138). The
    // running-break arm used to take its branch before it ever looked at
    // `args.dur`, so `tm break zzzz` was refused by name on a fresh tree and
    // silently accepted — ending the break, discarding both arguments and
    // exiting 0 — when a break was running. One verb, two acceptances, and a
    // user could not tell which they had got. Parsing here, ahead of the
    // branch, refuses the same spelling in both arms.
    //
    // D20 also settles what a *valid* argument does to a running break:
    // **nothing**. `tm break 20m` with a break running still just ends it;
    // retiming was considered and declined as a new feature, so `asked` is
    // read by the starting arm alone.
    let asked = match &args.dur {
        Some(s) => Some(dur(s, ctx.block_min())?.as_minutes()),
        None => None,
    };
    super::kernel_bridge::gate(&ctx, "break")?;
    let rec = Recorder::start(&ctx, "break")?;
    let running = ctx.state.break_.clone();
    let out = if let Some(br) = running {
        let actual = end_break(&mut ctx)?;
        ctx.save_state()?;
        BreakOut {
            action: "ended".to_string(),
            planned_min: br.planned_min,
            actual_min: actual,
            place: br.place,
        }
    } else {
        let planned = asked.unwrap_or(ctx.cfg.day.break_min);
        ctx.state.break_ = Some(BreakState {
            started: Some(ctx.now_tz.time()),
            planned_min: planned,
            place: args.place.clone(),
        });
        if let Some(a) = ctx.state.active.as_mut() {
            a.paused = true;
        }
        ctx.save_state()?;
        BreakOut {
            action: "started".to_string(),
            planned_min: planned,
            actual_min: None,
            place: args.place.clone(),
        }
    };
    ctx.reload()?;
    day_note(
        &ctx,
        match out.actual_min {
            Some(a) => format!("break ended {a}m/{}m", out.planned_min),
            None => format!(
                "break {}m{}",
                out.planned_min,
                out.place
                    .as_ref()
                    .map(|p| format!(" where={p}"))
                    .unwrap_or_default()
            ),
        },
    )?;
    rec.finish(&ctx, format!("break {}", out.action))?;
    emit(
        ctx.json,
        || match out.actual_min {
            Some(a) => format!("break ended · {a}m of {}m", out.planned_min),
            None => format!(
                "break {}m{}",
                out.planned_min,
                out.place
                    .as_ref()
                    .map(|p| format!(" ({p})"))
                    .unwrap_or_default()
            ),
        },
        &out,
    )?;
    Ok(0)
}

/// `tm interrupt --json` / `tm resume --json`.
#[derive(Debug, Serialize)]
pub struct InterruptOut {
    /// `interrupt` or `resume`.
    pub action: String,
    /// The block that was interrupted, if any.
    pub id: Option<String>,
    /// Minutes lost (on resume).
    pub lost_min: Option<u32>,
    /// Items dropped from today's plan as a consequence (§9).
    pub dropped: Vec<String>,
}

/// `tm interrupt`.
pub fn interrupt(g: &Globals) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    if ctx.state.interrupt.is_some() {
        return Err(CliError::msg("already interrupted — `tm resume` first"));
    }
    super::kernel_bridge::gate(&ctx, "interrupt")?;
    let rec = Recorder::start(&ctx, "interrupt")?;
    let id = ctx.state.active.as_ref().map(|a| a.id.to_string());
    ctx.state.interrupt = Some(InterruptState {
        started: Some(ctx.now_tz.time()),
        id: ctx.state.active.as_ref().map(|a| a.id.clone()),
    });
    if let Some(a) = ctx.state.active.as_mut() {
        a.paused = true;
    }
    ctx.save_state()?;
    ctx.append_event(Event::Interrupt { id: id.clone() })?;
    ctx.reload()?;
    day_note(
        &ctx,
        format!(
            "interrupt{}",
            id.as_ref().map(|i| format!(" ^{i}")).unwrap_or_default()
        ),
    )?;
    rec.finish(&ctx, "interrupt")?;

    let out = InterruptOut {
        action: "interrupt".to_string(),
        id,
        lost_min: None,
        dropped: Vec::new(),
    };
    emit(ctx.json, || "interrupted".to_string(), &out)?;
    Ok(0)
}

/// `tm resume`.
pub fn resume(g: &Globals) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    preflight(&ctx, "resume")?;
    let Some(int) = ctx.state.interrupt.clone() else {
        return Err(CliError::msg("nothing to resume"));
    };
    let rec = Recorder::start(&ctx, "resume")?;
    let started = int.started.unwrap_or_else(|| ctx.now_tz.time());
    let lost = (ctx.now_tz - ctx.at(started)).num_minutes().max(0) as u32;

    // §9: the tail the lost minutes cost — §10.1's `resume{dropped}` names
    // each item once, however many blocks it held in the plan that is being
    // replaced.
    let mut seen = BTreeSet::new();
    let before: Vec<String> = ctx
        .last_plan()
        .map(|p| {
            p.segments
                .iter()
                .filter_map(|s| s.item.clone())
                .filter(|i| seen.insert(i.clone()))
                .collect()
        })
        .unwrap_or_default();
    ctx.state.interrupt = None;
    if let Some(a) = ctx.state.active.as_mut() {
        a.paused = false;
    }
    ctx.save_state()?;
    let (plan, prios) = planning::build(&ctx, false)?;
    let after: Vec<String> = plan
        .segments
        .iter()
        .filter_map(|s| s.item.as_ref().map(|i| i.to_string()))
        .collect();
    let dropped: Vec<String> = before
        .into_iter()
        .filter(|i| !after.contains(i))
        .collect();

    ctx.append_event(Event::Resume {
        lost_min: lost,
        dropped: dropped.clone(),
    })?;
    planning::write_plan(&mut ctx, &plan, &prios)?;
    ctx.reload()?;
    day_note(
        &ctx,
        format!(
            "resume lost={lost}m{}",
            if dropped.is_empty() {
                String::new()
            } else {
                format!(" dropped={}", dropped.join(","))
            }
        ),
    )?;
    rec.finish(&ctx, format!("resume (lost {lost}m)"))?;

    let out = InterruptOut {
        action: "resume".to_string(),
        id: int.id.map(|i| i.to_string()),
        lost_min: Some(lost),
        dropped,
    };
    emit(
        ctx.json,
        || format!("resumed · lost {lost}m"),
        &out,
    )?;
    Ok(0)
}

/// `tm pause --json`.
#[derive(Debug, Serialize)]
pub struct PauseOut {
    /// The item.
    pub id: Id,
    /// Whether the timer is now paused.
    pub paused: bool,
}

/// `tm pause` — toggles the running block's timer.
pub fn pause(g: &Globals) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let Some(mut active) = ctx.state.active.clone() else {
        return Err(CliError::msg("nothing is running"));
    };
    super::kernel_bridge::gate(&ctx, "pause")?;
    let rec = Recorder::start(&ctx, "pause")?;
    active.paused = !active.paused;
    let paused = active.paused;
    let id = active.id.clone();
    ctx.state.active = Some(active);
    ctx.save_state()?;
    ctx.append_event(if paused {
        Event::Pause { id: id.to_string() }
    } else {
        Event::Unpause { id: id.to_string() }
    })?;
    ctx.reload()?;
    day_note(
        &ctx,
        format!(
            "{} {}",
            if paused { "pause" } else { "unpause" },
            id.token()
        ),
    )?;
    rec.finish(&ctx, if paused { "pause" } else { "unpause" })?;

    let out = PauseOut {
        id: id.clone(),
        paused,
    };
    emit(
        ctx.json,
        || {
            format!(
                "{} {}",
                if paused { "paused" } else { "resumed" },
                out.id.token()
            )
        },
        &out,
    )?;
    Ok(0)
}

/// `tm energy --json`.
#[derive(Debug, Serialize)]
pub struct EnergyOut {
    /// `HH:MM`.
    pub at: String,
    /// What was predicted.
    pub pred: u8,
    /// What you reported.
    pub rep: u8,
    /// `rep − pred`.
    pub delta: i8,
    /// Hours since wake.
    pub hsw: f64,
    /// Location.
    pub loc: String,
    /// Whether the non-zero δ triggered a replan (§8.5).
    pub replanned: bool,
}

/// `tm energy 0-5 [--at HH:MM]`.
pub fn energy(g: &Globals, args: &super::EnergyArgs) -> Result<i32, CliError> {
    if args.level > 5 {
        return Err(CliError::msg("energy is 0–5"));
    }
    let mut ctx = Ctx::load(g, true)?;
    preflight(&ctx, "energy")?;
    let rec = Recorder::start(&ctx, "energy")?;
    let at: NaiveTime = match &args.at {
        Some(t) => parse_time(t)?,
        None => ctx.now_tz.time(),
    };
    let when = ctx.at(at);
    let f = features(&ctx, when);
    let pred = energy::predict(&ctx.model, &ctx.cfg, &f);
    let loc = ctx.state.loc.clone().unwrap_or_else(|| "lounge".to_string());
    let entry = log::LogEntry::new(
        when.fixed_offset(),
        Event::Energy {
            pred,
            rep: args.level,
            hsw: f.hsw,
            loc: loc.clone(),
        },
    );
    ctx.append_entry(&entry)?;
    ctx.reload()?;
    let delta = args.level as i8 - pred as i8;

    // §8.5: "Non-zero δ triggers a replan" — the posterior correction
    // re-energises every later slot (§9's "slots re-energised").
    let mut replanned = false;
    if delta != 0 {
        let (plan, prios) = planning::build(&ctx, false)?;
        planning::write_plan(&mut ctx, &plan, &prios)?;
        ctx.reload()?;
        replanned = true;
    }
    day_note(
        &ctx,
        format!(
            "energy pred={pred} rep={}{}",
            args.level,
            if replanned { " replan" } else { "" }
        ),
    )?;
    rec.finish(&ctx, format!("energy {}", args.level))?;

    let out = EnergyOut {
        at: fmt_time(at),
        pred,
        rep: args.level,
        delta,
        hsw: f.hsw,
        loc,
        replanned,
    };
    emit(
        ctx.json,
        || {
            format!(
                "energy {} (pred {}) at {}{}",
                out.rep,
                out.pred,
                out.at,
                if out.replanned { " · replanned" } else { "" }
            )
        },
        &out,
    )?;
    Ok(0)
}

/// `tm idle --json`.
#[derive(Debug, Serialize)]
pub struct IdleOut {
    /// `work`, `break`, `routine`, `interrupt` or `leak`.
    pub attributed: String,
    /// Minutes attributed.
    pub min: u32,
}

/// `tm idle <w|b|t|i|l>` (§9.2).
pub fn idle(g: &Globals, args: &super::IdleArgs) -> Result<i32, CliError> {
    let attributed = match args.kind.to_ascii_lowercase().as_str() {
        "w" | "work" => "work",
        "b" | "break" => "break",
        "t" | "routine" => "routine",
        "i" | "interrupt" => "interrupt",
        "l" | "leak" => "leak",
        other => {
            return Err(CliError::msg(format!(
                "unknown attribution {other:?} (w work · b break · t routine · i interrupt · l leak)"
            )))
        }
    };
    let mut ctx = Ctx::load(g, true)?;
    super::kernel_bridge::gate(&ctx, "idle")?;
    let rec = Recorder::start(&ctx, "idle")?;
    let min = args.min.unwrap_or_else(|| {
        let last = ctx.replay.last_effective_t;
        match last {
            Some(t) => (ctx.now - t).num_minutes().clamp(0, 24 * 60) as u32,
            None => ctx.cfg.day.idle_min,
        }
    });
    ctx.append_event(Event::Idle {
        attributed: attributed.to_string(),
        min,
    })?;
    ctx.reload()?;
    day_note(&ctx, format!("idle {attributed} {min}m"))?;
    rec.finish(&ctx, format!("idle {attributed} {min}m"))?;

    let out = IdleOut {
        attributed: attributed.to_string(),
        min,
    };
    emit(
        ctx.json,
        || format!("{}m attributed to {}", out.min, out.attributed),
        &out,
    )?;
    Ok(0)
}
