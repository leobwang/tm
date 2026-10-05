//! **The capacity request's I/O half** (stage 5 D10 step L8, host half; design
//! `kernel/design/stage5/stage5-D9-D10-design.md` §13.6, §13.8; the pure half moved
//! to `tm_core::planwire` at stage 6 W-40 track E, README gap 2875).
//!
//! Since step L8 the shipped binary's §8.4 lookahead and every §7 priority come
//! from the kernel: `Look.lookahead` (the owner's D10: each future day an exact
//! mixture of the day at the lounge and the day at home, in units over
//! `capDen = 10^18`, D17) and `Look.prioritiesWithFloors` (step 3's EDF pass,
//! §7.1's bin at the exact availability, §7.2's row, §7.4's hysteresis, and the
//! floor pass). Nothing else in the Rust builds a capacity request, and nothing
//! else reads one back.
//!
//! **Where the encoder lives.** `tm` is a `[[bin]]`, so a test could not link
//! the section this module built, and the harness spelled it again
//! (`tm/tests/support/planreq.rs`, the third spelling README gap 2006 counted
//! two of). The PURE half — every configured decimal read as the text its file
//! writes ([`tm_core::planwire::Written`], [`tm_core::planwire::written_pair`];
//! D10, D17, parity P26), the section's tables, the candidates in the fork's
//! service order, and §16's `batchMaxMin` the planner section reads beside them
//! — is [`tm_core::planwire::capacity_json`] since W-40, and this module keeps
//! what takes a `Ctx`:
//!
//! * [`check_plan`] runs the same checks over `config.toml` and
//!   `.tm/model.json` before a request is built, so a weight outside `[0, 1]` or
//!   with more than 18 written decimal places fails every verb that computes
//!   capacity or priority **by file and key** (§13.2, parity P26); the kernel's
//!   refusal stays the authority, and [`named_refusal`] names the file and key
//!   of every refusal a configured value can cause.
//! * [`request`] reads the files, then builds the whole request: the plan's
//!   documents (walls are the kernel's reading, gap 111), `now`, `blockMin`, the
//!   zone table from [`super::tz_table`] (the one zone encoder), a **`log`
//!   section** (D24's seam), and the `capacity` section from
//!   `planwire::capacity_json` — both weekday tables raw (the kernel picks,
//!   D10-4), today's `wake`, the learned curves, the prior, `[day]`,
//!   `[priority]`, `days`, and day 0's own host-only facts — `at`, `state`,
//!   `posterior`, `sleep` — with the candidates when priorities are asked for
//!   (their facts are the host's, gap 113).
//!
//!   **`day0` is gone (step L9, gap 93 closed).** The host no longer hands in a
//!   histogram of today: the kernel derives day 0 from its own replay of the
//!   `log` section, and refuses `day0WithoutLog` when a capacity request
//!   carries none. What still crosses is only what the kernel cannot know —
//!   the instant the verb ran, `.tm/state.json`'s runtime facts, `--allow-home`,
//!   and the `[energy]` decimals the posterior and the sleep debt read. Today's
//!   sleep and energy reports do **not** cross.
//! * [`read_answer`] parses the response: `den` must be `capDen`, unit counts are
//!   digit strings read into `u128` (D17), and each grant becomes a [`Prio`]
//!   whose integer minutes are floors beside their exact values (D15).
//!
//! **The horizon (gap 98).** The kernel's lookahead is at most 3,660 days
//! (`Look.maxLookaheadDays`) and never runs past 9999-12-31.
//! `planwire::horizon` clamps the fork's `priority::lookahead_days` to both and
//! [`ask`] says so on stderr when it clamps (parity P30: a deadline past it sees
//! the capacity of the days it has).
//!
//! [`Prio`]: tm_core::priority::Prio

use std::collections::BTreeMap;

use chrono::NaiveDate;
use serde_json::{json, Value};

use tm_core::capacity::UnitCapacity;
use tm_core::model::Id;
use tm_core::planwire::{self, CapacityIn, InputDefect, Written, CONFIG_FILE, MODEL_FILE};
use tm_core::priority::{self, Candidate};
use tm_core::store::Store;

use super::ctx::Ctx;
use super::kernel_bridge;
use super::kernel_log;
use super::out::CliError;
use super::tz_table;

pub use tm_core::planwire::Ranked;

// ---------------------------------------------------------------------------
// The inputs, checked by file and key (§13.2, P26)
// ---------------------------------------------------------------------------

/// A configured value the request cannot carry: the sentence `planwire` wrote,
/// as the message every verb prints (unchanged by the move, byte for byte).
fn input_error(e: InputDefect) -> CliError {
    CliError::msg(e.0)
}

/// **The literals of the plan `ctx` loaded**, read from its files now
/// ([`Written::parse`] over `config.toml` and `.tm/model.json`, each `None`
/// when absent).
fn written_of(ctx: &Ctx) -> Result<Written, CliError> {
    let read = |rel: &str| -> Result<Option<String>, CliError> {
        if ctx.store.exists(rel) {
            Ok(Some(ctx.store.read_text(rel)?))
        } else {
            Ok(None)
        }
    };
    Written::parse(read(tm_core::store::CONFIG_PATH)?.as_deref(), read(tm_core::store::MODEL_PATH)?.as_deref())
        .map_err(input_error)
}

/// **Every configured decimal the capacity request carries, checked over the plan
/// `ctx` loaded, as its files write it** — `planwire::check_inputs` over the
/// literals [`written_of`] reads.
pub fn check_plan(ctx: &Ctx) -> Result<(), CliError> {
    planwire::check_inputs(&ctx.cfg, &ctx.model, &written_of(ctx)?).map_err(input_error)
}

/// **A capacity refusal a configured value causes, by file and key** (P26).
/// `None` for a refusal only a defect of this module can cause (the clock, the
/// zone table, the candidates' shape): those stay the kernel's named issue.
pub fn named_refusal(issue: &super::out::KernelIssue) -> Option<CliError> {
    let text = issue.message.strip_prefix("kernel refusal: ")?;
    let text = text.split(" — ").next()?;
    let (name, key) = text.split_once(' ').unwrap_or((text, ""));
    let weekday = |k: &str| k.rsplit('.').next().unwrap_or_default().to_string();
    let (file, what): (&str, String) = match name {
        "badWeight" | "weightAboveOne" | "weightPrecision" if key.starts_with("pLounge.model.") => {
            (MODEL_FILE, format!("p_lounge.{}", weekday(key)))
        }
        "badWeight" | "weightAboveOne" | "weightPrecision" => {
            (CONFIG_FILE, format!("expected.p_lounge.{}", weekday(key)))
        }
        "badClock" if key.starts_with("arrival.model.") => {
            (MODEL_FILE, format!("expected_arrival.{}", weekday(key)))
        }
        "badClock" if key == "day.windowCap" => (CONFIG_FILE, "day.window_cap".to_string()),
        "badClock" if key == "day.windDown" => (CONFIG_FILE, "day.wind_down".to_string()),
        "badClock" if key == "day.bed" => (CONFIG_FILE, "day.bed".to_string()),
        "badClock" => (CONFIG_FILE, format!("expected.arrival.{}", weekday(key))),
        "badCurve" => (MODEL_FILE, key.to_string()),
        "badPrior" | "badStep" | "badLevel" => (CONFIG_FILE, format!("energy.{key}")),
        "badCap" => (CONFIG_FILE, "location.home_max_ci".to_string()),
        "badDay" => {
            let k = match key {
                "blockMin" => "day.block_min",
                "breakMin" => "day.break_min",
                "breakAfterBlocks" => "day.break_after_blocks",
                "minLastBlockMin" => "day.min_last_block_min",
                "windowHours" => "day.window_hours",
                "budgetRatio" => "day.budget_ratio",
                _ => return None,
            };
            (CONFIG_FILE, k.to_string())
        }
        // Stage 6 step L9: day 0's four configured decimals, and the model's fitted shift.
        "badPosterior" => {
            let k = match key {
                "posterior.fullHours" => "energy.posterior_full_hours",
                "posterior.zeroHours" => "energy.posterior_zero_hours",
                _ => return None,
            };
            (CONFIG_FILE, k.to_string())
        }
        "badSleep" if key == "sleep.shiftModel" => (MODEL_FILE, "sleep_debt_shift".to_string()),
        "badSleep" => {
            let k = match key {
                "sleep.shiftConfig" => "energy.sleep_debt.shift",
                "sleep.underHours" => "energy.sleep_debt.under_hours",
                _ => return None,
            };
            (CONFIG_FILE, k.to_string())
        }
        "badBins" => (CONFIG_FILE, "priority.bins".to_string()),
        "badSafety" => (CONFIG_FILE, "priority.safety".to_string()),
        "badDefaultPriority" => (CONFIG_FILE, "priority.default_priority".to_string()),
        _ => return None,
    };
    Some(CliError::msg(format!(
        "{file}: {what} is outside what the kernel accepts ({text}); tm cannot compute capacity or \
         priorities until it is fixed (kernel/README.md parity P26)"
    )))
}

// ---------------------------------------------------------------------------
// The horizon (gap 98)
// ---------------------------------------------------------------------------

/// Say on stderr that the horizon clamped (not while the TUI owns the screen).
fn say_clamped(today: NaiveDate, want: u32, days: u32) {
    if kernel_bridge::capturing_kernel_stderr() {
        return;
    }
    let through = today + chrono::Duration::days(i64::from(days) - 1);
    eprintln!(
        "tm: the capacity lookahead is clamped to {days} days (through {through}; {want} were needed): a \
         deadline or floor after that sees only those days' capacity (kernel/README.md gap 98, parity P30)"
    );
}

// ---------------------------------------------------------------------------
// The request
// ---------------------------------------------------------------------------

/// **The capacity request** for `days` days from today, with the candidates when
/// `ranked` is given. Returns the request and the order the candidates were
/// sent in ([`planwire::send_order`], the order `planwire::capacity_json` wrote
/// them in).
pub fn request(ctx: &Ctx, allow_home: bool, days: u32, ranked: Option<&Ranked<'_>>) -> Result<(String, Vec<usize>), CliError> {
    request_on(ctx, &ctx.state, allow_home, days, ranked)
}

/// [`request`] over `state` in place of `ctx.state` — [`planner_request`]'s, which
/// reads the state as `tm plan`'s roll leaves it.
fn request_on(
    ctx: &Ctx,
    state: &tm_core::store::RuntimeState,
    allow_home: bool,
    days: u32,
    ranked: Option<&Ranked<'_>>,
) -> Result<(String, Vec<usize>), CliError> {
    request_with(ctx, state, allow_home, days, ranked, &reads(ctx)?)
}

/// **Every byte a capacity request reads from the plan directory, read once** (W-45 track Q, README gap 4662):
/// `config.toml`'s and `.tm/model.json`'s literals ([`written_of`]), the documents as [`Ctx::reading`] gives them,
/// the zone table under the replay cache (`tz_table::wire_for`, `tz.json`), and the log as [`Ctx::log_now`] gives
/// it. [`request_with`] reads nothing else from disk: the checkpoint the log section resumes is the process's own
/// (`kernel_log::capacity_log_section`; its `ckpt.json` is read only by a process that has run no replay, and a
/// context is loaded by one).
struct Reads {
    written: Written,
    docs: Vec<Value>,
    tz_wire: Value,
    log: Vec<u8>,
}

/// Read them.
fn reads(ctx: &Ctx) -> Result<Reads, CliError> {
    // Every configured decimal as its file writes it (D10, D17): read here, checked and sent
    // by the codec, which is the one spelling of the section (README gap 2875).
    let written = written_of(ctx)?;
    // The documents: the whole tree, as `kernel_bridge::apply` sends it — read through
    // `Ctx::reading`, so a TUI past midnight that holds §6.3's automatic close in memory sends the
    // documents `tm plan` sends after its own close (the owner's D91, README gap 4342).
    let reading = ctx.reading()?;
    let mut docs = Vec::new();
    for rel in reading.store().list_files()? {
        let text = reading.store().read_text(&rel)?;
        docs.push(kernel_bridge::doc_json(&rel, &kernel_bridge::doc_lines(&text)));
    }
    let cache = ctx.store.root().join(".tm/cache/replay");
    let tz_wire = tz_table::wire_for(Some(&cache), ctx.cfg.tz);
    // The log as the request reads it (`Ctx::log_now`): with the lines that close would log (D91).
    let log = ctx.log_now()?;
    Ok(Reads { written, docs, tz_wire, log })
}

/// [`request_on`] over [`Reads`] already read: nothing here touches the plan directory.
fn request_with(
    ctx: &Ctx,
    state: &tm_core::store::RuntimeState,
    allow_home: bool,
    days: u32,
    ranked: Option<&Ranked<'_>>,
    r: &Reads,
) -> Result<(String, Vec<usize>), CliError> {
    let input = CapacityIn {
        cfg: &ctx.cfg,
        model: &ctx.model,
        written: &r.written,
        tree: &ctx.tree,
        state,
        now: ctx.now_tz,
        // The day record `planwire::planned_loc` falls back to: the location is the
        // planner's reading, not `Ctx::loc`'s lounge (D81, parity P76).
        replay: &ctx.replay,
        allow_home,
        days,
    };
    let section = planwire::capacity_json(&input, ranked).map_err(input_error)?;
    let order = ranked.map(|r| planwire::send_order(r.cands)).unwrap_or_default();

    // Stage 6 step L9: the `log` section day 0 is derived from (D24's seam).  The kernel answers
    // both sections in one call and `runCapZ` hands the log answer's replay to the capacity
    // reader; without it the kernel refuses `day0WithoutLog` rather than invent an empty day.
    let log = kernel_log::capacity_log_section(ctx.store.root(), &r.log, &r.tz_wire, kernel_log::day_of(ctx.today))
        .map_err(super::ctx::genesis_error)?;
    let rest = json!({
        "docs": r.docs,
        "now": ctx.today.to_string(),
        "blockMin": ctx.block_min(),
        "tz": r.tz_wire,
        "capacity": section,
    })
    .to_string();
    // The `log` section is **spliced as text**: its checkpoint is read in build order
    // (`Seal.readCkptFields`) and `serde_json::Value` is a `BTreeMap`, so parsing it here would
    // alphabetise those keys and the kernel would refuse `badCkpt v`.
    let request = format!("{{\"log\":{log},{}", &rest[1..]);
    Ok((request, order))
}

// ---------------------------------------------------------------------------
// The answer
// ---------------------------------------------------------------------------

/// What the kernel answered: the first `min(days, 7)` days in units, and one
/// priority per candidate in the candidates' own order.
///
/// **`tm_core::planwire`'s type since stage 6 W-35**, and so is the reading of
/// it: `tm` is a `[[bin]]`, so a test that ranked the fork "as the shipped
/// binary runs it" (D53) could only copy this reader, and three copies existed
/// (README gap 2006). The code moved unchanged; the defects it names are the
/// same strings, under the same `capacity response:` prefix.
pub use tm_core::planwire::CapacityAnswer as Answer;

/// A response defect: loud, named, never a wrong answer.
fn defect(what: &str) -> CliError {
    CliError::Kernel(kernel_bridge::fault_issue(&format!("capacity response: {what}"), ""))
}

/// **Read the response** of a request built by [`request`] with `order` —
/// [`tm_core::planwire::read_capacity_answer`], each defect named as before.
pub fn read_answer(resp: &Value, order: &[usize], ranked: bool) -> Result<Answer, CliError> {
    tm_core::planwire::read_capacity_answer(resp, order, ranked).map_err(|e| defect(&e.0))
}

/// **The capacity request's own bytes, on stderr** (W-40 track E, README gap
/// 3720), when this is set: one line, [`TRACE_REQUEST_PREFIX`] and the request
/// exactly as [`ask`] hands it to the kernel. Opt-in in shipped code, as
/// `tm_kernel_ffi::TRACE_CALLS_ENV` and `ctx::TRACE_SCOPE_ENV` are, and for the
/// same reason: `tm` is a `[[bin]]`, so the only way a test can read the request
/// the binary SENDS — its documents, its zone table, its log section, its
/// capacity section — is to run the binary and read it.
/// `tm/tests/planner_request_keys.rs` diffs its key set against the harness's.
/// Silent while the TUI owns the screen, as [`say_clamped`] is.
pub const TRACE_REQUEST_ENV: &str = "TM_TRACE_CAPACITY_REQUEST";
/// The line [`TRACE_REQUEST_ENV`] prints, before the request's bytes.
pub const TRACE_REQUEST_PREFIX: &str = "capacity request: ";

/// **Ask the kernel** for `want` days of capacity from today (clamped by
/// `planwire::horizon`), and the priorities of `ranked` when given.
pub fn ask(ctx: &Ctx, allow_home: bool, want: u32, ranked: Option<&Ranked<'_>>) -> Result<Answer, CliError> {
    let (days, clamped) = planwire::horizon(ctx.today, want);
    if clamped {
        say_clamped(ctx.today, want, days);
    }
    let (req, order) = request(ctx, allow_home, days, ranked)?;
    if std::env::var_os(TRACE_REQUEST_ENV).is_some() && !kernel_bridge::capturing_kernel_stderr() {
        eprintln!("{TRACE_REQUEST_PREFIX}{req}");
    }
    let (resp, _) = match kernel_bridge::call_text(&req) {
        Ok(r) => r,
        Err(CliError::Kernel(issue)) => {
            return Err(named_refusal(&issue).unwrap_or(CliError::Kernel(issue)));
        }
        Err(e) => return Err(e),
    };
    let answer = read_answer(&resp, &order, ranked.is_some())?;
    if let Some(r) = ranked {
        for (c, p) in r.cands.iter().zip(&answer.prios) {
            if c.id != p.id {
                return Err(defect("a grant answers another candidate"));
            }
        }
    }
    Ok(answer)
}

/// **§7 and §8.4 from the kernel**: the priorities of `cands` over a lookahead
/// long enough for every deadline and floor (`priority::lookahead_days`), and
/// its first days.
pub fn rank(ctx: &Ctx, cands: &[Candidate], yesterday: &BTreeMap<Id, u8>, allow_home: bool) -> Result<Answer, CliError> {
    let want = priority::lookahead_days(cands, ctx.today);
    ask(ctx, allow_home, want, Some(&Ranked { cands, yesterday }))
}

/// **R3's planner request** (the W-41 repair, README gaps 4130 and 4142; sent by
/// every planning verb since R3): the ranked capacity request ([`request`], over
/// the candidates `priority::collect_candidates` collects and the hysteresis
/// input) with the `planner` section — `planwire::planner_json` over
/// `.tm/state.json`, the replay and the plan date's routine instances, and the
/// running block's worked minutes as the binary reads them (`day::worked_min`,
/// gap 3043) — spliced by `planwire::with_planner`.
///
/// `tm check` asks the kernel for this day and names every refusal of it (P78);
/// [`plan_day`] — `tm plan`, `tm now`, every verb that replans, and the TUI
/// (R3) — sends it and reads the day back. A planner refusal stops each of
/// them, and D80 made two of them refusals BY NAME so they are findable (D32's
/// shape).
///
/// **It reads `.tm/state.json` as `tm plan`'s roll leaves it, in memory**
/// (`RuntimeState::roll_to`; the owner's D84, parity P83's rule for the TUI,
/// applied once here for every caller — README gaps 4263, 4323 and 4334, the
/// W-42 repair). `tm check` writes nothing and so never rolled: past midnight
/// it asked the kernel for MONDAY's day on Tuesday — `planner.routines`
/// carrying Monday's instances and `capacity.state.date` Monday's — while `tm
/// plan` and the TUI plan Tuesday's, so the refusal it names was a refusal of a
/// day no planning surface asks for. `tm plan`'s housekeeping and the TUI's
/// re-collection have rolled the state already, so for them this is a no-op.
///
/// **Its reads and its build are two halves** (W-45 track Q, README gap 4662): [`tick_inputs`] reads from the plan
/// directory, once, everything the request carries that the context does not hold in memory, and
/// [`planner_ask_from`] builds the request from them and the context alone (it was `planner_request_from` until
/// the W-45 repair, which made [`planner_ask`] the one entry `tm check` and T19 build through). This is the two in one call, so
/// `tm plan` and `tm check` read the files as they stand when the verb runs. The TUI's minute tick (the owner's
/// D103) is the caller the halves exist for: it holds the context its last reload read, and a tick built from
/// that reload's [`TickInputs`] reads NOTHING from disk — the documents, the log, the configured literals and the
/// stored plan it was ranked from all the reload's, one consistent read, as fork 4748911's tick replanned from the
/// App's own data.
#[cfg(test)]
pub fn planner_request(ctx: &Ctx, allow_home: bool) -> Result<String, CliError> {
    Ok(planner_ask(ctx, allow_home)?.request)
}

/// **[`planner_request`] and what it was built from** — the plan directory read
/// once and [`planner_ask_from`] over that read, with T19's instrument. `tm check`
/// asks this and reads the answer with [`read_day`], the decoder every planning
/// verb reads its day with (the W-45 repair, README gap 4742).
pub fn planner_ask(ctx: &Ctx, allow_home: bool) -> Result<PlannerAsk, CliError> {
    let read = std::time::Instant::now();
    let inputs = tick_inputs(ctx)?;
    let read = read.elapsed();
    // **T19's instrument** (README gap 4662): opt-in, as [`TRACE_REQUEST_ENV`] is, and silent while the TUI owns
    // the screen. Set to `k`, the request is built `k` times from the one read and each build is timed — what a
    // tick pays, warm, in this process — and the line says so; every build must be byte-identical, or the
    // instrument is measuring something other than one tick's request.
    let builds = std::env::var(TRACE_BUILD_ENV).ok().and_then(|k| k.parse::<usize>().ok()).filter(|k| *k > 0);
    let Some(k) = builds.filter(|_| !kernel_bridge::capturing_kernel_stderr()) else {
        return planner_ask_from(ctx, &inputs, allow_home, None);
    };
    let mut took = Vec::with_capacity(k);
    let mut asked: Option<PlannerAsk> = None;
    for _ in 0..k {
        let t = std::time::Instant::now();
        let built = planner_ask_from(ctx, &inputs, allow_home, None)?;
        took.push(t.elapsed().as_nanos().to_string());
        if asked.as_ref().is_some_and(|a| a.request != built.request) {
            return Err(defect("two builds of one tick's request differ"));
        }
        asked = Some(built);
    }
    let asked = asked.ok_or_else(|| defect("no build of the tick's request"))?;
    eprintln!("{TRACE_BUILD_PREFIX}read {} ns; built {} ns; {} bytes", read.as_nanos(), took.join(","), asked.request.len());
    Ok(asked)
}

/// **The opt-in that times [`planner_request`]'s two halves** (T19, README gap 4662): its value is how many times
/// to build the request from the one read.
pub const TRACE_BUILD_ENV: &str = "TM_TRACE_PLANNER_BUILD";
/// The line [`TRACE_BUILD_ENV`] prints.
pub const TRACE_BUILD_PREFIX: &str = "planner request: ";

/// **What a tick's planner request reads from disk** (W-45 track Q, README gap 4662): the capacity request's
/// [`Reads`] — `config.toml`'s and `.tm/model.json`'s literals, every document, `tz.json`, the log — and the
/// hysteresis input, which `.tm/last_plan.json` holds before the day's first plan ([`Ctx::hysteresis_input`]).
/// Read by [`tick_inputs`]; the TUI keeps the one its reload read.
pub struct TickInputs {
    reads: Reads,
    yesterday: BTreeMap<Id, u8>,
}

/// **Read a tick's inputs**, once.
pub fn tick_inputs(ctx: &Ctx) -> Result<TickInputs, CliError> {
    Ok(TickInputs { reads: reads(ctx)?, yesterday: ctx.hysteresis_input() })
}


/// **[`planner_request`] and what it was built from**: the request, the
/// candidates it ranks (in `collect_candidates` order) and the order they were
/// sent in (`planwire::send_order`, which [`read_answer`] reads the grants by),
/// and the lookahead's horizon — the days asked for, the days wanted, and
/// whether `planwire::horizon` clamped them (gap 98, parity P30).
pub struct PlannerAsk {
    /// The request's text.
    pub request: String,
    /// The candidates the capacity section ranks.
    pub cands: Vec<Candidate>,
    /// The order they were sent in.
    pub order: Vec<usize>,
    /// The lookahead's days.
    pub days: u32,
    /// The days `priority::lookahead_days` wanted.
    pub want: u32,
    /// Whether the horizon clamped them.
    pub clamped: bool,
}

/// **[`planner_request`], with §9.1's what-if when `extend` names one** — `blocks`
/// more blocks on the item, its candidate facts grown as fork
/// `PlanOverrides::apply` grows them (`planwire::grown`, the owner's D58: the host's
/// one reading of the facts, never derived in the kernel, D34) — over
/// [`TickInputs`] already read: nothing here touches the plan directory.
pub fn planner_ask_from(
    ctx: &Ctx,
    inputs: &TickInputs,
    allow_home: bool,
    extend: Option<(&Id, u32)>,
) -> Result<PlannerAsk, CliError> {
    let mut state = ctx.state.clone();
    state.roll_to(ctx.today);
    let cands = priority::collect_candidates(&ctx.tree, &ctx.replay, &ctx.cfg, &ctx.model, ctx.today, ctx.now_tz);
    let yesterday = &inputs.yesterday;
    let want = priority::lookahead_days(&cands, ctx.today);
    let (days, clamped) = planwire::horizon(ctx.today, want);
    let ranked = Ranked { cands: &cands, yesterday };
    let (request, order) = request_with(ctx, &state, allow_home, days, Some(&ranked), &inputs.reads)?;
    // The section composed once, by the body every harness that builds it calls (README gap 4890):
    // the routines, the what-if, the running block's worked minutes (`day::worked_min`'s reading).
    let planner =
        tm_core::plansection::planner_section(&state, &ctx.replay, ctx.now_tz, ctx.cfg.tz, &ctx.tree, &cands, &ctx.cfg, extend);
    Ok(PlannerAsk { request: planwire::with_planner(&request, &planner), cands, order, days, want, clamped })
}

/// **The day the kernel planned** (R3), with what it was ranked by: the
/// candidates and their priorities (1:1, the grants of the same response), and
/// §9.1's what-if when one was asked.
pub struct Planned {
    /// The day, read by the host's codec (`planwire::read_plan`).
    pub day: tm_core::dayplan::DayPlan,
    /// The candidates the day was ranked over.
    pub cands: Vec<Candidate>,
    /// Their priorities.
    pub prios: Vec<tm_core::priority::Prio>,
    /// The lookahead's days, from the same answer (the Queue's "fits"; the W-45
    /// repair, README gap 4743).
    pub caps: Vec<UnitCapacity>,
    /// §9.1's what-if (`plan.overtime`), when `extend` asked for one.
    pub overtime: Option<tm_core::dayplan::PlanDiff>,
}

/// **§8's day, asked of the kernel** — R3's body swap (D48, D50): the plan
/// directory read once ([`tick_inputs`]) and [`plan_day_from`] over that read.
/// `tm plan`, `tm now` and every verb that replans call this, so they read the
/// files as they stand when the verb runs.
pub fn plan_day(ctx: &Ctx, allow_home: bool, extend: Option<(&Id, u32)>) -> Result<Planned, CliError> {
    plan_day_from(ctx, &tick_inputs(ctx)?, allow_home, extend)
}

/// **[`plan_day`] over [`TickInputs`] already read** — the request
/// [`planner_ask_from`] builds from them and the context alone, sent once, and
/// the answer read by the host's codec: the grants into priorities
/// ([`read_answer`], each checked to answer its own candidate) and the `plan`
/// object into a [`tm_core::dayplan::DayPlan`] (`planwire::read_plan`, whose
/// hash check refuses a day the decoder bent). A refusal is the kernel's, by
/// name — a configured value's by file and key (P26, [`named_refusal`]); a
/// response the codec cannot read is a fault, never a wrong day. **The TUI's
/// minute tick calls this** with the inputs its last reload or re-collection
/// read (the owner's D103, README gap 4662): a tick reads nothing from the
/// plan directory, as fork 4748911's tick replanned from the App's own data.
pub fn plan_day_from(
    ctx: &Ctx,
    inputs: &TickInputs,
    allow_home: bool,
    extend: Option<(&Id, u32)>,
) -> Result<Planned, CliError> {
    let ask = planner_ask_from(ctx, inputs, allow_home, extend)?;
    if ask.clamped {
        say_clamped(ctx.today, ask.want, ask.days);
    }
    if std::env::var_os(TRACE_REQUEST_ENV).is_some() && !kernel_bridge::capturing_kernel_stderr() {
        eprintln!("{TRACE_REQUEST_PREFIX}{}", ask.request);
    }
    read_day(ctx, ask).map_err(|e| match e {
        CliError::Kernel(issue) => named_refusal(&issue).unwrap_or(CliError::Kernel(issue)),
        e => e,
    })
}

/// **The kernel's answer to a [`PlannerAsk`], read by the host's ONE codec** (the
/// W-45 repair, README gap 4742): sent once, the grants read into priorities
/// ([`read_answer`], each checked to answer its own candidate) and the `plan`
/// object into a [`tm_core::dayplan::DayPlan`] (`planwire::read_plan`, whose hash
/// check refuses a day the decoder bent). A refusal comes back as the kernel's
/// own issue, unrenamed, so `tm check` can point at the line it names; a
/// response the codec cannot read is a fault. [`plan_day_from`] and `tm check`
/// both read through this, so a decoder fault `tm plan` would meet is one `tm
/// check` meets: until the repair `tm check` sent the request and never decoded
/// the answer, and printed `no problems` on a tree every planning verb faulted on
/// (README gap 4711).
pub fn read_day(ctx: &Ctx, ask: PlannerAsk) -> Result<Planned, CliError> {
    let (resp, _) = kernel_bridge::call_text(&ask.request)?;
    let answer = read_answer(&resp, &ask.order, true)?;
    for (c, p) in ask.cands.iter().zip(&answer.prios) {
        if c.id != p.id {
            return Err(defect("a grant answers another candidate"));
        }
    }
    let read = planwire::DayCtx { tz: ctx.cfg.tz, cands: &ask.cands, prios: &answer.prios };
    let day = planwire::read_plan(&resp["ok"]["plan"], &read).map_err(|e| {
        CliError::Kernel(kernel_bridge::fault_issue(&format!("planner response: {e}"), ""))
    })?;
    Ok(Planned { day: day.day, cands: ask.cands, prios: answer.prios, caps: answer.days, overtime: day.overtime })
}

/// **`tm plan --week`'s seven days** from the kernel.
pub fn week(ctx: &Ctx, allow_home: bool) -> Result<Vec<UnitCapacity>, CliError> {
    Ok(ask(ctx, allow_home, 7, None)?.days)
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use tm_core::planwire::{decimal_pair, PairErr, WEIGHT_PLACES};

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(4096))]

        /// **T15**: every finite non-negative double's pair is exactly the value
        /// its shortest text writes (the pair, rendered back as a decimal, parses to
        /// the same double), the denominator is `10^places` with `places` the text's,
        /// and a pair is refused exactly when the text has more places than allowed.
        #[test]
        fn t15_decimal_pair_is_the_shortest_text(bits in any::<u64>(), max in 0u32..=20) {
            let x = f64::from_bits(bits);
            match decimal_pair(x, max) {
                Err(PairErr::NotFinite) => prop_assert!(!x.is_finite()),
                Err(PairErr::Negative) => prop_assert!(x.is_finite() && x < 0.0),
                Err(PairErr::TooManyPlaces(n)) => {
                    prop_assert!(x.is_finite() && x >= 0.0 && n > max as usize);
                    prop_assert_eq!(format!("{x}").split_once('.').map_or(0, |(_, f)| f.len()), n);
                }
                Ok((num, den)) => {
                    prop_assert!(x.is_finite() && x >= 0.0);
                    let places = den.len() - 1;
                    prop_assert!(places <= max as usize);
                    prop_assert!(den.starts_with('1') && den[1..].bytes().all(|b| b == b'0'));
                    prop_assert!(num.bytes().all(|b| b.is_ascii_digit()) && (num == "0" || !num.starts_with('0')));
                    let padded = format!("{num:0>width$}", width = places + 1);
                    let (int, frac) = padded.split_at(padded.len() - places);
                    let back: f64 = format!("{int}.{frac}0").parse().unwrap();
                    prop_assert_eq!(back.to_bits(), x.abs().to_bits());
                }
            }
        }

        /// T15 over the lounge weights a hand edit writes: every decimal of at most
        /// 18 places in [0, 1] is sent as exactly itself.
        #[test]
        fn t15_a_written_weight_is_sent_as_written(n in 0u64..=1_000_000_000_000_000u64, places in 0u32..=15) {
            let den = 10u64.pow(places);
            let n = n % (den + 1);
            let text = if places == 0 { format!("{n}") } else { format!("{}.{:0>w$}", n / den, n % den, w = places as usize) };
            let x: f64 = text.parse().unwrap();
            let (num, d) = decimal_pair(x, WEIGHT_PLACES).unwrap();
            // The pair equals the written decimal as rationals.
            let (num, d) = (num.parse::<u128>().unwrap(), d.parse::<u128>().unwrap());
            prop_assert_eq!(num * u128::from(den), u128::from(n) * d);
        }
    }
}
