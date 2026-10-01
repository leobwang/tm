//! **The request R3 will send: four readings, pinned by value** — stage 6 W-41,
//! track E (README gaps 4040-4050; parity P76 and P77).
//!
//! * **P76** — the campaign's D81 call on README gap 3861. Before a tree's first
//!   `tm arrive` `.tm/state.json` holds no location, and fork 4748911 read that
//!   one fact two ways: its planner (`Planner::new`) as `Loc::Any` — the HOME
//!   curve, no home cap — and day 0's capacity (`Ctx::today_slots`, through
//!   `Ctx::loc`) as the LOUNGE. The kernel has one input for both
//!   (`Look.Today.loc`), and the capacity section now carries the planner's
//!   reading, `planwire::planned_loc`. What it moves is measured here by value:
//!   [`p76_the_capacity_section_carries_the_planners_location`],
//!   [`p76_moves_day_zero_and_no_bin_on_a_plain_morning`],
//!   [`p76_names_a_ci_five_item_due_today_impossible_where_the_lounge_ranked_it`]
//!   and [`p76_any_is_the_home_curve_with_no_home_cap`].
//! * **P77** — the campaign's D81 call on README gap 3860. A TUI left open past
//!   local midnight replans with the state it loaded, dated yesterday; the kernel
//!   reads that state as `tm plan`'s roll leaves it (`Look.Today.forToday`: none
//!   of its window, budget or arrival), where the fork planned the state's date —
//!   and the request the TUI builds is not yet `tm plan`'s (README gap 4050):
//!   [`p77_a_tui_left_open_past_midnight_plans_the_day_tm_plan_would_plan`].
//! * **Gap 3941** (README gap 4042) — the harness's worked minutes are the
//!   binary's (`day::worked_min`, D75):
//!   [`gap_3941_the_harness_reads_the_logs_worked_minutes_across_midnight`].
//! * **Gap 3962** (measured under README gap 4042) — the replay
//!   R3's swap hands `planwire::planner_json` holds the open block whatever its
//!   age: [`gap_3962_the_binarys_replay_holds_an_open_block_begun_ten_days_ago`].

mod cli_common;
mod tui_common;

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[allow(dead_code)]
#[path = "support/planreq.rs"]
mod planreq;

#[allow(dead_code)]
#[path = "support/forkday.rs"]
mod forkday;

#[allow(dead_code)]
#[path = "support/plangen.rs"]
mod plangen;

#[allow(dead_code)]
#[path = "support/forkclass.rs"]
mod forkclass;

use std::path::Path;

use chrono::{DateTime, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use serde_json::{json, Value};

use tm_core::capacity::local_dt;
use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::Replay;
use tm_core::planwire::{self, CapacityAnswer, LoggedStarts};
use tm_core::priority::{self, Candidate, PrioClass};
use tm_core::store::{MemStore, RuntimeState, Store};
use tm_core::tree::Tree;

use cli_common::Tm;
use forkclass::{Built, ClassWorld};

/// `kernel_capacity.rs`' `TRACE_REQUEST_ENV` and its prefix, spelled out: `tm` is a
/// binary-only package (`planner_request_keys.rs` reads them the same way).
const TRACE_REQUEST_ENV: &str = "TM_TRACE_CAPACITY_REQUEST";
const TRACE_REQUEST_PREFIX: &str = "capacity request: ";
/// `ctx.rs`' `TRACE_SCOPE_ENV` and its line (`kernel_call_counts.rs` reads them so).
const TRACE_SCOPE_ENV: &str = "TM_TRACE_REPLAY_SCOPE";

/// The plain Monday morning every P76 world is planned at.
const MORNING: &str = "2026-09-07T09:00:00-05:00";

// ---------------------------------------------------------------------------
// Worlds and the requests built over them
// ---------------------------------------------------------------------------

/// `tm plan` at `at` with the capacity trace on: the ranked request the binary sent,
/// parsed only to READ it (its `log` section is in build order; nothing here re-sends it).
fn sent_request(tm: &Tm, at: &str) -> Value {
    let out = tm.run_env_at(at, &[(TRACE_REQUEST_ENV, "1")], &["plan"]);
    assert_eq!(out.code, 0, "`tm plan` failed:\n{}{}", out.stdout, out.stderr);
    let text = out
        .stderr
        .lines()
        .filter_map(|l| l.strip_prefix(TRACE_REQUEST_PREFIX))
        .filter_map(|t| serde_json::from_str::<Value>(t).ok())
        .rfind(|v| v["capacity"].get("candidates").is_some());
    text.expect("the binary printed its ranked capacity request (the trace is alive)")
}

/// A fixture tree of `tm-core/tests/fixtures`, copied into a fresh temporary plan.
fn fixture(name: &str) -> Tm {
    let tm = Tm::empty();
    let from = Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-core/tests/fixtures").join(name);
    copy_dir(&from, &tm.plan);
    tm
}

fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).expect("create dir");
    for entry in std::fs::read_dir(from).expect("read fixture") {
        let entry = entry.expect("dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            std::fs::copy(entry.path(), &target).expect("copy file");
        }
    }
}

/// `plan-basic` after `tm arrive home` at 08:00, with `.tm/state.json`'s `loc` then
/// cleared by hand: the cache holds no location and the log's day record does.
fn arrived_home_cache_cleared() -> Tm {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T08:00:00-05:00", &["arrive", "home"]);
    let path = tm.plan.join(".tm/state.json");
    let mut state: Value = serde_json::from_str(&std::fs::read_to_string(&path).expect("state")).expect("JSON");
    state["loc"] = Value::Null;
    std::fs::write(&path, state.to_string()).expect("state written");
    tm
}

/// `plan-basic` with one demanding task due today: `ci:5`, one block, `due:` 17:00.
fn ci_five_due_today() -> Tm {
    let tm = Tm::new();
    let week = tm.plan.join("week/2026-W37.md");
    let text = std::fs::read_to_string(&week).expect("the week file");
    let text = text.replacen("# Tasks\n", "# Tasks\n- [ ] 5 1b Deep focus sprint  due:2026-09-07T17:00 ^z1\n", 1);
    assert!(text.contains("^z1"), "the task went in");
    std::fs::write(&week, text).expect("the week file written");
    tm
}

/// **A plan directory read as the harness reads one** — the request every planning suite
/// builds (`planreq::request`, through the binary's one encoder `planwire::capacity_json`),
/// over the tree on disk at `at`.
struct Read {
    tree: Tree,
    cfg: Config,
    replay: Replay,
    state: RuntimeState,
    docs: Vec<(String, String)>,
    log: String,
    now: DateTime<Tz>,
    cands: Vec<Candidate>,
}

fn read(dir: &Path, at: &str) -> Read {
    let store = MemStore::from_dir(dir).expect("the tree reads");
    let plan = store.read_tree().expect("the tree parses");
    let tree = Tree::build(&plan.files, &plan.config);
    let log = std::fs::read_to_string(dir.join(".tm/log.jsonl")).unwrap_or_default();
    let replay = chokepoint::replay_of_text(&log, plan.config.tz);
    let state = store.load_state().expect("state.json parses");
    let docs = planreq::docs_of_dir(dir);
    let now = DateTime::parse_from_rfc3339(at).expect("an instant").with_timezone(&plan.config.tz);
    let cands = priority::collect_candidates(&tree, &replay, &plan.config, &Model::default(), now.date_naive(), now);
    Read { tree, cfg: plan.config, replay, state, docs, log, now, cands }
}

impl Read {
    fn world(&self) -> planreq::World<'_> {
        planreq::World {
            docs: &self.docs,
            log: &self.log,
            tree: &self.tree,
            cfg: &self.cfg,
            state: &self.state,
            now: self.now,
            cands: &self.cands,
            replay: &self.replay,
        }
    }

    /// The harness's request, with the capacity section's `state.loc` and `allowHome`
    /// replaced when `loc` names them — the probe of what the location moves.
    fn request(&self, loc: Option<(&str, bool)>) -> (Value, Vec<usize>) {
        let (mut req, order) = planreq::request(&self.world(), None);
        if let Some((l, allow_home)) = loc {
            req["capacity"]["state"]["loc"] = json!(l);
            req["capacity"]["state"]["allowHome"] = json!(allow_home);
        }
        (req, order)
    }

    /// The kernel's capacity answer (its grants and its first days) to [`Read::request`].
    fn answer(&self, loc: Option<(&str, bool)>) -> CapacityAnswer {
        let (req, order) = self.request(loc);
        let resp = planreq::call(&req);
        planwire::read_capacity_answer(&resp, &order, true)
            .unwrap_or_else(|e| panic!("the capacity answer reads: {e}: {}", resp["err"]))
    }
}

/// Day 0 as whole-minute floors, for a message.
fn floors(a: &CapacityAnswer) -> [u32; 6] {
    a.days[0].minutes_at_level_floor()
}

// ---------------------------------------------------------------------------
// P76: one location for the planner and day 0's capacity
// ---------------------------------------------------------------------------

/// **The capacity section carries the planner's location** (P76, `planwire::planned_loc`):
/// `any` on a tree no `tm arrive` located — where `Ctx::loc` read the lounge — the day
/// record's logged `arrive` where the cache holds none (fork `Planner::new`'s middle
/// reading), and the stored location wherever there is one. Read off the binary's own
/// request (`TM_TRACE_CAPACITY_REQUEST`), the one encoder R3 swaps in.
#[test]
fn p76_the_capacity_section_carries_the_planners_location() {
    let fresh = Tm::new();
    assert_eq!(sent_request(&fresh, MORNING)["capacity"]["state"]["loc"], "any", "no `tm arrive`: the planner's `any`");

    let cleared = arrived_home_cache_cleared();
    let state: Value = serde_json::from_str(&cleared.read(".tm/state.json")).expect("state");
    assert!(state["loc"].is_null(), "the cache holds no location: {state}");
    assert_eq!(sent_request(&cleared, MORNING)["capacity"]["state"]["loc"], "home", "the day record's `arrive`");

    let lounge = Tm::new();
    lounge.ok_at("2026-09-07T08:00:00-05:00", &["arrive", "lounge"]);
    assert_eq!(sent_request(&lounge, MORNING)["capacity"]["state"]["loc"], "lounge", "the stored location");

    let home_day = fixture("plan-home-day");
    assert_eq!(sent_request(&home_day, "2026-09-07T10:00:00-05:00")["capacity"]["state"]["loc"], "home", "the fixture's stored location");
}

/// **What P76 moves on a plain morning, by value** — `plan-basic` at 09:00, no `tm
/// arrive`: day 0's TOTAL is the same, its minutes sit at lower levels (the home curve
/// where the lounge's was read), the later days do not move, the grants' availability
/// falls for the candidates that need the top levels, and NO candidate's `p` moves — so
/// the shipped `tm plan` lays out and ranks the same day. (It is not so on every morning:
/// [`p76_names_a_ci_five_item_due_today_impossible_where_the_lounge_ranked_it`].)
#[test]
fn p76_moves_day_zero_and_no_bin_on_a_plain_morning() {
    let tm = Tm::new();
    let r = read(&tm.plan, MORNING);
    assert_eq!(r.request(None).0["capacity"]["state"]["loc"], "any", "the harness's request is the binary's encoder's");
    let any = r.answer(None);
    let lounge = r.answer(Some(("lounge", false)));
    println!("day 0 at 09:00: lounge {:?} -> any {:?}", floors(&lounge), floors(&any));
    assert_eq!(floors(&lounge), [0, 0, 30, 120, 90, 180], "fork `Ctx::today_slots`' day 0, read as the lounge");
    assert_eq!(floors(&any), [0, 0, 150, 150, 120, 0], "the planner's day 0, read as `any`");
    assert_eq!(any.days[0].total_units(), lounge.days[0].total_units(), "the same slots, at other levels");
    assert_eq!(any.days[1..], lounge.days[1..], "a later day is a mixture of both curves and does not read the location");
    let mut fell = Vec::new();
    for (a, l) in any.prios.iter().zip(&lounge.prios) {
        assert_eq!((&a.id, a.p, a.class), (&l.id, l.p, l.class), "a bin moved: {} lounge {:?} any {:?}", a.id, l, a);
        if a.avail_min != l.avail_min {
            fell.push(format!("{} {}→{}", a.id.token(), l.avail_min, a.avail_min));
            assert!(a.avail_min < l.avail_min, "{}: the home curve gives less at its levels", a.id);
        }
    }
    println!("availability moved: {}", fell.join(", "));
    assert_eq!(fell.len(), 3, "the three ci-4/5 candidates' availability falls: {fell:?}");
}

/// **And where it moves the shipped `tm plan`** — a `ci:5` task due today at 17:00 on the
/// same morning. Read as the lounge, day 0 holds 180 minutes at level 5 and the task is
/// ranked `p4` and dropped in silence (the fork's planner, on the home curve, has no
/// level-5 slot to give it); read as `any`, day 0 holds none, the task is HOT and
/// IMPOSSIBLE, and `tm plan` names it. Both directions, by value.
#[test]
fn p76_names_a_ci_five_item_due_today_impossible_where_the_lounge_ranked_it() {
    let tm = ci_five_due_today();
    let r = read(&tm.plan, MORNING);
    let at = |a: &CapacityAnswer| a.prios.iter().find(|p| p.id.as_str() == "z1").cloned().expect("z1 is a candidate");
    let (any, lounge) = (at(&r.answer(None)), at(&r.answer(Some(("lounge", false)))));
    println!("z1 lounge: p{} {:?} avail {}; any: p{} {:?} avail {} short {}", lounge.p, lounge.class, lounge.avail_min, any.p, any.class, any.avail_min, any.shortfall_min);
    assert_eq!((lounge.p, lounge.class, lounge.avail_min), (4, PrioClass::Dated, 180), "read as the lounge");
    assert_eq!((any.p, any.class, any.avail_min, any.shortfall_min), (0, PrioClass::Impossible, 0, 78), "read as `any`");
    let out = tm.ok_at(MORNING, &["plan"]).stdout;
    assert!(out.contains("IMPOSSIBLE z1 Deep focus sprint"), "the shipped `tm plan` names it:\n{out}");
    assert!(out.contains("· hot: z1"), "and calls it hot:\n{out}");
}

/// **`any` is the home curve with no home cap** (fork `energy::curve_key` and
/// `EnergyCtx::cap_for_location`, the kernel's `Look.curveKeyOf` and `Look.capLoc`): day 0
/// read as `any` is day 0 read as `home` with `--allow-home`, and not as `home` without it
/// (`home_max_ci = 3` lowers the curve's level-4 stretch).
#[test]
fn p76_any_is_the_home_curve_with_no_home_cap() {
    let tm = Tm::new();
    let r = read(&tm.plan, MORNING);
    let any = r.answer(Some(("any", false)));
    let home_lifted = r.answer(Some(("home", true)));
    let home_capped = r.answer(Some(("home", false)));
    assert_eq!(any.days[0], home_lifted.days[0], "`any` is the home curve, uncapped");
    assert_ne!(any.days[0], home_capped.days[0], "the home cap bites on this morning");
    assert_eq!(floors(&home_capped), [0, 0, 150, 270, 0, 0], "capped at ci 3");
}

// ---------------------------------------------------------------------------
// P77: a TUI left open past midnight
// ---------------------------------------------------------------------------

/// **R3's request over a world, as `forkclass::kernel_answer_with_grants` builds it** — the
/// harness's request, the what-if's grown facts and the host's worked minutes — with the order
/// its candidates were sent in, and the kernel's day read back over that world.
fn r3_request(b: &Built) -> (Value, Vec<usize>) {
    let (mut req, order) = planreq::request(&b.request_world(), forkclass::whatif_json(b));
    if let Some(worked) = forkclass::host_worked(b) {
        planwire::add_worked_min(&mut req["planner"], worked);
    }
    (req, order)
}

fn r3_day(req: &Value, b: &Built, order: &[usize]) -> tm_core::planwire::KernelDay {
    let resp = planreq::call(req);
    planreq::kernel_day_of(&resp, &b.request_world(), order).unwrap_or_else(|e| panic!("the kernel plans the world: {e}")).0
}

/// The routine instances a request sends, as `id@inst`.
fn routines_of(req: &Value) -> Vec<String> {
    req["planner"]["routines"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default()
        .iter()
        .map(|r| format!("{}@{}", r["id"].as_str().unwrap_or_default(), r["inst"].as_str().unwrap_or("-")))
        .collect()
}

/// **A TUI left open past local midnight: the kernel reads its stale state as `tm plan`'s roll
/// leaves it** (P77, the campaign's D81 call on README gap 3860) **— and the request it would
/// send is not yet `tm plan`'s** (README gap 4050).
///
/// The world is the TUI's own (`tui_common`: §4.3's day, `^t3` running since 09:32,
/// `.tm/state.json` dated Monday with its window, budget and arrival), opened at 23:50 Monday
/// and left open to 00:30 Tuesday: `App::tick` moves `now` and `today`, replans, and rolls
/// nothing. Through the request R3's host sends:
///
/// * **the kernel's reading, registered**: the kernel's day for the stale request IS its day
///   for the same request with both `state` objects (the capacity section's and the planner
///   section's) rolled as the binary's housekeeping rolls them (`RuntimeState::roll_to`,
///   `ctx.rs`' `roll_day`) — Tuesday's day, from 00:30; and the date gate is what makes them
///   one (Monday's window kept on a state dated Tuesday plans another day), while the fork
///   plans the state's date, Monday (`planwire::plan_date`);
/// * **the request is not `tm plan`'s**: the harness — as the TUI does between reloads —
///   collects the candidates and §8.2 step 2's routine instances on the PLANNED date,
///   `planwire::plan_date`, the stale state's Monday, so the request misses Tuesday's
///   instances that `tm plan`'s request, built over the rolled state, carries (`breakfast`,
///   mandatory, at 06:00) — and the two days differ. Pinned so the step that closes gap
///   4050 sees this flip.
#[test]
fn p77_a_tui_left_open_past_midnight_plans_the_day_tm_plan_would_plan() {
    let cfg = tui_common::config();
    let tuesday = tui_common::date().succ_opt().expect("tomorrow");
    let now = local_dt(cfg.tz, tuesday, NaiveTime::from_hms_opt(0, 30, 0).expect("time"));
    let log = tui_common::log(&cfg);
    let mut app = tui_common::app_with_log_text(tui_common::at(&cfg, 23, 50), tui_common::state(), &log);
    let loaded = app.state.clone();
    app.tick(now);
    assert_eq!((app.today, app.state.date), (tuesday, Some(tui_common::date())), "the TUI holds Monday's state on Tuesday");
    assert_eq!(app.state, loaded, "a tick rolls nothing");
    let stale = app.state.clone();
    assert!(stale.window.is_some() && stale.budget.is_some() && stale.arrival.is_some(), "the stale state's day facts are set");
    let mut rolled = stale.clone();
    assert!(rolled.roll_to(tuesday), "the binary's housekeeping rolls this state");

    let built = |state: RuntimeState| Built::of(ClassWorld { docs: tui_common::tree_texts(), log: log.clone(), state, now, mult: None, ratio: None });
    let (b_stale, b_rolled) = (built(stale.clone()), built(rolled));
    let (req_stale, order) = r3_request(&b_stale);
    let (req_rolled, order_rolled) = r3_request(&b_rolled);
    let k_stale = r3_day(&req_stale, &b_stale, &order);
    assert_eq!(k_stale.day.date, tuesday, "the kernel plans now's date");
    assert_eq!(k_stale.day.window.0, now, "the day runs from now: Monday's 07:00 arrival is not Tuesday's");
    assert!(k_stale.day.segments.iter().any(|s| s.flags.current), "the running block is the current row");

    // The kernel's reading: the same request, its two `state` objects rolled.
    let mut req_read = req_stale.clone();
    req_read["capacity"]["state"] = req_rolled["capacity"]["state"].clone();
    req_read["planner"]["state"] = req_rolled["planner"]["state"].clone();
    assert_ne!(req_read, req_stale, "the rolled state is another state on the wire");
    assert_eq!(r3_day(&req_read, &b_stale, &order), k_stale, "the stale state is read as the rolled one: one day, hash and what-if");

    // Non-vacuity (AGENTS §5.2): a state that WAS today's is read whole — Monday's window,
    // budget and arrival dated Tuesday plan another window — so the date gate is what makes
    // the two above one.
    let mut req_today = req_stale.clone();
    req_today["capacity"]["state"]["date"] = json!(tuesday.to_string());
    assert_ne!(r3_day(&req_today, &b_stale, &order).day.window, k_stale.day.window, "a state dated today is read whole");

    // Gap 4050: the request `tm plan` would send after its roll carries Tuesday's routine
    // instances, and the stale world's does not.
    let (r_stale, r_rolled) = (routines_of(&req_stale), routines_of(&req_rolled));
    println!("routine instances: stale world {r_stale:?}; rolled world {r_rolled:?}");
    assert!(r_rolled.iter().any(|r| r == "breakfast@2026-09-08"), "tm plan's request carries Tuesday's breakfast: {r_rolled:?}");
    assert!(!r_stale.iter().any(|r| r.ends_with("@2026-09-08")), "the stale world's request carries no Tuesday instance: {r_stale:?}");
    let k_rolled = r3_day(&req_rolled, &b_rolled, &order_rolled);
    assert_eq!(k_rolled.day.date, tuesday);
    assert_ne!(k_rolled.hash, k_stale.hash, "so the TUI's day is not yet tm plan's (gap 4050)");
    assert!(
        k_rolled.day.segments.iter().any(|s| s.item.as_ref().is_some_and(|i| i.as_str() == "breakfast"))
            && !k_stale.day.segments.iter().any(|s| s.item.as_ref().is_some_and(|i| i.as_str() == "breakfast")),
        "the difference is Tuesday's breakfast"
    );

    // The fork's half, while it is here: it plans the STATE's date (`planwire::plan_date`).
    assert_eq!(planwire::plan_date(&stale, now), tui_common::date(), "the fork plans Monday on this state");
}

// ---------------------------------------------------------------------------
// Gaps 3941 and 3962: the worked minutes and the replay the swap reads
// ---------------------------------------------------------------------------

/// **The harness reads the binary's worked minutes where the old reading was wrong**
/// (README gaps 3941 and 4042). `tm start ^t4` at Monday 23:00 and `tm now` at 00:40
/// Tuesday (its housekeeping rolls `.tm/state.json` to Tuesday): `forkclass::host_worked`
/// is the log's 100 minutes — `day::worked_min`'s, which `tm now` prints — where the
/// cache's `23:00` on the planned date (Tuesday's, after `now`) read 0. And on a world the
/// binary never builds — a running block the log does not hold — it answers `None`, as
/// `day::worked_min` does, and the kernel reads fork `active_run`'s own clock.
#[test]
fn gap_3941_the_harness_reads_the_logs_worked_minutes_across_midnight() {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T23:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    let at = "2026-09-08T00:40:00-05:00";
    let shown = tm.json_at(at, &["now"]);
    assert_eq!(shown["active"]["elapsed_min"], 100, "the binary's own reading: {}", shown["active"]);
    let r = read(&tm.plan, at);
    assert_eq!(r.state.date, Some(NaiveDate::from_ymd_opt(2026, 9, 8).expect("date")), "the cache rolled");
    let b = Built::of(ClassWorld { docs: r.docs.clone(), log: r.log.clone(), state: r.state.clone(), now: r.now, mult: None, ratio: None });
    assert_eq!(forkclass::host_worked(&b), Some(100), "the harness reads the log's start");
    let a = r.state.active.as_ref().expect("^t4 runs");
    let cache = local_dt(r.cfg.tz, b.date(), a.started);
    assert!(cache > r.now, "the cache's 23:00 on the planned date is tonight's, after now: the old reading counted 0 ({cache})");

    // A running block the log does not hold: no number, as the binary's own reading.
    let cfg = tui_common::config();
    let mut state = tui_common::state();
    if let Some(a) = state.active.as_mut() {
        a.started = NaiveTime::from_hms_opt(23, 30, 0).expect("time");
    }
    let midnight = local_dt(cfg.tz, tui_common::date().succ_opt().expect("tomorrow"), NaiveTime::from_hms_opt(0, 30, 0).expect("time"));
    let empty = Built::of(ClassWorld { docs: tui_common::tree_texts(), log: String::new(), state, now: midnight, mult: None, ratio: None });
    assert_eq!(forkclass::host_worked(&empty), None, "the log holds no open block for it");
    assert_eq!(empty.worked(), Some(60), "fork `active_run`'s clock since the cache's start, which the kernel then reads");
}

/// **The harness nets a break running across midnight out of the block as the binary does**
/// (README gap 4121, the W-41 land step's composition of track E's `forkclass::host_worked`
/// with track T's P73). `tm start ^t4` at Monday 23:00, `tm break 30m` at 23:50, and `tm now`
/// at 00:10 Tuesday: the binary places the running break at the latest 23:50 at or before
/// `now` (`BreakState::started_at`, P73) — Monday's — and nets its 20 minutes out of the 70,
/// and so does the harness's one reading of the host's worked minutes. Track E wrote that
/// reading with the break's `HH:MM` on `now`'s date — Tuesday's 23:50, after `now`, netting
/// nothing — which agreed with the binary on every world until P73 moved the binary's.
#[test]
fn the_harness_nets_a_break_across_midnight_as_the_binary_does() {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T23:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T23:50:00-05:00", &["break", "30m"]);
    let at = "2026-09-08T00:10:00-05:00";
    let shown = tm.json_at(at, &["now"]);
    let r = read(&tm.plan, at);
    assert!(r.state.break_.as_ref().is_some_and(|x| x.started.is_some()), "a break runs: {:?}", r.state.break_);
    let b = Built::of(ClassWorld { docs: r.docs.clone(), log: r.log.clone(), state: r.state.clone(), now: r.now, mult: None, ratio: None });
    let host = forkclass::host_worked(&b);
    assert_eq!(serde_json::json!(host), shown["active"]["elapsed_min"], "the binary's own reading: {}", shown["active"]);
    assert_eq!(host, Some(50), "70 minutes since the start, the break's 20 netted out");
}

/// **The replay R3's swap hands `planwire::planner_json` holds the open block whatever its
/// age** (README gap 3962). `ctx.replay` is the verb's SCOPED replay (`hot` for `tm now`
/// and `tm plan`), and a block begun ten days before the verb is still its open block:
/// `tm now` shows the log's 14,400 minutes — the cache's `09:00` on today's date would
/// read 0 — and the whole log's replay names the same start, which is what
/// `LoggedStarts` reads.
#[test]
fn gap_3962_the_binarys_replay_holds_an_open_block_begun_ten_days_ago() {
    let tm = Tm::new();
    tm.ok_at("2026-08-28T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    let out = tm.run_env_at(MORNING, &[(TRACE_SCOPE_ENV, "1")], &["--json", "now"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.lines().any(|l| l == "replay scope: hot"), "the verb's scope: {}", out.stderr);
    let shown: Value = serde_json::from_str(&out.stdout).expect("JSON");
    assert_eq!(shown["active"]["elapsed_min"], 10 * 1440, "the scoped replay's open block: {}", shown["active"]);
    let r = read(&tm.plan, MORNING);
    let logged = LoggedStarts::of(&r.replay);
    let started = DateTime::parse_from_rfc3339("2026-08-28T09:00:00-05:00").expect("an instant");
    assert_eq!(logged.block, Some(("t4".to_string(), started)), "the start `state_json` sends");
}
