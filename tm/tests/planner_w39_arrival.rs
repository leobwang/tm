//! **The day's arrival, window and budget have one reading each, and it is the
//! fork's** — stage 6 W-39, track A (README gaps 3390, 3398, 3535 and 3531).
//!
//! * **Gap 3390.** Fork `Planner::new` reads its arrival in three steps: the
//!   state's own, else the day's first logged `arrive`, else `now`. The kernel's
//!   planner reads the same three since W-39 (`Look.Today.planArrivalSec` over
//!   `Planner.PlanReq.loggedArrival`). [`the_woken_day_is_planned_from_the_logged_arrival`]
//!   builds the world with the binary's own verbs — `tm arrive` at 07:00, then
//!   `tm wake` — lets the shipped `tm plan` (the fork's planner until R3) print
//!   its window, and asks the kernel's planner, through `tm_kernel_call`, for the
//!   day of the same files.
//! * **Gap 3398.** D42's rebuild of that world restored the arrival, window and
//!   budget `tm wake` cleared until the W-39 repair (README gap 3710); it now
//!   derives what the wake wrote, and the kernel plans the same day from either
//!   cache — the same test, after `rm .tm/state.json`.
//!   [`two_arrivals_then_a_wake_plan_one_day_from_either_cache`] is the world
//!   on which the old rebuild MOVED the day: two arrivals, then a wake.
//! * **Gap 3535.** Day 0's capacity counts a stored window only dated today with
//!   its budget (`Look.Today.storedWindow`), the planner whenever the state is
//!   today's (`Look.Today.planWindow`); the two are one on every state the
//!   binary writes (`Look.Today.storedWindow_is_planWindow_on_a_written_state`,
//!   over `Look.Today.BinaryWritten`). [`every_state_the_binary_writes_stores_a_window_only_with_its_day_and_budget`]
//!   drives every writer of `.tm/state.json`'s window — `tm arrive`, `tm wake`,
//!   the day roll and D42's rebuild, one arrival and two — and reads the file
//!   after each verb.
//! * **Gap 3531.** The file-kind `ci` default is written twice, `Horizon::default_ci`
//!   and `Tm.DocKind.ciDefault`. [`the_hosts_file_kind_ci_default_is_the_kernels`]
//!   pins the host's table to the kernel's rows and the candidates it collects
//!   to the wire values `PlannerWit.the_plan_and_the_wire_read_the_file_kinds_ci_alike`
//!   decides `PlanCheck.candsAgree` at, so an edit to one table and not the
//!   other fails a committed check.
//!
//! The fork comparison is one `BEGIN THE FORK PLANNER` region, which R3 deleted.

mod cli_common;
mod planner_common;

#[allow(dead_code)]
#[path = "support/forkday.rs"]
mod forkday;

#[allow(dead_code)]
#[path = "support/srcwalk.rs"]
mod srcwalk;

use std::path::Path;

use chrono::{DateTime, NaiveDate};
use chrono_tz::Tz;
use cli_common::Tm;
use planner_common::{at, of_texts, Fixture};
use serde_json::Value;
use tm_core::energy::Model;
use tm_core::model::Horizon;
use tm_core::priority;
use tm_core::store::{MemStore, Store};
use tm_core::tree::Tree;

/// The plan directory a drive left, loaded as `planner_common::load_with_log`
/// loads a fixture: the tree, the log's text and its replay, `.tm/state.json`
/// and the documents the request sends.
fn fixture_of(dir: &Path) -> Fixture {
    let store = MemStore::from_dir(dir).expect("the tree reads");
    let plan = store.read_tree().expect("the tree parses");
    let tree = Tree::build(&plan.files, &plan.config);
    let log = std::fs::read_to_string(dir.join(".tm/log.jsonl")).unwrap_or_default();
    let replay = planner_common::chokepoint::replay_of_text(&log, plan.config.tz);
    let state = store.load_state().expect("state.json parses");
    let docs = planner_common::planreq::docs_of_dir(dir);
    Fixture { tree, cfg: plan.config, replay, state, model: Model::default(), docs, log }
}

/// A day's window in the plan's zone.
fn window_of(day: &tm_core::dayplan::DayPlan, tz: Tz) -> (DateTime<Tz>, DateTime<Tz>) {
    (day.window.0.with_timezone(&tz), day.window.1.with_timezone(&tz))
}

/// `tm arrive` at 07:00, then `tm wake 06:05` at 07:30: gap 3390's world, built by
/// the binary's own verbs.
fn woken_tree() -> Tm {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]);
    tm.ok_at("2026-09-07T07:30:00-05:00", &["wake", "06:05"]);
    tm
}

/// **README gaps 3390 and 3398, on the binary's own files.** `tm arrive` at 07:00
/// and `tm wake 06:05` at 07:30 leave a state dated today with no arrival, window
/// or budget, beside a log that keeps the `arrive`. The shipped `tm plan` at
/// 10:30 prints the fork's window, 07:00–16:00; the kernel's planner, asked
/// through the FFI for the day of the same files, answers the same window — and
/// after `rm .tm/state.json` the next verb rebuilds the state the wake left (no
/// arrival, window or budget: README gap 3710, D42 and D45) and the kernel plans
/// the same day again.
#[test]
fn the_woken_day_is_planned_from_the_logged_arrival() {
    let tm = woken_tree();
    let st = tm.state();
    assert_eq!(st["date"], "2026-09-07", "{st}");
    for key in ["arrival", "window", "budget"] {
        assert!(st[key].is_null(), "`tm wake` clears `{key}`: {st}");
    }
    assert!(tm.log().iter().any(|e| e["ev"] == "arrive"), "the log keeps the `arrive`");

    let plan = tm.ok_at("2026-09-07T10:30:00-05:00", &["plan"]);
    assert!(
        plan.stdout.contains("window 07:00–16:00"),
        "the shipped `tm plan` plans from the logged arrival:\n{}",
        plan.stdout
    );

    let now = at("2026-09-07", 10, 30);
    let want = (at("2026-09-07", 7, 0), at("2026-09-07", 16, 0));
    let woken = fixture_of(&tm.plan);
    let tz = woken.cfg.tz;
    let k = woken.kernel_day(&woken.state, now).expect("the kernel plans the woken day");
    assert_eq!(window_of(&k, tz), want, "the kernel's planner, through the FFI");

    // D42: the next verb rebuilds the state from the log (README gaps 3398,
    // 3710) — and what it rebuilds is what the cache held: the wake's.
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    tm.ok_at("2026-09-07T10:30:00-05:00", &["plan"]);
    let st = tm.state();
    for key in ["arrival", "window", "budget"] {
        assert!(st[key].is_null(), "the rebuild derives the wake's `{key}`: {st}");
    }
    let rebuilt = fixture_of(&tm.plan);
    let r = rebuilt.kernel_day(&rebuilt.state, now).expect("the kernel plans the rebuilt day");
    assert_eq!(window_of(&r, tz), want, "the rebuilt state's window");
    assert_eq!(r.budget_blocks, k.budget_blocks, "the rebuilt state's budget");
    assert_eq!(r.hash(), k.hash(), "the rebuild moves nothing the kernel plans");
    assert_eq!(r.segments, k.segments, "row for row");
}

/// `window` present ⇒ `date` is today and `budget` is present:
/// `Look.Today.BinaryWritten`, read off the file the binary wrote.
fn binary_written(st: &Value, today: &str) -> bool {
    st["window"].is_null() || (st["date"] == today && !st["budget"].is_null())
}

/// One verb of a drive: the instant, the arguments, or a deletion of the cache.
enum Step {
    Run(&'static str, &'static [&'static str]),
    DropCache,
}

/// **README gap 3535: every `.tm/state.json` the binary writes stores a window
/// only beside its day and its budget** — the class on which
/// `Look.Today.storedWindow_is_planWindow_on_a_written_state` makes day 0's
/// capacity and the planner read one stored window. Each drive reaches one
/// writer of the window: `tm arrive` (once and twice in a day), `tm wake` after
/// an arrival, the day roll on the first verb of the next day, and D42's rebuild
/// from one arrival record and from two (`Ctx::arrival_window`). The file is
/// read after EVERY step, and every writer is seen to write a window at least
/// once, so the class is not held vacuously.
#[test]
fn every_state_the_binary_writes_stores_a_window_only_with_its_day_and_budget() {
    use Step::{DropCache, Run};
    let drives: [&[Step]; 4] = [
        // Arrive, work, wake (clears), arrive again, plan.
        &[
            Run("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]),
            Run("2026-09-07T07:05:00-05:00", &["start", "^t4", "--energy", "4"]),
            Run("2026-09-07T08:00:00-05:00", &["stop"]),
            Run("2026-09-07T08:30:00-05:00", &["wake", "06:05"]),
            Run("2026-09-07T09:00:00-05:00", &["plan"]),
            Run("2026-09-07T12:00:00-05:00", &["arrive", "home"]),
            Run("2026-09-07T12:30:00-05:00", &["plan"]),
        ],
        // Two arrivals, then the rebuild: the log carries no payload for the second.
        &[
            Run("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]),
            Run("2026-09-07T09:00:00-05:00", &["arrive", "home"]),
            DropCache,
            Run("2026-09-07T10:00:00-05:00", &["plan"]),
        ],
        // The day roll: an arrival, then the first verb of the next day.
        &[
            Run("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]),
            Run("2026-09-08T08:00:00-05:00", &["plan"]),
            Run("2026-09-08T08:10:00-05:00", &["arrive", "lounge"]),
            DropCache,
            Run("2026-09-08T09:00:00-05:00", &["plan"]),
        ],
        // Gap 3390's world, then the rebuild: since gap 3710 it derives what
        // `tm wake` cleared as cleared, as the cache held it.
        &[
            Run("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]),
            Run("2026-09-07T07:30:00-05:00", &["wake", "06:05"]),
            Run("2026-09-07T10:30:00-05:00", &["plan"]),
            DropCache,
            Run("2026-09-07T10:30:00-05:00", &["plan"]),
        ],
    ];
    let mut states = 0;
    let mut with_window = 0;
    for (d, drive) in drives.iter().enumerate() {
        let tm = Tm::new();
        for (s, step) in drive.iter().enumerate() {
            let now = match step {
                Run(now, args) => {
                    tm.ok_at(now, args);
                    *now
                }
                DropCache => {
                    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
                    continue;
                }
            };
            let st = tm.state();
            let today = &now[..10];
            assert!(
                binary_written(&st, today),
                "drive {d} step {s} (`tm {now}`): a window without its day or its budget: {st}"
            );
            states += 1;
            with_window += usize::from(!st["window"].is_null());
        }
    }
    println!("{states} states read, {with_window} of them storing a window, every one beside its day and budget");
    assert!(with_window >= 5 && with_window < states, "{with_window} of {states}");
}

/// Every `.tm/state.json` field D42 derives from the log and the day's plan
/// reads: the date, the wake, the arrival, the window, the budget and the
/// location.
fn day_fields(st: &Value) -> Value {
    serde_json::json!({
        "date": st["date"], "wake": st["wake"], "arrival": st["arrival"],
        "window": st["window"], "budget": st["budget"], "loc": st["loc"],
    })
}

/// **README gap 3710: two arrivals, then a wake — deleting the cache moves
/// nothing.** `tm arrive lounge` at 07:00, `tm arrive home` at 09:00 and `tm wake
/// 06:05` at 09:30 leave no arrival, window or budget in `.tm/state.json`; the
/// shipped `tm plan` at 10:30 plans from the day's FIRST logged `arrive`
/// (07:00–16:00, fork `Planner::new`), and so does the kernel's planner. Until
/// the W-39 repair the rebuild restored the day's LAST arrival (D45) whatever
/// followed it: `rm .tm/state.json` then gave 09:00–18:00, re-timed the rows,
/// added one and appended a `plan` line to the log — the authority written
/// because its cache was deleted. Asserted here, by value: the rebuilt state's
/// day fields ARE the cache's, the second `tm plan` prints the same bytes and
/// logs nothing, and the kernel plans the same window, rows and hash from both.
/// A wake followed by another arrival keeps D45: the last arrival is restored.
#[test]
fn two_arrivals_then_a_wake_plan_one_day_from_either_cache() {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]);
    tm.ok_at("2026-09-07T09:00:00-05:00", &["arrive", "home"]);
    tm.ok_at("2026-09-07T09:30:00-05:00", &["wake", "06:05"]);
    let cached = tm.state();
    let before = tm.ok_at("2026-09-07T10:30:00-05:00", &["plan"]);
    assert!(before.stdout.contains("window 07:00–16:00"), "{}", before.stdout);
    let now = at("2026-09-07", 10, 30);
    let woken = fixture_of(&tm.plan);
    let tz = woken.cfg.tz;
    let k = woken.kernel_day(&woken.state, now).expect("the kernel plans the woken day");
    assert_eq!(window_of(&k, tz), (at("2026-09-07", 7, 0), at("2026-09-07", 16, 0)));

    let log = std::fs::read_to_string(tm.plan.join(".tm/log.jsonl")).expect("the log");
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    let after = tm.ok_at("2026-09-07T10:30:00-05:00", &["plan"]);
    assert_eq!(day_fields(&tm.state()), day_fields(&cached), "the rebuild is the cache");
    assert_eq!(after.stdout, before.stdout, "the day `tm plan` prints does not move");
    assert_eq!(
        std::fs::read_to_string(tm.plan.join(".tm/log.jsonl")).expect("the log"),
        log,
        "deleting the cache writes nothing to the log"
    );
    let rebuilt = fixture_of(&tm.plan);
    let r = rebuilt.kernel_day(&rebuilt.state, now).expect("the kernel plans the rebuilt day");
    assert_eq!(window_of(&r, tz), window_of(&k, tz), "the kernel's window");
    assert_eq!((r.hash(), &r.segments), (k.hash(), &k.segments), "row for row");

    // D45 stands where the last verb was an arrival: arrive, wake, arrive.
    tm.ok_at("2026-09-07T11:00:00-05:00", &["arrive", "lounge"]);
    let cached = tm.state();
    assert_eq!(cached["arrival"], "11:00", "{cached}");
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    tm.ok_at("2026-09-07T11:30:00-05:00", &["plan"]);
    assert_eq!(day_fields(&tm.state()), day_fields(&cached), "the last arrival, D45");
}

/// **README gap 3531's Rust half: the host's file-kind `ci` table is the
/// kernel's.** `Horizon::default_ci` holds routines 1, optional 0 and every other
/// file kind 3 — `Tm.DocKind.ciDefault`'s three rows — and the candidates the
/// host collects for a box-less routine line and an optional line with no `ci`
/// carry 1 and 0, which are the wire values `PlannerWit.furnitureCands` sends
/// where `PlannerWit.the_plan_and_the_wire_read_the_file_kinds_ci_alike`
/// decides `PlanCheck.candsAgree`.
#[test]
fn the_hosts_file_kind_ci_default_is_the_kernels() {
    let kernel_table = [
        ("routines.md", 1),
        ("optional.md", 0),
        ("backlog.md", 3),
        ("inbox.md", 3),
        ("month/2026-09.md", 3),
        ("week/2026-W37.md", 3),
        ("day/2026-09-09.md", 3),
        ("calendar/2026-W37.md", 3),
    ];
    for (path, ci) in kernel_table {
        let h = Horizon::from_path(path).unwrap_or_else(|| panic!("{path} is a file kind"));
        assert_eq!(h.default_ci(), ci, "{path}: the host's default against `Tm.DocKind.ciDefault`'s");
    }
    let fx = of_texts(
        &[
            ("routines.md", "- lunch win:11:30-13:30 dur:30m every:day\n"),
            ("optional.md", "- Severance S3E4  dur:1h\n"),
        ],
        "",
    );
    let now = at("2026-09-09", 10, 0);
    let date = NaiveDate::from_ymd_opt(2026, 9, 9).expect("date");
    let cands = priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, date, now);
    let ci = |id: &str| cands.iter().find(|c| c.id.as_str() == id).map(|c| c.ci);
    assert_eq!(ci("lunch"), Some(1), "the routine's candidate: {:?}", cands.iter().map(|c| (&c.id, c.ci)).collect::<Vec<_>>());
    assert_eq!(ci("Severance S3E4"), Some(0), "the optional's candidate");
}

