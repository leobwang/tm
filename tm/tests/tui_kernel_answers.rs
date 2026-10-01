//! **The TUI's fork-planned tests, answered by the kernel now** — and **a Review screen that
//! draws the kernel's cut of the week** (stage 6 W-40 track H, README gap 3721).
//!
//! Fifteen tests reach the fork's planner through the `tm` crate's own TUI code (README gap
//! 3476): `tui::tests::the_meeting_pause_is_said_on_the_status_line`, three of
//! `tui_today_ghost` and eleven of `tui_today_prompts`. They test the shipped TUI, which plans
//! with the fork until R3's body swap, and they assert values the FORK produced — and the
//! kernel's answer on those worlds was never computed, so the swap would change their
//! assertions blind. [`TUI_TESTS`] is the fifteen, each with EVERY planner call its own code
//! makes ([`Ask`]: the world, and whether §9.1's what-if is asked there — a `tick` replans, so
//! a test that ticks plans at more than one instant), what it asserts that a planner produces,
//! and the verdict; `the_kernel_answers_every_fork_planned_tui_world` computes the kernel's
//! answer at every one of those calls NOW, through the request R3's host sends
//! (`forkclass::kernel_answer_with_grants`: the harness's request with the host's worked minutes
//! and the what-if's grown facts — README gap 3720 says where the binary's own encoder still
//! differs), and holds each verdict to it. The fork's side is the tests' own asserted values,
//! written here, so this part needs no fork region and outlives R3; while the fork is here, its
//! region holds the same worlds' LIVE fork answers to the kernel's — the drops each test reads,
//! and the WHOLE answer through the frozen lines' one comparison (`forkclass::compare_line`
//! over the comparand built from the in-tree fork) — so no verdict rests on a reading of a test
//! alone.
//!
//! And no TUI test saw a cut week: `tui_common` builds every `App` with `PauseCut::default()`,
//! under which `review::heat_of` draws a Pause whole, as the fork did.
//! `the_review_screen_draws_the_kernels_cut_of_every_frozen_week` builds the App over every
//! world `support/forkgrid.rs` freezes whose week is the one the Review screen shows, with the
//! kernel's own cut of that week, and holds the Review screen's grid to the CLI's and to fork
//! 4748911's frozen grid with P63's cells named.

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
#[path = "support/forkclass.rs"]
mod forkclass;

#[allow(dead_code)]
#[path = "support/plangen.rs"]
mod plangen;

/// The comparand's departures by their properties (`forkplan::is_p46`, and in the region the
/// whole comparand, `forkplan::comparand_answers`).
#[allow(dead_code)]
#[path = "support/forkplan.rs"]
mod forkplan;

#[allow(dead_code)]
#[path = "support/forkgrid.rs"]
mod forkgrid;

/// The binary's walls form with a `week`, spelled for a test (`day::week_cut`'s request).
#[allow(dead_code)]
#[path = "support/weekcut.rs"]
mod weekcut;

use serde_json::Value;

use tm_core::dayplan::{DayPlan, SegKind};
use tm_core::log::Event;
use tm_core::model::{Id, IsoWeek};
use tm_core::planwire::KernelDay;
use tm_core::store::ActiveBlock;

use forkclass::{Built, ClassWorld};
use tui_common::app::App;

/// **What a fork-planned TUI test asserts that a planner produces.**
#[derive(Clone, Copy, Debug, PartialEq)]
enum Asserted {
    /// `Overtime::drops` (§9.1's "x extend +1 block → drops: …"), as the test or its snapshot
    /// pins it: the what-if's `removed` items, each `title (pN)`.
    Drops(&'static [&'static str]),
    /// Nothing a planner produces: the test reads the state, the replay, the clock and the
    /// arrival record, and the planner is only reached on the way (`overtime_due` builds the
    /// whole box; `replan` and `tick` replace the plan the assertions do not read). The kernel
    /// must still answer every call — the swap will ask it there.
    Nothing,
}

/// **The verdict on one test's assertions**: the kernel's answer against the fork's asserted
/// value.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Verdict {
    /// The kernel answers what the test asserts.
    Equal,
    /// The kernel answers otherwise, by a registered parity number — named, and held to that
    /// number's property on the world (`kernel/parity.txt`).
    Registered(u32),
}

/// **The fork's LIVE answer against the kernel's on a test's first world** — wider than the
/// verdict, which is about what the test asserts.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Live {
    /// The fork's drops are the kernel's, and the comparand — the fork with every registered
    /// departure applied by its property — answers the kernel's whole day and what-if.
    Equal,
    /// The fork's drops differ from the kernel's by a registered number, and the comparand,
    /// which applies that number and no other on the world, answers the kernel's day and
    /// what-if.
    Registered(u32),
    /// A finding, by its README gap: the fork and the kernel plan different days, and no
    /// registered number says so.
    Finding(u32),
}

/// **The world one planner call plans over**, as `tui_common` builds it.
#[derive(Clone, Copy, Debug, PartialEq)]
enum TuiWorld {
    /// `app_at(h, m)`: §4.3's day, `^t3` running since 09:32 with `est_min` 192.
    At(u32, u32),
    /// `tight_overtime_app()`: 10:42, `est_min` 60, the budget 3.
    Tight,
    /// `tight_overtime_app()` ticked to `h:m` (`App::tick` replans with the state unchanged).
    TightAt(u32, u32),
    /// `overtime_app_for(id, est, h, m)`.
    For(&'static str, u32, u32, u32),
    /// `the_elapsed_minutes_are_worked_minutes_not_wall_clock`'s: a pause 11:00–11:20 logged,
    /// at `h:m`.
    Paused(u32, u32),
    /// `a_block_started_before_midnight_still_goes_overtime`'s: `^t3` started 23:30 with
    /// `est_min` 60, an empty log, 00:30 the next day — `.tm/state.json` still dated the day
    /// before, as the TUI holds it from midnight until its next reload (README gap 3860).
    Midnight,
    /// `the_two_prompts_keep_their_own_clocks`' last world: `idle_app(9, 50)` with `^t3`
    /// running again from 09:32, `est_min` 10.
    IdleThenRunning,
    /// The ghost tests' `app_at(10, 42)` replanned, with the arrival record or without it.
    Replanned { arrival: bool },
    /// `tui::tests::the_meeting_pause_is_said_on_the_status_line`'s: `plan-basic`'s fixture
    /// directory, `tm wake 06:05` at 09:00 (the fixture's own instant, no `--slept`),
    /// `tm start ^t4` at 12:00 and `tm now` at 13:20, inside the meeting — the CLI's verb path,
    /// which plans the day to draw it, run from the TUI. No `tm arrive` runs, so the day holds no
    /// location (README gap 3861).
    MeetingNow,
}

/// **One planner call a test's own code makes**: the world, and whether §9.1's what-if is asked
/// there (`App::overtime_due` → `extend_drops`, which plans the day twice).
#[derive(Clone, Copy, Debug, PartialEq)]
struct Ask {
    world: TuiWorld,
    whatif: bool,
}

const fn ask(world: TuiWorld, whatif: bool) -> Ask {
    Ask { world, whatif }
}

/// One fork-planned test: its name, every planner call its own code makes (the first is the
/// one its assertions read), what it asserts a planner produces, and the verdicts.
struct TuiTest {
    name: &'static str,
    asks: &'static [Ask],
    asserted: Asserted,
    verdict: Verdict,
    live: Live,
}

/// **The fifteen** (README gap 3476's list), each with every planner call its code makes.
/// `the_overtime_prompt_fires_past_est_times_the_multiplier` asks `app_at(12, 0)` first and
/// gets no prompt — `overtime_due` returns before any planner when the estimate is not reached
/// — so its one call is at 12:51; `the_elapsed_minutes_are_worked_minutes_not_wall_clock`'s
/// 12:51 app likewise. `the_overtime_prompt_asks_again_after_the_reprompt_interval` ticks to
/// 13:01 (a replan, no prompt) and 13:08 (a replan and the what-if);
/// `a_prompt_never_steals_a_character_from_the_command_line` ticks the tight app to 12:51 (a
/// replan; the `:` line holds the prompt back) and asks a fresh tight app's what-if.
const TUI_TESTS: [TuiTest; 15] = [
    TuiTest {
        name: "tui_today_prompts::the_overtime_prompt_fires_past_est_times_the_multiplier",
        asks: &[ask(TuiWorld::At(12, 51), true)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Equal,
    },
    TuiTest {
        name: "tui_today_prompts::the_overtime_box",
        asks: &[ask(TuiWorld::At(12, 51), true)],
        asserted: Asserted::Drops(&[]),
        verdict: Verdict::Equal,
        live: Live::Equal,
    },
    TuiTest {
        name: "tui_today_prompts::the_overtime_prompt_asks_again_after_the_reprompt_interval",
        asks: &[ask(TuiWorld::At(12, 51), true), ask(TuiWorld::At(13, 1), false), ask(TuiWorld::At(13, 8), true)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Equal,
    },
    TuiTest {
        name: "tui_today_prompts::the_overtime_box_names_what_extending_would_drop",
        asks: &[ask(TuiWorld::Tight, true)],
        asserted: Asserted::Drops(&["Claude Code drafts tests (p3)"]),
        verdict: Verdict::Registered(46),
        live: Live::Registered(46),
    },
    TuiTest {
        name: "tui_today_prompts::the_overtime_keys_run_the_matching_verbs",
        asks: &[ask(TuiWorld::At(12, 51), true)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Equal,
    },
    TuiTest {
        name: "tui_today_prompts::the_overtime_box_names_the_remainder_that_stays_in_the_week_queue",
        asks: &[ask(TuiWorld::For("m1", 300, 15, 2), true)],
        asserted: Asserted::Drops(&[]),
        verdict: Verdict::Equal,
        live: Live::Equal,
    },
    TuiTest {
        name: "tui_today_prompts::the_elapsed_minutes_are_worked_minutes_not_wall_clock",
        asks: &[ask(TuiWorld::Paused(13, 4), true)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Equal,
    },
    TuiTest {
        name: "tui_today_prompts::a_block_started_before_midnight_still_goes_overtime",
        asks: &[ask(TuiWorld::Midnight, true)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Finding(3860),
    },
    TuiTest {
        name: "tui_today_prompts::the_two_prompts_keep_their_own_clocks",
        asks: &[ask(TuiWorld::IdleThenRunning, true)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Equal,
    },
    TuiTest {
        name: "tui_today_prompts::a_prompt_never_steals_a_character_from_the_command_line",
        asks: &[ask(TuiWorld::Tight, true), ask(TuiWorld::TightAt(12, 51), false)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Registered(46),
    },
    TuiTest {
        name: "tui_today_prompts::a_prompt_is_drawn_over_the_screen",
        asks: &[ask(TuiWorld::At(12, 51), true)],
        asserted: Asserted::Drops(&[]),
        verdict: Verdict::Equal,
        live: Live::Equal,
    },
    TuiTest {
        name: "tui_today_ghost::the_ghost_row_is_the_recorded_arrival_plan",
        asks: &[ask(TuiWorld::Replanned { arrival: true }, false)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Equal,
    },
    TuiTest {
        name: "tui_today_ghost::adherence_is_measured_against_the_recorded_plan",
        asks: &[ask(TuiWorld::Replanned { arrival: true }, false)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Equal,
    },
    TuiTest {
        name: "tui_today_ghost::a_day_with_no_arrival_record_has_no_ghost_and_no_adherence",
        asks: &[ask(TuiWorld::Replanned { arrival: false }, false)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Equal,
    },
    TuiTest {
        name: "tui::tests::the_meeting_pause_is_said_on_the_status_line",
        asks: &[ask(TuiWorld::MeetingNow, false)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Finding(3861),
    },
];

/// The unit test's verbs (`tui::tests`' `fixture`, `wake` and its two `verb` calls), run by
/// the shipped binary from `plan-basic`.
fn meeting_now_steps() -> Vec<forkgrid::Step> {
    vec![
        forkgrid::Step::run("2026-09-07T09:00:00-05:00", &["wake", "06:05"]),
        forkgrid::Step::run("2026-09-07T12:00:00-05:00", &["start", "^t4"]),
        forkgrid::Step::run("2026-09-07T13:20:00-05:00", &["now"]),
    ]
}

/// **The app a world builds, and the log's text and documents it was built from** — through
/// `tui_common`'s own constructors, none of which plans (`with_plan` takes the hand-built day;
/// `refresh` draws it), so nothing here reaches the fork.
fn app_of(w: TuiWorld) -> (App, String, Vec<(String, String)>) {
    let cfg = tui_common::config();
    let texts = tui_common::tree_texts();
    match w {
        TuiWorld::At(h, m) => (tui_common::app_at(h, m), tui_common::log(&cfg), texts),
        TuiWorld::Tight => (tui_common::tight_overtime_app(), tui_common::log(&cfg), texts),
        TuiWorld::TightAt(h, m) => {
            // `App::tick` moves `now` and `today` and replans; the state, log and tree stay.
            let mut app = tui_common::tight_overtime_app();
            app.now = tui_common::at(&cfg, h, m);
            app.today = app.now.date_naive();
            app.refresh();
            (app, tui_common::log(&cfg), texts)
        }
        TuiWorld::For(id, est, h, m) => (tui_common::overtime_app_for(id, est, h, m), tui_common::log(&cfg), texts),
        TuiWorld::Paused(h, m) => {
            let log = tui_common::log_plus(
                &cfg,
                vec![
                    tui_common::entry(&cfg, 11, 0, Event::Pause { id: "t3".into() }),
                    tui_common::entry(&cfg, 11, 20, Event::Unpause { id: "t3".into() }),
                ],
            );
            (tui_common::app_with_log_text(tui_common::at(&cfg, h, m), tui_common::state(), &log), log, texts)
        }
        TuiWorld::Midnight => {
            let mut state = tui_common::state();
            if let Some(a) = state.active.as_mut() {
                a.started = chrono::NaiveTime::from_hms_opt(23, 30, 0).expect("time");
                a.est_min = 60;
            }
            let midnight = tm_core::capacity::local_dt(
                cfg.tz,
                tui_common::date().succ_opt().expect("tomorrow"),
                chrono::NaiveTime::from_hms_opt(0, 30, 0).expect("time"),
            );
            (tui_common::app_with_log_text(midnight, state, ""), String::new(), texts)
        }
        TuiWorld::IdleThenRunning => {
            let mut app = tui_common::idle_app(9, 50);
            app.state.active = Some(ActiveBlock {
                id: Id::new("t3"),
                started: chrono::NaiveTime::from_hms_opt(9, 32, 0).expect("time"),
                est_min: 10,
                paused: false,
            });
            (app, tui_common::log(&cfg), texts)
        }
        TuiWorld::Replanned { arrival } => {
            let mut app = tui_common::app_at(10, 42);
            if !arrival {
                // The test clears the record and replans; `replan` refreshes the digests, which
                // `refresh` does alone, without a planner.
                app.arrival.clear();
                app.refresh();
            }
            (app, tui_common::log(&cfg), texts)
        }
        TuiWorld::MeetingNow => {
            // The world the unit test's verbs leave, built by the shipped binary: the same three
            // verbs at the same instants, read back whole.
            let tmp = tempfile::TempDir::new().expect("a temporary directory");
            let dir = tmp.path().join("plan");
            let ran = forkgrid::run_steps(&dir, &meeting_now_steps());
            assert!(ran.iter().all(|s| matches!(s, forkgrid::Step::Run { code: 0, .. })), "the unit test's verbs all succeed: {ran:?}");
            let world = forkgrid::GridWorld::read(&dir);
            let state: tm_core::store::RuntimeState =
                serde_json::from_str(world.file(".tm/state.json").expect("state.json")).expect("a state");
            let docs = world.docs();
            let files = tm_core::store::MemStore::from_dir(&dir).and_then(|s| tm_core::store::Store::read_tree(&s)).expect("the tree");
            let now = chrono::DateTime::parse_from_rfc3339("2026-09-07T13:20:00-05:00").expect("an instant").with_timezone(&cfg.tz);
            let log = world.log().to_string();
            let app = tui_common::app_of_world(
                &docs,
                files,
                cfg,
                tui_common::World { now, state, log: &log, week_cut: Default::default() },
                DayPlan::empty(now.date_naive(), (now, now), 0),
                None,
                Vec::new(),
            );
            (app, log, docs)
        }
    }
}

/// **An app's world as the comparand reads it**: its documents, log, state and instant
/// (`forkclass::ClassWorld`, at the default configuration, which is `plan-basic`'s —
/// `the_tui_worlds_are_read_at_plan_basics_configuration`).
fn built_of(app: &App, log: &str, texts: &[(String, String)]) -> Built {
    Built::of(ClassWorld { docs: texts.to_vec(), log: log.to_string(), state: app.state.clone(), now: app.now, mult: None, ratio: None })
}

/// **The kernel's answer on an app's world, asked as R3's host will ask it** —
/// `forkclass::kernel_answer_with_grants`: the request the harness builds (the binary's
/// capacity encoder's shape and the host codec's `planner` section), with the running block's
/// worked minutes (the host's one reading, README gap 3043's key) and §9.1's what-if for one
/// block on it with the candidate's grown facts (D58) whenever a block runs.
fn kernel_answer(app: &App, log: &str, texts: &[(String, String)]) -> Result<(Built, KernelDay), String> {
    let b = built_of(app, log, texts);
    let k = forkclass::kernel_answer_with_grants(&b)?.0;
    Ok((b, k))
}

/// **`forkclass::kernel_answer_with_grants`' request, its capacity section's location replaced**
/// when `loc` names one — README gap 3861's probe. The request and the order it sent.
fn request_with_loc(b: &Built, loc: Option<&str>) -> (Value, Vec<usize>) {
    let pw = b.request_world();
    let (mut req, order) = planreq::request(&pw, forkclass::whatif_json(b));
    if let Some(worked) = forkclass::host_worked(b) {
        tm_core::planwire::add_worked_min(&mut req["planner"], worked);
    }
    if let Some(l) = loc {
        req["capacity"]["state"]["loc"] = serde_json::json!(l);
    }
    (req, order)
}

/// The kernel's day for [`request_with_loc`]'s request with `loc` sent.
fn kernel_day_with_loc(b: &Built, loc: &str) -> Result<KernelDay, String> {
    let (req, order) = request_with_loc(b, Some(loc));
    let resp = planreq::call(&req);
    planreq::kernel_day_of(&resp, &b.request_world(), &order).map(|(k, _)| k)
}

/// **P46's row, read off the kernel's day** (`forkplan::p46_row`'s property): the running
/// block reserved from `now`, marked current, its note the fork's saturating `left`.
fn has_p46_row(k: &KernelDay, b: &Built) -> bool {
    let id = b.world.state.active.as_ref().map(|a| a.id.clone());
    k.day.segments.iter().any(|s| {
        s.kind == SegKind::Block && s.flags.current && s.item == id && s.start == b.world.now
            && s.flags.note.as_deref() == Some("running · 0m left")
    })
}

/// The kernel's drops, as `App::overtime` spells them: each removed item `title (pN)`, its
/// `p` from the app's plan (`App::priority_of`), else its title alone.
fn drops_of(app: &App, k: &KernelDay) -> Vec<String> {
    k.overtime
        .as_ref()
        .map(|d| d.removed.clone())
        .unwrap_or_default()
        .iter()
        .map(|id| match app.priority_of(id) {
            Some(p) => format!("{} (p{p})", app.title_of(id)),
            None => app.title_of(id),
        })
        .collect()
}

/// README gap 3860's kernel half, which outlives R3: on a state dated the day before `now`, the
/// kernel plans `now`'s date — the state's window, budget and arrival are not today's
/// (`Look.Today.forToday`) — where fork `planwire::plan_date` plans the state's.
fn plans_nows_date_on_a_stale_state(app: &App, k: &KernelDay) -> bool {
    k.day.date == app.now.date_naive() && app.state.date.is_some_and(|d| d != k.day.date)
}

/// **The kernel answers every fork-planned TUI world, and each verdict holds** — README gap
/// 3721. For every one of the fifteen and EVERY planner call its own code makes: the kernel
/// plans the world (no refusal, the rows it draws counted) and, where the call asks §9.1's
/// what-if, answers it. On the first call — the one the test's assertions read — the kernel's
/// drops are the asserted ones (`Verdict::Equal`) or differ by a registered number whose
/// property holds on the world (`Verdict::Registered`). One does:
/// `the_overtime_box_names_what_extending_would_drop`'s `^t3` is in overtime (70 of 60 minutes
/// worked) on a day whose budget has one block left, and parity P46 reserves a running block in
/// overtime to the end of its block where fork `active_run` refuses it — so the kernel's day
/// already spends the last block on `^t3` and extending it drops nothing, where the fork's
/// spends it on `^t4` and extending `^t3` drops `^t4`. The table is printed, so the swap's
/// author reads every kernel answer before the swap.
#[test]
fn the_kernel_answers_every_fork_planned_tui_world() {
    // Every distinct world once (several tests share one), answered on its own thread.
    let mut worlds: Vec<TuiWorld> = Vec::new();
    for a in TUI_TESTS.iter().flat_map(|t| t.asks.iter()) {
        if !worlds.contains(&a.world) {
            worlds.push(a.world);
        }
    }
    let answered: Vec<(TuiWorld, Result<(App, Built, KernelDay), String>)> = std::thread::scope(|s| {
        let hs: Vec<_> = worlds
            .iter()
            .map(|&w| {
                s.spawn(move || {
                    let (app, log, texts) = app_of(w);
                    let k = kernel_answer(&app, &log, &texts).map(|(b, k)| (app, b, k));
                    (w, k)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().expect("a worker")).collect()
    });
    let mut table = Vec::new();
    let mut findings = Vec::new();
    let mut calls = 0usize;
    for t in &TUI_TESTS {
        for (i, a) in t.asks.iter().enumerate() {
            let (app, b, k) = match answered.iter().find(|(w, _)| *w == a.world).map(|(_, r)| r) {
                Some(Ok(x)) => (&x.0, &x.1, &x.2),
                Some(Err(e)) => {
                    findings.push(format!("{} at {:?}: the kernel refused the world: {e}", t.name, a.world));
                    continue;
                }
                None => unreachable!("every world was answered"),
            };
            calls += 1;
            if a.whatif && k.overtime.is_none() {
                findings.push(format!("{} at {:?}: the kernel answered no what-if", t.name, a.world));
            }
            let drops = drops_of(app, k);
            if i > 0 {
                table.push(format!("  then {:?} (what-if {}) | kernel: {} rows, drops {drops:?}", a.world, a.whatif, k.day.segments.len()));
                continue;
            }
            let held = match (t.asserted, t.verdict) {
                (Asserted::Drops(want), v) => {
                    let want: Vec<String> = want.iter().map(|s| (*s).to_string()).collect();
                    match v {
                        Verdict::Equal => drops == want,
                        // P46's property on the world: the running block is in overtime by the
                        // comparand's own predicate, and the kernel's day reserves it from `now`.
                        Verdict::Registered(46) => drops != want && forkplan::is_p46(b, &b.world.state) && has_p46_row(k, b),
                        Verdict::Registered(_) => false,
                    }
                }
                (Asserted::Nothing, Verdict::Equal) => true,
                (Asserted::Nothing, Verdict::Registered(_)) => false,
            };
            if !held {
                findings.push(format!("{}: the verdict {:?} does not hold: the kernel drops {drops:?}, the test asserts {:?}", t.name, t.verdict, t.asserted));
            }
            // The verdict on what the test asserts and the live answer on its world agree where the
            // test asserts the drops: a registered verdict is the live difference's number.
            let consistent = match (t.asserted, t.verdict, t.live) {
                (Asserted::Drops(_), Verdict::Equal, Live::Equal) => true,
                (Asserted::Drops(_), Verdict::Registered(n), Live::Registered(m)) => n == m,
                (Asserted::Drops(_), _, _) => false,
                (Asserted::Nothing, _, _) => true,
            };
            if !consistent {
                findings.push(format!("{}: the verdict {:?} and the live answer {:?} disagree", t.name, t.verdict, t.live));
            }
            // A finding's kernel half, which outlives R3 (the fork's half is the region's) — and
            // gap 3860's reading bites nowhere else: every other world's state is today's.
            if t.live != Live::Finding(3860) && plans_nows_date_on_a_stale_state(app, k) {
                findings.push(format!("{}: read as gap 3860's stale state, and its state is today's", t.name));
            }
            match t.live {
                Live::Finding(3860) if !plans_nows_date_on_a_stale_state(app, k) => {
                    findings.push(format!("{}: the kernel no longer plans now's date on a state dated yesterday (gap 3860)", t.name));
                }
                Live::Finding(3861) => {
                    // The day holds no location, the request carries `Ctx::loc`'s lounge, and which
                    // curve the kernel plans on moves the day — so what R3's encoder sends for a day
                    // before `tm arrive` is a decision.
                    let sent = request_with_loc(b, None).0["capacity"]["state"]["loc"].clone();
                    let any = kernel_day_with_loc(b, "any").map(|d| d.hash);
                    if b.world.state.loc.is_some() || sent != "lounge" || any.as_ref().is_ok_and(|h| *h == k.hash) {
                        findings.push(format!("{}: gap 3861 no longer holds: loc {:?}, sent {sent}, the day sent `any` {any:?}, sent lounge {}", t.name, b.world.state.loc, k.hash));
                    }
                }
                _ => {}
            }
            table.push(format!(
                "{} | {:?} | asserts {:?} | kernel: {} rows, drops {drops:?} | {:?} | live {:?}",
                t.name,
                a.world,
                t.asserted,
                k.day.segments.len(),
                t.verdict,
                t.live
            ));
        }
    }
    println!("{}", table.join("\n"));
    println!("the kernel answered {calls} planner call(s) of the fifteen tests, over {} distinct world(s)", worlds.len());
    assert!(findings.is_empty(), "{}", findings.join("\n  "));
    assert_eq!(TUI_TESTS.len(), 15, "README gap 3476's fifteen");
    assert_eq!(calls, TUI_TESTS.iter().map(|t| t.asks.len()).sum::<usize>(), "every planner call was answered");
}

/// **The TUI worlds are read at `plan-basic`'s configuration** — `forkclass::Built` reads every
/// world at `Config::default()`, and the TUI's is `plan-basic`'s `config.toml`; the two are one
/// configuration, field for field, so the comparand and the kernel read the TUI's world as the
/// TUI does.
#[test]
fn the_tui_worlds_are_read_at_plan_basics_configuration() {
    assert_eq!(format!("{:?}", tm_core::config::Config::default()), format!("{:?}", tui_common::config()));
}

/// **What the asserted values read instead of a planner**, computed without one — the
/// `Asserted::Nothing` verdicts are measured, not read off the tests: the overtime numbers
/// those tests pin are the state's and the replay's (`App::active_elapsed_min`), and the ghost
/// tests' are the arrival record's and the log's (the ghost row's window and budget are
/// `.tm/state.json`'s whenever it holds them, as it does here, so the replanned day is never
/// read).
#[test]
fn the_tui_tests_planner_free_assertions_read_no_planner() {
    let (app, _, _) = app_of(TuiWorld::At(12, 51));
    let a = app.state.active.as_ref().expect("a running block");
    assert_eq!((a.id.as_str(), a.est_min, app.active_elapsed_min()), ("t3", 192, Some(199)));
    let (app, _, _) = app_of(TuiWorld::Paused(13, 4));
    assert_eq!(app.active_elapsed_min(), Some(192));
    let (app, _, _) = app_of(TuiWorld::Midnight);
    assert_eq!(app.active_elapsed_min(), Some(60));
    let (app, _, _) = app_of(TuiWorld::IdleThenRunning);
    assert!(app.active_elapsed_min().is_some_and(|m| m >= 10), "past its ten-minute estimate");
    for arrival in [true, false] {
        let (app, _, _) = app_of(TuiWorld::Replanned { arrival });
        assert!(app.state.window.is_some() && app.state.budget.is_some(), "the ghost row reads the state's window and budget");
        assert_eq!(app.status.adherence_pct, arrival.then_some(75), "adherence is the record's and the log's");
    }
}

/// **The kernel's drops and P46's row are read as the TUI reads them** (non-vacuity, AGENTS
/// §5.2): the fifteen worlds' kernel what-ifs drop nothing, so a reading of the drops that
/// answered nothing would pass them all. On the overtime world with `^t3` given 90 minutes and
/// the budget four blocks, the kernel's what-if drops the evening's optional `Factorio` (no `p`:
/// the title alone); a what-if naming `^t4` and `Factorio` reads `title (pN)` and the title,
/// exactly as `App::overtime` spells a drop; and P46's row is on the overtime world's kernel day
/// and not on a day whose block has minutes left.
#[test]
fn the_kernels_drops_and_p46s_row_are_read_as_the_tui_reads_them() {
    let cfg = tui_common::config();
    let mut app = tui_common::overtime_app(10, 42, 90);
    app.state.budget = Some(4);
    app.refresh();
    let (b, mut k) = kernel_answer(&app, &tui_common::log(&cfg), &tui_common::tree_texts()).expect("the kernel answers");
    assert_eq!(drops_of(&app, &k), vec!["Factorio".to_string()], "the kernel's what-if drops on this world");
    assert!(!has_p46_row(&k, &b) && !forkplan::is_p46(&b, &b.world.state), "no P46 row where the block has minutes left");
    if let Some(o) = k.overtime.as_mut() {
        o.removed = vec![Id::new("t4"), Id::new("Factorio")];
    }
    assert_eq!(drops_of(&app, &k), vec!["Claude Code drafts tests (p3)".to_string(), "Factorio".to_string()]);
    let (app, log, texts) = app_of(TuiWorld::Tight);
    let (b, k) = kernel_answer(&app, &log, &texts).expect("the kernel answers");
    assert!(has_p46_row(&k, &b) && forkplan::is_p46(&b, &b.world.state), "P46's row on the overtime world");
}

/// **The meeting world is the unit test's own** (AGENTS §5.4: is the world the one the code
/// runs on?): the binary's verbs over `plan-basic` leave D61's pause logged at the meeting's
/// start, `^t4` running and paused — the status line's notice in the unit test is about that
/// pause — the wake at 06:05 with no sleep given (`slept_min` 0, `tm wake 06:05` with no
/// `--slept`), and no location: no `tm arrive` ran (README gap 3861).
#[test]
fn the_meeting_world_is_the_unit_tests_own() {
    let (app, log, _) = app_of(TuiWorld::MeetingNow);
    let a = app.state.active.as_ref().expect("^t4 runs");
    assert_eq!((a.id.as_str(), a.paused), ("t4", true), "D61 paused the block for the meeting");
    assert!(log.lines().any(|l| l.contains("\"ev\":\"pause\"") && l.contains("12:50:00")), "the pause at the wall's start: {log}");
    let wake = log.lines().find(|l| l.contains("\"ev\":\"wake\"")).expect("a wake");
    assert!(wake.contains("06:05:00") && wake.contains("\"slept_min\":0"), "the fixture's wake: {wake}");
    assert_eq!((app.state.loc.as_deref(), app.state.window), (None, None), "no `tm arrive` ran");
}

/// The heat of an app's Review screen, as JSON.
fn screen_heat(app: &App) -> Value {
    serde_json::to_value(&app.reviews().week.heat).expect("the heat serialises")
}

/// **The Review screen draws the KERNEL's cut of the week, on every frozen world it shows**
/// (README gap 3721, P63): over every world `support/forkgrid.rs` freezes whose review instant
/// falls in the week it reviews — the Review screen shows the week of `now` — the App holds the
/// kernel's cut of that week (`weekcut::walls_week_request`, the binary's walls form with a
/// `week`), and `App::reviews`' heat grid is, cell for cell, the CLI's `tm --json review week`
/// on the same world and fork 4748911's frozen grid with P63's cells moved. The floors: every
/// line but the sealed one (reviewed from the week after) compared, a named cell among them,
/// a pause past local midnight among them.
#[test]
fn the_review_screen_draws_the_kernels_cut_of_every_frozen_week() {
    let lines = forkgrid::frozen_lines();
    let check = |line: &Value| -> Result<Option<(usize, bool)>, String> {
        let who = line["name"].as_str().unwrap_or("?").to_string();
        let world = forkgrid::GridWorld::of_json(&line["world"]).map_err(|e| format!("{who}: {e}"))?;
        let cfg = world.cfg();
        let tz = cfg.tz;
        let at = forkgrid::line_at(line, tz)?;
        let date = chrono::NaiveDate::parse_from_str(line["date"].as_str().unwrap_or_default(), "%Y-%m-%d").map_err(|e| format!("{who}: {e}"))?;
        if IsoWeek::from_date(at.date_naive()) != IsoWeek::from_date(date) {
            return Ok(None);
        }
        let state: tm_core::store::RuntimeState =
            serde_json::from_str(world.file(".tm/state.json").ok_or_else(|| format!("{who}: no state.json"))?).map_err(|e| format!("{who}: {e}"))?;
        if state.break_.as_ref().is_some_and(|b| b.started.is_some()) {
            return Err(format!("{who}: a running break, which `weekcut::walls_week_request` does not send"));
        }
        let tmp = tempfile::TempDir::new().map_err(|e| e.to_string())?;
        let dir = tmp.path().join("plan");
        world.write(&dir);
        let files = tm_core::store::MemStore::from_dir(&dir).and_then(|s| tm_core::store::Store::read_tree(&s)).map_err(|e| format!("{who}: {e}"))?;
        let docs = world.docs();
        let monday = IsoWeek::from_date(date).monday();
        let resp = planreq::call(&weekcut::walls_week_request(&docs, world.log(), &cfg, at, monday));
        let cut = weekcut::read_week_cut(&resp, tz).map_err(|e| format!("{who}: the kernel's cut: {e}"))?;
        let app = tui_common::app_of_world(
            &docs,
            files,
            cfg,
            tui_common::World { now: at, state, log: world.log(), week_cut: cut },
            DayPlan::empty(at.date_naive(), (at, at), 0),
            None,
            Vec::new(),
        );
        let tui = screen_heat(&app);
        let cli = forkgrid::review(&world, line["date"].as_str().unwrap_or_default(), line["at"].as_str().unwrap_or_default())
            .map_err(|e| format!("{who}: {e}"))?
            .heat;
        if tui != cli {
            return Err(format!("{who}: the Review screen and `tm review week` draw two grids"));
        }
        let named = forkgrid::cells_of(&line["p63"]).map_err(|e| format!("{who}: {e}"))?;
        let want = forkgrid::comparand(&line["fork"]["heat"], &named).map_err(|e| format!("{who}: {e}"))?;
        let findings = forkgrid::compare_heat(&format!("the Review screen on {who}"), &tui, &want);
        if !findings.is_empty() {
            return Err(findings.join("\n  "));
        }
        let past_midnight = line["fork"]["pauses"].as_array().into_iter().flatten().any(|p| {
            matches!((p[0].as_str(), p[2].as_str()), (Some(d), Some(e)) if e.get(..10).is_some_and(|ed| ed > d))
        });
        Ok(Some((named.len(), past_midnight)))
    };
    let results: Vec<Result<Option<(usize, bool)>, String>> = std::thread::scope(|s| {
        let chunks: Vec<&[Value]> = lines.chunks(lines.len().div_ceil(8).max(1)).collect();
        let handles: Vec<_> = chunks.into_iter().map(|c| s.spawn(move || c.iter().map(&check).collect::<Vec<_>>())).collect();
        handles.into_iter().flat_map(|h| h.join().expect("a worker")).collect()
    });
    let failed: Vec<&String> = results.iter().filter_map(|r| r.as_ref().err()).collect();
    let compared: Vec<(usize, bool)> = results.iter().filter_map(|r| r.as_ref().ok().copied().flatten()).collect();
    let named: usize = compared.iter().map(|c| c.0).sum();
    println!(
        "the Review screen with the kernel's cut: {} of {} frozen week(s) compared (the rest are reviewed from another week), {named} named cell(s), {} with a pause past midnight",
        compared.len(),
        lines.len(),
        compared.iter().filter(|c| c.1).count()
    );
    assert!(failed.is_empty(), "{}", failed.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n  "));
    assert_eq!(compared.len(), lines.len() - 1, "every frozen week but the sealed one (reviewed from the week after) is the Review screen's");
    assert!(named > 0, "no cell P63 names was drawn by the Review screen");
    assert!(compared.iter().any(|c| c.1), "no pause past midnight was drawn by the Review screen");
}

/// **The blind spot every TUI test had** (README gap 3721): with `PauseCut::default()` — what
/// `tui_common` built every App with until now — the meeting world's Review screen draws the
/// meeting's pause WHOLE, as fork 4748911 did (`pause` 10 + 50, no `wall`), and with the
/// kernel's cut it draws the wall (10 + 50) and no pause: the one case no TUI test could see.
#[test]
fn an_uncut_week_is_drawn_as_the_fork_drew_it() {
    let lines = forkgrid::frozen_lines();
    let line = lines.iter().find(|l| l["name"] == "cli/meeting").expect("the meeting world is frozen");
    let world = forkgrid::GridWorld::of_json(&line["world"]).expect("a stored world");
    let cfg = world.cfg();
    let tz = cfg.tz;
    let at = forkgrid::line_at(line, tz).expect("an instant");
    let tmp = tempfile::TempDir::new().expect("a temporary directory");
    let dir = tmp.path().join("plan");
    world.write(&dir);
    let files = tm_core::store::MemStore::from_dir(&dir).and_then(|s| tm_core::store::Store::read_tree(&s)).expect("the tree");
    let state: tm_core::store::RuntimeState = serde_json::from_str(world.file(".tm/state.json").expect("state.json")).expect("a state");
    let docs = world.docs();
    let monday = chrono::NaiveDate::from_ymd_opt(2026, 9, 7).expect("a date");
    let resp = planreq::call(&weekcut::walls_week_request(&docs, world.log(), &cfg, at, monday));
    let cut = weekcut::read_week_cut(&resp, tz).unwrap_or_else(|e| panic!("the kernel's cut: {e}"));
    let app_with = |week_cut| {
        tui_common::app_of_world(
            &docs,
            files.clone(),
            cfg.clone(),
            tui_common::World { now: at, state: state.clone(), log: world.log(), week_cut },
            DayPlan::empty(at.date_naive(), (at, at), 0),
            None,
            Vec::new(),
        )
    };
    let cell = |h: &Value, hour: usize, style: usize| h[0]["hours"][hour][style].as_u64().unwrap_or_default();
    let (pause, wall) = (4, 7);
    let cut = screen_heat(&app_with(cut));
    assert_eq!((cell(&cut, 12, wall), cell(&cut, 13, wall), cell(&cut, 12, pause) + cell(&cut, 13, pause)), (10, 50, 0), "{}", cut[0]);
    let blind = screen_heat(&app_with(Default::default()));
    assert_eq!((cell(&blind, 12, pause), cell(&blind, 13, pause), cell(&blind, 13, wall)), (10, 50, 0), "an uncut pause is drawn whole: {}", blind[0]);
    // The uncut grid IS fork 4748911's, cell for cell: the frozen grid with no cell named.
    let fork = forkgrid::comparand(&line["fork"]["heat"], &[]).expect("the fork's grid");
    let findings = forkgrid::compare_heat("the uncut Review screen", &blind, &fork);
    assert!(findings.is_empty(), "{}", findings.join("\n  "));
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gap 3721)
//
// **The fork's LIVE answer on the same worlds**, while it is here: what each test's own call
// reaches (`App::overtime_due`'s drops, `App::replan`'s day), held to the kernel's on every
// world, and the WHOLE answer on every world through the frozen lines' one comparison
// (`forkclass::compare_line` over the comparand built from the in-tree fork), so a verdict
// above rests on the fork's answer and not only on a test's reading of it.

/// A test's first planner call's world — the one its assertions read.
fn first_world(t: &TuiTest) -> TuiWorld {
    t.asks[0].world
}

/// **A class line for a TUI world, its answers the in-tree comparand's** — the shape
/// `forkclass::compare_line` reads (`support/forkp56.rs` builds the same for a seeded day), never
/// frozen: the world, its class and every answer of `forkclass::ANSWERS`.
fn live_line(name: &str, b: &Built, answers: &Value) -> Value {
    let mut line = serde_json::json!({"name": name, "class": forkclass::class_of(b).key(), "world": b.world.to_json()});
    for key in forkclass::ANSWERS {
        forkclass::set_answer(&mut line, key, answers[key].clone());
    }
    line
}

/// **The fork's live answers are the asserted ones, the kernel's whole answer is the
/// comparand's, and every live difference is named** — for each world the fifteen plan over
/// (each once, every planner call of every test): the comparand (the in-tree fork with every
/// registered departure applied by its property, `forkplan::comparand_answers`) and the kernel
/// agree on the whole day and the what-if (`forkclass::compare_line`, the frozen lines' one
/// comparison) — except on a `Live::Finding` world, where the finding holds as its gap states
/// it; `overtime_due`'s drops (the fork's what-if through the TUI's own `extend_drops`) are what
/// each test on the world asserts; they are the kernel's under `Live::Equal`, and under
/// `Live::Registered(n)` they are not and the comparand departs from the shipped fork on the
/// world by `n` and by no other number. The ghost worlds' `replan` reaches a day.
#[test]
fn the_fork_and_the_kernel_answer_every_tui_world_as_the_verdicts_say() {
    let mut worlds: Vec<(TuiWorld, bool)> = Vec::new();
    for a in TUI_TESTS.iter().flat_map(|t| t.asks.iter()) {
        match worlds.iter_mut().find(|(w, _)| *w == a.world) {
            Some(entry) => entry.1 |= a.whatif,
            None => worlds.push((a.world, a.whatif)),
        }
    }
    // A test's live verdict is about its first world; a world two tests share keeps one verdict,
    // and a world that is only a later call is held to the comparand like any other (`Equal`).
    let live_of = |w: TuiWorld| -> Live {
        let lives: Vec<Live> = TUI_TESTS.iter().filter(|t| first_world(t) == w).map(|t| t.live).collect();
        assert!(lives.windows(2).all(|p| p[0] == p[1]), "{w:?}: one world, one live answer: {lives:?}");
        lives.first().copied().unwrap_or(Live::Equal)
    };
    let mut tally = forkclass::ClassTally::default();
    let mut summary = Vec::new();
    for (w, whatif) in worlds {
        let live = live_of(w);
        let (mut app, log, texts) = app_of(w);
        let (b, k) = kernel_answer(&app, &log, &texts).unwrap_or_else(|e| panic!("{w:?}: {e}"));
        let prios = forkclass::kernel_answer_with_grants(&b).expect("the kernel answers").1;
        let answers = forkplan::comparand_answers(&b, &prios, &forkplan::InTree).expect("the in-tree fork answers");
        let flags: Vec<u32> = forkclass::parity_flags(&answers).into_iter().filter(|(_, set)| *set).map(|(n, _)| n).collect();
        let findings = forkclass::compare_line(&live_line(&format!("{w:?}"), &b, &answers), &mut tally);
        match live {
            Live::Finding(3860) => {
                // README gap 3860, pinned: a state dated YESTERDAY, which the binary's
                // housekeeping rolls at the first verb after midnight and the TUI does not until
                // its next reload — the kernel plans `now`'s date with none of the state's facts
                // (`Look.Today.forToday`), the fork `state.date`'s (`planwire::plan_date`).
                assert!(plans_nows_date_on_a_stale_state(&app, &k), "{w:?}: the kernel plans now's date");
                assert_eq!(answers["day"]["day"]["date"], "2026-09-07", "{w:?}: the fork plans the state's date");
                assert!(!findings.is_empty(), "{w:?}: gap 3860 says the two plan different days, and the comparison found none");
                assert!(findings.iter().any(|f| f.contains("date")), "{w:?}: the finding names the date: {findings:?}");
            }
            Live::Finding(3861) => {
                // README gap 3861, pinned: a day before its first `tm arrive` holds no location;
                // the request carries `Ctx::loc`'s reading of it, the LOUNGE, and the kernel plans
                // that curve, where fork `Planner::new` reads `Loc::Any` — `energy::curve_key`'s
                // HOME curve, with no home cap. Sent `any`, the kernel plans the fork's day,
                // digest for digest.
                assert_eq!(b.world.state.loc, None, "{w:?}: a day no `tm arrive` located");
                let sent = request_with_loc(&b, None).0;
                assert_eq!(sent["capacity"]["state"]["loc"], "lounge", "{w:?}: the request carries `Ctx::loc`'s lounge");
                assert!(!findings.is_empty(), "{w:?}: gap 3861 says the two plan different days, and the comparison found none");
                let any = kernel_day_with_loc(&b, "any").unwrap_or_else(|e| panic!("{w:?}: {e}"));
                assert_eq!(serde_json::json!(any.hash), answers["day"]["hash"], "{w:?}: sent `any`, the kernel plans the fork's day");
            }
            Live::Finding(g) => panic!("{w:?}: gap {g} names no finding this test pins"),
            _ => assert!(findings.is_empty(), "{w:?}: the kernel's answer is not the comparand's:\n  {}", findings.join("\n  ")),
        }
        if whatif {
            let fork = app.overtime_due().map(|o| o.drops).unwrap_or_else(|| panic!("{w:?}: no overtime is due"));
            for t in TUI_TESTS.iter().filter(|t| first_world(t) == w) {
                if let Asserted::Drops(want) = t.asserted {
                    assert_eq!(fork, want.iter().map(|s| (*s).to_string()).collect::<Vec<_>>(), "{}: the fork's drops are not the asserted ones", t.name);
                }
            }
            let kernel = drops_of(&app, &k);
            match live {
                Live::Equal => assert_eq!(fork, kernel, "{w:?}: the fork's drops against the kernel's"),
                Live::Registered(n) => {
                    assert_ne!(fork, kernel, "{w:?}: a registered P{n} difference on drops the kernel shares");
                    assert_eq!(flags, vec![n], "{w:?}: the comparand departs from the shipped fork by P{n} and by no other number");
                }
                Live::Finding(_) => {}
            }
        }
        if matches!(w, TuiWorld::Replanned { .. }) {
            app.replan();
            assert!(!app.plan.segments.is_empty(), "{w:?}: the fork planned no row");
        }
        summary.push(format!("{w:?} | what-if {whatif} | comparand flags {flags:?} | {live:?}"));
    }
    println!("{}", summary.join("\n"));
    println!("{}", tally.line(0));
}
// END THE FORK PLANNER
