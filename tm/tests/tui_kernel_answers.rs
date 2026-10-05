//! **The TUI's fork-planned tests, answered by the kernel now** — and **a Review screen that
//! draws the kernel's cut of the week** (stage 6 W-40 track H, README gap 3721).
//!
//! Sixteen tests reach the fork's planner through the `tm` crate's own TUI code (README gap
//! 3476's fifteen, and since W-41 the sixteenth its list did not hold, gap 4090): `tui::tests::the_meeting_pause_is_said_on_the_status_line`, three of
//! `tui_today_ghost` and eleven of `tui_today_prompts`. They test the shipped TUI, which plans
//! with the fork until R3's body swap, and they assert values the FORK produced — and the
//! kernel's answer on those worlds was never computed, so the swap would change their
//! assertions blind. [`TUI_TESTS`] is the sixteen, each with EVERY planner call its own code
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
//! **Since W-41 track H fork 4748911's WHOLE DAY on each of those worlds is frozen by value**
//! (README gaps 3963 and 3866, the owner's D81: the TUI's in-memory worlds count as worlds the
//! shipped binary builds): `tests/fixtures/fork-4748911-planner-tui.jsonl` holds one class line
//! per distinct world — the world as the TUI test's own constructors build it, and the fork's
//! answers (`forkclass::ANSWERS`) taken from `tm-oracle plan`, fork 4748911 out of the tree,
//! with every registered departure applied by `forkplan::comparand_answers` and carried by its
//! flag. Outside the fork region the kernel is held to every line by the frozen lines' one
//! comparison, `forkclass::compare_line`, so the verdicts that assert nothing a planner
//! produces — twelve of the sixteen — compare the kernel's whole day with the fork's, and keep
//! doing so after R3 deletes the region's live comparison
//! (`the_kernel_plans_every_frozen_tui_world_as_fork_4748911_planned_it`).
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

/// The committed history a bless holds its lines against (README gap 4151).
#[allow(dead_code)]
#[path = "support/frozenhist.rs"]
mod frozenhist;

use std::collections::BTreeSet;

use serde_json::{json, Value};

use tm_core::dayplan::{DayPlan, SegKind};
use tm_core::log::Event;
use tm_core::model::{Id, IsoWeek};
use tm_core::planwire::KernelDay;
use tm_core::store::{ActiveBlock, RuntimeState};

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
    /// **The kernel departs by a registered number the shipped fork's inputs do not carry** (W-41
    /// track H, README gap 4090): the world's frozen line carries the number's flag, and the kernel
    /// is held to the number's PROPERTY against fork 4748911's day by value — today P69, a start
    /// read from the log (`forkplan::p69_day_unmet`). Since the owner's D89 (W-42 track C, README
    /// gap 4133) the comparand carries P69 too, by a transformation of the fork's inputs
    /// (`forkplan::p69_state`), so the line is ALSO held to the comparand's whole day and what-if.
    Departs(u32),
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
    /// `a_block_started_before_midnight_still_goes_overtime`'s, as the TUI holds it since D84
    /// (`tui_common::before_midnight_app` at 00:30 the next day): `^t3` stopped at 22:30 an hour
    /// short and started again at 23:30 in the log, the state rolled to the new day with
    /// `active.started` `23:30` and `est_min` 60. Until W-45 (README gap 4321) it was `.tm/state.json`
    /// still dated the day before over an empty log — gap 3860's stale state, which the binary no
    /// longer holds and `the_kernel_plans_nows_date_on_a_stale_state` now pins on its own.
    Midnight,
    /// `the_two_prompts_keep_their_own_clocks`' last world: `idle_app(9, 50)` with `^t3`
    /// running again from 09:32, `est_min` 10.
    IdleThenRunning,
    /// The ghost tests' `app_at(10, 42)` replanned, with the arrival record or without it.
    Replanned { arrival: bool },
    /// `worked_midnight_timer.rs`' (`tui_common::after_midnight_app`) at `h:m` on the day after the
    /// fixture's: `^t4` started 23:00 the evening before with `est_min` 60, paused 23:30–00:30 by a
    /// typed pair, the state rolled to the new day with `active.started` still `23:00` (README gap
    /// 4090: the sixteenth test, which W-40's list of fifteen did not hold).
    AfterMidnight(u32, u32),
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

/// **The sixteen** (README gap 3476's list, and gap 4090's sixteenth — found by W-41's simulation of
/// R3, whose guard tripped on a test this list did not hold), each with every planner call its code
/// makes.
/// `the_overtime_prompt_fires_past_est_times_the_multiplier` asks `app_at(12, 0)` first and
/// gets no prompt — `overtime_due` returns before any planner when the estimate is not reached
/// — so its one call is at 12:51; `the_elapsed_minutes_are_worked_minutes_not_wall_clock`'s
/// 12:51 app likewise. `the_overtime_prompt_asks_again_after_the_reprompt_interval` ticks to
/// 13:01 (a replan, no prompt) and 13:08 (a replan and the what-if);
/// `a_prompt_never_steals_a_character_from_the_command_line` ticks the tight app to 12:51 (a
/// replan; the `:` line holds the prompt back) and asks a fresh tight app's what-if.
const TUI_TESTS: [TuiTest; 16] = [
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
        // `Finding(3860)` until W-45: the world was a state dated the day before. Re-drawn as the
        // TUI holds it since D84 (README gap 4321), the start is the log's and the cache's clock
        // falls on the plan's date: P69, as the sixteenth test's world.
        live: Live::Departs(69),
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
        name: "worked_midnight_timer::the_overtime_prompt_comes_after_midnight",
        asks: &[ask(TuiWorld::AfterMidnight(1, 0), true)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        live: Live::Departs(69),
    },
    TuiTest {
        name: "tui::tests::the_meeting_pause_is_said_on_the_status_line",
        asks: &[ask(TuiWorld::MeetingNow, false)],
        asserted: Asserted::Nothing,
        verdict: Verdict::Equal,
        // `Finding(3861)` until W-41: the request carried `Ctx::loc`'s lounge. Since D81
        // (parity P76) it carries the planner's `any`, and the kernel plans the fork's day.
        live: Live::Equal,
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
            let midnight = tm_core::capacity::local_dt(
                cfg.tz,
                tui_common::date().succ_opt().expect("tomorrow"),
                chrono::NaiveTime::from_hms_opt(0, 30, 0).expect("time"),
            );
            let (app, log) = tui_common::before_midnight_app(midnight);
            (app, log, texts)
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
        TuiWorld::AfterMidnight(h, m) => {
            let now = tm_core::capacity::local_dt(
                cfg.tz,
                tui_common::date().succ_opt().expect("tomorrow"),
                chrono::NaiveTime::from_hms_opt(h, m, 0).expect("time"),
            );
            let (app, log) = tui_common::after_midnight_app(now);
            (app, log, texts)
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
/// (`Look.Today.forToday`) — where fork `planwire::plan_date` plans the state's. Since W-45 no TUI
/// world holds such a state (README gap 4321), and `the_kernel_plans_nows_date_on_a_stale_state`
/// holds the kernel to it on the one that did.
fn plans_nows_date_on_a_stale_state(state: &RuntimeState, now: chrono::DateTime<chrono_tz::Tz>, k: &KernelDay) -> bool {
    k.day.date == now.date_naive() && state.date.is_some_and(|d| d != k.day.date)
}

/// **Gap 3860's kernel half, on the world the Midnight test built until W-45** (README gaps 3860
/// and 4321): `.tm/state.json` dated the fixture's day, `^t3` running from 23:30 with 60 minutes
/// estimated, an empty log, at 00:30 the next day — a world the binary no longer holds (D42 ends the
/// block on load; D84 rolls the TUI's state at the date change), kept here because it is the one
/// world that shows the reading. The kernel plans `now`'s date on it, and on the same world with the
/// state dated today the reading does not fire. The kernel alone; no fork, so it outlives R3.
#[test]
fn the_kernel_plans_nows_date_on_a_stale_state() {
    let cfg = tui_common::config();
    let tomorrow = tui_common::date().succ_opt().expect("tomorrow");
    let midnight = tm_core::capacity::local_dt(cfg.tz, tomorrow, chrono::NaiveTime::from_hms_opt(0, 30, 0).expect("time"));
    let mut state = tui_common::state();
    if let Some(a) = state.active.as_mut() {
        a.started = chrono::NaiveTime::from_hms_opt(23, 30, 0).expect("time");
        a.est_min = 60;
    }
    let texts = tui_common::tree_texts();
    let stale = tui_common::app_with_log_text(midnight, state.clone(), "");
    let (_, k) = kernel_answer(&stale, "", &texts).expect("the kernel plans the stale world");
    assert_eq!(k.day.date, tomorrow, "the kernel plans now's date");
    assert!(plans_nows_date_on_a_stale_state(&stale.state, stale.now, &k), "gap 3860's reading does not fire on a stale state");
    state.date = Some(tomorrow);
    let rolled = tui_common::app_with_log_text(midnight, state, "");
    let (_, k) = kernel_answer(&rolled, "", &texts).expect("the kernel plans the rolled world");
    assert!(!plans_nows_date_on_a_stale_state(&rolled.state, rolled.now, &k), "gap 3860's reading fires on a state dated today");
}

/// **The kernel answers every fork-planned TUI world, and each verdict holds** — README gap
/// 3721. For every one of the sixteen and EVERY planner call its own code makes: the kernel
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
    // **The whole answer on every world, against fork 4748911's frozen day** (README gap 3963):
    // what a verdict that asserts nothing a planner produces is held to, by value — and it is
    // computed on every world, so the drops verdicts' worlds are compared whole as well.
    let frozen = tui_lines();
    let whole: Vec<(TuiWorld, Vec<String>)> = worlds
        .iter()
        .map(|w| {
            let unmet = match frozen.iter().find(|l| l["name"] == tui_name(*w)) {
                Some(l) => frozen_unmet(l, &mut forkclass::ClassTally::default()),
                None => vec![format!("{w:?}: no frozen TUI line holds fork 4748911's day on this world")],
            };
            (*w, unmet)
        })
        .collect();
    let whole_holds = |w: TuiWorld| whole.iter().find(|(x, _)| *x == w).is_some_and(|(_, u)| u.is_empty());
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
                // The test asserts nothing a planner produces, so its verdict is about the whole
                // answer: on every world its own code plans over, the kernel's day and what-if are
                // fork 4748911's frozen ones by value (README gap 3963), or the world's finding
                // holds as its gap states it.
                (Asserted::Nothing, Verdict::Equal) => t.asks.iter().all(|x| whole_holds(x.world)),
                (Asserted::Nothing, Verdict::Registered(_)) => false,
            };
            if !held {
                let whole_unmet: Vec<&String> = t.asks.iter().flat_map(|x| whole.iter().filter(move |(w, _)| *w == x.world)).flat_map(|(_, u)| u).collect();
                findings.push(format!(
                    "{}: the verdict {:?} does not hold: the kernel drops {drops:?}, the test asserts {:?}{}",
                    t.name,
                    t.verdict,
                    t.asserted,
                    if whole_unmet.is_empty() { String::new() } else { format!("; against fork 4748911's frozen day: {whole_unmet:?}") }
                ));
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
            // Gap 3860's reading bites every world: since W-45 (README gap 4321) none holds a stale
            // state, and the reading itself is pinned by `the_kernel_plans_nows_date_on_a_stale_state`.
            if plans_nows_date_on_a_stale_state(&app.state, app.now, k) {
                findings.push(format!("{}: read as gap 3860's stale state, and its state is today's", t.name));
            }
            if a.world == TuiWorld::MeetingNow {
                // Gap 3861's world, closed by the campaign's D81 call at W-41 (parity P76): the day holds
                // no location and the request carries the planner's reading of it, `any`
                // (`planwire::planned_loc`), where it carried `Ctx::loc`'s lounge — and the
                // location still moves the day here, so the pin is not vacuous. (Its verdict,
                // `Live::Equal`, is held whole through `verdict_unmet` against the frozen day.)
                let sent = forkplan::request_with_loc(b, None).0["capacity"]["state"]["loc"].clone();
                let lounge = forkplan::kernel_day_with_loc(b, "lounge").map(|d| d.hash);
                if b.world.state.loc.is_some() || sent != "any" || lounge.as_ref().is_ok_and(|h| *h == k.hash) {
                    findings.push(format!("{}: P76 does not hold: loc {:?}, sent {sent}, the day sent `lounge` {lounge:?}, sent `any` {}", t.name, b.world.state.loc, k.hash));
                }
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
    println!("the kernel answered {calls} planner call(s) of the sixteen tests, over {} distinct world(s)", worlds.len());
    assert!(findings.is_empty(), "{}", findings.join("\n  "));
    assert_eq!(TUI_TESTS.len(), 16, "README gap 3476's fifteen and gap 4090's sixteenth");
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
    // The sixteenth world reads the timer `worked_midnight_timer.rs` asserts on its own copy of it
    // (README gap 4090): 40 worked at 00:40, 59 at 00:59, 60 at 01:00 — the log's start and its
    // pause, never the rolled `state.date`'s `23:00`.
    for (h, m, worked) in [(0, 40, 40), (0, 59, 59), (1, 0, 60)] {
        let (app, _, _) = app_of(TuiWorld::AfterMidnight(h, m));
        assert_eq!(app.today, tui_common::date().succ_opt().expect("tomorrow"));
        assert_eq!(app.active_elapsed_min(), Some(worked), "{h:02}:{m:02}: the midnight-timer test's own reading");
    }
    for arrival in [true, false] {
        let (app, _, _) = app_of(TuiWorld::Replanned { arrival });
        assert!(app.state.window.is_some() && app.state.budget.is_some(), "the ghost row reads the state's window and budget");
        assert_eq!(app.status.adherence_pct, arrival.then_some(75), "adherence is the record's and the log's");
    }
}

/// **The kernel's drops and P46's row are read as the TUI reads them** (non-vacuity, AGENTS
/// §5.2): the sixteen tests' kernel what-ifs drop nothing, so a reading of the drops that
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

// ---------------------------------------------------------------------------
// Fork 4748911's whole day on every TUI world, frozen (W-41 track H, README gaps 3963, 3866)
// ---------------------------------------------------------------------------

/// **The frozen TUI days** — one class line per distinct world the sixteen plan over, each the
/// world as the test's own constructors build it ([`app_of`]) and fork 4748911's answers for it
/// (`forkclass::ANSWERS`), asked of `tm-oracle plan` over the kernel's grants as R3's host asks
/// them, every registered departure applied by `forkplan::comparand_answers` and carried by its
/// flag. The owner's D81 counts the TUI's in-memory worlds as worlds the shipped binary builds,
/// which is what admits them as class lines; they are held to their tests' constructors, not to
/// `forkclass::binary_holds` (a TUI state need not be one D42's rebuild reproduces: the
/// `For("m1", …)` world runs `^m1` where the log holds `^t3` open, and the `Midnight` world's
/// log is empty).
const FROZEN_TUI: &str = "fork-4748911-planner-tui.jsonl";

/// Where the frozen TUI days live.
fn tui_path() -> std::path::PathBuf {
    forkday::frozen_path().with_file_name(FROZEN_TUI)
}

/// The frozen TUI lines, in file order; a name carried twice FAILS.
fn tui_lines() -> Vec<Value> {
    tui_lines_of(&std::fs::read_to_string(tui_path()).unwrap_or_else(|e| panic!("{}: {e}", tui_path().display())))
}

/// [`tui_lines`] over a file's text.
fn tui_lines_of(text: &str) -> Vec<Value> {
    let mut seen = BTreeSet::new();
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Value = serde_json::from_str(l).expect("a frozen TUI line is JSON");
            let name = v["name"].as_str().expect("a frozen TUI line names its world").to_string();
            assert!(seen.insert(name.clone()), "two frozen TUI lines for {name}");
            v
        })
        .collect()
}

/// **Every distinct world the sixteen plan over**, in [`TUI_TESTS`]' order — what the frozen
/// file holds a line for, no more and no fewer.
fn tui_worlds() -> Vec<TuiWorld> {
    let mut out: Vec<TuiWorld> = Vec::new();
    for a in TUI_TESTS.iter().flat_map(|t| t.asks.iter()) {
        if !out.contains(&a.world) {
            out.push(a.world);
        }
    }
    out
}

/// A frozen TUI line's name.
fn tui_name(w: TuiWorld) -> String {
    format!("tui {w:?}")
}

/// The world a frozen line's name names, if the sixteen still plan over it.
fn tui_world_named(name: &str) -> Option<TuiWorld> {
    tui_worlds().into_iter().find(|w| tui_name(*w) == name)
}

/// The tests whose own code plans over `w`, by name.
fn tui_tests_of(w: TuiWorld) -> Vec<&'static str> {
    TUI_TESTS.iter().filter(|t| t.asks.iter().any(|a| a.world == w)).map(|t| t.name).collect()
}

/// **A world's verdict on the whole answer** — the [`Live`] of the tests whose FIRST call plans
/// over it (one world, one verdict), and `Equal` for a world only a later call reaches.
fn live_of(w: TuiWorld) -> Live {
    let lives: Vec<Live> = TUI_TESTS.iter().filter(|t| t.asks[0].world == w).map(|t| t.live).collect();
    assert!(lives.windows(2).all(|p| p[0] == p[1]), "{w:?}: one world, one live answer: {lives:?}");
    lives.first().copied().unwrap_or(Live::Equal)
}

/// **A TUI line**: the world's name, the tests that plan over it, its class (a function of the
/// world, as every class line's is), the world, and the answers given.
fn tui_line(w: TuiWorld, b: &Built, answers: &Value) -> Value {
    let mut line = json!({
        "name": tui_name(w),
        "tests": tui_tests_of(w),
        "class": forkclass::class_of(b).key(),
        "world": b.world.to_json(),
    });
    for key in forkclass::ANSWERS {
        forkclass::set_answer(&mut line, key, answers[key].clone());
    }
    // A number no fork input carries is carried by its flag alone, in its own home (gap 4090).
    if let Live::Departs(n) = live_of(w) {
        let flag = format!("p{n}");
        line[flag.as_str()] = json!({flag.as_str(): true});
    }
    line
}

/// **A departing world's stated difference, held against a line's answers** — P69's property
/// over the kernel's day `k` and the frozen lines' one comparison's `findings`; every other verdict
/// is that there are no findings. (Gap 3861's finding was closed by P76 at W-41's land step, and gap
/// 3860's — the last finding this file pinned — lost its world at W-45, README gap 4321: its
/// kernel half is `the_kernel_plans_nows_date_on_a_stale_state`.) Empty when the verdict holds.
/// One definition for the frozen comparison and, while the fork is here, the region's live one.
fn verdict_unmet(w: TuiWorld, live: Live, b: &Built, k: &KernelDay, line: &Value, findings: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    match live {
        Live::Departs(69) => {
            // P69 (README gap 4090): the kernel reads the running block's start off the log, where
            // fork 4748911 puts the cache's clock on the plan's date — held to P69's property against
            // fork 4748911's own day by value, which is also where the departure is shown real.
            // Since the owner's D89 (README gap 4133) the comparand plans from a start the fork CAN
            // be asked with (`forkplan::p69_state`), so the comparison holds the WHOLE day and
            // what-if as well and must find nothing; until D89 it held only the property, and a
            // bent row after the running one passed.
            let fork = forkclass::shipped_of(line);
            match forkplan::logged_start(b) {
                Some(logged) => out.extend(forkplan::p69_day_unmet(&tui_name(w), fork, b, logged, k)),
                None => out.push(format!("{w:?}: P69 departs on a world whose log holds no start for its running block")),
            }
            out.extend(findings.iter().cloned());
            if forkplan::p69_state(b, &b.world.state).is_none() {
                out.push(format!("{w:?}: P69 departs here and its transformation does not reach the world (D89)"));
            }
            if line["p69"]["p69"] != true {
                out.push(format!("{w:?}: P69 departs here and the line carries no `p69` flag"));
            }
        }
        Live::Departs(n) => out.push(format!("{w:?}: P{n} names no property this file holds")),
        Live::Equal | Live::Registered(_) => out.extend(findings.iter().cloned()),
    }
    out
}

/// **One frozen TUI line against the kernel**: the frozen lines' one comparison
/// (`forkclass::compare_line`, the kernel asked as R3's host asks) and the world's verdict
/// ([`verdict_unmet`]). Empty when it holds.
fn frozen_unmet(line: &Value, t: &mut forkclass::ClassTally) -> Vec<String> {
    let name = line["name"].as_str().unwrap_or("?");
    let Some(w) = tui_world_named(name) else {
        return vec![format!("{name}: no test plans over this world any more — the line is STALE")];
    };
    let b = match ClassWorld::of_json(&line["world"], tui_common::config().tz) {
        Ok(world) => Built::of(world),
        Err(e) => return vec![format!("{name}: {e}")],
    };
    let k = match forkclass::kernel_answer(&b) {
        Ok(k) => k,
        Err(e) => return vec![format!("{name}: the kernel did not plan the world: {e}")],
    };
    let findings = forkclass::compare_line(line, t);
    verdict_unmet(w, live_of(w), &b, &k, line, &findings)
}

/// **Every frozen TUI world is the one its tests build** (AGENTS §5.4; README gap 3963): the
/// file holds a line for every distinct world the sixteen plan over and for no other, each world
/// byte for byte what [`app_of`] builds now through `tui_common`'s own constructors — so a
/// change to a constructor that moves a world fails by name, and the bless decides whether it is
/// a D64(b) re-draw — each naming the tests that plan over it, and a re-drawn line saying why.
#[test]
fn every_frozen_tui_world_is_the_one_its_tests_build() {
    let lines = tui_lines();
    let want: Vec<String> = tui_worlds().into_iter().map(tui_name).collect();
    let have: Vec<String> = lines.iter().map(|l| l["name"].as_str().unwrap_or_default().to_string()).collect();
    assert_eq!(have, want, "the frozen TUI lines are the sixteen's worlds, in their order");
    let mut bad = Vec::new();
    for l in &lines {
        let w = tui_world_named(l["name"].as_str().unwrap_or_default()).expect("a world, checked above");
        let (app, log, texts) = app_of(w);
        let b = built_of(&app, &log, &texts);
        if b.world.to_json() != l["world"] {
            let first = forkplan::first_difference("world", &l["world"], &b.world.to_json());
            bad.push(format!("{}: the test builds another world now ({})", tui_name(w), first.unwrap_or_default()));
        }
        if l["tests"] != json!(tui_tests_of(w)) {
            bad.push(format!("{}: the line names the tests {}, and {:?} plan over it", tui_name(w), l["tests"], tui_tests_of(w)));
        }
        // The line the bless writes from its own answers is the committed line, byte for byte.
        let mut again = tui_line(w, &b, l);
        if let Some(why) = l.get("d64b") {
            again["d64b"] = why.clone();
        }
        if again != *l {
            bad.push(format!("{}: the bless would write another line ({})", tui_name(w), forkplan::first_difference("line", l, &again).unwrap_or_default()));
        }
        if let Some(why) = l.get("d64b").and_then(Value::as_str) {
            if !forkclass::is_d64b_reason(why) {
                bad.push(format!("{}: re-drawn with the reason {why:?}, which is not dated or names no D64(b)", tui_name(w)));
            }
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n  "));
}

/// **The kernel plans every frozen TUI world as fork 4748911 planned it** — README gaps 3963
/// and 3866, the comparison that outlives R3: on every frozen TUI line the kernel's whole day
/// and what-if, asked as R3's host asks them, against fork 4748911's answers by value
/// (`forkclass::compare_line`, with each registered departure by its property — P46's
/// reservation, P47's pause, and the rest the comparand's flags carry), except where the world's
/// verdict is a finding, which must hold as its gap states it ([`verdict_unmet`]). Neither side
/// is in-tree code a test process runs after R3: one is the kernel, the other bytes on disk.
#[test]
fn the_kernel_plans_every_frozen_tui_world_as_fork_4748911_planned_it() {
    let lines = tui_lines();
    let mut t = forkclass::ClassTally::default();
    let mut unmet = Vec::new();
    let mut summary = Vec::new();
    for l in &lines {
        let u = frozen_unmet(l, &mut t);
        let flags: Vec<u32> = forkclass::parity_flags(l).into_iter().filter(|f| f.1).map(|f| f.0).collect();
        let w = tui_world_named(l["name"].as_str().unwrap_or_default());
        summary.push(format!("{} | comparand flags {flags:?} | {:?} | {}", l["name"].as_str().unwrap_or("?"), w.map(live_of), if u.is_empty() { "holds" } else { "UNMET" }));
        unmet.extend(u);
    }
    println!("{}", summary.join("\n"));
    println!("{}", t.line(unmet.len()));
    assert!(unmet.is_empty(), "{} frozen TUI line(s) unmet:\n  {}", unmet.len(), unmet.join("\n  "));
    assert_eq!(lines.len(), tui_worlds().len(), "every world the sixteen plan over is compared");
    assert!(t.whatifs > 0 && t.p46 > 0 && t.p47 > 0, "the TUI lines exercise the what-if, P46 and P47: {t:?}");
}

/// The oracle at `TM_ORACLE`, when set (D23's shape: every arm that asks it is inert without it).
fn the_oracle() -> Option<forkplan::Oracle> {
    forkplan::oracle_path().map(forkplan::Oracle::new)
}

/// **A world's fork answers over `fp`**: the kernel's grants as R3's host asks them, and
/// `forkplan::comparand_answers` — the frozen lines' one definition — with `fp` planning.
fn tui_answers(b: &Built, fp: &dyn forkplan::ForkPlan) -> Result<(Value, Vec<tm_core::priority::Prio>), String> {
    let prios = forkclass::kernel_answer_with_grants(b)?.1;
    let answers = forkplan::comparand_answers(b, &prios, fp)?;
    Ok((answers, prios))
}

/// **The frozen TUI days are fork 4748911's answer today, out of the tree** (`TM_ORACLE`, D23's
/// shape; outlives R3): every line's answers, asked again of `tm-oracle plan` through the
/// comparand's one definition over the kernel's grants now, are the frozen ones, key for key.
#[test]
#[ignore]
fn the_frozen_tui_days_are_the_forks_oracle_answer_today() {
    let Some(oracle) = the_oracle() else { return };
    let mut stale = Vec::new();
    for l in tui_lines() {
        let b = Built::of(ClassWorld::of_json(&l["world"], tui_common::config().tz).expect("a stored world"));
        let (now, _) = tui_answers(&b, &oracle).unwrap_or_else(|e| panic!("{}: {e}", l["name"]));
        stale.extend(forkclass::ANSWERS.iter().filter(|k| now[**k] != l[**k]).map(|k| format!("{}: `{k}`", l["name"].as_str().unwrap_or("?"))));
    }
    println!("tm-oracle plan asked {} time(s)", *oracle.asked.lock().expect("census"));
    assert!(stale.is_empty(), "the fork oracle does not answer the frozen TUI days as frozen:\n  {}", stale.join("\n  "));
}

/// **Freeze the TUI days** — inert without `TM_TUI_BLESS`, and it asks `TM_ORACLE` (fork 4748911
/// out of the tree, as the brief of README gap 3963 asks). Every world of [`tui_worlds`] is built
/// through its tests' own constructors and written with the oracle's answers. A line the file
/// already holds is held to the owner's D64 exactly as the class lines' re-bless is
/// (`forkclass::d64_allows`, with the shipped fork's day asked of the oracle and the reasons
/// `TM_TUI_BLESS_BECAUSE`, and since the owner's D85 a corrected harness reading's in
/// `TM_TUI_BLESS_HARNESS`, D64(c)); a WORLD that moved is a re-draw, allowed only with D64(b)'s
/// reason in `TM_TUI_BLESS_REDRAW` (dated, naming `D64(b)`), which the line then carries as
/// `d64b`; a line HEAD holds that no test plans over any more is refused. Each change is named; a
/// refusal writes nothing. `TM_TUI_BLESS_OUT` writes elsewhere, for a dry run.
///
/// **What a line is held against is the file's COMMITTED history** (W-42 track C, README gap
/// 4151; `frozenhist::held`): its latest version at HEAD or at any first-parent commit since
/// `kernel/ratchet.py`'s base — never the working copy, so deleting the file or a line of it is
/// not a fresh freeze. W-41's land step froze this file fresh with the fixture removed (README
/// gaps 4123 and 4139); under this rule that run would have been held to the committed line.
#[test]
#[ignore]
fn the_frozen_tui_days_are_blessed() {
    if std::env::var_os("TM_TUI_BLESS").is_none() {
        eprintln!("inert: set TM_TUI_BLESS=1 (with TM_ORACLE) to write {FROZEN_TUI}");
        return;
    }
    let oracle = the_oracle().expect("TM_TUI_BLESS asks the fork: set TM_ORACLE");
    let because = forkclass::because_of("TM_TUI_BLESS_BECAUSE");
    let harness = forkclass::harness_of("TM_TUI_BLESS_HARNESS");
    let redraw = std::env::var("TM_TUI_BLESS_REDRAW").ok();
    let registered = forkclass::registered_parity();
    let held = frozenhist::held(&tui_path(), frozenhist::key_of("name")).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{}", held.census(FROZEN_TUI));
    let (mut out, mut refused, mut changed, mut added) = (String::new(), Vec::new(), Vec::new(), 0usize);
    for w in tui_worlds() {
        let (app, log, texts) = app_of(w);
        let b = built_of(&app, &log, &texts);
        let (answers, prios) = tui_answers(&b, &oracle).unwrap_or_else(|e| panic!("{w:?}: {e}"));
        let mut line = tui_line(w, &b, &answers);
        match held.get(&tui_name(w)) {
            None => added += 1,
            Some(old) if old["world"] != line["world"] => match redraw.as_deref() {
                Some(why) if forkclass::is_d64b_reason(why) => {
                    line["d64b"] = json!(why);
                    changed.push(format!("{} re-drawn", tui_name(w)));
                }
                _ => refused.push(format!(
                    "{}: its test builds another world now — a re-draw, which needs D64(b)'s reason in TM_TUI_BLESS_REDRAW",
                    tui_name(w)
                )),
            },
            Some(old) => {
                if let Some(why) = old.get("d64b") {
                    line["d64b"] = why.clone();
                }
                let ask = forkplan::ForkAsk { state: &b.world.state, now: b.world.now, d60: false, p64: false, prios: &prios, extend: None, log_line: None };
                let shipped = forkplan::ForkPlan::plan(&oracle, &b, &ask).unwrap_or_else(|e| panic!("{w:?}: {e}")).fork_day;
                match forkclass::d64_allows(old, &line, &shipped, &because, harness.as_deref(), &registered) {
                    Err(e) => refused.push(e),
                    Ok(keys) if !keys.is_empty() => changed.push(format!("{} `{}`", tui_name(w), keys.join("`, `"))),
                    Ok(_) => {}
                }
            }
        }
        out.push_str(&serde_json::to_string(&line).expect("a line serialises"));
        out.push('\n');
    }
    for name in &held.head {
        if tui_world_named(name).is_none() {
            refused.push(format!("{name}: a frozen line no test plans over any more"));
        }
    }
    eprintln!("TUI days: {added} line(s) added, {} changed ({}), {} refused", changed.len(), changed.join("; "), refused.len());
    assert!(refused.is_empty(), "the TUI re-bless is refused and wrote nothing:\n  {}", refused.join("\n  "));
    let path = std::env::var_os("TM_TUI_BLESS_OUT").map(std::path::PathBuf::from).unwrap_or_else(tui_path);
    std::fs::write(path, out).expect("the frozen TUI days are written");
}

/// **A frozen TUI name carried twice is refused** (AGENTS §5.8: the reader's guard has an input
/// that fails it).
#[test]
#[should_panic(expected = "two frozen TUI lines for")]
fn a_frozen_tui_name_carried_twice_is_refused() {
    let one = serde_json::to_string(&tui_lines()[0]).expect("a line");
    tui_lines_of(&format!("{one}\n{one}\n"));
}

/// **The frozen comparison bites** (AGENTS §5.8): a frozen line bent in its day, in its what-if,
/// or in its world's verdict is refused by name — and a line no test plans over is STALE.
#[test]
fn the_frozen_tui_comparison_bites_a_bent_line() {
    let lines = tui_lines();
    let held = |l: &Value| frozen_unmet(l, &mut forkclass::ClassTally::default());
    let plain = lines.iter().find(|l| l["name"] == tui_name(TuiWorld::At(12, 51))).expect("the overtime world").clone();
    assert!(held(&plain).is_empty(), "the unbent line holds: {:?}", held(&plain));
    let mut day = plain.clone();
    day["day"]["day"]["segments"][1]["end"] = json!("2026-09-07T23:59:00-05:00");
    assert!(held(&day).iter().any(|f| f.contains("tui At(12, 51)")), "a bent day passed: {:?}", held(&day));
    let mut whatif = plain.clone();
    whatif["whatif"]["full"]["drift_min"] = json!(9999);
    assert!(held(&whatif).iter().any(|f| f.contains("what-if")), "a bent what-if passed");
    let mut stale = plain.clone();
    stale["name"] = json!("tui NoSuchWorld");
    assert!(held(&stale).iter().any(|f| f.contains("STALE")), "a stale line passed");
    // A departing world's verdict bites too: since W-45 the Midnight line is P69's (README gap
    // 4321), and without its flag it is refused —
    let midnight = lines.iter().find(|l| l["name"] == tui_name(TuiWorld::Midnight)).expect("the midnight world").clone();
    assert!(held(&midnight).is_empty(), "the midnight line holds P69's property: {:?}", held(&midnight));
    let mut bare = midnight.clone();
    bare.as_object_mut().expect("a line").remove("p69");
    assert!(held(&bare).iter().any(|f| f.contains("carries no `p69` flag")), "the midnight line without its P69 flag passed");
    // — and gap 4090's line, P69's, without its flag or with the kernel's running row in the fork's day —
    let after = lines.iter().find(|l| l["name"] == tui_name(TuiWorld::AfterMidnight(1, 0))).expect("the after-midnight world").clone();
    assert!(held(&after).is_empty(), "the after-midnight line holds P69's property");
    let mut unflagged = after.clone();
    unflagged.as_object_mut().expect("a line").remove("p69");
    assert!(held(&unflagged).iter().any(|f| f.contains("carries no `p69` flag")), "a P69 line without its flag passed");
    let ab = Built::of(ClassWorld::of_json(&after["world"], tui_common::config().tz).expect("a world"));
    let ak = forkclass::kernel_answer(&ab).expect("the kernel plans");
    let mut holding = after.clone();
    holding["shipped"]["day"]["segments"] = serde_json::to_value(&ak.day).expect("a day")["segments"].clone();
    assert!(held(&holding).iter().any(|f| f.contains("departs nowhere")), "a P69 line whose fork day holds the kernel's row passed");
    // — and since the owner's D89, P69's comparand WHOLE (README gap 4133): a step-5 row a minute
    // longer (`work`) and two step-5 rows' items swapped (`swap`) in the frozen comparand — the two
    // bends P69's property alone let through at the W-41 repair — each refused by name.
    let step5 = |r: &Value| r["kind"] == "block" && r["flags"]["current"] != true && r["flags"]["open"] != true;
    let mut work = after.clone();
    let rows = work["day"]["day"]["segments"].as_array_mut().expect("the comparand's rows");
    let r = rows.iter_mut().find(|r| step5(r)).expect("a step-5 row on the after-midnight day");
    r["end"] = json!((forkplan::at(&r["end"]).expect("an end") + chrono::Duration::minutes(1)).to_rfc3339());
    assert!(held(&work).iter().any(|f| f.contains("tui AfterMidnight(1, 0)") && f.contains("the rows differ at")), "a bent step-5 row passed: {:?}", held(&work));
    let mut swap = after.clone();
    let rows = swap["day"]["day"]["segments"].as_array_mut().expect("the comparand's rows");
    let i = rows.iter().position(|r| step5(r)).expect("a step-5 row");
    let j = rows.iter().position(|r| step5(r) && r["item"] != rows[i]["item"]).expect("a second step-5 item");
    let (a, z) = (rows[i]["item"].clone(), rows[j]["item"].clone());
    rows[i]["item"] = z;
    rows[j]["item"] = a;
    assert!(held(&swap).iter().any(|f| f.contains("tui AfterMidnight(1, 0)") && f.contains("the rows differ at")), "two swapped step-5 rows passed: {:?}", held(&swap));
    // — and gap 3861's world, `Live::Equal` since P76 (W-41's land step): the kernel sent `any`
    // plans the frozen fork day, and a line whose fork day is the kernel's LOUNGE day — what the
    // request carried until P76 — is refused by the whole-day comparison.
    let meeting = lines.iter().find(|l| l["name"] == tui_name(TuiWorld::MeetingNow)).expect("the meeting world").clone();
    assert!(held(&meeting).is_empty(), "the meeting line holds whole under P76: {:?}", held(&meeting));
    let b = Built::of(ClassWorld::of_json(&meeting["world"], tui_common::config().tz).expect("a world"));
    let lounge = forkplan::kernel_day_with_loc(&b, "lounge").expect("the kernel plans the lounge day");
    let mut agreeing = meeting.clone();
    agreeing["day"] = forkclass::frozen_day(&lounge.day);
    assert!(held(&agreeing).iter().any(|f| f.contains("tui MeetingNow")), "a meeting line holding the lounge day passed: {:?}", held(&agreeing));
}

