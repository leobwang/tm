//! **The planner's generated days** — the generator `planner_invariants.rs`'
//! arms draw from, moved here at stage 6 W-37 track H (README gaps 3080 and
//! 3084) so that it outlives R3.
//!
//! # Why it lives in `tests/support/`
//!
//! R3 deletes `tm-core/src/planner.rs`, and every differential arm of
//! `planner_invariants.rs` plans with it. The GENERATOR plans with nothing: a
//! [`Case`] is a tree, a log and a `.tm/state.json`, and [`build`] parses them
//! with the host's readers. Two things must survive the fork's deletion and
//! both need it:
//!
//! * **the comparand keyed by class** (`support/forkclass.rs`,
//!   `planner_classes.rs`): its worlds were DRAWN from this generator (README
//!   gap 3080 — until W-37 by a harness that lived in a scratchpad, because the
//!   generator was private to a file that track could not touch), and
//!   `forkclass::class_draws` now re-draws every one of them from here, so a
//!   frozen world is the generator's own draw by a test and not by a sentence;
//! * **the arms that plan with the kernel** — `planner_invariants.rs`' §8.3
//!   invariants and its cell comparison, asked of the kernel's day on every
//!   generated case since W-37.
//!
//! # The widenings live here too
//!
//! Three arms widen what the shared generator draws — the hash arm a learned
//! multiplier and a break in today's log, the W-35 arm a running break and a
//! forced overtime, the step-8 arm a travel day and a spent budget — and the
//! class draw applies ONE arm's widenings per case, exactly as that arm does.
//! So each widening is ONE function here, called by its arm and by the draw:
//! [`set_multiplier`], [`log_a_break`], [`run_a_break`], [`force_overtime`] and
//! [`widen_for_notes`]. A second copy in a draw harness is AGENTS §5.3's defect
//! and was how the W-36 draw was made.
//!
//! # A generated world is one the binary can build (owner D64(b), README gap 3138)
//!
//! Until W-37 the generator set `state.interrupt` and wrote no `interrupt` line,
//! and D42's reconcile rebuilds `.tm/state.json`'s open interruption from the
//! log (`tm/src/cli/ctx.rs`' `derived_state` / `reconcile_state`) — so the
//! binary, handed such a world, plans it as NOT interrupted. Every generated
//! interruption is now LOGGED as `tm interrupt` logs it ([`interruption`]): at
//! its start, carrying the block that was running then, and pausing that block
//! (`tm/src/cli/day.rs`' `interrupt`); and it starts after the last block the
//! log closes, because a block ended inside an interruption would carry
//! minutes `tm done` does not write. A running break likewise starts after the
//! last `start`/`done` the log holds ([`run_a_break`]), because `tm start` and
//! `tm done` end a running break (`day.rs`' `end_break`).

#![allow(dead_code)]

use chrono::{DateTime, Duration, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use proptest::prelude::*;
use serde_json::{json, Value};
use tm_core::capacity::local_dt;
use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::{Event, LogEntry, Replay};
use tm_core::model::Id;
use tm_core::priority::{self, Candidate};
use tm_core::store::{ActiveBlock, BreakState, InterruptState, RuntimeState};
use tm_core::tree::Tree;

use crate::chokepoint;

pub const DAY: &str = "2026-09-07";
pub const MAX_ITEMS: usize = 40;

/// The five §4.3 routines a case may switch on, and the evening wall the late
/// day carries.
pub const ROUTINES: [&str; 6] = [
    "- lunch      win:11:30-13:30 dur:30m  every:day",
    "- workout    win:16:00-19:00 dur:1h   every:Mon,Wed,Fri",
    "- shower     win:07:00-23:00 dur:20m  after-done:2d~1d",
    "- breakfast  win:06:00-09:00 dur:30m  every:day pref:wake+10m",
    "- sleep      win:22:00-08:00 dur:8h30m every:day ci:0",
    // **THE SIXTH CONTENDS WITH `lunch` FOR ONE POSITION** (W-32, README gap
    // 2226). The five above have pairwise-disjoint placeable windows, so §8.2
    // step 2's ORDERING half — "mandatory first, then the moment the window
    // closes; the tightest window claims its position first" — was asserted by
    // nothing: an auditor reversed `collect_routines`' sort and no row of any
    // case moved. `teatime` is mandatory, its window is 11:00-12:00 and it needs
    // the whole hour, so it has EXACTLY ONE feasible position and it overlaps
    // `lunch`'s 11:30-13:30. Sorted by the window's close it takes 11:00-12:00
    // and `lunch` follows at 12:00; sorted any other way — by id, by the window's
    // OPEN, or reversed — `lunch` takes 11:30-12:00 first and `teatime` is left
    // with 30 free minutes for a 60-minute job and goes unplaced, which step 6
    // cannot repair either (its window holds no free hour and no assigned slot
    // an hour long to displace). So the placement is the ordering: the two rows
    // below cannot both exist under any other order.
    //
    // **IT IS NOT IN `case_strategy`'s RANGE, ON PURPOSE.** `routines` is drawn
    // `0u8..32` and stays there: proptest's stored regressions are SEEDS, not
    // values, so widening the range re-maps every one of the sixteen entries in
    // `planner_invariants.proptest-regressions` — including `af6b8c79…`, which
    // D46 says replays on every run — onto different cases. The draw is made by
    // `two_routines_contend_for_one_position` below instead, which costs nothing
    // and keeps them. README gap 2226 records what that leaves open.
    "- teatime    win:11:00-12:00 dur:1h   every:day",
];
pub const OPTIONALS: &str = "- Watch something  dur:1h\n- Play something   dur:2h max:4h/w\n";

/// **A dated window task** (W-38, README gap 3200) — `plan-basic`'s `^a3`, "Pick up
/// package", with a generated id: a task whose `win:` is a stretch of today, which §8.2
/// step 2 places as a Routine row and §7 answers `p = 0` (a mandatory window instance) —
/// the row fork `emit_segments` marks `⚠` and the kernel's `Planner.PlanReq.routineHot`
/// marks. The shared generator writes none (its routines are `routines.md` lines, which
/// carry no `⚠` on either side), so until W-38 no frozen generated day held the mark.
pub const WINDOW_TASK: &str = "- [ ] 1 Pick up package  win:2026-09-07T09:00/21:00 dur:20m ^xaa\n";

/// The document [`WINDOW_TASK`] is written into, under `plan-basic`'s own heading.
pub const WINDOW_TASK_DOC: &str = "backlog.md";

/// **A break `tm break` logged inside the running block** (W-38, README gap 3282; the
/// W-36 worked arm's widening): `tm break <len>m` at `t` pauses the block and a second
/// `tm break` at `t + len` ends it (`tm/src/cli/day.rs`' `take_break` and `end_break`),
/// which un-pauses the block and appends ONE line, stamped at the break's start, planned
/// and taken `len` minutes, with no place. The replay's open block never sees it (so the
/// log's reading of the block's worked minutes counts it as worked) and the host's
/// `Replay::active_worked_min` nets it out — the one class on which the two readings
/// differ on a day with no running break, which parity P55 is about.
pub fn inner_break_line(t: DateTime<Tz>, len: u32) -> String {
    format!("{{\"t\":\"{}\",\"ev\":\"break\",\"planned_min\":{len},\"actual_min\":{len}}}\n", t.to_rfc3339())
}

/// **A world's documents with the dated window task added** (README gap 3200): the one
/// widening `forkclass::window_worlds` derives from a stored world. `false`, and nothing
/// written, when the documents already hold the task's document.
pub fn with_window_task(docs: &mut Vec<(String, String)>) -> bool {
    if docs.iter().any(|(p, _)| p == WINDOW_TASK_DOC) {
        return false;
    }
    docs.push((WINDOW_TASK_DOC.to_string(), format!("# Untied\n{WINDOW_TASK}")));
    true
}
pub const EVENING_WALL: &str = "- [ ] 3 Long evening at:2026-09-07T15:00/21:00 ^wev\n";

pub fn date() -> NaiveDate {
    NaiveDate::parse_from_str(DAY, "%Y-%m-%d").expect("date")
}

pub fn at(tz: Tz, h: u32, m: u32) -> DateTime<Tz> {
    local_dt(tz, date(), NaiveTime::from_hms_opt(h, m, 0).expect("time"))
}

/// One generated item line.
#[derive(Debug, Clone)]
pub struct Spec {
    pub ci: u8,
    pub k: u8,
    pub est_b: u32,
    /// A `≤ batch_max_min` estimate instead of `est_b` blocks (§7.5).
    pub small: Option<u32>,
    pub due_in: Option<u8>,
    pub dep: Option<usize>,
    pub loc_home: bool,
    pub atomic: bool,
    /// **`[?]`, `hot` and `min:` lines** (W-33 repair, README gap 2568). §8.2 step 8's
    /// comparison below reads `waiting`, the hot-flag arm of `hot` and the FLOOR arm of
    /// `impossible`, and this generator wrote only `- [ ]` lines with no `hot` and no
    /// `min:` -- so `waiting` was compared as `[]` against `[]` on every day, and the two
    /// arms were compared on none (the reuse critic's census). A field compared only at
    /// its default value is a check no input can fail (AGENTS §9.2).
    pub waiting: bool,
    pub hot: bool,
    /// `min:<n>b/d`, a per-day floor of `n` blocks.
    pub floor: Option<u32>,
    /// **The item's written `@parent`** (stage 6 W-27), an index taken modulo
    /// the item's own position so the link always names an item **earlier** in
    /// the one generated file: never dangling, never a cycle, never itself.
    ///
    /// It is here because the generated corpus carried **no `@` token at all**
    /// and so the `parent` cell of every row was the empty string on both
    /// sides. `the_kernel_reads_every_day_the_fork_planned` compares that cell
    /// — and an auditor perturbed `Emit.parentCell` and watched the arm stay
    /// **green** while `kernel_row_cells` (whose fixture day has parents)
    /// failed. A cell compared only at its default value is a check no input
    /// can fail (AGENTS §9.2). README gap 1437's neighbour.
    pub parent: Option<usize>,
}

/// One generated wall.
#[derive(Debug, Clone)]
pub struct WallSpec {
    pub hour: u32,
    pub hours: u32,
}

/// Everything one case varies.
#[derive(Debug, Clone)]
pub struct Case {
    pub items: Vec<Spec>,
    pub walls: Vec<WallSpec>,
    pub now_idx: usize,
    pub done_blocks: u32,
    pub report: Option<u8>,
    /// Bit i switches [`ROUTINES`]`[i]` on.
    pub routines: u8,
    pub optionals: bool,
    /// The day is spent at home: §8.2 step 3's `home_max_ci` caps every slot.
    pub home: bool,
    /// `(item index, minutes running so far, est_min)` — `state.active`.
    pub active: Option<(usize, u32, u32)>,
    /// Minutes ago the open interruption started.
    pub interrupt: Option<u32>,
    /// A late arrival plus the evening wall: §8.1 pushes the window past the
    /// wind-down.
    pub late: bool,
}

impl Case {
    /// The hour `tm arrive` was logged at.
    pub fn arrival_hour(&self) -> u32 {
        if self.late {
            11
        } else {
            7
        }
    }
    pub fn wake_time(&self) -> NaiveTime {
        NaiveTime::from_hms_opt(if self.late { 9 } else { 6 }, 30, 0).expect("time")
    }
    /// `now` — arrival, +1h30, +3h or +5h.
    pub fn now(&self, tz: Tz) -> DateTime<Tz> {
        let base = at(tz, self.arrival_hour(), 0);
        base + Duration::minutes(match self.now_idx {
            0 => 0,
            1 => 90,
            2 => 180,
            _ => 300,
        })
    }
    /// The instant `tm arrive` was logged at.
    pub fn arrival(&self, tz: Tz) -> DateTime<Tz> {
        at(tz, self.arrival_hour(), 0)
    }
    /// The blocks the log may hold: one an hour since arrival.
    pub fn done(&self, tz: Tz) -> u32 {
        let room = ((self.now(tz) - self.arrival(tz)).num_minutes() / 60).max(0) as u32;
        self.done_blocks.min(room).min(self.items.len() as u32)
    }
}

pub fn spec_strategy() -> impl Strategy<Value = Spec> {
    (
        0u8..=5,
        1u8..=4,
        1u32..=4,
        // A third of the items are small enough to batch (§7.5), and they
        // share a `ci` so that they really do group.
        prop_oneof![2 => Just(None), 1 => prop::option::of(prop::sample::select(vec![10u32, 15, 20]))],
        // Deadlines cluster on today and tomorrow, so `p = 0` is common and
        // "HOT before queue" has something to say.
        prop_oneof![
            3 => Just(Some(0u8)),
            2 => Just(Some(1u8)),
            2 => prop::option::of(2u8..=9),
        ],
        prop::option::of(0usize..MAX_ITEMS),
        any::<bool>(),
        any::<bool>(),
        // Half the items are written under a parent, so the `parent` cell is
        // compared at a real value on most rows rather than only at `""`.
        prop_oneof![1 => Just(None), 1 => prop::option::of(0usize..MAX_ITEMS)],
        // A sixth of the lines wait, a sixth are flagged hot, a fifth carry a daily floor.
        prop_oneof![5 => Just(false), 1 => Just(true)],
        prop_oneof![5 => Just(false), 1 => Just(true)],
        prop_oneof![4 => Just(None), 1 => prop::option::of(1u32..=12)],
    )
        .prop_map(|(ci, k, est_b, small, due_in, dep, loc_home, atomic, parent, waiting, hot,
                    floor)| Spec {
            // Small items cluster on two `ci` levels so that §7.5 really does
            // group them (batching needs an equal `ci`).
            ci: if small.is_some() { 2 + ci % 2 } else { ci },
            k,
            est_b,
            small,
            due_in,
            dep,
            loc_home,
            atomic,
            parent,
            waiting,
            hot,
            floor,
        })
}

pub fn case_strategy() -> impl Strategy<Value = Case> {
    (
        prop::collection::vec(spec_strategy(), 1..=MAX_ITEMS),
        prop::collection::vec((8u32..=17, 1u32..=2), 0..=2),
        0usize..4,
        0u32..=3,
        prop::option::of(0u8..=5),
        0u8..32,
        any::<bool>(),
        any::<bool>(),
        prop::option::of((0usize..MAX_ITEMS, 5u32..=90, 30u32..=180)),
        prop::option::of(5u32..=60),
        any::<bool>(),
    )
        .prop_map(
            |(
                items,
                walls,
                now_idx,
                done_blocks,
                report,
                routines,
                optionals,
                home,
                active,
                interrupt,
                late,
            )| Case {
                walls: walls
                    .into_iter()
                    .map(|(hour, hours)| WallSpec { hour, hours })
                    .collect(),
                active: active.map(|(i, ago, est)| (i % items.len(), ago, est)),
                items,
                now_idx,
                done_blocks,
                report,
                routines,
                optionals,
                home,
                interrupt,
                late,
            },
        )
}

/// Three letters, so the id is always valid and always unique.
pub fn id_of(prefix: char, i: usize) -> String {
    let a = (b'a' + (i / 26) as u8) as char;
    let b = (b'a' + (i % 26) as u8) as char;
    format!("{prefix}{a}{b}")
}

pub fn week_text(case: &Case) -> String {
    let mut s = String::from("---\nweek: 2026-W37\n---\n# Milestones\n");
    for (i, sp) in case.items.iter().enumerate() {
        let id = id_of('z', i);
        let est = match sp.small {
            Some(m) => format!("{m}m"),
            None => format!("{}b", sp.est_b),
        };
        let mut line = format!(
            "- [{}] {} {est} Item{i} !{}",
            if sp.waiting { '?' } else { ' ' },
            sp.ci,
            sp.k
        );
        // **The written parent** (W-27). `% i` keeps the link pointing at an
        // earlier line of this same file, so `Tree::dangling_parents` and
        // `Tree::parent_cycles` are both empty by construction and the case is
        // a tree the fork loads rather than one it rejects.
        if let Some(par) = sp.parent {
            if i > 0 {
                line.push_str(&format!(" @{}", id_of('z', par % i)));
            }
        }
        if let Some(d) = sp.due_in {
            let due = date() + Duration::days(i64::from(d));
            line.push_str(&format!(" due:{due}T23:59"));
        }
        if let Some(dep) = sp.dep {
            if i > 0 {
                line.push_str(&format!(" after:^{}", id_of('z', dep % i)));
            }
        }
        if sp.loc_home {
            line.push_str(" loc:home");
        }
        if sp.atomic {
            line.push_str(" atomic");
        }
        if let Some(n) = sp.floor {
            line.push_str(&format!(" min:{n}b/d"));
        }
        if sp.hot {
            line.push_str(" hot");
        }
        line.push_str(&format!(" ^{id}\n"));
        s.push_str(&line);
    }
    s
}

pub fn calendar_text(case: &Case) -> String {
    let mut s = String::new();
    for (j, w) in case.walls.iter().enumerate() {
        let end = (w.hour + w.hours).min(23);
        if end <= w.hour {
            continue;
        }
        s.push_str(&format!(
            "- [ ] 3 Wall{j} at:{DAY}T{:02}:00/{:02}:00 ^{}\n",
            w.hour,
            end,
            id_of('w', j)
        ));
    }
    if case.late {
        s.push_str(EVENING_WALL);
    }
    s
}

pub fn routines_text(case: &Case) -> String {
    let mut s = String::new();
    for (i, line) in ROUTINES.iter().enumerate() {
        if case.routines & (1 << i) != 0 {
            s.push_str(line);
            s.push('\n');
        }
    }
    s
}

pub fn log_text(case: &Case, cfg: &Config, arrival: &Arrival, typed: bool) -> String {
    let tz = cfg.tz;
    let arrive = case.arrival_hour();
    let done = case.done(tz);
    let wake = case.wake_time();
    let loc = arrival.loc;
    let mut s = format!(
        "{{\"t\":\"{DAY}T{:02}:{:02}:00-05:00\",\"ev\":\"wake\",\"slept_min\":480}}\n\
         {{\"t\":\"{DAY}T{arrive:02}:00:00-05:00\",\"ev\":\"arrive\",\"loc\":\"{loc}\",\
         \"window\":[\"{}\",\"{}\"],\"budget\":{}}}\n",
        wake.format("%H").to_string().parse::<u32>().unwrap_or(6),
        wake.format("%M").to_string().parse::<u32>().unwrap_or(0),
        arrival.window.0.format("%H:%M"),
        arrival.window.1.format("%H:%M"),
        arrival.budget,
    );
    for j in 0..done {
        let id = id_of('z', j as usize);
        let start = arrive + j;
        s.push_str(&format!(
            "{{\"t\":\"{DAY}T{start:02}:00:00-05:00\",\"ev\":\"start\",\"id\":\"{id}\",\"pred\":4,\"hsw\":{}.0,\"slept_min\":480,\"loc\":\"{loc}\",\"blocks_done\":{j},\"since_break_min\":0}}\n",
            start - 6
        ));
        s.push_str(&format!(
            "{{\"t\":\"{DAY}T{:02}:55:00-05:00\",\"ev\":\"done\",\"id\":\"{id}\",\"est_min\":60,\"actual_min\":55,\"went\":1,\"tags\":[],\"ci\":3}}\n",
            start
        ));
    }
    if let Some(rep) = case.report {
        s.push_str(&format!(
            "{{\"t\":\"{DAY}T{:02}:05:00-05:00\",\"ev\":\"energy\",\"pred\":4,\"rep\":{rep},\"hsw\":1.08,\"loc\":\"{loc}\"}}\n",
            arrive
        ));
    }
    // **The open interruption, logged as `tm interrupt` logs it** (owner
    // D64(b), README gap 3138): one line at its start, in the order the verbs
    // ran — before the running block's `start` when the interruption began
    // first (`tm start` does not end one), after it when it interrupted that
    // block and so names it.
    let intr = interruption(case, tz);
    let intr_line = intr.as_ref().map(|i| {
        LogEntry::new(i.at.fixed_offset(), Event::Interrupt { id: i.id.clone() })
            .to_json()
            .expect("an interrupt entry serialises")
            + "\n"
    });
    let over_the_block = intr.as_ref().is_some_and(|i| i.id.is_some());
    if !over_the_block {
        s.push_str(intr_line.as_deref().unwrap_or_default());
    }
    // The block that is running at `now`, as the log records it.
    if let Some((id, started)) = active_block(case, tz) {
        s.push_str(&format!(
            "{{\"t\":\"{DAY}T{:02}:{:02}:00-05:00\",\"ev\":\"start\",\"id\":\"{id}\",\"pred\":4,\"hsw\":4.0,\"slept_min\":480,\"loc\":\"{loc}\",\"blocks_done\":{done},\"since_break_min\":0}}\n",
            started.format("%H"),
            started.format("%M"),
        ));
        // **The meetings the block ran into, logged as the binary's housekeeping logs
        // them** (owner D61; W-37 repair, README gap 3340): a world whose running block
        // passed a wall's start with no `pause` logged is one the binary does not hold —
        // the first verb after the wall began writes it — so the generator writes it,
        // in file order, before the interruption that named the block (whose own verb's
        // housekeeping ran first).
        for (t, pause) in timer_marks(case, &arrival.walls, tz, typed).marks {
            let ev = if pause { Event::Pause { id: id.clone() } } else { Event::Unpause { id: id.clone() } };
            s.push_str(&(LogEntry::new(t.fixed_offset(), ev).to_json().expect("a timer entry serialises") + "\n"));
        }
    }
    if over_the_block {
        s.push_str(intr_line.as_deref().unwrap_or_default());
    }
    s
}

/// **What `tm arrive` logs and `.tm/state.json` holds of it** (owner D42/D45; W-37
/// repair, README gap 3340): the location, and the window and budget `tm arrive`
/// computes at the arrival over the day's walls — fork `capacity::window_and_budget`,
/// which is the binary's `Ctx::arrival_window` — so the log's `arrive` line and the
/// cache agree, as D42's rebuild demands. Until the repair the log said `[arrival,
/// arrival + 8h]` and the cache `[arrival, 16:00]` (a late day none), and the home
/// day's cache said `home` while its log said `lounge`: no generated world was one the
/// binary can build.
#[derive(Clone, Debug)]
pub struct Arrival {
    pub loc: &'static str,
    pub window: (NaiveTime, NaiveTime),
    pub budget: u32,
    /// Today's walls, read off the tree ([`walls_of_tree`]), which the window was
    /// computed over and the meetings are logged against.
    pub walls: Vec<(DateTime<Tz>, DateTime<Tz>)>,
}

pub fn arrival_of(case: &Case, tree: &Tree, cfg: &Config) -> Arrival {
    let walls = walls_of_tree(tree, cfg.tz);
    let at = case.arrival(cfg.tz);
    let (end, budget) = tm_core::capacity::window_and_budget(at, &walls, cfg);
    Arrival {
        loc: if case.home { "home" } else { "lounge" },
        window: (at.time(), end.time()),
        budget,
        walls,
    }
}

/// **Today's walls of a tree**, as the binary's `Ctx::walls_on` reads them: every
/// open Interval item overlapping the day, its start moved back by `buffer:`, sorted
/// by start.
pub fn walls_of_tree(tree: &Tree, tz: Tz) -> Vec<(DateTime<Tz>, DateTime<Tz>)> {
    let mut out = Vec::new();
    for item in tree.iter() {
        if item.state.is_closed() {
            continue;
        }
        let id = Tree::key_of(item);
        let tm_core::model::Shape::Interval { start, end } = tree.effective_shape(&id) else {
            continue;
        };
        let start = match item.buffer {
            Some(b) => start - Duration::minutes(i64::from(b.as_minutes())),
            None => start,
        };
        if start.date() > date() || end.date() < date() {
            continue;
        }
        out.push((local_dt(tz, start.date(), start.time()), local_dt(tz, end.date(), end.time())));
    }
    out.sort_by_key(|(a, _)| *a);
    out
}

/// The running block's timer marks a day's walls write, and what they leave.
#[derive(Clone, Debug, Default)]
pub struct TimerMarks {
    /// `(instant, is a pause)`, in the order the verbs wrote them.
    pub marks: Vec<(DateTime<Tz>, bool)>,
    /// Whether a typed pause longer than the first meeting was drawn.
    pub typed: bool,
    /// Whether the last mark is a pause (the block is paused at `now`).
    pub paused: bool,
}

/// **The marks D61's housekeeping writes over the running block** (the kernel's
/// `WallTimer.writes`, as the verbs a user runs through the day write them): for each
/// joined wall span that began after the block started and by `now`, a `pause` at its
/// start, and an `unpause` at its end once it has ended — unless the block's timer was
/// already stopped when the span began (an open interruption from its start, the
/// running block's own or one it was started inside), and with no `unpause` when an
/// interruption began inside the span (its mark, not the wall's pause, is then the last
/// word on the timer). With `typed`, the first such span that leaves ten minutes on
/// either side inside `(started, now)` is covered instead by a TYPED pause from ten
/// minutes before it to ten minutes after it (`tm pause` twice), and the walls it
/// covers write nothing (the timer was stopped when they began).
pub fn timer_marks(case: &Case, walls: &[(DateTime<Tz>, DateTime<Tz>)], tz: Tz, typed: bool) -> TimerMarks {
    let mut out = TimerMarks::default();
    let Some((_, started)) = active_block(case, tz) else { return out };
    let now = case.now(tz);
    let stop_from = interruption(case, tz).map(|i| i.at.max(started));
    let mut spans = walls.to_vec();
    spans.sort();
    let mut merged: Vec<(DateTime<Tz>, DateTime<Tz>)> = Vec::new();
    for (lo, hi) in spans {
        match merged.last_mut() {
            Some(m) if lo <= m.1 => m.1 = m.1.max(hi),
            _ => merged.push((lo, hi)),
        }
    }
    let ten = Duration::minutes(10);
    let mut typed_until: Option<DateTime<Tz>> = None;
    for (lo, hi) in merged.into_iter().filter(|(lo, _)| *lo > started && *lo <= now) {
        if stop_from.is_some_and(|s| lo >= s) || typed_until.is_some_and(|u| lo <= u) {
            continue;
        }
        if typed && !out.typed && lo - ten > started && hi + ten < now
            && stop_from.is_none_or(|s| hi + ten < s)
            && out.marks.last().is_none_or(|m| lo - ten > m.0)
        {
            out.marks.push((lo - ten, true));
            out.marks.push((hi + ten, false));
            typed_until = Some(hi + ten);
            out.typed = true;
            continue;
        }
        out.marks.push((lo, true));
        if hi <= now && stop_from.is_none_or(|s| hi <= s) {
            out.marks.push((hi, false));
        }
    }
    out.paused = out.marks.last().is_some_and(|m| m.1);
    out
}

/// **The open interruption a case draws, as `tm interrupt` leaves it** (owner
/// D64(b), README gap 3138): when it began, and the block it interrupted.
#[derive(Clone, Debug, PartialEq)]
pub struct Interruption {
    /// Its start — `ago` minutes before `now`, and never before the arrival or
    /// inside a block the log closes (see [`interruption`]).
    pub at: DateTime<Tz>,
    /// The block that was running when it began, which `tm interrupt` records
    /// (`Event::Interrupt { id }`, `state.interrupt.id`) and pauses.
    pub id: Option<String>,
}

/// **When a case's interruption began, and what it interrupted** — the one
/// reading [`log_text`] and [`build`] share, so the log and `.tm/state.json`
/// cannot disagree about it (D42's reconcile compares them and the log wins).
///
/// It starts no earlier than a minute after the last `done` the log holds — the
/// bound [`active_block`] gives the running block — because `tm interrupt`
/// during a block and `tm done` after it would leave a `done` whose
/// `actual_min` nets the interruption out, and the generator writes 55 for
/// every closed block. `started < at` decides whether the running block was
/// running when it began: `tm interrupt` then names it and pauses it, and
/// otherwise `tm start` ran during the interruption, which neither ends it nor
/// pauses the new block.
pub fn interruption(case: &Case, tz: Tz) -> Option<Interruption> {
    let ago = case.interrupt?;
    let after_done = case.arrival(tz) + Duration::minutes(i64::from(case.done(tz)) * 60 - 4);
    let at = (case.now(tz) - Duration::minutes(i64::from(ago)))
        .max(case.arrival(tz))
        .max(after_done);
    let id = active_block(case, tz)
        .filter(|(_, started)| *started < at)
        .map(|(id, _)| id);
    Some(Interruption { at, id })
}

/// The running block's item and start instant, when the case has one and it
/// fits after everything the log already holds.
pub fn active_block(case: &Case, tz: Tz) -> Option<(String, DateTime<Tz>)> {
    let (idx, ago, _) = case.active?;
    let now = case.now(tz);
    let last_done =
        case.arrival(tz) + Duration::minutes(i64::from(case.done(tz)) * 60 - 5);
    let started = (now - Duration::minutes(i64::from(ago))).max(last_done + Duration::minutes(1));
    if started >= now {
        return None;
    }
    Some((id_of('z', idx.min(case.items.len() - 1)), started))
}

pub struct World {
    pub tree: Tree,
    pub cfg: Config,
    pub replay: Replay,
    pub model: Model,
    pub now: DateTime<Tz>,
    pub state: RuntimeState,
    /// **The generated log, kept as bytes** (stage 6 W-28, step R2's response
    /// half): `Planner.PlanReq.run` is this call's own replay through D24's
    /// seam, so the kernel is handed the same lines the fork's `Replay` was
    /// built from and resumes them itself.
    pub log: String,
    /// **The four generated files, kept as bytes** (stage 6 W-25, step R2).
    /// `Tree::from_texts` consumes them and hands back the fork's reading; the
    /// kernel is given the same bytes and does its own, which is the whole
    /// point of [`the_kernel_reads_every_day_the_fork_planned`].
    pub docs: Vec<(String, String)>,
}

pub fn build(case: &Case) -> World {
    build_with(case, Config::default(), false)
}

/// [`build`] under a given configuration, and with the P56 arm's typed pause
/// ([`timer_marks`]) when `typed`.
pub fn build_with(case: &Case, cfg: Config, typed: bool) -> World {
    let tz = cfg.tz;
    let week = week_text(case);
    let cal = calendar_text(case);
    let routines = routines_text(case);
    let optionals = if case.optionals { OPTIONALS } else { "" };
    let files = [
        ("week/2026-W37.md", week.as_str()),
        ("calendar/2026-W37.md", cal.as_str()),
        ("routines.md", routines.as_str()),
        ("optional.md", optionals),
    ];
    let tree = Tree::from_texts(&files, &cfg);
    let docs = files.iter().map(|(p, t)| ((*p).to_string(), (*t).to_string())).collect();
    let arrival = arrival_of(case, &tree, &cfg);
    let log = log_text(case, &cfg, &arrival, typed);
    let replay = chokepoint::replay_of_text(&log, tz);
    let now = case.now(tz);
    let intr = interruption(case, tz);
    let marks = timer_marks(case, &arrival.walls, tz, typed);
    let state = RuntimeState {
        date: Some(date()),
        wake: Some(case.wake_time()),
        arrival: Some(arrival.window.0),
        loc: Some(arrival.loc.to_string()),
        // What `tm arrive` stored — the same window and budget its `arrive` line
        // carries (D42); on a late day the evening wall pushes the end past midnight.
        window: Some(arrival.window),
        budget: Some(arrival.budget),
        active: case.active.and_then(|(_, _, est)| {
            active_block(case, tz).map(|(id, started)| ActiveBlock {
                id: Id::new(id),
                started: started.naive_local().time(),
                est_min: est,
                // `tm interrupt` pauses the block it interrupts (D64(b)), and since
                // W-38 `tm start` inside an open interruption writes the block paused
                // (D69, parity P60, README gap 3283) -- so an OPEN interruption pauses
                // the running block whether it names it or not (README gap 3478); a
                // meeting whose pause is the last word on the timer holds it paused (D61).
                paused: intr.is_some() || marks.paused,
            })
        }),
        interrupt: intr.as_ref().map(|i| InterruptState {
            started: Some(i.at.naive_local().time()),
            id: i.id.as_deref().map(Id::new),
        }),
        ..RuntimeState::default()
    };
    World {
        tree,
        cfg,
        log,
        replay,
        model: Model::default(),
        now,
        state,
        docs,
    }
}

impl World {
    /// The generated files as the wire carries them.
    pub fn docs_json(&self) -> Vec<Value> {
        self.docs
            .iter()
            .map(|(path, text)| json!({"path": path, "lines": text.lines().collect::<Vec<_>>()}))
            .collect()
    }
    pub fn candidates(&self) -> Vec<Candidate> {
        priority::collect_candidates(
            &self.tree,
            &self.replay,
            &self.cfg,
            &self.model,
            date(),
            self.now,
        )
    }
}

/// **The arms' widenings of the shared generator** — one definition each, called
/// by the arm that draws it and by `forkclass::class_draws`, which applies one
/// arm's widenings per draw exactly as that arm does (W-37 track H; until then
/// the class draw re-spelled them in a scratch harness, README gap 3080).
impl World {
    /// **The hash arm's learned multiplier** (`the_kernel_hashes_the_day_the_fork_hashes`):
    /// the `_default` duration multiplier of the model both planners read.
    pub fn set_multiplier(&mut self, mult: Option<f64>) {
        if let Some(m) = mult {
            self.model.duration.insert(tm_core::energy::DEFAULT_TAG.to_string(), m);
        }
    }

    /// **A break in today's log** (the hash arm's, W-34, README gap 2511): `log_text`
    /// writes none, so the fork's `rest_debt_min` was 0 on every generated day. Planned
    /// `planned` minutes and taken `actual`, right after the last `done` (or ten minutes
    /// after arrival), and only on a day with no running block and no interruption: a
    /// break inside either is §9's pause, a different event. Both sides replay the same
    /// bytes — the log and the replay are rebuilt together. Whether one was written.
    pub fn log_a_break(&mut self, case: &Case, brk: Option<(u32, u32)>) -> bool {
        let tz = self.cfg.tz;
        let (Some((planned, actual)), None, None) = (brk, case.active, case.interrupt) else {
            return false;
        };
        let t = if case.done(tz) > 0 {
            case.arrival(tz) + Duration::minutes(i64::from(case.done(tz)) * 60 - 5)
        } else {
            case.arrival(tz) + Duration::minutes(10)
        };
        if t + Duration::minutes(i64::from(actual)) >= self.now {
            return false;
        }
        let line = format!(
            "{{\"t\":\"{}\",\"ev\":\"break\",\"planned_min\":{planned},\"actual_min\":{actual}}}",
            t.to_rfc3339()
        );
        self.log = format!("{}{line}\n", self.log);
        self.replay = chokepoint::replay_of_text(&self.log, tz);
        true
    }

    /// **A running break** (the W-35 arm's, parity P45): drawn `ago` minutes before `now`
    /// for `planned` minutes at `place`, on a day with no interruption, pausing a running
    /// block as `tm break` does (`tm/src/cli/day.rs`' `take_break`). `.tm/state.json`
    /// alone holds it: a break is logged when it ENDS.
    ///
    /// **It starts no earlier than a minute after the last `start` or `done` the log
    /// holds** (W-37, owner D64(b)): `tm start`, `tm done` and `tm stop` each END a
    /// running break (`day.rs`' `end_break`), so a break still running at `now` began
    /// after the last of them. Two frozen class worlds (`break-block/lounge`, a break at
    /// 09:40 under a block started 09:56, and `break-block/late`, 10:53 under 10:56) had
    /// it before, which the shipped binary cannot hold. The break's start, when drawn.
    pub fn run_a_break(&mut self, case: &Case, brk: Option<(u32, u32, &str)>) -> Option<DateTime<Tz>> {
        let tz = self.cfg.tz;
        let (Some((ago, planned, place)), None) = (brk, case.interrupt) else {
            return None;
        };
        let last_done = (case.done(tz) > 0)
            .then(|| case.arrival(tz) + Duration::minutes(i64::from(case.done(tz)) * 60 - 5));
        let started = active_block(case, tz).map(|(_, s)| s);
        // ... and after the last timer mark the log holds (W-37 repair, README gap 3340):
        // a meeting's `pause`/`unpause` is written by the verbs of the day, and a break
        // taken before one would have stopped the timer, so the wall would have written
        // nothing — the world the generator logged is the one with no break before it.
        let last_mark = self
            .log
            .lines()
            .filter(|l| l.contains("\"ev\":\"pause\"") || l.contains("\"ev\":\"unpause\""))
            .filter_map(|l| serde_json::from_str::<Value>(l).ok())
            .filter_map(|v| v["t"].as_str().and_then(|t| DateTime::parse_from_rfc3339(t).ok()))
            .map(|t| t.with_timezone(&tz))
            .max();
        let floor = last_done.into_iter().chain(started).chain(last_mark).max().map(|t| t + Duration::minutes(1));
        let t = floor.map_or(self.now - Duration::minutes(i64::from(ago)), |f| {
            (self.now - Duration::minutes(i64::from(ago))).max(f)
        });
        if t.date_naive() != date() || t > self.now {
            return None;
        }
        self.state.break_ = Some(BreakState {
            started: Some(t.time()),
            planned_min: planned,
            place: Some(place.to_string()),
        });
        if let Some(a) = self.state.active.as_mut() {
            a.paused = true;
        }
        Some(t)
    }

    /// **Today's walls, read off the tree** ([`walls_of_tree`]).
    pub fn walls_today(&self) -> Vec<(DateTime<Tz>, DateTime<Tz>)> {
        walls_of_tree(&self.tree, self.cfg.tz)
    }

    /// **Overtime, drawn and not only met** (the W-35 arm's, W-35 land step, README gap
    /// 2910): the shared generator reaches an overtime day on 1-5 of ~280 cases, so half of
    /// the no-break days (`brk_drawn` false) lower the running block's estimate to the
    /// minutes it has run — a day the generator can already draw, drawn more often.
    pub fn force_overtime(&mut self, case: &Case, over: bool, brk_drawn: bool) {
        if let (true, false, Some((_, ran, _))) = (over, brk_drawn, case.active) {
            if let Some(a) = self.state.active.as_mut() {
                a.est_min = a.est_min.min(ran.max(1));
            }
        }
    }
}

/// The configured `budget_ratio` under which §8.1's `budget_blocks` is `done`
/// (README gap 3340): `done × block_min / (window_hours × 60)`.
pub fn spent_ratio(done: u32, cfg: &Config) -> f64 {
    f64::from(done) * f64::from(cfg.block_min()) / (cfg.day.window_hours * 60.0)
}

/// **The two note kinds the generator never draws, drawn here** (a WIDENING of
/// what this arm sees, D46; the shared generator is untouched). Measured on
/// this block's first run: 91 notes compared on 81 of 273 days, EVERY ONE a
/// `noPosition` — the generator writes no `travel-day` wall, and its budget of
/// 6 is never spent by its at most 3 done blocks, so `travelDay` and
/// `budgetSpent` were compared on no day at all. `travel` flags the first
/// calendar wall `travel-day` (fork `Item::is_travel_day`, the kernel's
/// `travelDay`), which zeroes the day's budget; `spent` stores a budget equal
/// to the blocks already done on a day that has done some. Both sides read the
/// changed world: the kernel through `docs` and `state.budget`, the fork
/// through the tree rebuilt from the same bytes and the same `state`.
pub fn widen_for_notes(w: &mut World, case: &Case, travel: bool, spent: bool) -> (bool, bool) {
    let tz = w.cfg.tz;
    let mut did = (false, false);
    if travel {
        if let Some((_, text)) = w.docs.iter_mut().find(|(p, _)| p == "calendar/2026-W37.md") {
            if let Some(first) = text.lines().next().map(str::to_string) {
                if !first.is_empty() {
                    *text = text.replacen(&first, &format!("{first} travel-day"), 1);
                    did.0 = true;
                }
            }
        }
    }
    // **A spent budget, as the binary can hold one** (W-37 repair, README gap 3340): the
    // budget is `tm arrive`'s (§8.1's `budget_blocks`, from the configuration), so a day
    // whose budget its done blocks have spent is a day whose configured `budget_ratio`
    // makes the budget exactly the blocks done — here `done / 8` at the default eight
    // hours and one-hour blocks. Until the repair `.tm/state.json` alone said `budget:
    // done` while the log's `arrive` said 6, which D42's rebuild undoes.
    if spent && !case.late {
        let done = case.done(tz);
        if done > 0 {
            let mut cfg = w.cfg.clone();
            cfg.day.budget_ratio = spent_ratio(done, &cfg);
            let widened_travel = did.0;
            let docs = w.docs.clone();
            *w = build_with(case, cfg, false);
            if widened_travel {
                w.docs = docs;
                let files: Vec<(&str, &str)> = w.docs.iter().map(|(p, t)| (p.as_str(), t.as_str())).collect();
                w.tree = Tree::from_texts(&files, &w.cfg);
            }
            did.1 = w.state.budget == Some(done);
        }
    }
    if did.0 {
        let files: Vec<(&str, &str)> =
            w.docs.iter().map(|(p, t)| (p.as_str(), t.as_str())).collect();
        w.tree = Tree::from_texts(&files, &w.cfg);
    }
    did
}
