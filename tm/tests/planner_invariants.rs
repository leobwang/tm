//! §8.3's invariants as `proptest` properties over random trees, random logs
//! and a random `now` — "tests first for §8.3 invariants: they are the
//! specification" (§17.2).
//!
//! Each case builds a week file of up to 40 items with random `ci`, `!k`,
//! estimate, deadline, dependency, `loc:` and `atomic`, a random subset of the
//! §4.3 routines (windows, a `pref:` anchor, sleep), optionally the two
//! `optional.md` lines, up to two calendar walls, a log with a random number of
//! finished blocks and an optional energy report, and plans at a random instant
//! inside the window. A case may also be **running a block**
//! (`state.active` + the matching `start` in the log), **interrupted**
//! (`state.interrupt`), or a **late day** whose §8.1 window is pushed past the
//! 21:30 wind-down by a six-hour evening wall. Then every invariant of §8.3 is
//! checked:
//!
//! * **purity** — the same input twice gives an identical `DayPlan`;
//! * **stability** — a replan an hour later changes no segment that had ended,
//!   except the ones that had not *finished* ([`SegFlags::open`]: the running
//!   interruption and the running block, which grow rather than move);
//! * **no overbooking** — Σ planned Block minutes ≤ `remaining_budget ×
//!   block_min` (the running block excepted: §9 gives it its minutes whatever
//!   the budget says), no segment overlaps a Wall, nothing is planned after
//!   wind-down, and no two placements overlap;
//! * **energy filter** — every Block the planner *assigned* has `item.ci ≤
//!   slot.energy`, and the one block it did not assign — the one already
//!   running — takes no slot at all;
//! * **monotone rank** — equal `p` and equal `ci`: the lower line order is
//!   never left unassigned while the other is assigned;
//! * **tail-drop** — taking a block off the budget removes a tail and
//!   re-shuffles nothing;
//! * **HOT before queue**, **IMPOSSIBLE never dropped**, **walls never
//!   moved** (exactly where the calendar says, to the minute);
//! * and §8.2 step 8's **diagnostics**, which have to agree with the timeline
//!   they describe.
//!
//! Where a property needs a fair comparison it is restricted to the
//! candidates the rule is written about — a `loc:`-constrained, `atomic` or
//! `max:`-capped item is skipped by §8.2 step 5 for reasons the invariant is
//! not about, and the Active item is excepted by §8.3 itself.

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

/// **The `plan` section's wire**, shared with `tm/tests/kernel_row_cells.rs`
/// since stage 6 W-25 (step R2): one encoder, two callers (AGENTS §5.3).
#[allow(dead_code)]
#[path = "support/rowwire.rs"]
mod rowwire;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;

use chrono::{DateTime, Duration, NaiveDate, NaiveTime, Timelike};
use chrono_tz::Tz;
use proptest::prelude::*;
use serde_json::{json, Value};
use tm_core::capacity::{self, local_dt, Exact, CAP_DEN};
use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::Replay;
use tm_core::model::{Id, Loc, Shape, WindowRange};
use tm_core::planner::{self, DayPlan, PlanInput, SegKind, Segment};
use tm_core::priority::{self, Candidate, Prio, PrioClass};
use tm_core::store::{ActiveBlock, InterruptState, RuntimeState};
use tm_core::tree::Tree;

const DAY: &str = "2026-09-07";
const MAX_ITEMS: usize = 40;

/// The five §4.3 routines a case may switch on, and the evening wall the late
/// day carries.
const ROUTINES: [&str; 5] = [
    "- lunch      win:11:30-13:30 dur:30m  every:day",
    "- workout    win:16:00-19:00 dur:1h   every:Mon,Wed,Fri",
    "- shower     win:07:00-23:00 dur:20m  after-done:2d~1d",
    "- breakfast  win:06:00-09:00 dur:30m  every:day pref:wake+10m",
    "- sleep      win:22:00-08:00 dur:8h30m every:day ci:0",
];
const OPTIONALS: &str = "- Watch something  dur:1h\n- Play something   dur:2h max:4h/w\n";
const EVENING_WALL: &str = "- [ ] 3 Long evening at:2026-09-07T15:00/21:00 ^wev\n";

fn date() -> NaiveDate {
    NaiveDate::parse_from_str(DAY, "%Y-%m-%d").expect("date")
}

fn at(tz: Tz, h: u32, m: u32) -> DateTime<Tz> {
    local_dt(tz, date(), NaiveTime::from_hms_opt(h, m, 0).expect("time"))
}

/// One generated item line.
#[derive(Debug, Clone)]
struct Spec {
    ci: u8,
    k: u8,
    est_b: u32,
    /// A `≤ batch_max_min` estimate instead of `est_b` blocks (§7.5).
    small: Option<u32>,
    due_in: Option<u8>,
    dep: Option<usize>,
    loc_home: bool,
    atomic: bool,
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
    parent: Option<usize>,
}

/// One generated wall.
#[derive(Debug, Clone)]
struct WallSpec {
    hour: u32,
    hours: u32,
}

/// Everything one case varies.
#[derive(Debug, Clone)]
struct Case {
    items: Vec<Spec>,
    walls: Vec<WallSpec>,
    now_idx: usize,
    done_blocks: u32,
    report: Option<u8>,
    /// Bit i switches [`ROUTINES`]`[i]` on.
    routines: u8,
    optionals: bool,
    /// The day is spent at home: §8.2 step 3's `home_max_ci` caps every slot.
    home: bool,
    /// `(item index, minutes running so far, est_min)` — `state.active`.
    active: Option<(usize, u32, u32)>,
    /// Minutes ago the open interruption started.
    interrupt: Option<u32>,
    /// A late arrival plus the evening wall: §8.1 pushes the window past the
    /// wind-down.
    late: bool,
}

impl Case {
    /// The hour `tm arrive` was logged at.
    fn arrival_hour(&self) -> u32 {
        if self.late {
            11
        } else {
            7
        }
    }
    fn wake_time(&self) -> NaiveTime {
        NaiveTime::from_hms_opt(if self.late { 9 } else { 6 }, 30, 0).expect("time")
    }
    /// `now` — arrival, +1h30, +3h or +5h.
    fn now(&self, tz: Tz) -> DateTime<Tz> {
        let base = at(tz, self.arrival_hour(), 0);
        base + Duration::minutes(match self.now_idx {
            0 => 0,
            1 => 90,
            2 => 180,
            _ => 300,
        })
    }
    /// The instant `tm arrive` was logged at.
    fn arrival(&self, tz: Tz) -> DateTime<Tz> {
        at(tz, self.arrival_hour(), 0)
    }
    /// The blocks the log may hold: one an hour since arrival.
    fn done(&self, tz: Tz) -> u32 {
        let room = ((self.now(tz) - self.arrival(tz)).num_minutes() / 60).max(0) as u32;
        self.done_blocks.min(room).min(self.items.len() as u32)
    }
}

fn spec_strategy() -> impl Strategy<Value = Spec> {
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
    )
        .prop_map(|(ci, k, est_b, small, due_in, dep, loc_home, atomic, parent)| Spec {
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
        })
}

fn case_strategy() -> impl Strategy<Value = Case> {
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
fn id_of(prefix: char, i: usize) -> String {
    let a = (b'a' + (i / 26) as u8) as char;
    let b = (b'a' + (i % 26) as u8) as char;
    format!("{prefix}{a}{b}")
}

fn week_text(case: &Case) -> String {
    let mut s = String::from("---\nweek: 2026-W37\n---\n# Milestones\n");
    for (i, sp) in case.items.iter().enumerate() {
        let id = id_of('z', i);
        let est = match sp.small {
            Some(m) => format!("{m}m"),
            None => format!("{}b", sp.est_b),
        };
        let mut line = format!("- [ ] {} {est} Item{i} !{}", sp.ci, sp.k);
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
        line.push_str(&format!(" ^{id}\n"));
        s.push_str(&line);
    }
    s
}

fn calendar_text(case: &Case) -> String {
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

fn routines_text(case: &Case) -> String {
    let mut s = String::new();
    for (i, line) in ROUTINES.iter().enumerate() {
        if case.routines & (1 << i) != 0 {
            s.push_str(line);
            s.push('\n');
        }
    }
    s
}

fn log_text(case: &Case, tz: Tz) -> String {
    let arrive = case.arrival_hour();
    let done = case.done(tz);
    let wake = case.wake_time();
    let mut s = format!(
        "{{\"t\":\"{DAY}T{:02}:{:02}:00-05:00\",\"ev\":\"wake\",\"slept_min\":480}}\n\
         {{\"t\":\"{DAY}T{arrive:02}:00:00-05:00\",\"ev\":\"arrive\",\"loc\":\"lounge\",\
         \"window\":[\"{arrive:02}:00\",\"{:02}:00\"],\"budget\":6}}\n",
        wake.format("%H").to_string().parse::<u32>().unwrap_or(6),
        wake.format("%M").to_string().parse::<u32>().unwrap_or(0),
        (arrive + 8).min(23),
    );
    for j in 0..done {
        let id = id_of('z', j as usize);
        let start = arrive + j;
        s.push_str(&format!(
            "{{\"t\":\"{DAY}T{start:02}:00:00-05:00\",\"ev\":\"start\",\"id\":\"{id}\",\"pred\":4,\"hsw\":{}.0,\"slept_min\":480,\"loc\":\"lounge\",\"blocks_done\":{j},\"since_break_min\":0}}\n",
            start - 6
        ));
        s.push_str(&format!(
            "{{\"t\":\"{DAY}T{:02}:55:00-05:00\",\"ev\":\"done\",\"id\":\"{id}\",\"est_min\":60,\"actual_min\":55,\"went\":1,\"tags\":[],\"ci\":3}}\n",
            start
        ));
    }
    if let Some(rep) = case.report {
        s.push_str(&format!(
            "{{\"t\":\"{DAY}T{:02}:05:00-05:00\",\"ev\":\"energy\",\"pred\":4,\"rep\":{rep},\"hsw\":1.08,\"loc\":\"lounge\"}}\n",
            arrive
        ));
    }
    // The block that is running at `now`, as the log records it.
    if let Some((id, started)) = active_block(case, tz) {
        s.push_str(&format!(
            "{{\"t\":\"{DAY}T{:02}:{:02}:00-05:00\",\"ev\":\"start\",\"id\":\"{id}\",\"pred\":4,\"hsw\":4.0,\"slept_min\":480,\"loc\":\"lounge\",\"blocks_done\":{done},\"since_break_min\":0}}\n",
            started.format("%H"),
            started.format("%M"),
        ));
    }
    s
}

/// The running block's item and start instant, when the case has one and it
/// fits after everything the log already holds.
fn active_block(case: &Case, tz: Tz) -> Option<(String, DateTime<Tz>)> {
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

struct World {
    tree: Tree,
    cfg: Config,
    replay: Replay,
    model: Model,
    now: DateTime<Tz>,
    state: RuntimeState,
    /// **The generated log, kept as bytes** (stage 6 W-28, step R2's response
    /// half): `Planner.PlanReq.run` is this call's own replay through D24's
    /// seam, so the kernel is handed the same lines the fork's `Replay` was
    /// built from and resumes them itself.
    log: String,
    /// **The four generated files, kept as bytes** (stage 6 W-25, step R2).
    /// `Tree::from_texts` consumes them and hands back the fork's reading; the
    /// kernel is given the same bytes and does its own, which is the whole
    /// point of [`the_kernel_reads_every_day_the_fork_planned`].
    docs: Vec<(String, String)>,
}

fn build(case: &Case) -> World {
    let cfg = Config::default();
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
    let log = log_text(case, tz);
    let replay = chokepoint::replay_of_text(&log, tz);
    let now = case.now(tz);
    let arrival = NaiveTime::from_hms_opt(case.arrival_hour(), 0, 0).expect("time");
    let state = RuntimeState {
        date: Some(date()),
        wake: Some(case.wake_time()),
        arrival: Some(arrival),
        loc: Some(if case.home { "home" } else { "lounge" }.to_string()),
        // A late day stores no window, so §8.1's formula runs and the evening
        // wall pushes the end past midnight.
        window: (!case.late).then(|| {
            (
                arrival,
                NaiveTime::from_hms_opt(16, 0, 0).expect("time"),
            )
        }),
        budget: (!case.late).then_some(6),
        active: case.active.and_then(|(_, _, est)| {
            active_block(case, tz).map(|(id, started)| ActiveBlock {
                id: Id::new(id),
                started: started.naive_local().time(),
                est_min: est,
                paused: false,
            })
        }),
        interrupt: case.interrupt.map(|ago| InterruptState {
            started: Some(
                (now - Duration::minutes(i64::from(ago)))
                    .max(case.arrival(tz))
                    .naive_local()
                    .time(),
            ),
            id: None,
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
    fn input<'a>(&'a self, state: &'a RuntimeState, now: DateTime<Tz>) -> PlanInput<'a> {
        PlanInput::new(
            &self.tree,
            &self.replay,
            &self.cfg,
            &self.model,
            state,
            now,
        )
    }
    /// The generated files as the wire carries them.
    fn docs_json(&self) -> Vec<Value> {
        self.docs
            .iter()
            .map(|(path, text)| json!({"path": path, "lines": text.lines().collect::<Vec<_>>()}))
            .collect()
    }
    fn candidates(&self) -> Vec<Candidate> {
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

/// The candidates §8.3's comparisons are written about: plain, splittable,
/// uncapped work with no location constraint and no placement window.
fn comparable(c: &Candidate) -> bool {
    c.eligible()
        && !c.is_wall
        && !c.is_optional
        && c.window.is_none()
        && c.splittable
        && c.cap.is_none()
        && c.loc == Loc::Any
        && c.remaining_min > 0
}

/// The items the plan *proposes* — the blocks the log already holds are not
/// the planner's doing and never count as "assigned" for §8.3.
fn assigned_set(day: &DayPlan, from: DateTime<Tz>) -> BTreeSet<Id> {
    day.assigned_from(from).into_iter().collect()
}

/// The slot layout, as `(start, items)` — what the tail-drop invariant
/// compares.
fn layout(day: &DayPlan) -> Vec<(DateTime<Tz>, Vec<Id>)> {
    day.segments
        .iter()
        .filter(|s| s.kind.is_work())
        .map(|s| (s.start, s.items()))
        .collect()
}

/// **The cells the kernel is allowed to disagree with the fork about on a
/// GENERATED day, with the gap that records why.**
///
/// The same two holes `tm/tests/kernel_row_cells.rs` declares on its fixture
/// day, and no others — a third name appearing here would be a finding, not a
/// widening:
///
/// * **`note`** (gap **1102**, and the `note: null` decision in `seg_json`) —
///   `SegFlags::note` is a `String` the fork's planner wrote as prose and
///   `Planner.Note` is eleven names with their arguments, so a host whose
///   planner produced text has nothing to send. The kernel **derives** the
///   column and cannot derive the `⚠` branch, which needs the fork's
///   `effective_due`.
/// * **`est`** (gap **1101**) — the fork's `est_cell` reads `est_original`
///   first and this kernel has one estimate view, `Core.est`, which is `est:`
///   then the leading estimate. A line carrying both makes the two readers pick
///   different numbers.
///
/// Every other cell — `time`, `ci`, `p`, `mark`, `title`, `parent`, `actual`
/// and `batchNames` — is compared **exactly**, on every row of every case.
///
/// **And `parent` is now compared at a value** (W-27). It was in this list
/// before, and the list was true and empty of content for that one cell: the
/// generated corpus had no `@` token, so both readers wrote `""` on every row
/// and the cell asserted nothing. [`CENSUS`]'s fifth counter and the
/// `parents > 0` assertion are what make the membership load-bearing.
const CELL_HOLES: [&str; 2] = ["note", "est"];

/// `(rows compared, cases compared, note-hole firings, est-hole firings,
/// rows whose `parent` cell was NON-EMPTY)` — what
/// [`the_kernel_reads_every_day_the_fork_planned`] actually looked at.
///
/// **The fifth number is W-27's** and it is the one that makes the `parent`
/// comparison mean something. Until this run the generated corpus carried no
/// `@` token, so every row's `parent` cell was `""` on both sides and the
/// comparison could not fail whatever the kernel wrote; the arm is now asserted
/// to have seen the cell at a real value.
///
/// A proptest case body returns only a verdict, so the census is a side
/// channel — but it is read **inside the arm that fills it**, on every case,
/// and not by a separate `#[test]`. A separate test would race the arm in
/// cargo's default parallel run and pass by seeing nothing, which is the very
/// defect it exists to catch: "every cell of every row agreed" is a sentence a
/// fuzz comparing **no** rows also produces — AGENTS §9.2's "a check no input
/// can fail", which this campaign has met at five different levels.
static CENSUS: Mutex<[u64; 5]> = Mutex::new([0; 5]);

fn overlaps(a: &Segment, b: &Segment) -> bool {
    a.start < b.end && b.start < a.end
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 256, max_shrink_iters: 2_000, ..ProptestConfig::default() })]

    #[test]
    fn day_plan_satisfies_every_invariant(case in case_strategy()) {
        let w = build(&case);
        let tz = w.cfg.tz;
        let block_min = w.cfg.block_min();
        let day = planner::plan(&w.input(&w.state, w.now));

        // --- purity (§8.3, §17.2) ---------------------------------------
        prop_assert_eq!(&day, &planner::plan(&w.input(&w.state, w.now)));
        prop_assert_eq!(day.hash(), planner::plan(&w.input(&w.state, w.now)).hash());

        // --- the running block (§9) --------------------------------------
        // It is a fact, not a placement: exactly one `▶`, it belongs to
        // `state.active`, it starts at `now`, and it holds no slot.
        let current = day.current_segment();
        prop_assert!(
            day.segments.iter().filter(|s| s.flags.current).count() <= 1,
            "two blocks are running at once"
        );
        if let Some(seg) = current {
            let active = w.state.active.as_ref().expect("a `▶` needs `state.active`");
            prop_assert_eq!(seg.item.as_ref(), Some(&active.id));
            prop_assert!(seg.energy.is_none(), "the running block takes no slot: {:?}", seg);
            // Either the minutes it still needs (from `now`) or — in
            // overtime, when there is nothing left to reserve — the stretch it
            // has already run (up to `now`).
            prop_assert!(seg.start <= w.now && seg.end >= w.now, "{seg:?}");
        }
        let running_min = current.filter(|s| s.start >= w.now).map_or(0, Segment::minutes);

        // --- no overbooking ---------------------------------------------
        // §9 gives the running block its minutes whatever the budget says
        // (that is the state §9.1's overtime prompt runs in); everything the
        // planner *chose* fits the remaining budget.
        let remaining = capacity::remaining_budget(
            w.state.budget.unwrap_or(6),
            w.replay.blocks_done(date()),
        );
        prop_assert!(
            day.planned_block_minutes(w.now) - running_min <= remaining * block_min,
            "{} planned minutes ({running_min} of them running) for {remaining} blocks\n{day:?}",
            day.planned_block_minutes(w.now)
        );

        // No segment overlaps a Wall, and no two placements overlap.
        let placed: Vec<&Segment> = day
            .segments
            .iter()
            .filter(|s| {
                s.start >= w.now
                    && !matches!(s.kind, SegKind::Lost | SegKind::WindDown | SegKind::Sleep)
            })
            .collect();
        for (i, a) in placed.iter().enumerate() {
            for b in placed.iter().skip(i + 1) {
                if a.kind == SegKind::Wall && b.kind == SegKind::Wall {
                    // §8.2 step 1: overlapping walls are reported, not
                    // resolved — and nothing else is placed in the overlap,
                    // which the other pairs of this loop check.
                    if overlaps(a, b) && a.item != b.item {
                        let (x, y) = (
                            a.item.clone().expect("a wall names its item"),
                            b.item.clone().expect("a wall names its item"),
                        );
                        prop_assert!(
                            day.diagnostics
                                .conflicts
                                .iter()
                                .any(|(p, q)| (*p == x && *q == y) || (*p == y && *q == x)),
                            "unreported wall conflict {x} × {y}"
                        );
                    }
                    continue;
                }
                prop_assert!(!overlaps(a, b), "overlap: {a:?} / {b:?}");
            }
        }

        // Nothing is planned after wind-down (the strong form of "no Block
        // with ci ≥ 4 after wind-down"). A late day's window reaches past it.
        let wind = at(tz, 21, 30);
        for seg in day.segments.iter().filter(|s| s.kind.is_work()) {
            prop_assert!(seg.end <= wind, "work after wind-down: {seg:?}");
        }
        if case.late {
            prop_assert!(day.window.1 > wind, "the late day runs past the wind-down");
        }

        // --- walls never moved -------------------------------------------
        // Exactly where the calendar says: a wall segment is either the event
        // itself or the `buffer:` in front of it, both clipped to the day.
        for seg in day.segments.iter().filter(|s| s.kind == SegKind::Wall) {
            let id = seg.item.clone().expect("a wall names its item");
            let Shape::Interval { start, end } = w.tree.effective_shape(&id) else {
                prop_assert!(false, "{id} is not an interval");
                unreachable!()
            };
            let buffer = w.tree.get(&id).and_then(|i| i.buffer).map_or(0, |d| d.as_minutes());
            let midnight = at(tz, 0, 0);
            let s = local_dt(tz, start.date(), start.time());
            let e = local_dt(tz, end.date(), end.time());
            let event = (s.max(midnight), e.min(midnight + Duration::days(1)));
            let front = (s - Duration::minutes(i64::from(buffer)), s);
            prop_assert!(
                (seg.start, seg.end) == event
                    || (buffer > 0 && (seg.start, seg.end) == (front.0.max(midnight), front.1)),
                "a wall moved: {seg:?} is neither {event:?} nor {front:?}"
            );
        }

        // --- energy filter ------------------------------------------------
        let cands = w.candidates();
        let ci_of = |id: &Id| cands.iter().find(|c| c.id == *id).map_or(0, |c| c.ci);
        for seg in day.segments.iter().filter(|s| s.kind.is_work() && s.start >= w.now) {
            if seg.flags.current {
                continue; // checked above: it is not in a slot at all
            }
            let energy = seg.energy.expect("a planned block has an energy");
            for id in seg.items() {
                prop_assert!(ci_of(&id) <= energy, "{id} ci {} in a slot of {energy}", ci_of(&id));
            }
        }

        // --- the priority-dependent invariants ----------------------------
        let prios: Vec<Prio> = day.priorities.iter().map(|(_, p)| p.clone()).collect();
        prop_assert_eq!(prios.len(), cands.len());
        let done = assigned_set(&day, w.now);
        let max_energy = day
            .segments
            .iter()
            .filter(|s| s.kind.is_work())
            .filter_map(|s| s.energy)
            .max()
            .unwrap_or(0);

        // Monotone rank: equal p and ci → the higher-ranked of the two is never
        // the one left out. The running item is excepted: §9 gave it its slot.
        //
        // **"Higher-ranked" is `(root_order, own_order)`, not `own_order`**
        // (stage 6 W-27). §7.4's key is `priority::sort_key = (p, root_order,
        // own_order)` — the item's ROOT first, its own line second — so a child
        // of an early root outranks an unrelated item written on an earlier
        // line. This loop compared `own_order` alone, which is the same
        // relation **exactly when every item is its own root**, and until this
        // run the generated corpus had no `@parent` token, so it always was.
        // With parents drawn the two relations part company and the fork was
        // failing an invariant the spec does not state: six runs of 256 cases
        // failed here and six of the pre-parent generator passed. The fork is
        // right; this line was wrong. Seed `80a3875…` in
        // `planner_invariants.proptest-regressions` is the one that found it
        // (D46: a new seed is a finding and it stays). README gap 1661.
        let active_id = w.state.active.as_ref().map(|a| a.id.clone());
        for (i, a) in cands.iter().enumerate() {
            if !comparable(a) || Some(&a.id) == active_id.as_ref() {
                continue;
            }
            for (j, b) in cands.iter().enumerate().skip(i + 1) {
                if !comparable(b) || a.ci != b.ci || prios[i].p != prios[j].p {
                    continue;
                }
                if Some(&b.id) == active_id.as_ref() {
                    continue;
                }
                let rank = |c: &Candidate| (c.root_order, c.own_order);
                let (first, second) = if rank(a) <= rank(b) { (a, b) } else { (b, a) };
                if done.contains(&second.id) {
                    prop_assert!(
                        done.contains(&first.id),
                        "{} (later line) is assigned while {} is not",
                        second.id,
                        first.id
                    );
                }
            }
        }

        // HOT before queue, slot by slot: wherever a `p > 0` candidate got a
        // block, no `p = 0` candidate that the day left out could have taken
        // that same slot. (The `max_energy` form of this — "a HOT item that
        // fits *some* slot is never left out" — is nearly unfalsifiable,
        // because `max_energy` is measured over the slots that were filled.)
        // §7.5: a batch is won by its leader, and the small items sharing the
        // block ride along whatever their own key says. Those passengers never
        // "took" a slot from anyone.
        let carried = |id: &Id| -> bool {
            day.segments
                .iter()
                .filter(|s| s.kind.is_work() && s.items().contains(id))
                .any(|s| {
                    s.items().iter().any(|other| {
                        other != id
                            && cands
                                .iter()
                                .position(|c| c.id == *other)
                                .is_some_and(|j| prios[j].p == 0)
                    })
                })
        };
        let hot_left_out: Vec<&Candidate> = cands
            .iter()
            .zip(&prios)
            .filter(|(c, p)| comparable(c) && p.p == 0 && !done.contains(&c.id))
            .map(|(c, _)| c)
            .collect();
        for seg in day
            .segments
            .iter()
            .filter(|s| s.kind.is_work() && s.start >= w.now && !s.flags.current)
        {
            let Some(energy) = seg.energy else { continue };
            // A §7.5 batch is won by its leader and carries the rest of the
            // block with it, so the block counts as `p = 0` work when *any*
            // of its items is `p = 0`.
            let members: Vec<usize> = seg
                .items()
                .iter()
                .filter_map(|id| cands.iter().position(|c| c.id == *id))
                .collect();
            if members.is_empty()
                || members.iter().any(|j| prios[*j].p == 0 || !comparable(&cands[*j]))
            {
                continue;
            }
            for hot in &hot_left_out {
                prop_assert!(
                    hot.ci > energy,
                    "{:?} (p {}) took the {} slot of energy {energy} that HOT {} (ci {}) fits",
                    seg.items(),
                    prios[members[0]].p,
                    planner::fmt_clock(seg.start),
                    hot.id,
                    hot.ci
                );
            }
        }

        // IMPOSSIBLE never dropped (§7.3: "still scheduled with everything
        // available"). Placement is the HOT rule above — an IMPOSSIBLE
        // candidate is `p = 0`, so it only ever yields to other `p = 0` work.
        // What is checked here is that it is never *silently* dropped: the
        // banner names it and the shortfall.
        for (i, c) in cands.iter().enumerate() {
            if !prios[i].is_impossible() || c.is_wall {
                continue;
            }
            prop_assert!(
                day.diagnostics
                    .impossible
                    .iter()
                    .any(|(id, short, _)| *id == c.id && *short == prios[i].shortfall_min),
                "IMPOSSIBLE {} is not in the diagnostics",
                c.id
            );
            if !done.contains(&c.id) && comparable(c) && c.ci <= max_energy {
                // Everything that took a slot instead was at least as urgent.
                for (j, other) in cands.iter().enumerate() {
                    if comparable(other)
                        && done.contains(&other.id)
                        && other.ci >= c.ci
                        && Some(&other.id) != active_id.as_ref()
                        && !carried(&other.id)
                    {
                        prop_assert_eq!(
                            prios[j].p,
                            0,
                            "{} (p {}) took a slot the IMPOSSIBLE {} could have used",
                            other.id,
                            prios[j].p,
                            c.id
                        );
                    }
                }
            }
        }

        // --- nothing is wasted ---------------------------------------------
        // A Rest slot inside the budget means no candidate could take it: §8.2
        // step 5 turns a slot to Rest only when the first eligible candidate
        // does not fit it.
        // §8.2 step 5 counts *blocks*, not minutes ("while blocks_assigned <
        // remaining_budget"): a slot cut short by a wall costs a block all the
        // same, and so does the block that is running.
        let used_blocks = day
            .segments
            .iter()
            .filter(|s| s.kind.is_work() && s.start >= w.now)
            .count() as u32;
        if used_blocks < remaining {
            for rest in day.segments.iter().filter(|s| s.kind == SegKind::Rest) {
                let energy = rest.energy.unwrap_or(0);
                for c in cands.iter().filter(|c| comparable(c)) {
                    prop_assert!(
                        c.ci > energy || done.contains(&c.id),
                        "{} (ci {}) was left out while a Rest slot of energy {energy} stood",
                        c.id,
                        c.ci
                    );
                }
            }
        }
        prop_assert!(!day.segments.is_empty());

        // --- §8.2 step 8: the diagnostics describe this timeline ------------
        for (id, energy, ci) in &day.diagnostics.underused {
            prop_assert!(energy >= &(ci + 2), "{id}: gap {energy} − {ci} is not ≥ 2");
            prop_assert!(
                day.segments.iter().any(|s| s.kind.is_work()
                    && s.flags.underused
                    && s.energy == Some(*energy)
                    && s.items().contains(id)),
                "underused {id} belongs to no `↓` block"
            );
        }
        for seg in day.segments.iter().filter(|s| s.kind.is_work() && s.start >= w.now) {
            let Some(energy) = seg.energy else { continue };
            for id in seg.items() {
                let gap = energy.saturating_sub(ci_of(&id));
                prop_assert_eq!(
                    seg.flags.underused,
                    gap >= 2,
                    "{}: gap {} but flag {}",
                    id,
                    gap,
                    seg.flags.underused
                );
            }
        }
        for id in &day.diagnostics.hot {
            let i = cands.iter().position(|c| c.id == *id).expect("a candidate");
            prop_assert_eq!(prios[i].p, 0, "{} is in `hot` with p {}", id, prios[i].p);
        }
        for id in &day.diagnostics.dropped_tail {
            prop_assert!(
                !day.assigned().contains(id),
                "{id} is both dropped and assigned"
            );
        }
        for id in &day.diagnostics.deferred {
            prop_assert!(!day.assigned().contains(id), "{id} is both deferred and assigned");
        }
        for (id, deps) in &day.diagnostics.blocked {
            prop_assert!(!deps.is_empty(), "{id} is blocked by nothing");
            // §9's one exception: a block that is *already running* keeps its
            // minutes even when step 5 would refuse the item.
            prop_assert!(
                day.segments
                    .iter()
                    .filter(|s| s.kind.is_work() && s.start >= w.now && s.items().contains(id))
                    .all(|s| s.flags.current),
                "{id} is blocked and planned"
            );
        }
        for id in &day.diagnostics.waiting {
            let c = cands.iter().find(|c| c.id == *id).expect("a candidate");
            prop_assert!(c.waiting, "{id} is not waiting");
        }
        prop_assert_eq!(
            day.diagnostics.plan_honesty.is_some(),
            remaining > 0,
            "plan honesty is reported exactly when the day has a budget"
        );

        // --- tail-drop -----------------------------------------------------
        if remaining > 1 {
            let short_state = RuntimeState {
                budget: Some(w.state.budget.unwrap_or(6) - 1),
                ..w.state.clone()
            };
            let short = planner::plan(&w.input(&short_state, w.now));
            let (long_layout, short_layout) = (layout(&day), layout(&short));
            prop_assert!(short_layout.len() <= long_layout.len());
            prop_assert_eq!(
                &short_layout[..],
                &long_layout[..short_layout.len()],
                "losing a block re-shuffled the day"
            );
            for id in assigned_set(&short, w.now) {
                prop_assert!(done.contains(&id), "{id} appeared when the day got shorter");
            }
        }

        // --- stability -----------------------------------------------------
        // Everything that had *finished* by `now` is untouched; what had not —
        // an open interruption, the block that is running — is still there,
        // from the same minute, only longer.
        let later = planner::plan(&w.input(&w.state, w.now + Duration::hours(1)));
        for seg in day.segments.iter().filter(|s| s.end <= w.now) {
            if seg.flags.open {
                let grown = later.segments.iter().find(|s| {
                    s.start == seg.start && s.kind == seg.kind && s.item == seg.item
                });
                prop_assert!(
                    grown.is_some_and(|g| g.end >= seg.end),
                    "an open segment moved or shrank: {seg:?}"
                );
                continue;
            }
            prop_assert!(
                later.segments.contains(seg),
                "a replan moved a settled segment: {seg:?}"
            );
        }
    }
}




// ===========================================================================
// STEP R2 (stage 6 W-25): the generated days go through the KERNEL.
//
// §14.4's R2 says this file must exercise "the kernel's `dayPlan` through the
// FFI".  **When this arm was written at W-25 it could not**: `dayPlan` was not
// reachable through the FFI, because the `plan` REQUEST section carried the
// day's rows and not the planner's inputs, and `EmitWire.lean`'s own header
// assigned that section to step R3 (README gap **1431**, which priced what R3
// then needed, field by field).
//
// **THAT IS NO LONGER TRUE, AND THIS PARAGRAPH IS THE LAND STEP'S.**  D48 moved
// the wire into R2, W-27 landed its REQUEST half and W-28 its RESPONSE half, so
// `Planner.dayPlan` IS reachable through the FFI now and the section at the
// **THE KERNEL PLANS THE DAY** banner below exercises it.  This arm is kept
// because it is a *different* claim, not a superseded one: it sends the FORK's
// day in and checks the kernel's RENDERING of it, where the arm below asks the
// kernel to PLAN.  Read the two banners together; neither is the whole.
//
// What this arm covers, said plainly so the remainder is not mistaken for the
// whole: every day this file's generators produce — 40 random items, five routines, calendar walls, a random log, a
// running block, an open interruption, a late day — is handed to the kernel's
// `plan` section, and the kernel's nine cells for every row are compared
// against `emit::row_cells`'s.  Before W-25 that comparison existed on ONE
// hand-built fixture day (`tm/tests/kernel_row_cells.rs`); this makes it
// thousands of generated ones, and the two files share the encoder.
//
// It is NOT the tail-drop or stability half of R2: those are about a plan the
// kernel made.  The kernel DOES make one now (the banner below), but only §8.2
// steps 1 and 2 of it, so those two halves are still unclaimed — README gap
// **1670**, and the land step re-read this sentence rather than leaving it to
// read as though nothing had changed.
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        // Each case is an FFI call over a whole generated tree, so the count is
        // its own: `TM_PROPTEST_CASES` raises it and W-25's README block records
        // what it was run at (D46 — one run of a randomised test is a weak
        // claim).
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(64),
        max_shrink_iters: 2_000,
        ..ProptestConfig::default()
    })]

    /// **The kernel reads every day the fork planned, and writes the fork's
    /// cells for it.**
    ///
    /// Two claims, and the first is the one nothing else makes:
    ///
    /// 1. **No day the fork's planner produces is refused by the wire.** Every
    ///    `R10` bound the `plan` section carries — `Planner.maxCands` on the
    ///    segment list, `CapWire.maxCandId` on every id, `Look.maxPlanMinutes`
    ///    on `planned`, `Fin 6` on the energy, `maxBatch` on a batch — is a
    ///    number a real day could exceed, and a bound that is too tight refuses
    ///    a legitimate plan. `kernel_rows` returns the refusal instead of
    ///    panicking so this can be asserted rather than assumed.
    /// 2. **Cell for cell, row for row**, against `emit::row_cells`, with
    ///    [`CELL_HOLES`]'s two declared exceptions and no others. The kernel is
    ///    told no title, no `ci`, no estimate and no parent: those four come
    ///    from its own parse of the same generated bytes.
    #[test]
    fn the_kernel_reads_every_day_the_fork_planned(case in case_strategy()) {
        let w = build(&case);
        let day = planner::plan(&w.input(&w.state, w.now));
        let lean = match rowwire::kernel_rows(w.docs_json(), &day, &w.cfg) {
            Ok(rows) => rows,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the wire refused a day the fork planned: {head}");
                unreachable!()
            }
        };
        let fork = rowwire::fork_cells(&day, &w.tree, &w.cfg);
        prop_assert_eq!(
            lean.len(), fork.len(),
            "the kernel answered {} rows for {} segments (`Emit.rowsOf_length`'s wire half)",
            lean.len(), fork.len()
        );
        let mut seen = [0u64; 5];
        seen[0] = fork.len() as u64;
        seen[1] = 1;
        for (i, (f, l)) in fork.iter().zip(&lean).enumerate() {
            // **The `parent` cell, counted where it is not the default** (W-27).
            // Counted off the FORK's cell: the kernel's is the value under
            // test, and a census read off the value under test would report
            // whatever a broken kernel wrote.
            if !f.parent.is_empty() {
                seen[4] += 1;
            }
            for (cell, forked, kernelled) in rowwire::differences(f, l) {
                prop_assert!(
                    CELL_HOLES.contains(&cell),
                    "row {i}: the two readers disagree on an UNDECLARED cell {cell:?} \
                     — fork {forked:?}, kernel {kernelled:?}"
                );
                if cell == "note" {
                    seen[2] += 1;
                } else {
                    seen[3] += 1;
                }
            }
        }
        // **The fuzz compared something, asserted inside the fuzz.**
        //
        // A proptest arm runs its cases in sequence, so a cumulative claim here
        // is deterministic — where a separate `#[test]` reading the same census
        // would race the arm that fills it and pass by seeing nothing. "Every
        // cell agreed" is a sentence a fuzz comparing NO rows also produces
        // (AGENTS §9.2's "a check no input can fail"), and a declared hole that
        // has stopped firing is a claim that has changed (gaps 1101, 1102).
        let [rows, cases, notes, ests, parents] = {
            let mut c = CENSUS.lock().expect("census");
            for (a, b) in c.iter_mut().zip(seen) {
                *a += b;
            }
            *c
        };
        prop_assert!(rows >= 4 * cases, "only {rows} rows over {cases} cases");
        if cases >= 32 {
            prop_assert!(notes > 0, "the `note` hole has not fired in {cases} cases (gap 1102)");
            prop_assert!(ests > 0, "the `est` hole has not fired in {cases} cases (gap 1101)");
            // **The `parent` cell was compared at a real value** (W-27). Without
            // this the cell is in `differences`' nine and still asserts nothing:
            // `"" == ""` on every row of every case is the shape AGENTS §9.2
            // calls a check no input can fail, and an auditor's perturbation of
            // `Emit.parentCell` passed through it. A generator that stops
            // drawing parents now fails here instead of going quietly green.
            prop_assert!(
                parents > 0,
                "no row's `parent` cell was non-empty in {cases} cases — the `parent` \
                 comparison is vacuous (gap 1437's neighbour)"
            );
        }
        // **THE CENSUS IS PRINTED, so the README's figure can be RE-DERIVED.**
        //
        // It was write-only: asserted on and never shown, while the W-25 block
        // quoted "1,035 cases, 11,611 rows compared, note-hole 2,311, est-hole
        // 571" as a MEASUREMENT that no command in the committed tree produced
        // — it can only have come from a temporary print. AGENTS §5.11's own
        // rule is one measurement per number, from the committed harness.
        //
        // It prints on EVERY case, to stderr, and that is deliberate: this is
        // the one place the census can be read without racing the arm that
        // fills it (the sibling file's
        // `zz_the_declared_refusals_are_all_reachable` shape needs `--test-threads=1`, and this
        // arm's own comment above says why a separate `#[test]` would pass by
        // seeing nothing). Every line is a running prefix and the LAST is the
        // total. libtest captures it, so a green run is silent; read it with
        //
        //     cargo test --test planner_invariants -- --nocapture \
        //       the_kernel_reads_every_day_the_fork_planned
        eprintln!(
            "planner_invariants census: {cases} cases, {rows} rows compared, \
             note-hole {notes}, est-hole {ests}, parent-cells {parents}"
        );
    }
}

// ===========================================================================
// **THE KERNEL PLANS THE DAY** — stage 6 W-28, step R2's RESPONSE half (D48).
//
// The arm above sends the FORK's day through the `plan` section and compares
// the kernel's rendering of it. This one asks the kernel to **plan**, through
// `PlanWire.callExport`, and compares two planners.
//
// **What is compared, and why not everything, measured rather than assumed.**
// `Planner.dayRows` is §8.2 steps 1 and 2 and nothing else; steps 3 to 7 are
// P3..P7 and unwritten, and README gap **1670** records that the kernel's day
// therefore holds no step-5 assignment at all. Asserting segment-for-segment
// equality would be asserting something untrue of a half-built planner, and
// narrowing the generator until it came out true is what **D46** forbids. So
// this compares the answers the kernel is *complete* for:
//
//   * `plan.day`, the date it planned;
//   * `plan.window`, §8.1's working window — `Look.day0Window` on one side and
//     `Planner::window_and_budget` on the other, two readers README gap **320**
//     says can disagree, so a disagreement here is a **finding owed a parity
//     number** and not a hole to widen;
//   * `plan.budgetBlocks`;
//   * and **the walls**, the one row class step 1 completes, which §8.3's own
//     "walls are never moved" invariant is about — compared to the minute, both
//     ways, so a wall the kernel invents fails as loudly as one it drops.
//
// Everything else the kernel places (the routine rows, the replayed past, the
// rest/wind-down/sleep filler) is COUNTED and reported and asserted on only
// through the refusal claim, because the fork's day for those rows is the
// output of steps this kernel has not written.
//
// **The `routines` key CARRIES THE FORK'S OWN INSTANCES SINCE W-31**, and the
// sentence that stood here — "this arm has no honest collector" — was false.
// `Planner::collect_routines` reads the candidate list and the item's `shape`
// and nothing else, and both were already in this arm's hands; see
// [`World::routine_items`] and README gap **2220**. F2's recurrence expansion
// is still not built and D27 is still not done early: the expansion happened in
// `priority::collect_candidates` before the list existed. So the kernel places
// §8.2 step 2's rows here now, they are compared to the second, both ways, and
// the assigned-row comparison no longer exempts a day for holding one.
// ===========================================================================

/// `(cases, walls compared, kernel rows seen, window disagreements, budget
/// disagreements, assigned rows compared, cases EXEMPT from the assigned
/// comparison, cases whose §7 answers differ, compared cases whose slots agree
/// and whose items do not (gap 2007), and the two clock-based work-row
/// counts)`, then W-30's four §7-row counters: rows compared, rows whose
/// capacity (`avail`) differs and whose `until` is TODAY (parity **P41**), the
/// same with `until` beyond today (parity **P1**), rows an id could not key
/// because it named two rows on one side, and the days on which §7's whole
/// answer agreed so that step 5's assignment could be ASSERTED.
///
/// **W-31 adds four**: the days on which the FORK placed a §8.2 step-2 routine
/// row (the population the old exemption removed from the assigned-row
/// comparison, kept as a counter so a run that stopped drawing routines is
/// visible), the step-2 routine rows COMPARED, and the two candidate-set
/// counters README gap **2222** is about — fork-assigned row ids the kernel was
/// sent no candidate for, and fork-assigned row ids the kernel returned no §7
/// grant for.
static PLAN_CENSUS: Mutex<[u64; 26]> = Mutex::new([0; 26]);

/// **A configured double as the exact decimal pair the wire carries** (D17).
///
/// The kernel holds no `Float`, so every `[energy]` and `[expected]` decimal
/// crosses as `num/den`. This is `kernel_capacity::written_pair` restricted to
/// the shortest round-trip text of a `f64` — the shipped reader lives in the
/// `tm` binary and an integration test cannot link it, which is README gap
/// 2006: one concept, two readings, and the move belongs with R3's deletion.
fn dec(x: f64) -> Value {
    let t = format!("{x}");
    let (int, frac) = t.split_once('.').unwrap_or((t.as_str(), ""));
    json!({"num": format!("{int}{frac}"), "den": format!("1{}", "0".repeat(frac.len()))})
}

/// The same pair as JSON naturals, for the sections whose reader is `natAt`
/// rather than a digit string (the prior's step bounds).
fn decn(x: f64) -> Value {
    let v = dec(x);
    json!({"num": v["num"].as_str().unwrap_or("0").parse::<u64>().unwrap_or(0),
           "den": v["den"].as_str().unwrap_or("1").parse::<u64>().unwrap_or(1)})
}

/// A `NaiveTime` as the wire's `HH:MM`.
fn hhmm(t: NaiveTime) -> String {
    format!("{:02}:{:02}", t.hour(), t.minute())
}

/// The absolute second of a local time on [`DAY`].
fn day_sec(tz: Tz, t: NaiveTime) -> i64 {
    rowwire::kernel_sec(local_dt(tz, date(), t))
}

impl World {
    /// **`capacity.candidates.items`, the fork's own list** (W-29 repair,
    /// README gap 2005 — it closes gap 1905's first half).
    ///
    /// Gap 1905 said no honest encoder for `Look.Cand` existed on this side.
    /// One does, and it ships: `tm/src/cli/kernel_capacity.rs`'s `send_order`,
    /// `cand_json` and `plan_json` are what the `tm` binary sends on every
    /// `tm plan`. **They cannot be linked from here** — `tm` is a `[[bin]]`
    /// with no library target, so an integration test cannot `use` them — so
    /// this is that encoder's second spelling and README gap **2006** records
    /// the move (into `tm-core`, or out with R3) rather than pretending it is
    /// not one. Everything it reads is the FORK's: `collect_candidates` builds
    /// the records, `Tree::root`/`priority` the written `!k`, and the order is
    /// the fork's own `(effective_due, own_order, index)`.
    ///
    /// `yesterday` is `None` on every record because `RuntimeState::default()`
    /// leaves `priorities_yesterday` empty and the fork reads exactly that map
    /// (`planner.rs:988`) — the two sides agree by construction, not by luck.
    fn candidate_items(&self) -> Vec<Value> {
        let cands = self.candidates();
        // `kernel_capacity::send_order`: the fork's `priority::compute` sort, so
        // the kernel's stable sort by due date serves a date's deadlines in the
        // fork's order.
        let mut order: Vec<usize> = (0..cands.len()).collect();
        order.sort_by(|&a, &b| {
            let (ca, cb) = (&cands[a], &cands[b]);
            (ca.effective_due.is_none(), ca.effective_due, ca.own_order, a)
                .cmp(&(cb.effective_due.is_none(), cb.effective_due, cb.own_order, b))
        });
        order
            .iter()
            .map(|&i| {
                let c = &cands[i];
                let root_prio = self.tree.get(&self.tree.root(&c.id)).and_then(|r| r.priority);
                let floor = c.floor.as_ref().map(|r| {
                    json!({"left": r.amount.as_minutes().saturating_sub(c.floor_done_min),
                           "until": priority::period_range(r.per, date()).1.to_string()})
                });
                json!({
                    "id": c.id.as_str(), "ci": c.ci, "rootPrio": root_prio,
                    "remaining": c.remaining_min,
                    "due": c.effective_due.map(|d| d.date_naive().to_string()),
                    "window": c.window.is_some(), "wall": c.is_wall,
                    "optional": c.is_optional, "overdue": c.overdue,
                    "mandatory": c.mandatory, "hot": c.hot,
                    "yesterday": Option::<u8>::None,
                    "floor": floor,
                    // §8.2 step 5's nine (`Look.PlanFacts`), as `plan_json` sends them.
                    "plan": {"plannedMin": c.planned_min,
                             "multiplier": decn(c.multiplier),
                             "loc": c.loc.as_str(), "splittable": c.splittable,
                             "cap": c.cap.as_ref().map(|r| json!({
                                 "capMin": r.amount.as_minutes(), "doneMin": c.cap_done_min})),
                             "state": c.state.glyph().to_string(),
                             "blockedBy": c.blocked_by.iter().map(ToString::to_string)
                                 .collect::<Vec<String>>(),
                             "wallToday": c.wall_today}})
            })
            .collect()
    }

    /// **§8.2 step 2's instances, `collect_routines` read off the candidates
    /// ALREADY ON THE WIRE** (W-31, README gap 2220).
    ///
    /// The `routines` key was sent EMPTY for the whole of this arm's life, and
    /// the reason given was that "which occurrences are due today is F2's
    /// recurrence expansion (track K3, not built) and D34 forbids doing D27
    /// early, so a host collects them; this arm has no honest collector".
    /// **The first half is true and the second was false.** `Planner::
    /// collect_routines` (`planner.rs:1277`) reads NOTHING but the candidate
    /// list and the item's own `shape` — `c.window`, `c.remaining_min`,
    /// `c.mandatory`, `c.instance` and `daily_window`, which is `Shape::Window`
    /// with a `Daily` range — and this arm already builds that candidate list
    /// and already sends it (`candidate_items`). The recurrence expansion is
    /// `priority::collect_candidates`' and it has already run by the time the
    /// list exists. So the collector is the fork's own, on the fork's own
    /// input, and it is not a guess: it is the same move that closed gap
    /// 1905's first half one run earlier, applied to the other key.
    ///
    /// **`pref:` is NOT sent, on purpose**: `Planner.PlanReq.anchorOf` reads it
    /// out of the store (`e.val.pref`) and the store is the documents already
    /// in the request, so a `pref` on the wire would be §5.3's second reader of
    /// one fact. `RoutineIn` has no such field for the same reason.
    ///
    /// **Sleep is NOT split here**: `Planner.splitSleep` does it kernel-side
    /// off the same rule (the id `sleep`, or an overnight window of at least
    /// `SLEEP_MIN_MINUTES`), so the list goes over whole and the kernel's own
    /// splitter runs. A split here would be that rule's second spelling.
    ///
    /// This is `collect_routines`' **second spelling** and README gap **2221**
    /// records it beside gap 2061's three spellings of the grant wire: `tm` is
    /// a `[[bin]]` with no library target, and `RoutineInst` is private to
    /// `tm-core::planner` besides.
    fn routine_items(&self) -> Vec<Value> {
        let tz = self.cfg.tz;
        let day_start = local_dt(tz, date(), NaiveTime::MIN);
        let day_end = day_start + chrono::Duration::days(1);
        let mut out = Vec::new();
        for c in self.candidates() {
            if c.is_wall || c.is_optional || !c.eligible() {
                continue;
            }
            let Some((ws, we)) = c.window else { continue };
            if c.remaining_min == 0 {
                continue;
            }
            // `Planner::daily_window`: `Shape::Window` with a `Daily` range,
            // on today's date, rolled over midnight when it closes before it
            // opens.
            let hours = self.tree.get(&c.id).and_then(|i| match i.shape {
                Shape::Window { range: WindowRange::Daily { from, to }, .. } => {
                    let a = local_dt(tz, date(), from);
                    let mut b = local_dt(tz, date(), to);
                    if b <= a {
                        b += chrono::Duration::days(1);
                    }
                    Some((a, b))
                }
                _ => None,
            });
            let span = if we <= self.now {
                let (a, b) = hours.unwrap_or((day_start, day_end));
                (a.max(self.now).max(day_start), b.max(self.now))
            } else {
                let (mut a, mut b) = (ws.max(day_start), we.min(day_end));
                if let Some((ha, hb)) = hours {
                    a = a.max(ha);
                    b = b.min(hb);
                }
                (a, b)
            };
            out.push(json!({
                "id": c.id.as_str(),
                "inst": c.instance.map(|k| k.to_string()),
                "winLo": rowwire::kernel_sec(span.0),
                "winHi": rowwire::kernel_sec(span.1),
                "durMin": c.remaining_min,
                "mandatory": c.mandatory,
            }));
        }
        out
    }

    /// **The whole request the kernel plans from**: the generated documents,
    /// the generated log through D24's seam, the capacity section over
    /// `Config::default()`, and the `planner` section §9's runtime rows live in.
    ///
    /// The lookahead's own inputs — `pLounge`, `arrival`, `prior`, `homeMaxCi`,
    /// `posterior`, `sleep`, `priority` and `days` — are the shipped defaults
    /// spelled here rather than read off `Config`, and **none of them reaches
    /// what this arm compares**: §8.1's window is `[day]`, the stored window and
    /// the walls, and the walls are the documents'. They are here because the
    /// capacity section must decode for the planner section to be read at all.
    fn plan_request(&self) -> Value {
        let tz = self.cfg.tz;
        let week = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
        // **READ OFF `Config`, NEVER SPELLED** (W-29 repair, README gap 2005).
        // These three tables were hand-written literals said to be "the shipped
        // defaults"; they were not. `Config::default()` puts the lounge prior at
        // `0-1:4, 1-5:5, 5-8:4, 8-10:3, 10+:2` and the home prior at
        // `0-1:3, 1-4:4, 4-8:3, 8+:2`, `p_lounge` at 0.9/0.8/0.5/0.4 and the
        // expected arrival at 07:00 (10:00 at the weekend) — the literals said
        // `5/3/1`, `3/2`, 1.0 everywhere and `state.arrival` (00:00 when unset).
        // Nothing before this step read them: §8.1's window is `[day]` and the
        // walls, so the window and budget halves of this arm agreed anyway, and
        // §8.2 step 5's ENERGY FILTER — the one reader of the prior — was never
        // compared. DRIVEN: with the literals 2 of 19 routine-free cases cut the
        // day into different assigned slots; read off `Config`, 26 of 26 agree.
        let wds = [chrono::Weekday::Mon, chrono::Weekday::Tue, chrono::Weekday::Wed,
                   chrono::Weekday::Thu, chrono::Weekday::Fri, chrono::Weekday::Sat,
                   chrono::Weekday::Sun];
        let p_config: serde_json::Map<String, Value> = week
            .iter()
            .zip(wds)
            .map(|(k, wd)| ((*k).to_string(), dec(*self.cfg.expected.p_lounge.get(wd))))
            .collect();
        let arrival_tbl: serde_json::Map<String, Value> = week
            .iter()
            .zip(wds)
            .map(|(k, wd)| ((*k).to_string(), json!(hhmm(*self.cfg.expected.arrival.get(wd)))))
            .collect();
        let curve = |loc: &str| -> Value {
            Value::Array(
                self.cfg.energy.prior[loc]
                    .0
                    .iter()
                    .map(|s| json!({"from": decn(s.from), "to": s.to.map(decn), "level": s.level}))
                    .collect(),
            )
        };
        let d = &self.cfg.day;
        let capacity = json!({
            // **`wake` CROSSES** (W-30). `kernel_capacity::request` sends
            // `{"sec", "ns"}` when `state.wake` is set and `"log"` otherwise; this
            // arm sent NEITHER, so `Boundary.readWake` answered `.absent` and the
            // kernel measured §8.5's `hsw` from the weekday's expected arrival
            // while the fork measured it from the day's own wake. Every slot's
            // energy level rides on that.
            "wake": match self.state.wake {
                Some(t) => json!({"sec": t.num_seconds_from_midnight(), "ns": t.nanosecond()}),
                None => json!("log"),
            },
            "pLounge": {"config": p_config},
            "arrival": {"config": arrival_tbl},
            "prior": {"lounge": curve("lounge"), "home": curve("home")},
            "homeMaxCi": self.cfg.location.home_max_ci,
            "day": {"breakMin": d.break_min, "breakAfterBlocks": d.break_after_blocks,
                    "minLastBlockMin": d.min_last_block_min,
                    "windowHours": {"num": 8, "den": 1}, "windowCap": hhmm(d.window_cap),
                    "budgetRatio": {"num": 3, "den": 4},
                    "windDown": hhmm(d.wind_down), "bed": hhmm(d.bed)},
            "priority": {"bins": [{"num": 1, "den": 2}, {"num": 1, "den": 4},
                                  {"num": 1, "den": 10}],
                         "safety": {"num": 13, "den": 10}, "defaultPriority": 3,
                         "batchMaxMin": 20},
            "days": priority::lookahead_days(&self.candidates(), date()),
            "at": self.now.to_rfc3339(),
            "state": {
                "date": self.state.date.map(|x| x.to_string()),
                "window": self.state.window.map(|(f, t)| json!({"from": hhmm(f), "to": hhmm(t)})),
                "budget": self.state.budget,
                "arrival": self.state.arrival.map(hhmm),
                "loc": self.state.loc,
                "allowHome": false},
            "posterior": {"fullHours": {"num": 3, "den": 1}, "zeroHours": {"num": 6, "den": 1}},
            "sleep": {"shiftModel": null, "shiftConfig": {"neg": false, "num": 1, "den": 1},
                      "underHours": {"num": 7, "den": 1}},
            "candidates": {"hysteresis": self.cfg.priority.hysteresis,
                           "items": self.candidate_items()},
        });
        let mut runtime = serde_json::Map::new();
        if let Some(a) = &self.state.active {
            runtime.insert(
                "active".to_string(),
                json!({"id": a.id.to_string(), "started": day_sec(tz, a.started),
                       "estMin": a.est_min, "paused": a.paused}),
            );
        }
        if let Some(i) = &self.state.interrupt {
            if let Some(started) = i.started {
                runtime.insert(
                    "interrupt".to_string(),
                    json!({"started": day_sec(tz, started),
                           "id": i.id.as_ref().map(ToString::to_string)}),
                );
            }
        }
        json!({
            "docs": self.docs_json(),
            "now": DAY,
            "blockMin": self.cfg.block_min(),
            "tz": rowwire::tz_table::wire_for(None, tz),
            "log": {"ckpt": null, "from": 1,
                    "lines": self.log.lines().collect::<Vec<_>>(),
                    "terminated": true, "reseal": null,
                    "want": {"facts": true, "headersFrom": null, "render": []},
                    "sealed": null},
            "capacity": capacity,
            "planner": {"state": Value::Object(runtime), "routines": self.routine_items()},
        })
    }
}

/// The kernel's own day for a request, or the refusal it answered.
///
/// **The §8.4 answer travels with it under `__grants`** (W-30): one call answers `plan` and
/// `lookahead` together, and the lookahead's per-candidate grants are §7's WHOLE answer — the
/// ten fields `grant_fields` compares and `kernel_prios` reads back. A leading `__` is not a
/// key the wire has: `PlanWire.planKeys` lists the nine the `plan` object carries, so a reader
/// of either side cannot confuse it for one.
fn kernel_plan(req: &Value) -> Result<Value, String> {
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("the response is json");
    if resp["ok"]["plan"]["day"].is_null() {
        return Err(raw);
    }
    let mut p = resp["ok"]["plan"].clone();
    p["__grants"] = resp["ok"]["lookahead"]["grants"].clone();
    Ok(p)
}

/// `(start, stop)` of every Wall row of a kernel day, in the day's order.
fn kernel_walls(plan: &Value) -> Vec<(i64, i64)> {
    plan["segments"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default()
        .iter()
        .filter(|s| s["kind"] == "wall")
        .map(|s| (s["start"].as_i64().unwrap_or(-1), s["stop"].as_i64().unwrap_or(-1)))
        .collect()
}

/// **(start, stop, items) of every row §8.2 step 5 ASSIGNED**, on both sides, by the property
/// that distinguishes them and not by a list of the rows that are not them: a step-5 row is a
/// work row (Block or Batch) that carries a **slot energy**.
///
/// The three other sources of a work row each carry `energy: None` and each does so for a
/// reason a reader can check: §8.2 choice 5b's reservation *"is a reservation, not a slot, so
/// it carries no slot energy"* (fork `emit_segments`; kernel
/// `Planner.PlanReq.activeRow_is_an_energyless_block`), and the replayed past is played back
/// off the log, which has no slots in it (`Planner.pastRows`). Only the assign fold puts a row
/// in an energised slot, on either side.
///
/// **This was a `start >= now` restriction for one run of this arm and the clock was the wrong
/// subject** — driven: the arm failed with *"the kernel assigned [(63924379200, 63924380760,
/// [\"zaa\"])] from a request carrying no candidates"*, and with no candidates on the wire the
/// only work row the kernel can draw at or after `now` is §8.2 choice 5b's reservation. The
/// energy property names step 5's rows; the clock names "whatever has not started yet", which
/// is a different set. **No asymmetry between the two planners is claimed from that failure**
/// — the census counts the clock-based set on both sides, and it is 25 and 25. README gap
/// 1906.
fn kernel_assigned(plan: &Value, _now_sec: i64) -> Vec<(i64, i64, Vec<String>)> {
    plan["segments"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default()
        .iter()
        .filter(|s| {
            (s["kind"] == "block" || s["kind"] == "batch") && !s["energy"].is_null()
        })
        .map(|s| {
            // **THE KEY IS `batch`, AND THIS READ `ids`** (W-29 repair, README
            // gap 2015). `PlanWire.segJson` writes `batch` for a Batch row's
            // members and `item` for a Block's; `s["ids"]` is a key the kernel
            // has never written, so every Batch row read as EMPTY and fell
            // through to a null `item`. Nothing caught it because this function's
            // result was never compared with the fork's until this step — the
            // reader of a comparison that does not run is not a tested reader.
            let ids: Vec<String> = match s["batch"].as_array() {
                Some(a) if !a.is_empty() => {
                    a.iter().filter_map(|x| x.as_str().map(str::to_string)).collect()
                }
                _ => s["item"].as_str().map(str::to_string).into_iter().collect(),
            };
            (s["start"].as_i64().unwrap_or(-1), s["stop"].as_i64().unwrap_or(-1), ids)
        })
        .collect()
}

/// The same, off the fork's day, by the same property.
fn fork_assigned(day: &DayPlan, _from: DateTime<Tz>) -> Vec<(i64, i64, Vec<String>)> {
    day.segments
        .iter()
        .filter(|s| matches!(s.kind, SegKind::Block | SegKind::Batch(_)))
        .filter(|s| s.energy.is_some())
        .map(|s| {
            let ids: Vec<String> = match &s.kind {
                SegKind::Batch(ids) => ids.iter().map(ToString::to_string).collect(),
                _ => s.item.iter().map(ToString::to_string).collect(),
            };
            (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end), ids)
        })
        .collect()
}

/// **§7's WHOLE ANSWER for one candidate, kernel beside fork** (W-30) — the ten fields
/// `Look.FloorOut` carries and `kernel_capacity::parse` decodes into a `Prio`, not the `p`
/// alone the W-29 repair step compared.
///
/// It returns two lists: the fields of the **capacity** — what the §8.4 lookahead handed §7 —
/// that differ, and the fields **downstream** of it that differ. The split is the whole point.
/// Both registered divergences of this pass are capacity divergences and nothing else: parity
/// **P1** (the kernel mixes `w·L + (capDen − w)·H` over the two locations where the fork picks
/// one at the `p_lounge ≥ 0.5` threshold, so a future day's minutes land on different levels)
/// and parity **P41** (the kernel reads day 0 off the capacity section's own window cut, since
/// D24/L9 keeps every §9 row off that wire, where the fork point reads it off §8.2 step 3's
/// cut — walls, the running block, today's placed routines and the night already removed).
/// **Everything downstream is asserted to agree**, which is the statement P1's own register row
/// makes (*"future-day capacity **and everything downstream**"*) read as a test rather than as
/// a sentence: `allocation`, `shortfall`, `bin`, the HOT/IMPOSSIBLE class, `p` and `rawP` are
/// one function of `(k, need, avail, until)` and the two planners must compute it alike.
///
/// A wall carries no `p` on either side (`Planner.prioRow`, fork `sorted_candidates`' `7`), so
/// only its class is compared.
fn grant_fields(k: &Value, f: &Prio) -> (Vec<String>, Vec<String>) {
    let unit = |v: &Value| -> u128 {
        v.as_str().unwrap_or("0").parse::<u128>().unwrap_or(0) / 1_000_000_000_000_000_000
    };
    let cls = |c: PrioClass| -> &'static str {
        match c {
            PrioClass::Wall => "wall",
            PrioClass::Hot => "hot",
            PrioClass::Impossible => "impossible",
            PrioClass::Overdue => "overdue",
            PrioClass::Mandatory => "mandatory",
            PrioClass::HotFlag => "hotflag",
            PrioClass::Dated => "dated",
            PrioClass::Floor => "floor",
            PrioClass::Rank => "rank",
            PrioClass::Optional => "optional",
        }
    };
    let mut cap = Vec::new();
    let mut down = Vec::new();
    let say = |v: &mut Vec<String>, name: &str, a: String, b: String| {
        if a != b {
            v.push(format!("{name} kernel {a}, fork {b}"));
        }
    };
    // Is it a wall on both sides?  That half is compared for every row.
    say(&mut down, "class", k["class"].as_str().unwrap_or("?").to_string(), cls(f.class).to_string());
    if f.class == PrioClass::Wall {
        return (cap, down);
    }
    // The capacity §8.4 handed §7, and the two facts that are the candidate's own.
    say(&mut cap, "avail", unit(&k["avail"]).to_string(), f.avail_min.to_string());
    say(&mut cap, "until", format!("{:?}", k["until"].as_str()),
        format!("{:?}", f.until.map(|d| d.to_string()).as_deref()));
    say(&mut cap, "need", format!("{:?}", k["need"].as_u64()), f.need_min.to_string());
    say(&mut cap, "k", format!("{:?}", k["k"].as_u64()), f.k.to_string());
    // Everything §7 computes FROM that.
    say(&mut down, "allocation", unit(&k["allocation"]).to_string(), f.allocation_min.to_string());
    say(&mut down, "shortfall", unit(&k["shortfall"]).to_string(), f.shortfall_min.to_string());
    say(&mut down, "bin", format!("{:?}", k["bin"].as_u64()), format!("{:?}", f.bin));
    say(&mut down, "p", format!("{:?}", k["p"].as_u64()), f.p.to_string());
    say(&mut down, "rawP", format!("{:?}", k["rawP"].as_u64()), f.raw_p.to_string());
    (cap, down)
}

/// **The kernel's own §7 answer, read back as the fork's `Prio`** (W-30), so the fork can be
/// asked to plan the day WITH IT — `PlanInput::with_ranking`, which is exactly what the shipped
/// binary does (`planning::build_ranked` → `Ctx::priorities` → `kernel_capacity::rank`, then
/// `with_ranking`).
///
/// **Why a second fork run exists at all.** §8.2 step 5's assignment cannot be asserted against
/// a fork that ran its OWN §7 pass, because the two passes are given different capacity by
/// design — parity **P1** for the future days and parity **P41** for day 0 — and every
/// difference in `p` reaches step 5 as a different rank order. Measured at this commit, over
/// 526 cases, the number of days on which the whole §7 answer agreed row for row was **four**;
/// an assertion gated on that is an assertion that does not run, which is the defect this arm
/// shipped with for one whole run (README gap 2005). Handing the fork the kernel's answer makes
/// step 5 comparable on EVERY day, and it compares the thing the binary actually runs.
///
/// It is `kernel_capacity::parse`'s **third** spelling and README gap **2006** is amended to say
/// so rather than growing one quietly: `tm` is a `[[bin]]` with no library target.
///
/// `None` when the grants cannot be keyed 1:1 onto `cands` — an id naming two rows (§5.3's
/// carried instance), or a candidate the kernel answered nothing for. The census counts those
/// days; a guess would compare the kernel against a ranking neither planner holds.
fn kernel_prios(plan: &Value, cands: &[Candidate]) -> Option<Vec<Prio>> {
    let mut by_id: BTreeMap<&str, Option<&Value>> = BTreeMap::new();
    for g in plan["__grants"].as_array().map(Vec::as_slice).unwrap_or_default() {
        let id = g["id"].as_str()?;
        // A second row under one id poisons the entry rather than overwriting it.
        by_id.entry(id).and_modify(|e| *e = None).or_insert(Some(g));
    }
    let unit = |v: &Value| -> u128 { v.as_str().unwrap_or("0").parse::<u128>().unwrap_or(0) };
    let mut out = Vec::with_capacity(cands.len());
    for c in cands {
        let g = (*by_id.get(c.id.as_str())?)?;
        let class = match g["class"].as_str()? {
            "wall" => PrioClass::Wall,
            "hot" => PrioClass::Hot,
            "impossible" => PrioClass::Impossible,
            "overdue" => PrioClass::Overdue,
            "mandatory" => PrioClass::Mandatory,
            "hotflag" => PrioClass::HotFlag,
            "dated" => PrioClass::Dated,
            "floor" => PrioClass::Floor,
            "rank" => PrioClass::Rank,
            "optional" => PrioClass::Optional,
            _ => return None,
        };
        // A wall is off §7.2's scale on both sides: the kernel writes `p: null` and the fork's
        // own `Prio::wall` is the comparand, so it is built here rather than decoded.
        if class == PrioClass::Wall {
            // `Prio::wall` is private to `tm-core`; this is its body, and §7.2's
            // "off the scale" is what both spellings say (`priority.rs:842`).
            out.push(Prio {
                id: c.id.clone(),
                p: 0,
                class,
                k: c.k,
                u: None,
                bin: None,
                need_min: 0,
                avail_min: 0,
                avail_min_exact: Exact::default(),
                allocation_min: 0,
                allocation_min_exact: Exact::default(),
                shortfall_min: 0,
                shortfall_min_exact: Exact::default(),
                until: None,
                hysteresis_applied: false,
                raw_p: 0,
            });
            continue;
        }
        let avail = Exact::new(unit(&g["avail"]), CAP_DEN);
        let alloc = Exact::new(unit(&g["allocation"]), CAP_DEN);
        let short = Exact::new(unit(&g["shortfall"]), CAP_DEN);
        let need = u32::try_from(g["need"].as_u64()?).ok()?;
        let p = u8::try_from(g["p"].as_u64()?).ok()?;
        let raw_p = u8::try_from(g["rawP"].as_u64()?).ok()?;
        // `u` is the ONE field the grant does not carry, and §7.1's own definition rebuilds it:
        // `need / avail`, with a zero capacity infinite. Nothing step 5 reads uses it — the
        // planner reads `p` (`sort_key`, the hot flag) and `class` (§8.2 step 8's diagnostics) —
        // and it is filled honestly rather than left `None`, which would read as "no pass".
        let uu = if avail.num == 0 {
            if need == 0 { 0.0 } else { f64::INFINITY }
        } else {
            f64::from(need) / (avail.num as f64 / avail.den as f64)
        };
        out.push(Prio {
            id: c.id.clone(),
            p,
            class,
            k: u8::try_from(g["k"].as_u64()?).ok()?,
            u: Some(uu),
            bin: g["bin"].as_u64().map(|b| b as u8),
            need_min: need,
            avail_min: avail.floor_u32(),
            avail_min_exact: avail,
            allocation_min: alloc.floor_u32(),
            allocation_min_exact: alloc,
            shortfall_min: short.floor_u32(),
            shortfall_min_exact: short,
            until: g["until"].as_str().and_then(|d| NaiveDate::parse_from_str(d, "%Y-%m-%d").ok()),
            hysteresis_applied: p != raw_p,
            raw_p,
        });
    }
    Some(out)
}

/// The same, off the fork's day.
fn fork_walls(day: &DayPlan) -> Vec<(i64, i64)> {
    day.segments
        .iter()
        .filter(|s| matches!(s.kind, SegKind::Wall))
        .map(|s| (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end)))
        .collect()
}

proptest! {
    #![proptest_config(ProptestConfig {
        // **256, RAISED FROM 128 AT W-31** (128 from 64 at W-30) — the search,
        // not the generator (D46: narrowing a generator to lose a disagreement
        // is forbidden; widening the search to find one is the opposite move).
        // W-30 raised it because 64 cases had never found the slot-geometry
        // disagreement README gap **2062** carries and a 512-case run found it
        // on the fourth try. W-31 raises it because the population the run
        // compares grew by 4.6x in the same edit — `routines` crossing the wire
        // took `cases exempt` from 102 of 143 to 0 and `assigned-rows compared`
        // from 84 to 390 — so a case is worth more than it was, and the two
        // step-2 floors below want a count that reliably draws a routine.
        // Measured on this tree: the whole file costs 67.6 s at 256. The
        // comparison test alone costs 35.9 s at 128 with `routines` on the wire
        // against 24.2 s at the 128 W-30 shipped without them, so the key is
        // half again as expensive per case and the raise is the other half.
        // `TM_PROPTEST_CASES` still takes an auditor higher.
        cases: std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256),
        max_shrink_iters: 2_000,
        ..ProptestConfig::default()
    })]

    /// **The kernel plans the same day the fork plans**, as far as the kernel
    /// is built to plan it — see this section's header for exactly how far, and
    /// why the line is where it is.
    #[test]
    fn the_kernel_plans_the_day_the_fork_plans(case in case_strategy()) {
        let w = build(&case);
        let fork = planner::plan(&w.input(&w.state, w.now));
        let req = w.plan_request();
        let plan = match kernel_plan(&req) {
            Ok(p) => p,
            Err(raw) => {
                let head: String = raw.chars().take(400).collect();
                prop_assert!(false, "the kernel refused a day the fork planned: {head}");
                unreachable!()
            }
        };

        // **The date.**
        let fork_date = fork.date.to_string();
        prop_assert_eq!(
            plan["day"].as_str(), Some(fork_date.as_str()),
            "the two planners planned different days"
        );

        // **§8.1's window and budget**, the two readers README gap 320 is about.
        let (klo, khi) = (
            plan["window"]["lo"].as_i64().unwrap_or(-1),
            plan["window"]["hi"].as_i64().unwrap_or(-1),
        );
        let (flo, fhi) = (
            rowwire::kernel_sec(fork.window.0),
            rowwire::kernel_sec(fork.window.1),
        );
        let window_differs = (klo, khi) != (flo, fhi);
        let budget_differs =
            plan["budgetBlocks"].as_u64() != Some(u64::from(fork.budget_blocks));

        // **The walls, to the minute, both ways.**
        let kw = kernel_walls(&plan);
        let fw = fork_walls(&fork);
        prop_assert_eq!(
            &kw, &fw,
            "the two planners disagree about §8.2 step 1's walls \
             (kernel {:?}, fork {:?})", kw, fw
        );

        // **§8.2 step 5's rows, compared — and the exemption is a PROPERTY, not a list.**
        // P9 put `Planner.PlanReq.assignedRows` in the kernel's day, and since the W-29
        // repair step this arm SENDS the fork's candidates (`candidate_items`), so a
        // kernel day carries assigned Block and Batch rows on every case whose tree
        // generated one. What is still not sent is §10.2's `routines`, and that is the
        // exemption below — stated over the fork's own day, counted, and not universal.
        let now_sec = rowwire::kernel_sec(w.now);
        let ka = kernel_assigned(&plan, now_sec);
        // **Measured, not asserted**: the energy-less work rows at or after `now` — the set a
        // clock-based subject would have called "assigned". It is here because the first
        // version of this comparison used that subject and caught the reservation with it;
        // the counter is what says whether the two planners' clock-based sets even have the
        // same size, rather than a sentence claiming they do not. README gap 1906.
        let k_res = plan["segments"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .filter(|s| {
                (s["kind"] == "block" || s["kind"] == "batch")
                    && s["energy"].is_null()
                    && s["start"].as_i64().unwrap_or(-1) >= now_sec
            })
            .count() as u64;
        let f_res = fork
            .segments
            .iter()
            .filter(|s| {
                matches!(s.kind, SegKind::Block | SegKind::Batch(_))
                    && s.energy.is_none()
                    && s.start >= w.now
            })
            .count() as u64;
        let fa = fork_assigned(&fork, w.now);
        let cands = req["capacity"]["candidates"]["items"]
            .as_array()
            .map_or(0, Vec::len);
        // **A request with no candidates must produce no assigned row**, and
        // that is a consequence of the kernel's own definitions rather than of
        // this arm's input: `Planner.rankedCands.length ≤ cands.length`, so
        // `dayBatches` and `rawGroups` are empty and `assignedRows`' `groups[gi]?`
        // can never return one. It is asserted anyway because it is cheap, and
        // it is NO LONGER the whole of this comparison: the request above now
        // carries the fork's candidates and `cands` is 0 only for a case whose
        // tree generated nothing.
        if cands == 0 {
            prop_assert!(
                ka.is_empty(),
                "the kernel assigned {:?} from a request carrying no candidates", ka
            );
        }
        // **THE EXEMPTION'S `routines` HALF IS GONE, BECAUSE THE KEY CROSSES THE
        // WIRE** (W-31, README gap 2220). The clause read `fork_routines > 0`
        // and its own comment ended *"the day `routines` crosses the wire the
        // exemption empties with no edit here"* — that day is this one, and the
        // edit is the clause's deletion. It was firing on **102 of 143** cases,
        // which is 71% of the population, and it took §8.2 step 5's whole
        // assignment comparison with it: `assigned-rows compared` was 84 of the
        // 368 rows the kernel drew.
        //
        // What is left is `cands == 0`, and that is a property of the REQUEST,
        // not of the fork's day. The count is kept as a census figure so that a
        // run which stopped drawing routines — and therefore stopped exercising
        // step 2 at all — is visible rather than silently green.
        let fork_routines = fork
            .segments
            .iter()
            .filter(|s| matches!(s.kind, SegKind::Routine))
            .count();
        // **§7's WHOLE ANSWER, compared row by row, and the capacity half is told
        // apart from everything downstream of it** (W-30; the W-29 repair step
        // compared `(id, p)` and could say only *that* the two disagreed).
        //
        // `PlanWire.priosJson` writes `Planner.dayPriorities` into the `plan`
        // object and `kernel_plan` carries the lookahead's own `grants` beside
        // it — the ten fields `kernel_capacity::parse` turns into a `Prio` — so
        // the comparison can name WHICH field moved. Driven at this commit, over
        // 526 cases: **every** divergence of this pass is a divergence of the
        // capacity `avail`, and `allocation`, `shortfall`, `bin`, the class, `p`
        // and `rawP` follow it. That is asserted below, per row, which is P1's
        // own register row (*"future-day capacity **and everything downstream**"*)
        // read as a test instead of as a sentence.
        //
        // **Keyed by an id that names ONE row on each side.** §5.3's carried
        // instance can put an id in the list twice; such a row is not compared
        // and is COUNTED (`§7 rows unkeyable`) rather than silently collapsed
        // into a map, which is what the `(id, p)` `BTreeMap` did.
        let mut kg: BTreeMap<String, Vec<&Value>> = BTreeMap::new();
        for g in plan["__grants"].as_array().map(Vec::as_slice).unwrap_or_default() {
            kg.entry(g["id"].as_str().unwrap_or_default().to_string()).or_default().push(g);
        }
        let mut fg: BTreeMap<String, Vec<&Prio>> = BTreeMap::new();
        for (id, pr) in &fork.priorities {
            fg.entry(id.to_string()).or_default().push(pr);
        }
        let (mut g7, mut gcap0, mut gcapn, mut gdup) = (0u64, 0u64, 0u64, 0u64);
        let mut prios_differ = false;
        for (id, fl) in &fg {
            let Some(kl) = kg.get(id) else { continue };
            if kl.len() != 1 || fl.len() != 1 {
                gdup += 1;
                continue;
            }
            let (kr, fr) = (kl[0], fl[0]);
            let (cap, down) = grant_fields(kr, fr);
            g7 += 1;
            // **THE ASSERTION**: §7 is one function of the capacity it is given.
            // A field downstream of the capacity may differ only where the
            // capacity does, and where the capacity agrees nothing downstream
            // may move. Neither P1 nor P41 can reach this; a change to §7's own
            // arithmetic on either side fails here, naming the field.
            prop_assert!(
                !cap.is_empty() || down.is_empty(),
                "§7 answered differently for {id} while the capacity it was given AGREED: {}",
                down.join("; ")
            );
            if !cap.is_empty() {
                prios_differ = true;
                // **Which registered divergence it is, by the row's OWN `until`**:
                // a row summed to today alone is P41's (day 0's cut); a row that
                // reaches a later day is P1's (the mixture). Both are properties
                // of the row, not a list of case shapes.
                if fr.until.is_none_or(|d| d <= date()) {
                    gcap0 += 1;
                } else {
                    gcapn += 1;
                }
            } else if !down.is_empty() {
                prios_differ = true;
            }
        }
        // **§8.2 STEP 2's ROWS, COMPARED TO THE SECOND AND BOTH WAYS** (W-31).
        // The kernel places these now, and a row it places that nothing compares
        // is this campaign's third shape — a part built correctly and never
        // joined to the thing it is part of (D50, gap 501, `Tree.lean`). So they
        // are asserted, not counted: start, end and item, in timeline order,
        // which is the same statement the walls have had since W-29 and which a
        // routine the kernel invents or drops fails as loudly as one placed at
        // the wrong minute.
        //
        // **THE STATEMENT WAS FIRST WRITTEN OVER ALL THE FORK'S ROUTINE ROWS AND
        // THAT WAS FALSE — REFUTED AND RESTATED HERE** (§3.2's rule, applied to
        // a test). Written strict it held on 163 rows a side over 143 cases and
        // 527 a side over 517, and then a 512-case draw refuted it: seed
        // `af6b8c79…`, kept (D46), four items on a LATE day with `lunch` and
        // `shower` switched on, where the fork places `shower` at 21:00 and the
        // kernel places nothing. **It is not a kernel bug and not a fork quirk.**
        // `shower` is `after-done:2d~1d` with no `pref:`, so it is neither
        // mandatory nor anchored, and BOTH planners defer it at step 2 —
        // `Planner.placeStep`'s third branch and `place_mandatory_and_pref`'s
        // final `r.deferred = true` are the same rule. The fork then places it at
        // **§8.2 step 6**, which the kernel has not written.
        //
        // **AND THE FIRST RESTATEMENT WAS WORSE THAN THE STATEMENT IT REPLACED,
        // WHICH IS WHY THE MEASUREMENT IS QUOTED AND NOT THE INTENTION.** Telling
        // a step-2 row from a step-6 row by the fork's own `deferred` flag — set
        // by all three of step 6's branches (`planner.rs:1657`, `:1673`, `:1694`)
        // and left false by step 2's — is a true split, and comparing the kernel
        // against the fork's NON-deferred rows alone makes **107 of 301** rows
        // differ: what the fork defers to step 6 the kernel places at step 2, and
        // the two land in the same minute anyway most of the time, because step
        // 6's lowest-energy free position is usually step 2's earliest free one.
        // A 35% disagreement rate is the signature of the wrong comparand. So the
        // comparison is the WHOLE routine row list on both sides — the statement
        // that nearly holds — and the fork's deferred count rides beside it as
        // its own census figure.
        //
        // **IT IS A COUNTER AND NOT AN ASSERTION**, which is W-30's own move for
        // README gap 2062 and for the same reason: the strict statement held on
        // 163 rows a side over 143 cases and 527 a side over 517, and then failed,
        // so it is not a law of these two planners. It is **not swallowed by an
        // exemption** — "the fork deferred nothing today" would cover every case
        // seen here and is exactly the widening D46 forbids — and **the generator
        // was not touched**. Both directions are counted, the seed replays on
        // every run from here, and README gap **2224** carries it. The price is
        // stated where it is paid: a perturbation that renames step 2's rows
        // without moving their minutes was caught by the assertion and by nothing
        // else in the file (driven, see the README block), and with the assertion
        // withdrawn it is caught by nothing.
        let krout: Vec<(i64, i64, String)> = plan["segments"]
            .as_array().map(Vec::as_slice).unwrap_or_default().iter()
            .filter(|s| s["kind"] == "routine")
            .map(|s| (s["start"].as_i64().unwrap_or(-1), s["stop"].as_i64().unwrap_or(-1),
                      s["item"].as_str().unwrap_or_default().to_string()))
            .collect();
        let fdefer = fork.segments.iter()
            .filter(|s| matches!(s.kind, SegKind::Routine) && s.flags.deferred)
            .count() as u64;
        let frout: Vec<(i64, i64, String)> = fork.segments.iter()
            .filter(|s| matches!(s.kind, SegKind::Routine))
            .map(|s| (rowwire::kernel_sec(s.start), rowwire::kernel_sec(s.end),
                      s.item.as_ref().map(ToString::to_string).unwrap_or_default()))
            .collect();
        let ronly = krout.iter().filter(|r| !frout.contains(r)).count() as u64;
        let fonly = frout.iter().filter(|r| !krout.contains(r)).count() as u64;

        // **AND EVERY ROW THE FORK ASSIGNED IS A ROW THE KERNEL ANSWERED FOR**
        // (W-31, README gap 2222). W-29 measured *"the fork assigned 184-209
        // rows the kernel had no candidate for"* (gap 1905) and W-30 reported
        // the figure closed — but the measurement it offered for that was
        // `rows unkeyable`, which counts a §7 row an id could not KEY because it
        // named two rows on one side. That is a different quantity, and this
        // campaign's commonest shape is a claim of having checked that was never
        // made. So the quantity the sentence is about is measured here.
        //
        // **The candidate half is 0 BY CONSTRUCTION and is therefore counted,
        // not asserted**: `fork_assigned` reads ids off the fork's own day and
        // `candidate_items` sends the fork's own candidate list, so the first is
        // a subset of the second and no draw can make it otherwise. A counter
        // that cannot move is not an instrument, and saying so is the point of
        // printing it.
        //
        // **The GRANT half can move and is asserted.** The kernel may answer
        // nothing for a candidate the capacity section refused by name, or for
        // one dropped past `Planner.maxCands` — `Planner.PlanReq.rankedCands`
        // is bounded by the candidate list's own length and nothing makes it
        // meet it. A day on which either happened would be a day where the two
        // planners were handed different work, which is exactly what gap 1905's
        // sentence warned bounds any comparison. It names the id.
        let wire_ids: BTreeSet<&str> = req["capacity"]["candidates"]["items"]
            .as_array().map(Vec::as_slice).unwrap_or_default().iter()
            .filter_map(|c| c["id"].as_str()).collect();
        let f_uncand = fa.iter().flat_map(|r| r.2.iter())
            .filter(|id| !wire_ids.contains(id.as_str())).count() as u64;
        let ungranted: Vec<&String> = fa.iter().flat_map(|r| r.2.iter())
            .filter(|id| !kg.contains_key(id.as_str())).collect();
        prop_assert!(
            ungranted.is_empty(),
            "the fork assigned {:?}, which the kernel's §7 answered nothing for",
            ungranted
        );

        let exempt = cands == 0;
        let kslots: Vec<(i64, i64)> = ka.iter().map(|r| (r.0, r.1)).collect();
        let fslots: Vec<(i64, i64)> = fa.iter().map(|r| (r.0, r.1)).collect();
        // **§8.2 step 5's SLOT GEOMETRY: asserted, DRIVEN, and found FALSE at a
        // larger case count — so it is COUNTED and the seed is kept** (W-30, D46).
        //
        // The W-29 repair step counted 1 to 6 slot disagreements per 64-case run.
        // Two of the causes were this arm asking the two planners two different
        // questions, and both are named and fixed above: the request spelled
        // `days: 7` where `kernel_capacity::rank` sends the fork's own
        // `priority::lookahead_days`, and it sent no `wake` at all, so
        // `Boundary.readWake` answered `.absent` and §8.5's `hsw` — which every
        // slot's energy level rides on — was measured from the weekday's expected
        // arrival on one side and from the day's own wake on the other. With both
        // sent, three 512-case runs counted **0** slot disagreements and the
        // assertion was written.
        //
        // **It then failed on the fourth**, and the case is in
        // `planner_invariants.proptest-regressions` (`3a39ad72…`): three items —
        // an `atomic` four-block one, a plain one and a batchable — on a LATE day
        // at home with one wall and the workout routine, where the kernel assigns
        // **two** consecutive hours and the fork assigns **one**. It is not a
        // different cut of the same day; it is one more slot taken, so the
        // subject is step 5's own budget-and-commitment walk and not §8.4.
        // README gap **2062** carries it. The count stays in the census line, at
        // 0 on most runs, so the step that settles it sees the number and the
        // seed replays on every run from here.
        let slots_differ = !exempt && kslots != fslots;
        // **AND THE ITEM COUNTER IS THE COMPLEMENT OF THE SLOT ONE, NOT A SUBSET
        // OF IT** — it requires that the slots AGREE — so the census label read "of
        // those" said the opposite of what it counted, exactly like the two labels
        // gap 2123 repaired one line of prose earlier. This run printed `slots
        // differ .. 1, of those .. ITEMS differ 3`, and 3 cannot be a subset of 1.
        // The antecedent is the NON-EXEMPT days, which is what both counters are
        // taken over; README gap 2131 (W-30 repair) carries the correction.
        let ids_differ = !exempt && !slots_differ && ka != fa;
        // The second fork day: the same request, ranked by the KERNEL's §7 answer.
        let cvec = w.candidates();
        let kprios = kernel_prios(&plan, &cvec);
        let fa2 = kprios.as_ref().map(|ps| {
            let day = planner::plan(&w.input(&w.state, w.now).with_ranking(&cvec, ps));
            fork_assigned(&day, w.now)
        });
        // **AND NOW THE ITEM IN THE SLOT IS ASSERTED — against the fork ranked by
        // the KERNEL, which is the wiring the binary ships** (W-30).
        //
        // `ka != fa` above is not a step-5 statement and this arm spent a run
        // pretending it was. The fork it compares there ran its OWN §7 pass over
        // its OWN lookahead, and the two lookaheads differ by two REGISTERED
        // divergences — **P1** for the future days' mixture and **P41** for day
        // 0's cut — so a different `p` reaches step 5 as a different rank order
        // and the assignment follows it. Measured over 527 cases: the whole §7
        // answer agreed on **four** days. An assertion gated on that is an
        // assertion that does not run.
        //
        // So the fork is asked the question the kernel was asked:
        // `PlanInput::with_ranking(cands, kernel_prios)`, which is exactly
        // `planning::build_ranked` → `Ctx::priorities` → `kernel_capacity::rank`
        // → `with_ranking` in the shipped binary. Then §8.2 step 5 is the only
        // thing left that can differ, and **it does not**: over three 512-case
        // runs, 167/167, 167/167 and 168/168 non-exempt days agree on every
        // assigned row, slot AND item.
        //
        // **This is the assertion the W-29 audit's perturbation has to get
        // past**: reversing `emit_segments`' slot→group map leaves the geometry
        // alone and moves the occupant, which `ka != fa`'s COUNTER could only
        // watch rise. Driven again at this commit in a clone — see the README
        // block — and it fails here now, naming both rows.
        let same_question = !exempt && fa2.is_some();
        if let (false, Some(fa2)) = (exempt, fa2.as_ref()) {
            prop_assert_eq!(
                &ka, fa2,
                "§8.2 step 5 assigned differently from the fork ranked by the kernel's own \
                 §7 answer (kernel {:?}, fork {:?})", ka, fa2
            );
        }

        let rows = plan["segments"].as_array().map(Vec::len).unwrap_or(0) as u64;
        let [cases, walls, seen, wdiff, bdiff, acmp, aexempt, pdiff, sdiff, iddiff, kres, fres,
             grows, gday0, gdays, gdups, gsame, frdays, krows, funcand, fungrant, rdefer, ronlyc,
             fonlyc, frows, rboth] = {
            let mut c = PLAN_CENSUS.lock().expect("census");
            c[0] += 1;
            c[1] += kw.len() as u64;
            c[2] += rows;
            c[3] += u64::from(window_differs);
            c[4] += u64::from(budget_differs);
            c[5] += if exempt { 0 } else { ka.len() as u64 };
            c[6] += u64::from(exempt);
            c[7] += u64::from(prios_differ);
            c[8] += u64::from(slots_differ);
            c[9] += u64::from(ids_differ);
            c[10] += k_res;
            c[11] += f_res;
            c[12] += g7;
            c[13] += gcap0;
            c[14] += gcapn;
            c[15] += gdup;
            c[16] += u64::from(same_question);
            c[17] += u64::from(fork_routines > 0);
            c[18] += krout.len() as u64;
            c[19] += f_uncand;
            c[20] += ungranted.len() as u64;
            c[21] += fdefer;
            c[22] += ronly;
            c[23] += fonly;
            c[24] += frout.len() as u64;
            c[25] += krout.iter().filter(|r| frout.contains(r)).count() as u64;
            *c
        };
        // **THE COMPARISON IS NOT VACUOUS**, asserted inside the fuzz: a run
        // that planned nothing on either side produces "every wall agreed" too
        // (AGENTS §9.2).
        // **THE FLOOR IS ABOUT A RUN, NOT ABOUT A PREFIX** (W-29 repair, README
        // gap 2016). It used to fire at 32 cases, and the census counts
        // proptest's PERSISTED REGRESSION replays first — shrunk cases, which
        // carry no wall BY CONSTRUCTION, because shrinking removes everything
        // the failure did not need. D46 keeps a drawn seed, so the replay list
        // only ever grows, and the 19th entry pushed the wall-less prefix past
        // 32: DRIVEN, three consecutive runs failed `no wall was compared in 35
        // cases` while the same runs compared 108-120 walls over their full 76.
        // The floor now fires once the GENERATED phase has run, which is what
        // "a run that planned nothing on either side" was always about.
        let generated: u64 = std::env::var("TM_PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        if cases >= generated {
            prop_assert!(walls > 0, "no wall was compared in {cases} cases");
            prop_assert!(seen >= cases, "the kernel answered {seen} rows over {cases} cases");
            // **AND NEITHER IS THE ASSIGNED COMPARISON** (W-29 repair, README
            // gap 2005). This is the assertion whose absence let the arm ship
            // green while `assigned-rows compared` was 0 in every run: an
            // exemption every case satisfies is not an exemption, and it fails
            // HERE rather than in an auditor's census.
            prop_assert!(
                aexempt < cases,
                "every one of {cases} cases was exempt from the assigned-row comparison"
            );
            prop_assert!(acmp > 0, "no assigned row was compared in {cases} cases");
            // **AND NEITHER IS §7's** (W-30). `grant_fields` is the reader of a
            // comparison, and this campaign's own lesson is that the reader of a
            // comparison that does not run is not a tested reader (README gap
            // 2015). A run in which no §7 row was keyable compares nothing.
            prop_assert!(grows > 0, "no §7 row was compared in {cases} cases");
            // **AND THE ASSIGNMENT'S OWN COMPARISON HAS A FLOOR** (W-30). The
            // population is a third of the cases (167 of 527, measured), so a run
            // in which it is empty is a run in which the second fork call stopped
            // happening — and an assertion that does not run is the defect this
            // arm shipped with (README gap 2005).
            prop_assert!(
                gsame > 0,
                "step 5's assignment was asserted on no day of {cases} cases"
            );
            // **AND STEP 2 HAS ITS OWN THREE FLOORS** (W-31, repaired W-31 —
            // README gap 2265). The sentence here used to open "the routine rows
            // are asserted equal above", and they are NOT: two hundred lines up,
            // in the same commit, the equality was withdrawn to a counter and
            // says so — "IT IS A COUNTER AND NOT AN ASSERTION". So the floors
            // were guarding the vacuity of an assertion that does not exist.
            //
            // AND THE QUANTITY THEY TESTED WAS NOT THE ONE THE CAPTION NAMED.
            // `c[18] += krout.len()` is the number of routine rows THE KERNEL
            // placed, and the census line printed it as "routine rows compared":
            // nothing is compared into it, and on a planted run it read 279
            // while 279 kernel rows and 281 fork rows disagreed. The caption
            // names what is counted now — `krows` and `frows`, one per side —
            // and a third figure, `rboth`, is the rows that are on BOTH sides,
            // which is the only one of the three the word "compared" fits.
            //
            // The floor is `rboth`, because a run in which the `routines` key
            // silently stopped decoding gives `krows > 0` on the kernel side and
            // agrees with nothing (AGENTS §5.2's vacuous theorem, one layer in).
            // Three floors and not one: either of the others alone would let the
            // rest rot.
            prop_assert!(krows > 0, "the kernel placed no §8.2 step 2 routine row in {cases} cases");
            prop_assert!(
                rboth > 0,
                "not one §8.2 step 2 routine row agreed with the fork's in {cases} cases, \
                 so the comparison the counters below report is over two disjoint lists"
            );
            prop_assert!(
                frdays > 0,
                "the fork placed no routine on any of {cases} cases, so the days the \
                 `routines` exemption used to remove are not being drawn"
            );
        }
        eprintln!(
            "planner_invariants plan census: {cases} cases, {walls} walls compared, \
             {seen} kernel rows, window-differs {wdiff}, budget-differs {bdiff}, \
             assigned-rows compared {acmp}, cases exempt {aexempt}, \
             cases whose §7 answers differ {pdiff}, \
             NON-exempt days whose slots differ from the fork's OWN-§7 day {sdiff}, \
             of the NON-EXEMPT days, whose slots agree and whose ITEMS differ {iddiff}, \
             §7 rows compared {grows}, capacity differs to TODAY (P41) {gday0}, \
             beyond today (P1) {gdays}, rows unkeyable {gdups}, \
             days whose assignment was ASSERTED against the kernel-ranked fork {gsame}, \
             §8.2 step 2 routine rows the kernel placed {krows}, the fork placed \
             {frows}, on BOTH sides {rboth}, on {frdays} days the fork \
             placed one, fork-assigned ids with no kernel CANDIDATE {funcand} \
             (0 by construction), with no kernel §7 GRANT {fungrant}, \
             fork routine rows the fork DEFERRED to §8.2 step 6, which the kernel \
             has not written {rdefer}, step-2 rows only the kernel placed {ronlyc}, \
             only the fork placed {fonlyc} (gap 2224), \
             energy-less work rows from now: kernel {kres}, fork {fres}"
        );
        // **THE TWO DISAGREEMENTS ARE KEPT, NOT HIDDEN** (D46). A window or a
        // budget that differs is a finding: README gap 320's two readers, one of
        // them wrong, and the parity register is where a deliberate divergence
        // goes (check 10 says the next free number). They are asserted LAST so
        // the wall comparison above is reached on every case.
        prop_assert!(!window_differs, "§8.1's window: kernel ({klo}, {khi}), fork ({flo}, {fhi})");
        prop_assert!(
            !budget_differs,
            "§8.1's budget: kernel {:?}, fork {}", plan["budgetBlocks"], fork.budget_blocks
        );
    }
}
