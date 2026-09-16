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

use std::collections::BTreeSet;

use chrono::{DateTime, Duration, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use proptest::prelude::*;
use tm_core::capacity::{self, local_dt};
use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::Replay;
use tm_core::model::{Id, Loc, Shape};
use tm_core::planner::{self, DayPlan, PlanInput, SegKind, Segment};
use tm_core::priority::{self, Candidate, Prio};
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
    )
        .prop_map(|(ci, k, est_b, small, due_in, dep, loc_home, atomic)| Spec {
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
}

fn build(case: &Case) -> World {
    let cfg = Config::default();
    let tz = cfg.tz;
    let week = week_text(case);
    let cal = calendar_text(case);
    let routines = routines_text(case);
    let optionals = if case.optionals { OPTIONALS } else { "" };
    let tree = Tree::from_texts(
        &[
            ("week/2026-W37.md", week.as_str()),
            ("calendar/2026-W37.md", cal.as_str()),
            ("routines.md", routines.as_str()),
            ("optional.md", optionals),
        ],
        &cfg,
    );
    let replay = chokepoint::replay_of_text(&log_text(case, tz), tz);
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
        replay,
        model: Model::default(),
        now,
        state,
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

        // Monotone rank: equal p and ci → the earlier line is never the one
        // left out. The running item is excepted: §9 gave it its slot.
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
                let (first, second) = if a.own_order <= b.own_order { (a, b) } else { (b, a) };
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



