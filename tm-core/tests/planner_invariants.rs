//! §8.3's invariants as `proptest` properties over random trees, random logs
//! and a random `now` — "tests first for §8.3 invariants: they are the
//! specification" (§17.2).
//!
//! Each case builds a week file of up to 40 items with random `ci`, `!k`,
//! estimate, deadline, dependency, `loc:` and `atomic`, up to two calendar
//! walls on the planning day, a log with a random number of finished blocks
//! and an optional energy report, and plans at a random instant inside the
//! window. Then every invariant of §8.3 is checked:
//!
//! * **purity** — the same input twice gives an identical `DayPlan`;
//! * **stability** — a replan an hour later changes no segment that had ended;
//! * **no overbooking** — Σ planned Block minutes ≤ `remaining_budget ×
//!   block_min`, no segment overlaps a Wall, nothing is planned after
//!   wind-down, and no two placements overlap;
//! * **energy filter** — every Block has `item.ci ≤ slot.energy`;
//! * **monotone rank** — equal `p` and equal `ci`: the lower line order is
//!   never left unassigned while the other is assigned;
//! * **tail-drop** — taking a block off the budget removes a tail and
//!   re-shuffles nothing;
//! * **HOT before queue**, **IMPOSSIBLE never dropped**, **walls never
//!   moved**.
//!
//! Where a property needs a fair comparison it is restricted to the
//! candidates the rule is written about — a `loc:`-constrained, `atomic` or
//! `max:`-capped item is skipped by §8.2 step 5 for reasons the invariant is
//! not about, and the Active item is excepted by §8.3 itself.

use std::collections::BTreeSet;

use chrono::{DateTime, Duration, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use proptest::prelude::*;
use tm_core::capacity::{self, local_dt};
use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::{self, Log, Replay};
use tm_core::model::{Id, Loc, Shape};
use tm_core::planner::{self, DayPlan, PlanInput, SegKind, Segment};
use tm_core::priority::{self, Candidate, Prio};
use tm_core::store::RuntimeState;
use tm_core::tree::Tree;

const DAY: &str = "2026-09-07";
const MAX_ITEMS: usize = 40;

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
}

fn spec_strategy() -> impl Strategy<Value = Spec> {
    (
        0u8..=5,
        1u8..=4,
        1u32..=4,
        prop::option::of(0u8..=9),
        prop::option::of(0usize..MAX_ITEMS),
        any::<bool>(),
        any::<bool>(),
    )
        .prop_map(|(ci, k, est_b, due_in, dep, loc_home, atomic)| Spec {
            ci,
            k,
            est_b,
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
    )
        .prop_map(|(items, walls, now_idx, done_blocks, report)| Case {
            items,
            walls: walls
                .into_iter()
                .map(|(hour, hours)| WallSpec { hour, hours })
                .collect(),
            now_idx,
            done_blocks,
            report,
        })
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
        let mut line = format!("- [ ] {} {}b Item{i} !{}", sp.ci, sp.est_b, sp.k);
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
    s
}

/// `now` — 07:00, 08:30, 10:00 or 12:00 — and the blocks the log may hold.
fn now_of(tz: Tz, idx: usize) -> DateTime<Tz> {
    match idx {
        0 => at(tz, 7, 0),
        1 => at(tz, 8, 30),
        2 => at(tz, 10, 0),
        _ => at(tz, 12, 0),
    }
}

fn log_text(case: &Case, tz: Tz) -> String {
    let now = now_of(tz, case.now_idx);
    let room = ((now - at(tz, 7, 0)).num_minutes() / 60).max(0) as u32;
    let done = case.done_blocks.min(room).min(case.items.len() as u32);
    let mut s = String::from(
        concat!(
            r#"{"t":"2026-09-07T06:00:00-05:00","ev":"wake","slept_min":480}"#,
            "\n",
            r#"{"t":"2026-09-07T07:00:00-05:00","ev":"arrive","loc":"lounge","window":["07:00","16:00"],"budget":6}"#,
            "\n",
        ),
    );
    for j in 0..done {
        let id = id_of('z', j as usize);
        let start = 7 + j;
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
            "{{\"t\":\"{DAY}T07:05:00-05:00\",\"ev\":\"energy\",\"pred\":4,\"rep\":{rep},\"hsw\":1.08,\"loc\":\"lounge\"}}\n"
        ));
    }
    s
}

struct World {
    tree: Tree,
    cfg: Config,
    log: Log,
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
    let tree = Tree::from_texts(
        &[
            ("week/2026-W37.md", week.as_str()),
            ("calendar/2026-W37.md", cal.as_str()),
        ],
        &cfg,
    );
    let log = Log::parse(&log_text(case, tz));
    let replay = log::replay(&log.entries, None, tz);
    let state = RuntimeState {
        date: Some(date()),
        wake: Some(NaiveTime::from_hms_opt(6, 0, 0).expect("time")),
        arrival: Some(NaiveTime::from_hms_opt(7, 0, 0).expect("time")),
        loc: Some("lounge".to_string()),
        window: Some((
            NaiveTime::from_hms_opt(7, 0, 0).expect("time"),
            NaiveTime::from_hms_opt(16, 0, 0).expect("time"),
        )),
        budget: Some(6),
        ..RuntimeState::default()
    };
    World {
        tree,
        cfg,
        log,
        replay,
        model: Model::default(),
        now: now_of(tz, case.now_idx),
        state,
    }
}

impl World {
    fn input<'a>(&'a self, state: &'a RuntimeState, now: DateTime<Tz>) -> PlanInput<'a> {
        PlanInput::new(
            &self.tree,
            &self.log,
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

        // --- no overbooking ---------------------------------------------
        let remaining = capacity::remaining_budget(6, w.replay.blocks_done(date()));
        prop_assert!(
            day.planned_block_minutes(w.now) <= remaining * block_min,
            "{} planned minutes for {remaining} blocks",
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
        // with ci ≥ 4 after wind-down").
        let wind = at(tz, 21, 30);
        for seg in day.segments.iter().filter(|s| s.kind.is_work()) {
            prop_assert!(seg.end <= wind, "work after wind-down: {seg:?}");
        }

        // --- walls never moved -------------------------------------------
        for seg in day.segments.iter().filter(|s| s.kind == SegKind::Wall) {
            let id = seg.item.clone().expect("a wall names its item");
            let Shape::Interval { start, end } = w.tree.effective_shape(&id) else {
                prop_assert!(false, "{id} is not an interval");
                unreachable!()
            };
            let s = local_dt(tz, start.date(), start.time());
            let e = local_dt(tz, end.date(), end.time());
            prop_assert!(seg.start >= s - Duration::hours(24) && seg.end <= e);
        }

        // --- energy filter ------------------------------------------------
        let cands = w.candidates();
        let ci_of = |id: &Id| cands.iter().find(|c| c.id == *id).map_or(0, |c| c.ci);
        for seg in day.segments.iter().filter(|s| s.kind.is_work() && s.start >= w.now) {
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
        // left out.
        for (i, a) in cands.iter().enumerate() {
            if !comparable(a) {
                continue;
            }
            for (j, b) in cands.iter().enumerate().skip(i + 1) {
                if !comparable(b) || a.ci != b.ci || prios[i].p != prios[j].p {
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

        // HOT before queue: an eligible p = 0 candidate that fits some slot is
        // never left out while a p > 0 candidate of the same or lower ci works.
        for (i, hot) in cands.iter().enumerate() {
            if !comparable(hot) || prios[i].p != 0 || done.contains(&hot.id) || hot.ci > max_energy {
                continue;
            }
            for (j, other) in cands.iter().enumerate() {
                if !comparable(other) || prios[j].p == 0 || !done.contains(&other.id) {
                    continue;
                }
                prop_assert!(
                    other.ci < hot.ci,
                    "{} (p {}) works while HOT {} (p 0, ci {}) does not",
                    other.id,
                    prios[j].p,
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
                    if comparable(other) && done.contains(&other.id) && other.ci >= c.ci {
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
        let later = planner::plan(&w.input(&w.state, w.now + Duration::hours(1)));
        for seg in day.segments.iter().filter(|s| s.end <= w.now) {
            prop_assert!(
                later.segments.contains(seg),
                "a replan moved a settled segment: {seg:?}"
            );
        }
    }
}
