//! §7 end to end on the `plan-basic` fixture for Monday 2026-09-07 10:42:
//! the whole candidate set with its class, `p`, `u` and `fits` (§12.2's
//! columns), the assignment order (§7.4), the batches (§7.5) and
//! `tm plan --explain ^d1` (§13). The `planner.rs` types §8 defines are
//! checked at the end, since `DayPlan` carries the `Prio`s.
//!
//! The capacity is synthetic on purpose, so the snapshot pins §7's
//! arithmetic and not `capacity::lookahead`'s: today keeps half a day
//! (30/30/60/60 minutes at energy 2/3/4/5 = 3 blocks) and every later day a
//! whole one (60/60/120/120 = 6 blocks), for as many days as the furthest
//! deadline needs (`priority::lookahead_days` → 2026-11-20, 75 days).

use std::collections::BTreeMap;

use chrono::{DateTime, Duration, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use tm_core::capacity::{local_dt, DayCapacity};
use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::{self, Replay};
use tm_core::model::Id;
use tm_core::planner::{self, DayPlan, PlanInput, SegFlags, SegKind, Segment};
use tm_core::priority::{self, Candidate, Ineligible, Prio};
use tm_core::store::{MemStore, RuntimeState, Store};
use tm_core::tree::Tree;

const TZ: Tz = Tz::America__Chicago;

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/{name}", env!("CARGO_MANIFEST_DIR"))
}

fn date(s: &str) -> NaiveDate {
    NaiveDate::parse_from_str(s, "%Y-%m-%d").expect("date")
}

fn at(day: &str, h: u32, m: u32) -> DateTime<Tz> {
    local_dt(
        TZ,
        date(day),
        NaiveTime::from_hms_opt(h, m, 0).expect("time"),
    )
}

/// The `plan-basic` tree, its config, and an empty replay (the fixture has no
/// `.tm/log.jsonl`).
fn plan_basic() -> (Tree, Config, Replay) {
    let store = MemStore::from_dir(fixture("plan-basic")).expect("fixture readable");
    let plan = store.read_tree().expect("tree parses");
    let tree = Tree::build(&plan.files, &plan.config);
    assert!(tree.problems().is_empty(), "{:?}", tree.problems());
    let replay = log::replay(&[], None, plan.config.tz);
    (tree, plan.config, replay)
}

/// Today keeps half a day, later days a whole one (see the module docs).
fn caps(days: u32) -> Vec<DayCapacity> {
    let start = date("2026-09-07");
    (0..days as i64)
        .map(|i| {
            let mut d = DayCapacity::empty(start + Duration::days(i));
            d.minutes_at_level = if i == 0 {
                [0, 0, 30, 30, 60, 60]
            } else {
                [0, 0, 60, 60, 120, 120]
            };
            d
        })
        .collect()
}

fn today_candidates(tree: &Tree, cfg: &Config, replay: &Replay) -> Vec<Candidate> {
    priority::collect_candidates(
        tree,
        replay,
        cfg,
        &Model::default(),
        date("2026-09-07"),
        at("2026-09-07", 10, 42),
    )
}

fn find<'a>(cands: &'a [Candidate], id: &str) -> &'a Candidate {
    cands
        .iter()
        .find(|c| c.id.as_str() == id)
        .unwrap_or_else(|| panic!("no candidate {id}"))
}

fn fmt_u(u: Option<f64>) -> String {
    match u {
        Some(v) if v.is_finite() => format!("{v:.3}"),
        Some(_) => "inf".to_string(),
        None => "-".to_string(),
    }
}

/// One row per candidate: the §12.2 Queue columns plus the class §7.2 gave
/// it.
fn table(cands: &[Candidate], prios: &[Prio], cfg: &Config) -> String {
    let block = cfg.block_min();
    let mut out = format!(
        "{:<16} {:>2} {:<11} {:>2} {:>3} {:>6} {:>4} {:>6} {:>6} {:>10} {:<10}  {}\n",
        "id", "p", "class", "k", "ci", "u", "bin", "need", "fits", "until", "inst", "title"
    );
    for (c, p) in cands.iter().zip(prios) {
        assert_eq!(c.id, p.id, "compute keeps the candidate order");
        out.push_str(&format!(
            "{:<16} {:>2} {:<11} {:>2} {:>3} {:>6} {:>4} {:>6} {:>6} {:>10} {:<10}  {}\n",
            c.id.as_str(),
            p.p,
            p.class.label(),
            p.k,
            c.ci,
            fmt_u(p.u),
            p.bin.map_or("-".to_string(), |b| format!("+{b}")),
            priority::fmt_blocks(p.need_min, block),
            priority::fmt_blocks(p.allocation_min, block),
            p.until.map_or("-".to_string(), |d| d.to_string()),
            c.instance.map_or("-".to_string(), |k| k.to_string()),
            c.title,
        ));
    }
    out
}

// ---------------------------------------------------------------------------
// (h) the whole day, sorted
// ---------------------------------------------------------------------------

#[test]
fn plan_basic_priorities_and_order() {
    let (tree, cfg, replay) = plan_basic();
    let cands = today_candidates(&tree, &cfg, &replay);
    let days = priority::lookahead_days(&cands, date("2026-09-07"));
    assert_eq!(days, 75, "the furthest deadline is ^d2 on 2026-11-20");
    let caps = caps(days);

    let prios = priority::compute(&cands, &caps, &BTreeMap::new(), &cfg, date("2026-09-07"));
    insta::assert_snapshot!("plan_basic_priorities", table(&cands, &prios, &cfg));

    // `laundry` is `on-miss:persist` and the fixture has no log, so last
    // week's window was missed and carries into today (§5.3: overdue,
    // mandatory, `p = 0` by §7.2). It is the routine's *only* candidate: the
    // carried miss and this week's occurrence are one obligation, keyed on
    // the newest occurrence so that doing it once discharges the carry.
    let laundry: Vec<(&str, u8)> = cands
        .iter()
        .zip(&prios)
        .filter(|(c, _)| c.id.as_str() == "laundry")
        .map(|(c, p)| {
            (
                match c.instance {
                    Some(k) if k.to_string() == "2026-09-07" => "this week",
                    _ => "carried",
                },
                p.p,
            )
        })
        .collect();
    assert_eq!(laundry, vec![("this week", 0)]);

    let queue = priority::sorted(&prios, &cands);
    let order: Vec<&str> = queue.iter().map(Id::as_str).collect();
    insta::assert_snapshot!("plan_basic_order", order.join("\n"));

    // §8.2 step 1 places the Intervals that cover today: `^g1` (12:50 today),
    // not `^x1` (the Midterm on 2026-10-20). Both are walls, only one is this
    // day's, and the other is not in the queue at all.
    assert!(find(&cands, "g1").is_wall && find(&cands, "g1").wall_today);
    assert!(find(&cands, "x1").is_wall && !find(&cands, "x1").wall_today);
    assert_eq!(order.first(), Some(&"g1"));
    assert!(!queue.contains(&Id::new("x1")));

    // §5.1: the `[?]` item is listed as waiting rather than dropped, and it
    // takes no slot.
    let a4 = find(&cands, "a4");
    assert!(a4.waiting);
    assert_eq!(a4.ineligible_reason(), Some(Ineligible::Waiting));
    assert!(!queue.contains(&Id::new("a4")));

    // The queue is non-decreasing in p after the walls, which come first.
    // (Paired by position, since two candidates can share an id.)
    let walls: usize = cands
        .iter()
        .filter(|c| c.is_wall && c.wall_today && c.eligible())
        .count();
    let ranked = priority::sorted_candidates(&prios, &cands);
    assert_eq!(ranked.len(), queue.len());
    let ps: Vec<u8> = ranked
        .iter()
        .skip(walls)
        .map(|c| {
            let i = cands
                .iter()
                .position(|x| std::ptr::eq(x, *c))
                .expect("a candidate of this list");
            prios[i].p
        })
        .collect();
    assert!(ps.windows(2).all(|w| w[0] <= w[1]), "{ps:?}");

    // §5.5: the blocked item is diagnosed, not dropped.
    let blocked: Vec<String> = priority::blocked(&cands)
        .into_iter()
        .map(|(id, why)| format!("{}: {why}", id.as_str()))
        .collect();
    insta::assert_snapshot!("plan_basic_blocked", blocked.join("\n"));
    assert!(!queue.contains(&Id::new("t5")));

    // §7.5: the batches the planner consumes, in assignment order — all of
    // them, so the snapshot also pins what is *not* merged (§8.2 places the
    // window instances inside their own windows, not in a shared block).
    let groups = priority::batches(&ranked, &cfg);
    let batched: Vec<String> = groups
        .iter()
        .map(|b| {
            format!(
                "{} ci{} {}m: {}",
                if b.is_batch() { "batch" } else { "     " },
                b.ci,
                b.total_min,
                b.ids.iter().map(Id::as_str).collect::<Vec<_>>().join(" · ")
            )
        })
        .collect();
    insta::assert_snapshot!("plan_basic_batches", batched.join("\n"));
    assert!(
        !groups.iter().any(|b| b.is_batch()),
        "every small item here carries a window of its own"
    );

    // §10.2: what tomorrow's hysteresis reads.
    let stored = priority::priorities_for_state(&prios);
    assert_eq!(stored.get(&Id::new("d1")), Some(&4));
    assert!(!stored.contains_key(&Id::new("x1")));
    // `laundry` is today's carried `persist` instance: §7.2's `p = 0`, and
    // that is the baseline tomorrow compares against.
    assert_eq!(stored.get(&Id::new("laundry")), Some(&0));

    // §11 deadline health for the fixture day.
    let health = priority::deadline_health(&prios, &cands, date("2026-09-07"));
    insta::assert_json_snapshot!("plan_basic_deadline_health", health);
}

// ---------------------------------------------------------------------------
// (i) `tm plan --explain ^d1` (§13)
// ---------------------------------------------------------------------------

/// `^d1` is §4.3's `- [ ] 4 6b CS 234 pset 2 @O3 due:2026-09-11T23:59
/// max:2b/d`: root `^O3` is `!3` so `k = 3`, `need = 360 × 1.3 = 468`
/// (7.8b), and the capacity at energy ≥ 4 through Friday is
/// `120 + 4 × 240 = 1080` (18b), so `u = 0.433` → `+1` → `p = 4`.
#[test]
fn explain_d1_matches_the_spec_shape() {
    let (tree, cfg, replay) = plan_basic();
    let cands = today_candidates(&tree, &cfg, &replay);
    let caps = caps(priority::lookahead_days(&cands, date("2026-09-07")));
    let prios = priority::compute(&cands, &caps, &BTreeMap::new(), &cfg, date("2026-09-07"));

    let d1 = Id::new("d1");
    let prio = prios
        .iter()
        .find(|p| p.id == d1)
        .expect("^d1 has a priority");
    assert_eq!(prio.k, 3);
    assert_eq!(prio.need_min, 468);
    assert_eq!(prio.avail_min, 1080);
    assert_eq!(prio.bin, Some(1));
    assert_eq!(prio.p, 4);

    let text = priority::explain(&d1, &cands, &prios, &cfg);
    insta::assert_snapshot!("explain_d1", text);

    // The structured form is the same line, and leaves the planner's half
    // empty until a plan exists.
    let mut ex = priority::explanation(&d1, &cands, &prios, &cfg).expect("an explanation");
    assert_eq!(ex.to_string(), text);
    assert!(ex.slot_part.is_none());
    ex.slot_part = Some("slot 11:50 energy 4, ci 4, gap 0".to_string());
    insta::assert_snapshot!("explain_d1_with_slot", ex.to_string());

    // A blocked item says so where §13 prints `deps ok`.
    let t5 = priority::explain(&Id::new("t5"), &cands, &prios, &cfg);
    insta::assert_snapshot!("explain_t5_blocked", t5);
    // An impossible one names the shortfall (§7.3).
    let hot = priority::explain(&Id::new("nope"), &cands, &prios, &cfg);
    assert_eq!(hot, "^nope is not a candidate today");
}

/// The §7.3 banner text for an item that cannot make its deadline, on the
/// same fixture: `^d1` (CS 234 pset 2, 6b at ci 4, due Friday) against a week
/// of 30-minute days.
///
/// The scarcity has to be real. Sizing the capacity vector *shorter* than the
/// deadline produces the same banner from an artefact — the days beyond the
/// vector are missing, not empty — so this test keeps the full
/// `lookahead_days` horizon and starves it instead, and checks that `^x2`
/// (due 2026-10-20, far enough away for 30 minutes a day to add up) stays
/// comfortably dated in the very same run.
#[test]
fn explain_names_the_shortfall_when_impossible() {
    let (tree, cfg, replay) = plan_basic();
    let cands = today_candidates(&tree, &cfg, &replay);
    let today = date("2026-09-07");
    let days = priority::lookahead_days(&cands, today);
    let thin: Vec<DayCapacity> = (0..days as i64)
        .map(|i| {
            let mut d = DayCapacity::empty(today + Duration::days(i));
            d.minutes_at_level = [0, 0, 0, 0, 0, 30];
            d
        })
        .collect();

    let prios = priority::compute(&cands, &thin, &BTreeMap::new(), &cfg, today);
    // need 6b × 1.3 = 468 min, against 5 × 30 = 150 min through Friday.
    let d1 = prios.iter().find(|p| p.id == Id::new("d1")).expect("^d1");
    assert!(d1.is_impossible());
    assert_eq!((d1.need_min, d1.avail_min, d1.shortfall_min), (468, 150, 318));
    let text = priority::explain(&Id::new("d1"), &cands, &prios, &cfg);
    insta::assert_snapshot!("explain_d1_impossible", text);

    // The same run, the same capacity: the October deadline is not impossible,
    // which is what the sibling snapshot says too.
    let x2 = prios.iter().find(|p| p.id == Id::new("x2")).expect("^x2");
    assert!(!x2.is_hot(), "{x2:?}");
    assert_eq!(x2.class.label(), "dated");

    let health = priority::deadline_health(&prios, &cands, today);
    assert_eq!(health.impossible, 1);
}

// ---------------------------------------------------------------------------
// planner.rs types (§8)
// ---------------------------------------------------------------------------

/// `plan()` returns a valid, hashable `DayPlan` with §8.1's window and budget
/// from `state.json`.
///
/// (M4 note: the three assertions this test used to make about the *stub* —
/// no segments, no block minutes, a "planner not implemented" note — were
/// replaced when §8.2 landed. Everything else, including the whole hash
/// contract below, is unchanged.)
#[test]
fn planner_types_carry_the_window_budget_and_hash() {
    let (tree, cfg, replay) = plan_basic();
    let model = Model::default();
    let mut runtime = RuntimeState {
        date: Some(date("2026-09-07")),
        budget: Some(6),
        ..RuntimeState::default()
    };
    runtime.window = Some((
        NaiveTime::from_hms_opt(7, 0, 0).expect("time"),
        NaiveTime::from_hms_opt(16, 0, 0).expect("time"),
    ));
    let input = PlanInput::new(
        &tree,
        &replay,
        &cfg,
        &model,
        &runtime,
        at("2026-09-07", 10, 42),
    );
    let day = planner::plan(&input);
    assert_eq!(day.date, date("2026-09-07"));
    assert_eq!(
        day.window,
        (at("2026-09-07", 7, 0), at("2026-09-07", 16, 0))
    );
    assert_eq!(day.budget_blocks, 6);
    assert!(!day.segments.is_empty(), "§8.2 fills the day");
    assert!(day.block_minutes() <= 6 * 60, "§8.3: no overbooking");

    // Purity: the same input gives the same plan and the same hash.
    assert_eq!(planner::plan(&input), day);
    assert_eq!(day.hash(), planner::plan(&input).hash());

    // The hash contract itself is checked on a plan built by hand, so the
    // segment under test is the only one in it (M4: `plan()` now returns a
    // full day, and its first segment carries flags of its own).
    let hand = DayPlan::empty(day.date, day.window, day.budget_blocks);
    let empty_hash = hand.hash();
    assert_eq!(empty_hash.len(), 16);
    assert!(empty_hash.chars().all(|c| c.is_ascii_hexdigit()));
    assert_eq!(hand.hash(), empty_hash);

    // A different set of segments hashes differently; the diagnostics do not
    // enter the hash.
    let mut moved = hand.clone();
    moved.segments.push(Segment {
        start: at("2026-09-07", 11, 0),
        end: at("2026-09-07", 12, 0),
        kind: SegKind::Block,
        energy: Some(4),
        item: Some(Id::new("d1")),
        instance: None,
        flags: SegFlags {
            planned_min: Some(60),
            multiplier: Some(1.0),
            ..SegFlags::default()
        },
    });
    assert_ne!(moved.hash(), empty_hash);
    assert_eq!(moved.block_minutes(), 60);
    let mut noted = hand.clone();
    noted.diagnostics.rest_debt_min = 40;
    assert_eq!(noted.hash(), empty_hash);

    // §10.1: the hash says whether the plan *moved*. Working through the day
    // — marking the block done, becoming the current block, being drawn as
    // the arrival ghost, gaining a note — moves nothing, so a replan that
    // changes only those is not a replan.
    let one_block = moved.hash();
    for flip in [
        |f: &mut SegFlags| f.done = true,
        |f: &mut SegFlags| f.current = true,
        |f: &mut SegFlags| f.ghost = true,
        |f: &mut SegFlags| f.underused = true,
        |f: &mut SegFlags| f.hot = true,
        |f: &mut SegFlags| f.mandatory = true,
        |f: &mut SegFlags| f.deferred = true,
        |f: &mut SegFlags| f.note = Some("due today".to_string()),
    ] {
        let mut progressed = moved.clone();
        flip(&mut progressed.segments[0].flags);
        assert_ne!(progressed, moved);
        assert_eq!(
            progressed.hash(),
            one_block,
            "progress flags must not move the plan hash"
        );
    }
    // Moving the block, re-sizing it or putting another item in it does.
    let mut later = moved.clone();
    later.segments[0].start = at("2026-09-07", 11, 30);
    assert_ne!(later.hash(), one_block);
    let mut other = moved.clone();
    other.segments[0].item = Some(Id::new("t4"));
    assert_ne!(other.hash(), one_block);
    let mut resized = moved.clone();
    resized.segments[0].flags.planned_min = Some(96);
    assert_ne!(resized.hash(), one_block);

    // The whole plan serializes for `tm plan --json`.
    let json = serde_json::to_string(&moved).expect("DayPlan serializes");
    assert!(json.contains("\"budget_blocks\":6"), "{json}");

    // A `DayPlan` built by hand round-trips through the same helpers.
    let bare = DayPlan::empty(
        date("2026-09-08"),
        (at("2026-09-08", 7, 0), at("2026-09-08", 15, 0)),
        6,
    );
    assert!(bare.diagnostics.notes.is_empty());
    assert_eq!(bare.priorities, Vec::new());
}

/// §8.1 with no window in `state.json` — `tm plan` before `tm arrive`, or
/// after a rollover cleared it: `arrival = runtime.arrival, else now`,
/// `end = min(arrival + window_hours, window_cap)`. Not a zero-length window
/// with a full budget in it.
#[test]
fn plan_without_a_stored_window_uses_the_spec_formula() {
    let (tree, cfg, replay) = plan_basic();
    let model = Model::default();
    let runtime = RuntimeState {
        date: Some(date("2026-09-07")),
        ..RuntimeState::default()
    };
    assert!(runtime.window.is_none() && runtime.budget.is_none());

    let now = at("2026-09-07", 10, 42);
    let input = PlanInput::new(&tree, &replay, &cfg, &model, &runtime, now);
    let day = planner::plan(&input);
    // 10:42 + 8h = 18:42, inside the 19:00 cap, plus §8.1's `Σ duration(walls
    // inside the window)` — the 12:50–13:50 meeting — is 19:42. (Before M4 the
    // planner passed no walls to `window_and_budget` and this read 18:42.)
    assert_eq!(day.window, (now, at("2026-09-07", 19, 42)));
    assert_eq!(day.budget_blocks, 6);

    // `tm arrive` at 07:00 without a stored window: the window starts there.
    let arrived = RuntimeState {
        date: Some(date("2026-09-07")),
        arrival: Some(NaiveTime::from_hms_opt(7, 0, 0).expect("time")),
        ..RuntimeState::default()
    };
    let input = PlanInput::new(&tree, &replay, &cfg, &model, &arrived, now);
    let day = planner::plan(&input);
    // 07:00 + 8h = 15:00, plus the 12:50–13:50 wall inside it, is 16:00 —
    // which is exactly the window `.tm/state.json` stores in §4.3.
    assert_eq!(
        day.window,
        (at("2026-09-07", 7, 0), at("2026-09-07", 16, 0))
    );

    // A late arrival is capped at `window_cap` (19:00), never negative.
    let late = RuntimeState {
        date: Some(date("2026-09-07")),
        arrival: Some(NaiveTime::from_hms_opt(20, 0, 0).expect("time")),
        ..RuntimeState::default()
    };
    let input = PlanInput::new(&tree, &replay, &cfg, &model, &late, now);
    let day = planner::plan(&input);
    assert_eq!(day.window.0, at("2026-09-07", 20, 0));
    assert_eq!(day.window.1, at("2026-09-07", 20, 0));
}
