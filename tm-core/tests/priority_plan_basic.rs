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
use tm_core::log::{self, Log, Replay};
use tm_core::model::Id;
use tm_core::planner::{self, DayPlan, PlanInput, SegFlags, SegKind, Segment};
use tm_core::priority::{self, Candidate, Prio};
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

    // `laundry` is `on-miss:persist` and the fixture has no log, so it has two
    // pending instances: last week's carried one (§5.3: overdue, mandatory)
    // and this week's. They share an id, so the pairing of candidate to
    // priority is by position, not by id.
    let laundry: Vec<(&str, u8)> = cands
        .iter()
        .zip(&prios)
        .filter(|(c, _)| c.id.as_str() == "laundry")
        .map(|(c, p)| {
            (
                match c.instance {
                    Some(k) if k.to_string() == "2026-08-31" => "carried",
                    _ => "this week",
                },
                p.p,
            )
        })
        .collect();
    assert_eq!(laundry, vec![("carried", 0), ("this week", 5)]);

    let queue = priority::sorted(&prios, &cands);
    let order: Vec<&str> = queue.iter().map(Id::as_str).collect();
    insta::assert_snapshot!("plan_basic_order", order.join("\n"));

    // The queue is non-decreasing in p after the walls, which come first.
    // (Paired by position, since two candidates can share an id.)
    let walls: usize = cands.iter().filter(|c| c.is_wall && c.eligible()).count();
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

    // §7.5: the batches the planner consumes, in assignment order.
    let groups = priority::batches(&priority::sorted_candidates(&prios, &cands), &cfg);
    let batched: Vec<String> = groups
        .iter()
        .filter(|b| b.is_batch())
        .map(|b| {
            format!(
                "ci{} {}m: {}",
                b.ci,
                b.total_min,
                b.ids.iter().map(Id::as_str).collect::<Vec<_>>().join(" · ")
            )
        })
        .collect();
    insta::assert_snapshot!("plan_basic_batches", batched.join("\n"));

    // §10.2: what tomorrow's hysteresis reads.
    let stored = priority::priorities_for_state(&prios);
    assert_eq!(stored.get(&Id::new("d1")), Some(&4));
    assert!(!stored.contains_key(&Id::new("x1")));

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
/// same fixture: `^x2` (Midterm review, 8b at ci 5) becomes IMPOSSIBLE once
/// the week is the only capacity there is.
#[test]
fn explain_names_the_shortfall_when_impossible() {
    let (tree, cfg, replay) = plan_basic();
    let cands = today_candidates(&tree, &cfg, &replay);
    // Only the seven days §8.4 renders as the week grid: nowhere near the
    // October exam, so the review does not fit.
    let prios = priority::compute(&cands, &caps(7), &BTreeMap::new(), &cfg, date("2026-09-07"));
    let text = priority::explain(&Id::new("x2"), &cands, &prios, &cfg);
    insta::assert_snapshot!("explain_x2_impossible", text);
}

// ---------------------------------------------------------------------------
// planner.rs types (§8)
// ---------------------------------------------------------------------------

/// The stub `plan()` returns a valid, hashable `DayPlan` with §8.1's window
/// and budget from `state.json`, and says in the diagnostics that the
/// algorithm is not implemented yet.
#[test]
fn planner_types_carry_the_window_budget_and_hash() {
    let (tree, cfg, replay) = plan_basic();
    let log = Log::new();
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
        &log,
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
    assert!(day.segments.is_empty());
    assert_eq!(day.block_minutes(), 0);
    assert_eq!(day.diagnostics.notes, vec!["planner not implemented"]);

    // Purity: the same input gives the same plan and the same hash.
    assert_eq!(planner::plan(&input), day);
    let empty_hash = day.hash();
    assert_eq!(empty_hash.len(), 16);
    assert!(empty_hash.chars().all(|c| c.is_ascii_hexdigit()));
    assert_eq!(day.hash(), empty_hash);

    // A different set of segments hashes differently; the diagnostics do not
    // enter the hash.
    let mut moved = day.clone();
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
    let mut noted = day.clone();
    noted.diagnostics.rest_debt_min = 40;
    assert_eq!(noted.hash(), empty_hash);

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
