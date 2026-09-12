//! §7.2's rule lines and §7.4's hysteresis and sort key, on small
//! `Tree::from_texts` trees and synthetic capacity vectors: `!k` inheritance,
//! the floor rule, the pure-rank rule, optional, overdue, the `hot` flag,
//! mandatory routines, blocked items, sorting and batching (§7.5).

use std::collections::BTreeMap;

use chrono::{DateTime, Duration, FixedOffset, NaiveDate, NaiveTime, TimeZone};
use chrono_tz::Tz;
use tm_core::capacity::{local_dt, DayCapacity};
use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::{self, Event, LogEntry, Replay};
use tm_core::model::{Dep, Id, Period};
use tm_core::priority::{self, Candidate, Ineligible, PrioClass};
use tm_core::tree::Tree;

const TZ: Tz = Tz::America__Chicago;
const MONDAY: &str = "2026-09-07";

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

fn due(s: &str) -> DateTime<Tz> {
    at(s, 23, 59)
}

/// `days` days from Monday 2026-09-07, each with `minutes` at `level`.
fn flat(days: usize, level: usize, minutes: u32) -> Vec<DayCapacity> {
    let start = date(MONDAY);
    (0..days)
        .map(|i| {
            let mut d = DayCapacity::empty(start + Duration::days(i as i64));
            d.minutes_at_level[level] = minutes;
            d
        })
        .collect()
}

fn empty() -> BTreeMap<Id, u8> {
    BTreeMap::new()
}

fn no_log() -> Replay {
    log::replay(&[], None, TZ)
}

fn tree(files: &[(&str, &str)]) -> Tree {
    Tree::from_texts(files, &Config::default())
}

/// The candidates of a synthetic tree at 2026-09-07 10:42 with no history.
fn candidates(t: &Tree, replay: &Replay) -> Vec<Candidate> {
    priority::collect_candidates(
        t,
        replay,
        &Config::default(),
        &Model::default(),
        date(MONDAY),
        at(MONDAY, 10, 42),
    )
}

fn find<'a>(cands: &'a [Candidate], id: &str) -> &'a Candidate {
    cands
        .iter()
        .find(|c| c.id.as_str() == id)
        .unwrap_or_else(|| panic!("no candidate {id}; have {:?}", ids(cands)))
}

fn ids(cands: &[Candidate]) -> Vec<&str> {
    cands.iter().map(|c| c.id.as_str()).collect()
}

fn class_of(prios: &[tm_core::priority::Prio], id: &str) -> PrioClass {
    prios
        .iter()
        .find(|p| p.id.as_str() == id)
        .unwrap_or_else(|| panic!("no priority for {id}"))
        .class
}

fn p_of(prios: &[tm_core::priority::Prio], id: &str) -> u8 {
    prios
        .iter()
        .find(|p| p.id.as_str() == id)
        .unwrap_or_else(|| panic!("no priority for {id}"))
        .p
}

// ---------------------------------------------------------------------------
// (d) !k inheritance
// ---------------------------------------------------------------------------

/// §7.1: `k` is the *root's* `!k`. A child of an `!1` root gets `k = 1` even
/// with its own `!3` (which §12.2 warns about); an item with no root
/// priority gets `config.priority.default_priority` = 3.
#[test]
fn k_comes_from_the_root() {
    let t = tree(&[
        (
            "month/2026-09.md",
            "- [ ] 5 !1 Lean: through ch.8 ^r1\n- [ ] 2 !4 Admin ^r4\n",
        ),
        (
            "week/2026-W37.md",
            "- [ ] 4 3b Child of the !1 root @r1 !3 ^w1\n\
             - [ ] 4 1b Grandchild @w1 ^w2\n\
             - [ ] 2 1b Under the !4 root @r4 ^w3\n\
             - [ ] 3 2b Untied ^w4\n",
        ),
    ]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    let replay = no_log();
    let cands = candidates(&t, &replay);
    assert_eq!(find(&cands, "w1").k, 1);
    assert_eq!(find(&cands, "w2").k, 1);
    assert_eq!(find(&cands, "w3").k, 4);
    assert_eq!(find(&cands, "w4").k, 3);

    // p = k + 2 for all four (finite, undated, no floor), clamped at 7.
    let prios = priority::compute(
        &cands,
        &flat(7, 5, 240),
        &empty(),
        &Config::default(),
        date(MONDAY),
    );
    assert_eq!(p_of(&prios, "w1"), 3);
    assert_eq!(p_of(&prios, "w2"), 3);
    assert_eq!(p_of(&prios, "w3"), 6);
    assert_eq!(p_of(&prios, "w4"), 5);
    assert_eq!(class_of(&prios, "w4"), PrioClass::Rank);
}

/// `p` is clamped to 0..=7 even when `k + bin` would overshoot.
///
/// With the §16 defaults it cannot: `k ≤ 4` and `bin ≤ 3` land exactly on 7.
/// Overshooting takes either a fourth bin edge (`bin = 4`) or a `!k` outside
/// 1..=4 — which `check.rs` flags as `bad-ci` but `grammar.rs` still parses,
/// so `priority.rs` has to survive it. Both are exercised here; without the
/// clamp the first two cases give 8 and 9.
#[test]
fn p_is_clamped_to_seven() {
    let cfg = Config::default();
    let caps = flat(1, 5, 10_000);
    let today = date(MONDAY);

    // Four bin edges: u = 0.0078 falls in the fifth bin, +4, on top of k(4).
    let mut deep = cfg.clone();
    deep.priority.bins = vec![0.5, 0.25, 0.1, 0.05];
    let mut c = Candidate::new(Id::new("x"), 0, 4, 60, &cfg); // need 78
    c.effective_due = Some(due(MONDAY));
    let prios = priority::compute(&[c.clone()], &caps, &empty(), &deep, today);
    assert_eq!(prios[0].bin, Some(4));
    assert_eq!(prios[0].raw_p, 7, "4 + 4 clamped");
    assert_eq!(prios[0].p, 7);

    // An out-of-range `!k`: k(7) + 2 for the pure-rank line.
    let mut wild = Candidate::new(Id::new("w"), 0, 7, 60, &cfg);
    wild.effective_due = None;
    let prios = priority::compute(&[wild], &caps, &empty(), &cfg, today);
    assert_eq!(prios[0].k, 7);
    assert_eq!(prios[0].p, 7);

    // The default config lands on 7 exactly, from both rule lines.
    let prios = priority::compute(&[c], &caps, &empty(), &cfg, today);
    assert_eq!(prios[0].bin, Some(3)); // k(4) + 3 = 7
    assert_eq!(prios[0].p, 7);

    let mut c = Candidate::new(Id::new("y"), 0, 4, 60, &cfg);
    c.effective_due = None;
    let prios = priority::compute(&[c], &caps, &empty(), &cfg, date(MONDAY));
    assert_eq!(prios[0].p, 6); // k(4) + 2
}

// ---------------------------------------------------------------------------
// (c) hysteresis (§7.4)
// ---------------------------------------------------------------------------

/// `p` may improve by at most one per day; worsening is free; `p = 0` is
/// never held back; `hysteresis = false` disables all of it.
#[test]
fn hysteresis_limits_improvement_to_one_step() {
    let cfg = Config::default();
    let caps = flat(1, 5, 1000);
    let today = date(MONDAY);
    let id = Id::new("x");

    // Raw 2 (k 2, u = 0.65 → +0) against yesterday's 4 → 3.
    let mut c = Candidate::new(id.clone(), 0, 2, 500, &cfg); // need 650, u = 0.65
    c.effective_due = Some(due(MONDAY));
    let yesterday: BTreeMap<Id, u8> = [(id.clone(), 4)].into_iter().collect();
    let prios = priority::compute(&[c.clone()], &caps, &yesterday, &cfg, today);
    assert_eq!(prios[0].raw_p, 2);
    assert_eq!(prios[0].p, 3);
    assert!(prios[0].hysteresis_applied);

    // Two more days walk it down one step at a time.
    let yesterday: BTreeMap<Id, u8> = [(id.clone(), 3)].into_iter().collect();
    let prios = priority::compute(&[c.clone()], &caps, &yesterday, &cfg, today);
    assert_eq!(prios[0].p, 2);
    assert!(!prios[0].hysteresis_applied);

    // A new value of 0 is not held back.
    let mut hot = Candidate::new(id.clone(), 0, 2, 2000, &cfg); // u = 2.6 → HOT
    hot.effective_due = Some(due(MONDAY));
    let yesterday: BTreeMap<Id, u8> = [(id.clone(), 4)].into_iter().collect();
    let prios = priority::compute(&[hot], &caps, &yesterday, &cfg, today);
    assert_eq!(prios[0].raw_p, 0);
    assert_eq!(prios[0].p, 0);
    assert!(!prios[0].hysteresis_applied);

    // Worsening is free: yesterday 2, raw 5 → 5.
    let mut calm = Candidate::new(id.clone(), 0, 2, 60, &cfg); // need 78, u = 0.078 → +3
    calm.effective_due = Some(due(MONDAY));
    let yesterday: BTreeMap<Id, u8> = [(id.clone(), 2)].into_iter().collect();
    let prios = priority::compute(&[calm.clone()], &caps, &yesterday, &cfg, today);
    assert_eq!(prios[0].raw_p, 5);
    assert_eq!(prios[0].p, 5);
    assert!(!prios[0].hysteresis_applied);

    // Disabled by config: the raw value stands.
    let mut off = cfg.clone();
    off.priority.hysteresis = false;
    let yesterday: BTreeMap<Id, u8> = [(id.clone(), 4)].into_iter().collect();
    let prios = priority::compute(&[c], &caps, &yesterday, &off, today);
    assert_eq!(prios[0].raw_p, 2);
    assert_eq!(prios[0].p, 2);
    assert!(!prios[0].hysteresis_applied);
}

/// The `p` values stored for tomorrow are exactly the ones shown today
/// (§10.2), walls excluded.
#[test]
fn priorities_for_state_round_trips() {
    let cfg = Config::default();
    let t = tree(&[(
        "week/2026-W37.md",
        "- [ ] 3 1b A ^a\n- [ ] 5 2h Exam ^x at:2026-09-07T10:00/12:00\n",
    )]);
    let replay = no_log();
    let cands = candidates(&t, &replay);
    let prios = priority::compute(&cands, &flat(7, 5, 240), &empty(), &cfg, date(MONDAY));
    let stored = priority::priorities_for_state(&prios);
    assert_eq!(stored.get(&Id::new("a")), Some(&5));
    assert!(
        !stored.contains_key(&Id::new("x")),
        "walls are off the scale"
    );
}

// ---------------------------------------------------------------------------
// (e) the floor rule (§7.2)
// ---------------------------------------------------------------------------

fn done_entry(id: &str, minutes: u32, day: &str, hour: u32) -> LogEntry {
    let t = FixedOffset::west_opt(5 * 3600)
        .expect("offset")
        .with_ymd_and_hms(
            date(day).format("%Y").to_string().parse().expect("year"),
            date(day).format("%m").to_string().parse().expect("month"),
            date(day).format("%d").to_string().parse().expect("day"),
            hour,
            0,
            0,
        )
        .unwrap();
    LogEntry::new(
        t,
        Event::Done {
            id: id.to_string(),
            est_min: minutes,
            actual_min: minutes,
            went: Some(1),
            tags: Vec::new(),
            ci: 3,
            partial: true,
        },
    )
}

/// `min:6b/w` with 2b done this week: need is `(360 − 120) × 1.3 = 312` and
/// the capacity is the rest of the week at levels ≥ ci.
///
/// With 5 remaining weekdays of 240 min at level 5 (Mon–Fri of W37 in the
/// synthetic capacity), `avail = 1200`, `u = 312/1200 = 0.26` → bin +1 →
/// `p = k(3) + 1 = 4`.
#[test]
fn open_floor_uses_the_remainder_of_the_period() {
    let cfg = Config::default();
    let t = tree(&[("backlog.md", "- [ ] 3 Lean practice open min:6b/w ^f1\n")]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    let entries = vec![done_entry("f1", 120, MONDAY, 8)];
    let replay = log::replay(&entries, None, TZ);

    // done_this_period reads the logged minutes of the item's own period.
    assert_eq!(
        priority::done_this_period(&replay, &t, &Id::new("f1"), Period::Week, date(MONDAY)),
        120
    );
    assert_eq!(
        priority::period_range(Period::Week, date(MONDAY)),
        (date("2026-09-07"), date("2026-09-13"))
    );

    let cands = candidates(&t, &replay);
    let f1 = find(&cands, "f1");
    assert_eq!(f1.floor_done_min, 120);
    assert_eq!(f1.floor.expect("a floor").amount.as_minutes(), 360);
    assert_eq!(f1.floor_need_min(&cfg), Some(312));

    let caps = flat(5, 5, 240);
    let prios = priority::compute(&cands, &caps, &empty(), &cfg, date(MONDAY));
    let p = &prios[0];
    assert_eq!(p.class, PrioClass::Floor);
    assert_eq!(p.need_min, 312);
    assert_eq!(p.avail_min, 1200);
    assert_eq!(p.until, Some(date("2026-09-13")));
    assert!((p.u.unwrap() - 0.26).abs() < 1e-12);
    assert_eq!(p.bin, Some(1));
    assert_eq!(p.p, 4);
    assert_eq!(p.allocation_min, 312);
}

/// A floor that cannot be met in the rest of the period is HOT/IMPOSSIBLE
/// like any other `u ≥ 1`.
#[test]
fn an_unreachable_floor_is_impossible() {
    let cfg = Config::default();
    let t = tree(&[("backlog.md", "- [ ] 3 Practice open min:6b/w ^f1\n")]);
    let replay = no_log();
    let cands = candidates(&t, &replay);
    // 60 minutes left in the whole week against a need of 468.
    let prios = priority::compute(&cands, &flat(1, 5, 60), &empty(), &cfg, date(MONDAY));
    assert_eq!(prios[0].class, PrioClass::Impossible);
    assert_eq!(prios[0].need_min, 468);
    assert_eq!(prios[0].shortfall_min, 408);
    assert_eq!(prios[0].p, 0);
}

/// A `max:` cap that is used up makes the item ineligible (§6.2) — it stays
/// a candidate with a reason, it does not vanish.
#[test]
fn an_exhausted_cap_is_an_ineligibility_reason() {
    let t = tree(&[(
        "week/2026-W37.md",
        "- [ ] 4 6b CS 234 pset 2 due:2026-09-11T23:59 max:2b/d ^d1\n",
    )]);
    let entries = vec![done_entry("d1", 120, MONDAY, 9)];
    let replay = log::replay(&entries, None, TZ);
    let cands = candidates(&t, &replay);
    let d1 = find(&cands, "d1");
    assert_eq!(d1.cap_done_min, 120);
    assert_eq!(d1.cap_left_min(), Some(0));
    assert!(!d1.eligible());
    assert!(matches!(
        d1.ineligible_reason(),
        Some(Ineligible::CapReached { done_min: 120, .. })
    ));

    // Half the cap used: still eligible, one block left.
    let entries = vec![done_entry("d1", 60, MONDAY, 9)];
    let replay = log::replay(&entries, None, TZ);
    let cands = candidates(&t, &replay);
    assert!(find(&cands, "d1").eligible());
    assert_eq!(find(&cands, "d1").cap_left_min(), Some(60));
}

// ---------------------------------------------------------------------------
// (f) the p = 0 lines and the pure-rank line
// ---------------------------------------------------------------------------

/// One tree with an item of every §7.2 class: overdue-persist, the `hot`
/// flag, a mandatory window instance, an optional line, a blocked item, a
/// wall and a plain finite undated task.
#[test]
fn every_rule_line_of_the_spec() {
    let cfg = Config::default();
    let t = tree(&[
        (
            "week/2026-W37.md",
            "- [ ] 3 2b Late report due:2026-09-04 on-miss:persist ^ov\n\
             - [ ] 3 1b Burning #urgent hot ^ho\n\
             - [ ] 3 1b Draft the tests ^t4\n\
             - [ ] 3 1b Review the drafts after:^t4 ^t5\n\
             - [ ] 5 2h Midterm at:2026-09-07T14:00/16:00 ^x1\n\
             - [ ] 3 1b Plain task ^pl\n",
        ),
        (
            "backlog.md",
            "- [ ] 1 Pick up package win:2026-09-07T09:00/21:00 dur:20m ^a3\n",
        ),
        ("optional.md", "- Severance S3E4 dur:1h\n"),
    ]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    assert!(t.get(&Id::new("ho")).expect("ho").is_hot());

    let replay = no_log();
    let cands = candidates(&t, &replay);
    assert_eq!(
        ids(&cands),
        vec!["ov", "ho", "t4", "t5", "x1", "pl", "a3", "Severance S3E4"]
    );

    let prios = priority::compute(&cands, &flat(7, 5, 240), &empty(), &cfg, date(MONDAY));
    assert_eq!(class_of(&prios, "ov"), PrioClass::Overdue);
    assert_eq!(p_of(&prios, "ov"), 0);
    assert_eq!(class_of(&prios, "ho"), PrioClass::HotFlag);
    assert_eq!(p_of(&prios, "ho"), 0);
    assert_eq!(class_of(&prios, "a3"), PrioClass::Mandatory);
    assert_eq!(p_of(&prios, "a3"), 0);
    assert_eq!(class_of(&prios, "Severance S3E4"), PrioClass::Optional);
    assert_eq!(p_of(&prios, "Severance S3E4"), 5);
    assert_eq!(class_of(&prios, "x1"), PrioClass::Wall);
    assert_eq!(class_of(&prios, "pl"), PrioClass::Rank);
    assert_eq!(p_of(&prios, "pl"), 5); // k(3) + 2
    assert_eq!(class_of(&prios, "t5"), PrioClass::Rank);

    // The blocked item is present, with its reason, and out of the queue.
    let t5 = find(&cands, "t5");
    assert!(!t5.eligible());
    assert_eq!(t5.blocked_by, vec![Dep::Item(Id::new("t4"))]);
    assert_eq!(
        priority::blocked(&cands),
        vec![(
            Id::new("t5"),
            Ineligible::Blocked(vec![Dep::Item(Id::new("t4"))])
        )]
    );
    assert_eq!(priority::blocked(&cands)[0].1.to_string(), "blocked by ^t4");
    let queue = priority::sorted(&prios, &cands);
    assert!(!queue.contains(&Id::new("t5")));
    // Walls first, then p = 0, then the rest by line order.
    assert_eq!(
        queue.iter().map(Id::as_str).collect::<Vec<_>>(),
        vec!["x1", "ov", "ho", "a3", "t4", "pl", "Severance S3E4"]
    );
}

/// A mandatory routine instance is `p = 0` and carries its instance key
/// (§5.2); a window that closes after today is not mandatory.
#[test]
fn a_mandatory_routine_instance_is_p_zero() {
    let cfg = Config::default();
    let t = tree(&[(
        "routines.md",
        "- sleep    win:22:00-08:00 dur:8h30m every:day ci:0\n\
         - lunch    win:11:30-13:30 dur:30m every:day\n\
         - laundry  win:09:00-21:00 dur:30m every:week on-miss:persist\n",
    )]);
    let replay = no_log();
    let cands = candidates(&t, &replay);
    let lunch = find(&cands, "lunch");
    assert_eq!(lunch.remaining_min, 30);
    assert_eq!(lunch.ci, 1);
    assert!(lunch.instance.is_some());
    assert!(lunch.window.is_some());

    let prios = priority::compute(&cands, &flat(7, 5, 240), &empty(), &cfg, date(MONDAY));
    // Lunch's window closes today at 13:30 → mandatory (§5.2).
    assert_eq!(class_of(&prios, "lunch"), PrioClass::Mandatory);
    assert_eq!(p_of(&prios, "lunch"), 0);
    // Sleep's window runs to 08:00 tomorrow, so it is not mandatory today; it
    // competes on rank (the planner places it by its window, not by key).
    assert_eq!(class_of(&prios, "sleep"), PrioClass::Rank);
    // Laundry is `on-miss:persist` and the empty log means it has never been
    // done, so today's candidate is a carried instance: §5.3's "stays Pending
    // into the next day; mandatory; counts as overdue".
    assert!(find(&cands, "laundry").overdue);
    assert!(find(&cands, "laundry").mandatory);
    assert_eq!(class_of(&prios, "laundry"), PrioClass::Overdue);
    assert_eq!(p_of(&prios, "laundry"), 0);
}

// ---------------------------------------------------------------------------
// (g) batching (§7.5)
// ---------------------------------------------------------------------------

/// Three ci-2 items of ≤ 20 min share one block; a fourth would not fit
/// inside `block_min`, and an item of a different `ci` or above
/// `batch_max_min` stands alone.
#[test]
fn batching_groups_small_equal_ci_items() {
    let cfg = Config::default();
    let t = tree(&[(
        "backlog.md",
        "- [ ] 2 20m Insurance claim ^s1\n\
         - [ ] 2 20m Call the bank ^s2\n\
         - [ ] 3 15m Different ci ^d1\n\
         - [ ] 2 20m Pick up package ^s3\n\
         - [ ] 2 20m One too many ^s4\n\
         - [ ] 2 2b A big one ^b1\n",
    )]);
    let replay = no_log();
    let cands = candidates(&t, &replay);
    let prios = priority::compute(&cands, &flat(7, 5, 240), &empty(), &cfg, date(MONDAY));
    let order = priority::sorted_candidates(&prios, &cands);
    let groups = priority::batches(&order, &cfg);

    let shown: Vec<(Vec<&str>, u8, u32)> = groups
        .iter()
        .map(|b| (b.ids.iter().map(Id::as_str).collect(), b.ci, b.total_min))
        .collect();
    assert_eq!(
        shown,
        vec![
            (vec!["s1", "s2", "s3"], 2, 60),
            (vec!["d1"], 3, 15),
            (vec!["s4"], 2, 20),
            (vec!["b1"], 2, 120),
        ]
    );
    assert!(groups[0].is_batch());
    assert!(!groups[1].is_batch());
    assert_eq!(groups[0].total_remaining_min, 60);
    // Every candidate appears exactly once.
    let mut all: Vec<&str> = groups
        .iter()
        .flat_map(|b| b.ids.iter().map(Id::as_str))
        .collect();
    all.sort_unstable();
    assert_eq!(all, vec!["b1", "d1", "s1", "s2", "s3", "s4"]);
}

/// §7.4's sort key is `(p, root line order, own line order)`: two items of
/// equal `p` under the same root fall back to their own line order, and two
/// roots order by the root's line.
#[test]
fn sort_key_is_p_then_root_line_then_own_line() {
    let cfg = Config::default();
    let t = tree(&[
        (
            "month/2026-09.md",
            "- [ ] 3 !2 Second root ^r2\n- [ ] 3 !2 First root ^r1\n",
        ),
        (
            "week/2026-W37.md",
            "- [ ] 3 1b Under r1, later line @r1 ^b\n\
             - [ ] 3 1b Under r2 @r2 ^c\n\
             - [ ] 3 1b Under r1, earlier line @r1 ^a\n",
        ),
    ]);
    let replay = no_log();
    let cands = candidates(&t, &replay);
    let prios = priority::compute(&cands, &flat(7, 5, 240), &empty(), &cfg, date(MONDAY));
    // All three are k(2) + 2 = 4.
    for id in ["a", "b", "c"] {
        assert_eq!(p_of(&prios, id), 4);
    }
    // r2 is the first line of month/, so its child sorts first; the two
    // children of r1 keep their own line order.
    let queue = priority::sorted(&prios, &cands);
    assert_eq!(
        queue.iter().map(Id::as_str).collect::<Vec<_>>(),
        vec!["c", "b", "a"]
    );

    let key_b = priority::sort_key(
        prios.iter().find(|p| p.id.as_str() == "b").expect("b"),
        find(&cands, "b"),
    );
    assert_eq!(key_b, (4, (0, 2), (1, 1)));
}
