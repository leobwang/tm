//! Regressions for the review findings on `priority.rs`: one test per bug,
//! each named after the rule it broke.
//!
//! The capacity vectors are synthetic (`flat(days, level, minutes)`: `days`
//! consecutive days from Monday 2026-09-07 with `minutes` at energy `level`
//! and nothing else), so every number in the assertions is computed by hand.
//!
//! **Two kinds of test, since R3 leaves fork 4748911's §7 pass with no shipped caller** (stage 6
//! W-46 track C; README gap 4752, the class).  A test that also asserts what the binary keeps —
//! the candidates `collect_candidates` gives, `lookahead_days`, `priorities_for_state`,
//! `deadline_health`, `explain`, `sorted`, eligibility — reads the fork's grants, batches and cap
//! readings BY VALUE (`fork_compute`, `support/forkcap.rs`: this binary's frozen file,
//! `tm-oracle capacity` under `TM_ORACLE`), as it read tm-core's in-tree copies until W-46.  A
//! test whose every assertion is the fork pass's own behaviour still calls the in-tree copy and is
//! deleted with it at R3 (README "W-46 track C", the deletion list):
//! `an_instance_deadline_without_a_window_enters_the_edf_pass` and
//! `an_optional_is_never_held_above_p_five_by_hysteresis`.

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

/// Fork 4748911's answers, by value (W-46 track C).
#[allow(dead_code)]
#[path = "support/forkcap.rs"]
mod forkcap;

use std::collections::BTreeMap;

use chrono::{DateTime, Duration, FixedOffset, NaiveDate, NaiveTime, TimeZone};
use chrono_tz::Tz;
use tm_core::capacity::{local_dt, DayCapacity};
use tm_core::config::Config;
use tm_core::energy::Model;
use tm_core::log::{Event, LogEntry, Replay};
use tm_core::model::{Id, Period};
use tm_core::priority::{self, Candidate, Ineligible, Prio, PrioClass};
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
            let mut minutes_at_level = [0; 6];
            minutes_at_level[level] = minutes;
            DayCapacity { date: start + Duration::days(i as i64), minutes_at_level }
        })
        .collect()
}

/// **Fork 4748911's grants** — fork `priority::compute`, by value (`forkcap::rank`).
fn fork_compute(cands: &[Candidate], caps: &[DayCapacity], yesterday: &BTreeMap<Id, u8>, cfg: &Config, today: NaiveDate) -> Vec<Prio> {
    forkcap::rank(forkcap::store(), cands, caps, yesterday, cfg, today).0
}

fn empty() -> BTreeMap<Id, u8> {
    BTreeMap::new()
}

fn no_log() -> Replay {
    chokepoint::replay_of_text("", TZ)
}

fn tree(files: &[(&str, &str)]) -> Tree {
    Tree::from_texts(files, &Config::default())
}

/// The candidates of a synthetic tree on `day` at 10:42 with no history.
fn candidates_on(t: &Tree, replay: &Replay, day: &str) -> Vec<Candidate> {
    priority::collect_candidates(
        t,
        replay,
        &Config::default(),
        &Model::default(),
        date(day),
        at(day, 10, 42),
    )
}

fn candidates(t: &Tree, replay: &Replay) -> Vec<Candidate> {
    candidates_on(t, replay, MONDAY)
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

fn prio<'a>(prios: &'a [Prio], id: &str) -> &'a Prio {
    prios
        .iter()
        .find(|p| p.id.as_str() == id)
        .unwrap_or_else(|| panic!("no priority for {id}"))
}

// ---------------------------------------------------------------------------
// §7.2 floor line: the lookahead has to reach the end of the period
// ---------------------------------------------------------------------------

/// A `min:30b/m` floor is scored against the rest of the *month* (§7.2:
/// "capacity = rest of the period"), so [`priority::lookahead_days`] has to
/// size the lookahead from the floor's period end and not only from the
/// deadlines. Sized from the deadlines alone it returned 7, and a comfortable
/// monthly floor came out IMPOSSIBLE every day of the month.
#[test]
fn the_lookahead_reaches_the_end_of_a_floor_period() {
    let cfg = Config::default();
    let t = tree(&[("backlog.md", "- [ ] 3 Practice open min:30b/m ^f1\n")]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    let replay = no_log();
    let cands = candidates(&t, &replay);
    let today = date(MONDAY);

    // No candidate has a due at all, yet the month runs to 2026-09-30.
    assert!(cands.iter().all(|c| c.effective_due.is_none()));
    assert_eq!(
        priority::period_range(Period::Month, today).1,
        date("2026-09-30")
    );
    let days = priority::lookahead_days(&cands, today);
    assert_eq!(days, 24, "2026-09-07 through 2026-09-30 inclusive");

    // 24 days × 240 min = 5760 against a need of 30b × 1.3 = 2340.
    let prios = fork_compute(&cands, &flat(days as usize, 5, 240), &empty(), &cfg, today);
    let f1 = prio(&prios, "f1");
    assert_eq!(f1.class, PrioClass::Floor);
    assert_eq!(f1.need_min, 2340);
    assert_eq!(f1.avail_min, 5760);
    assert_eq!(f1.until, Some(date("2026-09-30")));
    assert_eq!(f1.bin, Some(1)); // u = 0.406
    assert_eq!(f1.p, 4); // k(3) + 1
    assert!(!f1.is_hot());

    // A weekly floor still needs at least the seven days of the week grid.
    let weekly = tree(&[("backlog.md", "- [ ] 3 Practice open min:6b/w ^f2\n")]);
    let cands = candidates(&weekly, &replay);
    assert!(priority::lookahead_days(&cands, today) >= 7);
}

// ---------------------------------------------------------------------------
// §7.3: an instance with a real deadline competes like any other
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// §7.2/§7.4: hysteresis never moves an optional off p = 5
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// §8.2 step 1: walls are the intervals that cover *today*
// ---------------------------------------------------------------------------

/// An `at:` interval in a week file is a wall, but only on the days it
/// covers. A Midterm six weeks out used to be collected as today's wall and
/// sorted ahead of everything, so a planner consuming `sorted()` walls-first
/// booked two hours of October into this Monday.
#[test]
fn an_interval_in_another_week_is_not_todays_wall() {
    let cfg = Config::default();
    let t = tree(&[(
        "week/2026-W37.md",
        "- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 loc:JCL ^x1\n\
         - [ ] 5 1h Standup at:2026-09-07T09:00/10:00 ^w0\n\
         - [ ] 3 1b Plain task ^pl\n",
    )]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    let replay = no_log();
    let cands = candidates(&t, &replay);

    let x1 = find(&cands, "x1");
    assert!(x1.is_wall, "an Interval is a wall");
    assert!(!x1.wall_today, "but not this day's");
    let w0 = find(&cands, "w0");
    assert!(w0.is_wall && w0.wall_today);

    let prios = fork_compute(&cands, &flat(75, 5, 240), &empty(), &cfg, date(MONDAY));
    assert_eq!(prio(&prios, "x1").class, PrioClass::Wall);
    // Only today's wall leads the assignment order; the October one is gone.
    let queue = priority::sorted(&prios, &cands);
    assert_eq!(
        queue.iter().map(Id::as_str).collect::<Vec<_>>(),
        vec!["w0", "pl"]
    );
}

/// `ics.rs` files an occurrence into the ISO week of its **start**, so a
/// Sunday-to-Tuesday conference lives in the *previous* week's calendar file.
/// Reading only the current week's file dropped it and the planner booked
/// blocks straight through a two-day event.
#[test]
fn a_wall_from_last_weeks_calendar_file_is_collected() {
    let t = tree(&[
        (
            "calendar/2026-W36.md",
            "- [ ] 1 Conference at:2026-09-06T09:00/2026-09-08T17:00 ^g9\n\
             - [ ] 3 Last Friday at:2026-09-04T09:00/10:00 ^g8\n",
        ),
        (
            "calendar/2026-W37.md",
            "- [ ] 3 Meeting w/ host at:2026-09-07T12:50/13:50 loc:zoom ^g1\n",
        ),
        (
            "calendar/2026-W38.md",
            "- [ ] 3 Next Monday at:2026-09-14T09:00/10:00 ^g7\n",
        ),
    ]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    let replay = no_log();
    let cands = candidates(&t, &replay);

    // The three weeks a sync writes are read; only the intervals that cover
    // today become candidates.
    assert_eq!(ids(&cands), vec!["g9", "g1"]);
    assert!(find(&cands, "g9").wall_today);
    assert!(find(&cands, "g1").wall_today);
}

// ---------------------------------------------------------------------------
// §5.2/§6.2: no instance today, no candidate today
// ---------------------------------------------------------------------------

/// A `win:`/`every:` item competes as an instance. On a day it has none it
/// used to be emitted as a plain candidate with `window: None`, so a Thursday
/// errand competed for Monday's blocks and nothing downstream could keep it
/// inside its §5.2 range.
#[test]
fn a_window_item_is_only_a_candidate_on_a_day_it_occurs() {
    let t = tree(&[
        (
            "backlog.md",
            "- [ ] 1 Pick up package win:2026-09-10T09:00/21:00 dur:20m ^a3\n\
             - [ ] 2 30m Insurance claim ^a1\n",
        ),
        (
            "week/2026-W37.md",
            "- [ ] 3 1b Workout win:16:00-19:00 dur:1h every:Tue ^w1\n",
        ),
    ]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    let replay = no_log();

    // Monday: neither the Thursday errand nor the Tuesday workout.
    let monday = candidates_on(&t, &replay, MONDAY);
    assert_eq!(ids(&monday), vec!["a1"]);

    // Tuesday: the workout, with its window attached.
    let tuesday = candidates_on(&t, &replay, "2026-09-08");
    assert!(ids(&tuesday).contains(&"w1"));
    let w1 = find(&tuesday, "w1");
    assert!(w1.instance.is_some());
    assert_eq!(
        w1.window,
        Some((at("2026-09-08", 16, 0), at("2026-09-08", 19, 0)))
    );

    // Thursday: the errand, inside its own window.
    let thursday = candidates_on(&t, &replay, "2026-09-10");
    let a3 = find(&thursday, "a3");
    assert_eq!(
        a3.window,
        Some((at("2026-09-10", 9, 0), at("2026-09-10", 21, 0)))
    );
    assert_eq!(a3.remaining_min, 20);
}

// ---------------------------------------------------------------------------
// §6.2/§7.2: `routine` events are minutes too
// ---------------------------------------------------------------------------

fn routine_done(item: &str, inst: &str, minutes: u32, hour: u32) -> LogEntry {
    let d = date(inst);
    let t = FixedOffset::west_opt(5 * 3600)
        .expect("offset")
        .with_ymd_and_hms(
            d.format("%Y").to_string().parse().expect("year"),
            d.format("%m").to_string().parse().expect("month"),
            d.format("%d").to_string().parse().expect("day"),
            hour,
            0,
            0,
        )
        .unwrap();
    LogEntry::new(
        t,
        Event::Routine {
            item: item.to_string(),
            inst: inst.to_string(),
            status: "done".to_string(),
            actual_min: Some(minutes),
        },
    )
}

/// §10.1's `routine` event credits no block, so `done_this_period` used to
/// read 0 for everything completed with `tm routine done` — and the §4.3
/// `max:4h/w` on an optional never bound.
#[test]
fn routine_minutes_count_towards_a_max_cap() {
    let t = tree(&[("optional.md", "- Factorio dur:2h max:4h/w\n")]);
    let entries: Vec<LogEntry> = ["2026-09-01", "2026-09-02", "2026-09-05", "2026-09-06"]
        .iter()
        .map(|d| routine_done("Factorio", d, 60, 20))
        .collect();
    let replay = chokepoint::replay_of_entries(&entries, TZ);
    let key = Id::new("Factorio");

    // The week of 2026-09-07 is Mon 09-07..Sun 09-13; last week's four hours
    // are outside it.
    assert_eq!(
        priority::done_this_period(&replay, &t, &key, Period::Week, date(MONDAY)),
        0
    );
    // Read from the Sunday before, they are all inside that week.
    assert_eq!(
        priority::done_this_period(&replay, &t, &key, Period::Week, date("2026-09-06")),
        240
    );

    let cands = candidates_on(&t, &replay, "2026-09-06");
    let f = find(&cands, "Factorio");
    assert_eq!(f.cap_done_min, 240);
    assert_eq!(forkcap::cand_facts(forkcap::store(), &[f], &Config::default())[0].cap_left_min, Some(0));
    assert!(!f.eligible(), "the 4h/w quota binds");
    assert!(matches!(
        f.ineligible_reason(),
        Some(Ineligible::CapReached { done_min: 240, .. })
    ));

    // Block minutes and routine minutes are summed, never double-counted.
    let cands = candidates(&t, &replay);
    assert_eq!(find(&cands, "Factorio").cap_done_min, 0);
}

// ---------------------------------------------------------------------------
// §7.5/§8.3: batching
// ---------------------------------------------------------------------------

/// §8.3's monotone rank: of two candidates with equal `p` and equal `ci`, the
/// one with the lower line order is never left unassigned while the other is
/// assigned. Gathering a batch forward past `^b1` used to pull the *later*
/// `^s2` into the first block and leave `^b1` behind.
#[test]
fn batching_never_overtakes_an_equal_key_candidate() {
    let cfg = Config::default();
    let t = tree(&[(
        "backlog.md",
        "- [ ] 2 20m Small one ^s1\n\
         - [ ] 2 2b Big one ^b1\n\
         - [ ] 2 20m Small two ^s2\n",
    )]);
    let replay = no_log();
    let cands = candidates(&t, &replay);
    let prios = fork_compute(&cands, &flat(7, 5, 240), &empty(), &cfg, date(MONDAY));
    let order = priority::sorted_candidates(&prios, &cands);
    assert_eq!(
        order.iter().map(|c| c.id.as_str()).collect::<Vec<_>>(),
        vec!["s1", "b1", "s2"]
    );
    // All three share (p, ci), so nothing may be gathered across `^b1`.
    assert!(order.iter().all(|c| c.ci == 2));
    let groups = forkcap::batches(forkcap::store(), &order, &cfg);
    assert_eq!(
        groups
            .iter()
            .map(|b| b.ids.iter().map(Id::as_str).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        vec![vec!["s1"], vec!["b1"], vec!["s2"]]
    );

    // A candidate of another `ci` in between is not comparable, so gathering
    // still skips over it (§7.5's "in key order").
    let t = tree(&[(
        "backlog.md",
        "- [ ] 2 20m Small one ^s1\n\
         - [ ] 3 20m Another ci ^o1\n\
         - [ ] 2 20m Small two ^s2\n",
    )]);
    let cands = candidates(&t, &replay);
    let prios = fork_compute(&cands, &flat(7, 5, 240), &empty(), &cfg, date(MONDAY));
    let groups = forkcap::batches(forkcap::store(), &priority::sorted_candidates(&prios, &cands), &cfg);
    assert_eq!(
        groups
            .iter()
            .map(|b| b.ids.iter().map(Id::as_str).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        vec![vec!["s1", "s2"], vec!["o1"]]
    );
}

/// §5.2: a window instance is placed inside its own range (§8.2 steps 2 and
/// 6). Two routines whose windows do not overlap were merged into one block
/// that could satisfy neither.
#[test]
fn window_instances_are_never_batched_together() {
    let cfg = Config::default();
    let t = tree(&[(
        "routines.md",
        "- vitamins win:07:00-08:00 dur:15m every:day\n\
         - meds     win:20:00-21:00 dur:15m every:day\n",
    )]);
    let replay = no_log();
    let cands = priority::collect_candidates(
        &t,
        &replay,
        &cfg,
        &Model::default(),
        date(MONDAY),
        at(MONDAY, 6, 0),
    );
    assert_eq!(ids(&cands), vec!["vitamins", "meds"]);
    assert!(cands.iter().all(|c| c.window.is_some() && c.ci == 1));

    let prios = fork_compute(&cands, &flat(7, 5, 240), &empty(), &cfg, date(MONDAY));
    let groups = forkcap::batches(forkcap::store(), &priority::sorted_candidates(&prios, &cands), &cfg);
    assert!(
        groups.iter().all(|b| !b.is_batch()),
        "disjoint windows cannot share a block: {groups:?}"
    );
}

// ---------------------------------------------------------------------------
// §10.2: two instances, one stored priority
// ---------------------------------------------------------------------------

/// A routine reaches the day once. §5.3's carried `on-miss:persist` instance
/// *is* the item's pending instance while it is open, so the occurrence that
/// has since come round is not a second candidate — the laundry used to be
/// planned twice on the same day, at `p = 0` and again at `p = 5`.
///
/// `priorities_for_state` still has to survive two rows for one id (§10.2's
/// map is keyed by id and `plan()` takes its candidates from the caller): it
/// used to keep whichever came last, dropping the `p = 0` row and giving
/// tomorrow's hysteresis the wrong baseline.
#[test]
fn priorities_for_state_keeps_the_most_urgent_of_two_instances() {
    let cfg = Config::default();
    let t = tree(&[(
        "routines.md",
        "- laundry win:09:00-21:00 dur:30m every:week on-miss:persist\n",
    )]);
    let replay = no_log();
    let cands = candidates(&t, &replay);
    assert_eq!(ids(&cands), vec!["laundry"], "one instance, not two");

    let prios = fork_compute(&cands, &flat(7, 5, 240), &empty(), &cfg, date(MONDAY));
    let ps: Vec<u8> = prios.iter().map(|p| p.p).collect();
    // Never logged, so last week's window is still owed: overdue and
    // mandatory, §7.2's `p = 0`. The one candidate is keyed on *this* week's
    // occurrence — the newest — so doing it once discharges the carry.
    assert_eq!(ps, vec![0]);
    assert_eq!(cands[0].instance.map(|k| k.to_string()).as_deref(), Some(MONDAY));

    // Two rows for one id, only `p` differing, as a caller-supplied candidate
    // list could still hold.
    let mut two = prios.clone();
    let mut ranked = prios[0].clone();
    ranked.p = 5;
    two.push(ranked);
    let stored = priority::priorities_for_state(&two);
    assert_eq!(stored.get(&Id::new("laundry")), Some(&0));
    assert_eq!(stored.len(), 1);
}

// ---------------------------------------------------------------------------
// §7.3/§11: the class never hides the deadline verdict
// ---------------------------------------------------------------------------

/// §7.2's cascade reports the more specific fact, so an item that carries the
/// `hot` flag *and* cannot make its deadline is classed `HotFlag`. §11's
/// #IMPOSSIBLE column, `Prio::is_hot` and the `--explain` banner read the
/// verdict off `u` and the shortfall instead, so marking an item hot no
/// longer hides it from the banner whose whole point is the shortfall.
#[test]
fn a_hot_flag_does_not_hide_an_impossible_deadline() {
    let cfg = Config::default();
    let caps = flat(5, 5, 120);
    let today = date(MONDAY);

    // need 480 × 1.3 = 624 by Wednesday, where 3 × 120 = 360 exist.
    let mut c = Candidate::new(Id::new("d1"), 3, 3, 480, &cfg);
    c.effective_due = Some(due("2026-09-09"));
    c.hot = true;
    let cands = vec![c.clone()];
    let prios = fork_compute(&cands, &caps, &empty(), &cfg, today);

    assert_eq!(prios[0].class, PrioClass::HotFlag);
    assert_eq!(prios[0].p, 0);
    assert_eq!(prios[0].avail_min, 360);
    assert_eq!(prios[0].shortfall_min, 264);
    assert!(prios[0].is_hot());
    assert!(prios[0].is_impossible());

    let health = priority::deadline_health(&prios, &cands, today);
    assert_eq!((health.hot, health.impossible), (0, 1));

    let text = priority::explain(&Id::new("d1"), &cands, &prios, &cfg);
    assert_eq!(
        text,
        "p = 0 (hot flag); IMPOSSIBLE: needs 10.4b, 6b available by 2026-09-09; deps ok"
    );

    // Without the flag, the very same numbers are classed IMPOSSIBLE.
    let plain = vec![Candidate {
        hot: false,
        ..c.clone()
    }];
    let prios = fork_compute(&plain, &caps, &empty(), &cfg, today);
    assert_eq!(prios[0].class, PrioClass::Impossible);
    assert_eq!(
        priority::deadline_health(&prios, &plain, today).impossible,
        1
    );

    // An overdue item keeps its own column and its own line: its deadline is
    // behind it, which `p = 0 (overdue…)` already says.
    let mut old = Candidate::new(Id::new("ov"), 3, 3, 60, &cfg);
    old.effective_due = Some(due("2026-09-04"));
    old.overdue = true;
    let old = vec![old];
    let prios = fork_compute(&old, &caps, &empty(), &cfg, today);
    assert_eq!(prios[0].class, PrioClass::Overdue);
    assert!(prios[0].is_impossible(), "nothing can be done by Friday now");
    let health = priority::deadline_health(&prios, &old, today);
    assert_eq!((health.hot, health.impossible, health.overdue), (0, 0, 1));
    assert_eq!(
        priority::explain(&Id::new("ov"), &old, &prios, &cfg),
        "p = 0 (overdue, on-miss persist); need 1.3b, avail 0b by 2026-09-04; deps ok"
    );

    // A `hot` flag on an item that *does* fit is HOT, not IMPOSSIBLE.
    let mut fits = Candidate::new(Id::new("d2"), 3, 3, 277, &cfg); // need 360 = avail
    fits.effective_due = Some(due("2026-09-09"));
    fits.hot = true;
    let fits = vec![fits];
    let prios = fork_compute(&fits, &caps, &empty(), &cfg, today);
    assert!(prios[0].is_hot() && !prios[0].is_impossible());
    let health = priority::deadline_health(&prios, &fits, today);
    assert_eq!((health.hot, health.impossible), (1, 0));
}

// ---------------------------------------------------------------------------
// §5.1/§8.2 step 8: waiting items are listed, not lost
// ---------------------------------------------------------------------------

/// §5.5: "a blocked high-priority item shows in diagnostics as blocked by
/// ^id rather than silently vanishing" — the same holds for `[?]`. Every
/// candidate source filters on `State::is_open()`, which excludes `[?]`, so
/// waiting items had no source at all and §8.2 step 8's `waiting` diagnostic
/// nothing to draw on.
#[test]
fn a_waiting_item_is_a_candidate_with_a_reason() {
    let cfg = Config::default();
    let t = tree(&[
        (
            "backlog.md",
            "- [?] 2 15m Ask Prof. Lee on-event:reply/7d waiting:2026-09-05 ^a4\n\
             - [ ] 2 30m Insurance claim ^a1\n",
        ),
        (
            "week/2026-W37.md",
            "- [?] 3 1b Await the review after:^a1 waiting:2026-09-06 ^wq\n",
        ),
        ("month/2026-09.md", "- [?] 3 !2 Not a candidate ^mq\n"),
    ]);
    assert!(t.problems().is_empty(), "{:?}", t.problems());
    let replay = no_log();
    let cands = candidates(&t, &replay);
    // `Tree::from_texts` keeps the file order it was given: backlog, week.
    assert_eq!(ids(&cands), vec!["a4", "a1", "wq"]);

    let a4 = find(&cands, "a4");
    assert!(a4.waiting);
    assert_eq!(a4.state, tm_core::model::State::Waiting);
    assert!(!a4.eligible());
    assert_eq!(a4.ineligible_reason(), Some(Ineligible::Waiting));
    assert_eq!(a4.ineligible_reason().expect("a reason").to_string(), "waiting");

    // §8.2 step 8 can build `diagnostics.waiting` from this.
    let waiting: Vec<&str> = priority::blocked(&cands)
        .iter()
        .filter(|(_, why)| matches!(why, Ineligible::Waiting))
        .map(|(id, _)| {
            if id.as_str() == "a4" {
                "a4"
            } else {
                "wq"
            }
        })
        .collect();
    assert_eq!(waiting, vec!["a4", "wq"]);

    // They take no slot.
    let prios = fork_compute(&cands, &flat(7, 5, 240), &empty(), &cfg, date(MONDAY));
    let queue = priority::sorted(&prios, &cands);
    assert_eq!(queue.iter().map(Id::as_str).collect::<Vec<_>>(), vec!["a1"]);
}
