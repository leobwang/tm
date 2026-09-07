//! Hand-computed recurrence cases (§5.1–§5.3) against the `plan-recur`
//! fixture: after-done due and validity, persist carry, skip, the calendar
//! rules, overnight windows, waiting timeouts and logged completions.

use std::path::{Path, PathBuf};

use chrono::{NaiveDate, NaiveDateTime};
use tm_core::config::Config;
use tm_core::grammar::{parse_file, ParsedFile};
use tm_core::log::{Event, Log, Replay};
use tm_core::model::{Id, Instance, InstanceKey, InstanceStatus, Item, OnMiss};
use tm_core::recur::{self, InstanceInfo};
use tm_core::tree::Tree;

const FILES: &[&str] = &[
    "month/2026-09.md",
    "week/2026-W37.md",
    "backlog.md",
    "routines.md",
    "optional.md",
];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/plan-recur")
}

struct World {
    tree: Tree,
    cfg: Config,
    replay: Replay,
    log: Log,
}

impl World {
    fn item(&self, key: &str) -> &Item {
        self.tree
            .get(&Id::new(key))
            .unwrap_or_else(|| panic!("{key} is in the fixture"))
    }
    /// The instances of `key` over `range`, evaluated at `today`.
    fn instances(&self, key: &str, range: (&str, &str), today: &str) -> Vec<Instance> {
        recur::instances(
            self.item(key),
            (date(range.0), date(range.1)),
            date(today),
            &self.replay,
            &self.cfg,
        )
    }
    fn one(&self, key: &str, on: &str, today: &str) -> Instance {
        let v = self.instances(key, (on, on), today);
        assert_eq!(v.len(), 1, "{key} on {on}: {v:?}");
        v.into_iter().next().expect("checked")
    }
    fn info(&self, key: &str, inst: &Instance, today: &str, now: &str) -> InstanceInfo {
        recur::instance_info(self.item(key), inst, date(today), dt(now))
    }
}

fn load() -> World {
    let cfg = Config::load(fixture_dir().join("config.toml")).unwrap();
    let parsed: Vec<ParsedFile> = FILES
        .iter()
        .map(|rel| {
            let text = std::fs::read_to_string(fixture_dir().join(rel)).unwrap();
            parse_file(rel, &text, &cfg)
        })
        .collect();
    let log = Log::read(fixture_dir().join(".tm/log.jsonl")).unwrap();
    let replay = log.replay(None, cfg.tz);
    World {
        tree: Tree::build(&parsed, &cfg),
        cfg,
        replay,
        log,
    }
}

fn date(s: &str) -> NaiveDate {
    tm_core::model::parse_date(s).unwrap()
}

fn dt(s: &str) -> NaiveDateTime {
    tm_core::model::parse_datetime(s).unwrap()
}

fn keys(v: &[Instance]) -> Vec<String> {
    v.iter().map(|i| i.key.to_string()).collect()
}

// ---------------------------------------------------------------------------
// after-done (§5.1, §5.3)
// ---------------------------------------------------------------------------

#[test]
fn shower_is_due_two_days_after_the_last_one_and_valid_for_one_more() {
    let w = load();
    let st = recur::after_done_state(w.item("shower"), &w.replay, date("2026-09-07"), &w.cfg)
        .expect("shower recurs on completion");
    assert_eq!(st.last_done_date, Some(date("2026-09-05")));
    assert_eq!(st.count, 5);
    assert_eq!(st.due, date("2026-09-07"));
    assert_eq!(st.due_at, dt("2026-09-07T23:00"));
    assert_eq!(st.valid_until, Some(date("2026-09-08")));
    assert_eq!(st.valid_until_at, Some(dt("2026-09-08T23:00")));
    assert!(!st.missed);

    let inst = w.one("shower", "2026-09-07", "2026-09-07");
    assert_eq!(inst.key, InstanceKey::Nth(6));
    assert_eq!(inst.status, InstanceStatus::Pending);
    assert_eq!(inst.due, Some(dt("2026-09-07T23:00")));
    assert_eq!(
        inst.window,
        Some((dt("2026-09-07T07:00"), dt("2026-09-08T23:00")))
    );

    // Day 2 of 2d~1d: still time tomorrow, so not yet mandatory.
    assert!(!recur::is_mandatory(
        w.item("shower"),
        &inst,
        date("2026-09-07"),
        dt("2026-09-07T10:42")
    ));
    // Day 3 is the last chance (§5.2).
    let inst = w.one("shower", "2026-09-08", "2026-09-08");
    assert_eq!(inst.key, InstanceKey::Nth(6));
    assert!(recur::is_mandatory(
        w.item("shower"),
        &inst,
        date("2026-09-08"),
        dt("2026-09-08T09:00")
    ));
    let info = w.info("shower", &inst, "2026-09-08", "2026-09-08T09:00");
    assert!(info.mandatory && info.last_chance && info.overdue);
    assert_eq!(info.carried_from, Some(date("2026-09-07")));
    assert_eq!(info.dur_min, Some(20));
}

#[test]
fn before_its_due_the_after_done_instance_is_pending_but_not_yet() {
    let w = load();
    // On 09-06 the shower done on 09-05 is not due until tomorrow, so a query
    // for that day alone sees nothing at all: #5 is behind it and #6 ahead.
    assert!(w
        .instances("shower", ("2026-09-06", "2026-09-06"), "2026-09-06")
        .is_empty());
    // …and pending, with a future due, in a range that reaches its due date.
    let v = w.instances("shower", ("2026-09-06", "2026-09-08"), "2026-09-06");
    let pending = v.last().expect("the pending instance is always there");
    assert_eq!(pending.key, InstanceKey::Nth(6));
    assert_eq!(pending.status, InstanceStatus::Pending);
    assert_eq!(
        pending.due,
        Some(dt("2026-09-07T23:00")),
        "the due tells the planner it is future"
    );
    let info = w.info("shower", pending, "2026-09-06", "2026-09-06T10:00");
    assert!(info.not_yet && !info.mandatory && !info.overdue);
    // …so the planner is not offered it today.
    let items: Vec<&Item> = w.tree.iter().collect();
    let today = recur::today_instances(
        items,
        date("2026-09-06"),
        dt("2026-09-06T10:00"),
        &w.replay,
        &w.cfg,
    );
    assert!(!today.iter().any(|(i, _)| i.item.as_str() == "shower"));
}

#[test]
fn a_missed_shower_is_due_immediately_with_the_same_ordinal() {
    let w = load();
    // By 2026-09-10 the 2d~1d chance of the 09-05 shower (due 09-07, valid
    // through 09-08) is gone. §5.3, window + after-done: the offset still runs
    // from the last *completion* — 09-05 + 2d = 09-07, already past — so the
    // next instance is due immediately, i.e. today, not two days from the miss.
    let st = recur::after_done_state(w.item("shower"), &w.replay, date("2026-09-10"), &w.cfg)
        .expect("after-done");
    assert!(st.missed);
    assert_eq!(st.last_done_date, Some(date("2026-09-05")));
    assert_eq!(st.due, date("2026-09-10"), "due immediately");
    assert_eq!(st.valid_until, Some(date("2026-09-11")));
    let inst = w.one("shower", "2026-09-10", "2026-09-10");
    assert_eq!(inst.key, InstanceKey::Nth(6), "still the sixth shower");
    assert_eq!(inst.status, InstanceStatus::Pending);
}

#[test]
fn after_done_without_a_validity_window_never_expires_and_never_is_a_last_chance() {
    let w = load();
    let st = recur::after_done_state(w.item("vitamins"), &w.replay, date("2026-09-07"), &w.cfg)
        .expect("after-done");
    assert_eq!(st.last_done_date, Some(date("2026-09-03")));
    assert_eq!(st.due, date("2026-09-05"));
    assert_eq!(st.valid_until, None);
    assert!(!st.missed);
    let inst = w.one("vitamins", "2026-09-07", "2026-09-07");
    assert_eq!(inst.status, InstanceStatus::Pending);
    let info = w.info("vitamins", &inst, "2026-09-07", "2026-09-07T10:42");
    assert!(info.overdue && info.deferred_from_yesterday);
    assert!(!info.last_chance && !info.mandatory);
    // Still placeable inside today's window.
    assert_eq!(
        inst.window,
        Some((dt("2026-09-05T07:00"), dt("2026-09-07T11:00")))
    );
}

// ---------------------------------------------------------------------------
// on_miss (§5.3)
// ---------------------------------------------------------------------------

#[test]
fn laundry_persists_and_is_mandatory_and_overdue_today() {
    let w = load();
    let v = w.instances("laundry", ("2026-09-01", "2026-09-21"), "2026-09-07");
    assert_eq!(
        keys(&v),
        vec!["2026-08-31", "2026-09-07", "2026-09-14", "2026-09-21"]
    );
    let carried = &v[0];
    assert_eq!(carried.status, InstanceStatus::Pending, "persist carries");
    let info = w.info("laundry", carried, "2026-09-07", "2026-09-07T10:42");
    assert!(info.overdue, "last week's window closed on Sunday");
    assert_eq!(info.carried_from, Some(date("2026-09-06")));
    assert!(info.mandatory, "§5.3: a carried persist instance is mandatory");
    assert!(info.deferred_from_yesterday);
    // This week's instance is open all week and not yet under pressure.
    let this_week = w.info("laundry", &v[1], "2026-09-07", "2026-09-07T10:42");
    assert!(!this_week.mandatory && !this_week.overdue);
    // …until Sunday, when its window closes.
    let sunday = w.info("laundry", &v[1], "2026-09-13", "2026-09-13T09:00");
    assert!(sunday.mandatory);
}

#[test]
fn a_missed_expire_window_expires_and_on_miss_next_is_skipped() {
    let w = load();
    // Two daily routines nobody logged on a day that is now past: stretch is
    // `on-miss:next`, lunch takes the calendar-window default, `expire`.
    let stretch = w.instances("stretch", ("2026-09-02", "2026-09-02"), "2026-09-07");
    assert_eq!(stretch[0].status, InstanceStatus::Skipped, "on-miss:next");
    let lunch = w.instances("lunch", ("2026-09-03", "2026-09-03"), "2026-09-07");
    assert_eq!(
        lunch[0].status,
        InstanceStatus::Expired,
        "nothing logged on 09-03"
    );
    assert_eq!(w.item("lunch").on_miss, OnMiss::Expire);
}

#[test]
fn skipping_an_instance_leaves_the_next_occurrence_unchanged() {
    let w = load();
    let v = w.instances("workout", ("2026-09-01", "2026-09-11"), "2026-09-07");
    assert_eq!(
        keys(&v),
        vec!["2026-09-02", "2026-09-04", "2026-09-07", "2026-09-09", "2026-09-11"]
    );
    assert_eq!(v[0].status, InstanceStatus::Done);
    assert_eq!(v[1].status, InstanceStatus::Skipped, "skipped on Friday");
    assert_eq!(v[2].status, InstanceStatus::Pending, "Monday is unchanged");
    assert_eq!(v[3].status, InstanceStatus::Pending);

    // What `tm skip workout` would append for today's instance.
    let now = tm_core::log::parse_timestamp("2026-09-07T16:05:00-05:00").unwrap();
    let entry = recur::skip_instance(w.item("workout"), &v[2], now);
    assert_eq!(
        entry.to_json().unwrap(),
        r#"{"t":"2026-09-07T16:05:00-05:00","ev":"skip","item":"workout","inst":"2026-09-07"}"#
    );
    // Replaying it makes today's instance Skipped and leaves Wednesday alone.
    let mut log = w.log.clone();
    log.push(entry);
    let replay = log.replay(None, w.cfg.tz);
    let after = recur::instances(
        w.item("workout"),
        (date("2026-09-07"), date("2026-09-09")),
        date("2026-09-07"),
        &replay,
        &w.cfg,
    );
    assert_eq!(after[0].status, InstanceStatus::Skipped);
    assert_eq!(after[1].status, InstanceStatus::Pending);
}

#[test]
fn a_logged_routine_done_marks_the_instance_done() {
    let w = load();
    let inst = w.one("groceries", "2026-09-07", "2026-09-07");
    assert_eq!(inst.status, InstanceStatus::Pending);
    let now = tm_core::log::parse_timestamp("2026-09-09T18:20:00-05:00").unwrap();
    let entry = recur::done_instance(w.item("groceries"), &inst, now, Some(45));
    assert!(matches!(
        &entry.ev,
        Event::Routine { item, inst, status, actual_min }
            if item == "groceries" && inst == "2026-09-07" && status == "done"
                && *actual_min == Some(45)
    ));
    let mut log = w.log.clone();
    log.push(entry);
    let replay = log.replay(None, w.cfg.tz);
    let after = recur::instances(
        w.item("groceries"),
        (date("2026-09-07"), date("2026-09-07")),
        date("2026-09-09"),
        &replay,
        &w.cfg,
    );
    assert_eq!(after[0].status, InstanceStatus::Done);
}

// ---------------------------------------------------------------------------
// calendar rules (§5.1)
// ---------------------------------------------------------------------------

#[test]
fn every_2w_sun_yields_alternating_sundays() {
    let w = load();
    let v = w.instances("deep-clean", ("2026-08-01", "2026-10-31"), "2026-09-07");
    assert_eq!(
        keys(&v),
        vec![
            "2026-08-02",
            "2026-08-16",
            "2026-08-30",
            "2026-09-13",
            "2026-09-27",
            "2026-10-11",
            "2026-10-25",
        ]
    );
    for pair in v.windows(2) {
        let (a, b) = (&pair[0], &pair[1]);
        let (InstanceKey::Date(a), InstanceKey::Date(b)) = (a.key, b.key) else {
            panic!("calendar instances are date-keyed");
        };
        assert_eq!((b - a).num_days(), 14);
        assert_eq!(a.format("%a").to_string(), "Sun");
    }
    assert_eq!(v[2].status, InstanceStatus::Done, "done on 08-30");
}

#[test]
fn every_month_15_lands_in_february_too() {
    let w = load();
    let v = w.instances("bins", ("2026-01-01", "2026-04-30"), "2026-09-07");
    assert_eq!(
        keys(&v),
        vec!["2026-01-15", "2026-02-15", "2026-03-15", "2026-04-15"]
    );
    // The instance is the 15th's own window, not the month's.
    assert_eq!(
        v[1].window,
        Some((dt("2026-02-15T07:00"), dt("2026-02-15T09:00")))
    );
}

#[test]
fn every_3d_is_anchored_at_the_first_logged_completion() {
    let w = load();
    let v = w.instances("water-plants", ("2026-08-24", "2026-09-08"), "2026-09-07");
    assert_eq!(
        keys(&v),
        vec![
            "2026-08-26",
            "2026-08-29",
            "2026-09-01",
            "2026-09-04",
            "2026-09-07",
        ],
        "phase fixed by the 08-26 completion"
    );
    assert_eq!(v[0].status, InstanceStatus::Done);
    assert_eq!(v[1].status, InstanceStatus::Expired);
    assert_eq!(v[4].status, InstanceStatus::Pending);
}

#[test]
fn every_weekday_skips_the_weekend() {
    let w = load();
    let v = w.instances("standup", ("2026-09-07", "2026-09-13"), "2026-09-07");
    assert_eq!(
        keys(&v),
        vec![
            "2026-09-07",
            "2026-09-08",
            "2026-09-09",
            "2026-09-10",
            "2026-09-11",
        ]
    );
}

#[test]
fn the_overnight_sleep_window_runs_into_the_next_day() {
    let w = load();
    let inst = w.one("sleep", "2026-09-07", "2026-09-07");
    assert_eq!(
        inst.window,
        Some((dt("2026-09-07T22:00"), dt("2026-09-08T08:00")))
    );
    assert_eq!(inst.due, Some(dt("2026-09-08T08:00")));
    // Last night's instance is still pending during the morning it ends.
    let last_night = w.one("sleep", "2026-09-06", "2026-09-07");
    assert_eq!(last_night.status, InstanceStatus::Pending);
    assert_eq!(
        last_night.window,
        Some((dt("2026-09-06T22:00"), dt("2026-09-07T08:00")))
    );
    // …and expired once the next day starts.
    let last_night = w.one("sleep", "2026-09-06", "2026-09-08");
    assert_eq!(last_night.status, InstanceStatus::Expired);
    // It was logged done on the 4th and 5th.
    assert_eq!(
        w.one("sleep", "2026-09-04", "2026-09-07").status,
        InstanceStatus::Done
    );
}

// ---------------------------------------------------------------------------
// on-event and waiting (§5.1)
// ---------------------------------------------------------------------------

#[test]
fn a_waiting_item_expires_after_its_timeout() {
    let w = load();
    let a4 = w.item("a4");
    let st = recur::waiting_state(a4, &w.replay, date("2026-09-07"), &w.cfg).expect("waiting");
    assert_eq!(st.since, Some(date("2026-09-05")));
    assert_eq!(st.days_waiting, 2);
    assert_eq!(st.timeout_at, Some(date("2026-09-12")));
    assert!(!st.expired);
    assert!(st.arrived.is_none());
    // No instance is pending while it waits (§5.1): it never takes a slot.
    assert!(w
        .instances("a4", ("2026-09-07", "2026-09-07"), "2026-09-07")
        .is_empty());

    // On the timeout day it is still waiting; the day after, the wait ends.
    let on_time = recur::waiting_state(a4, &w.replay, date("2026-09-12"), &w.cfg).unwrap();
    assert!(!on_time.expired);
    let late = recur::waiting_state(a4, &w.replay, date("2026-09-13"), &w.cfg).unwrap();
    assert!(late.expired);
    assert_eq!(late.days_waiting, 8);
    let v = w.instances("a4", ("2026-09-13", "2026-09-13"), "2026-09-13");
    assert_eq!(keys(&v), vec!["#2"], "one done, so the next is the second");
    assert_eq!(v[0].status, InstanceStatus::Pending);
}

#[test]
fn a_wait_without_a_timeout_never_expires() {
    let w = load();
    let st = recur::waiting_state(w.item("a5"), &w.replay, date("2026-12-31"), &w.cfg).unwrap();
    assert_eq!(st.timeout_at, None);
    assert!(!st.expired);
    assert_eq!(st.days_waiting, 133);
    assert!(w
        .instances("a5", ("2026-12-31", "2026-12-31"), "2026-12-31")
        .is_empty());
}

#[test]
fn an_arrived_event_ends_the_wait_and_the_next_instance_is_pending() {
    let w = load();
    let a7 = w.item("a7");
    let st = recur::waiting_state(a7, &w.replay, date("2026-09-07"), &w.cfg).unwrap();
    assert!(!st.expired, "the 3d timeout runs to 09-07");
    assert!(st.arrived.is_some(), "the dentist event was logged on 09-06");
    let v = w.instances("a7", ("2026-09-07", "2026-09-07"), "2026-09-07");
    assert_eq!(keys(&v), vec!["#2"]);

    assert!(recur::event_resolves(a7, "dentist"));
    assert!(!recur::event_resolves(a7, "reply"));
    assert!(recur::event_resolves(w.item("a4"), "reply"));

    // The line edits `tm event dentist ^a7` applies.
    let edits = recur::on_event_arrived(a7);
    let mut line = a7.line().clone();
    edits.apply(&mut line).unwrap();
    assert_eq!(
        line.to_string(),
        "- [ ] 2 10m Confirm the dentist slot  on-event:dentist/3d ^a7"
    );
    // …and what `tm done ^a6` writes when the wait starts.
    let a6 = w.item("a6");
    assert!(recur::waiting_state(a6, &w.replay, date("2026-09-07"), &w.cfg).is_none());
    let mut line = a6.line().clone();
    recur::on_done_waiting(a6, date("2026-09-07"))
        .apply(&mut line)
        .unwrap();
    assert_eq!(
        line.to_string(),
        "- [?] 2 15m Ping the landlord about the lease  on-event:lease waiting:2026-09-07 ^a6"
    );
}

// ---------------------------------------------------------------------------
// one-off windows (§5.2)
// ---------------------------------------------------------------------------

#[test]
fn a_one_off_window_is_mandatory_on_the_day_it_closes() {
    let w = load();
    let inst = w.one("a3", "2026-09-07", "2026-09-07");
    assert_eq!(
        inst.window,
        Some((dt("2026-09-07T09:00"), dt("2026-09-07T21:00")))
    );
    let info = w.info("a3", &inst, "2026-09-07", "2026-09-07T10:42");
    assert!(info.mandatory && info.last_chance);
    assert_eq!(info.dur_min, Some(20));
    // Once the window has passed there is nothing to place, and nothing to
    // badge either.
    let info = w.info("a3", &inst, "2026-09-07", "2026-09-07T21:30");
    assert!(!info.mandatory && !info.last_chance);
    // The next day it has expired (`on-miss:expire` carries nothing), and a
    // query for 09-08 alone does not reach the window at all.
    let v = w.instances("a3", ("2026-09-01", "2026-09-08"), "2026-09-08");
    assert_eq!(keys(&v), vec!["2026-09-07"]);
    assert_eq!(v[0].status, InstanceStatus::Expired);
    let after = w.info("a3", &v[0], "2026-09-08", "2026-09-08T09:00");
    assert!(!after.mandatory && !after.last_chance);
    assert!(!after.overdue, "expired, not carried into today");
    assert!(w
        .instances("a3", ("2026-09-08", "2026-09-08"), "2026-09-08")
        .is_empty());
}

#[test]
fn todays_instances_hold_what_the_planner_may_place() {
    let w = load();
    let items: Vec<&Item> = w.tree.iter().collect();
    let today = recur::today_instances(
        items,
        date("2026-09-07"),
        dt("2026-09-07T10:42"),
        &w.replay,
        &w.cfg,
    );
    let names: Vec<String> = today.iter().map(|(i, _)| i.item.to_string()).collect();
    // Windows that closed before 10:42 are gone (breakfast, standup, stretch,
    // last night's sleep); everything still placeable is here, each item once:
    // the laundry's carried `persist` instance is *the* laundry instance today
    // (§5.3), not one of two.
    assert_eq!(
        names,
        vec![
            "k1",
            "a3",
            "a6",
            "a7",
            "sleep",
            "lunch",
            "workout",
            "water-plants",
            "laundry",
            "groceries",
            "shower",
            "vitamins",
        ]
    );
    let mandatory: Vec<String> = today
        .iter()
        .filter(|(_, info)| info.mandatory)
        .map(|(i, _)| i.item.to_string())
        .collect();
    assert_eq!(
        mandatory,
        vec!["k1", "a3", "lunch", "workout", "water-plants", "laundry"]
    );
    // Overdue: last week's laundry window (persist, so it carries) and the
    // vitamins, whose after-done due passed on 09-05 with no validity limit.
    let carried: Vec<String> = today
        .iter()
        .filter(|(_, info)| info.overdue)
        .map(|(i, _)| i.item.to_string())
        .collect();
    assert_eq!(carried, vec!["laundry", "vitamins"]);
}
