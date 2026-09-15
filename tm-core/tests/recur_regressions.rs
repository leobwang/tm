//! Regressions for `recur.rs` (§5.1–§5.3), each one a bug a review found.
//!
//! Synthetic one-line items and hand-written logs, so every case is readable
//! on its own: phase anchors that must not depend on the caller's range, the
//! `every:Nw` week count across a 53-week ISO year, ordinals that must survive
//! a skip and two completions in one day, §5.3's `on-miss:next` row for
//! `after-done:`, and the `last_chance` badge at a window that has closed.

#[path = "../../tm/tests/support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

use chrono::{NaiveDate, NaiveDateTime};
use tm_core::config::Config;
use tm_core::grammar::{parse_line, ParseCtx};
use tm_core::log::Replay;
use tm_core::model::{Instance, InstanceKey, InstanceStatus, Item, IsoWeek};
use tm_core::recur;

fn cfg() -> Config {
    Config::default()
}

/// A routine line (`routines.md`: no state, no id — keyed by title).
fn routine(text: &str) -> Item {
    let ctx = ParseCtx::new("routines.md", cfg().block_min());
    parse_line(text, &ctx).expect("line parses")
}

/// A backlog line (`^id`, explicit state).
fn backlog(text: &str) -> Item {
    let ctx = ParseCtx::new("backlog.md", cfg().block_min());
    parse_line(text, &ctx).expect("line parses")
}

fn replay_of(jsonl: &str) -> Replay {
    chokepoint::replay_of_text(jsonl, cfg().tz)
}

fn date(s: &str) -> NaiveDate {
    tm_core::model::parse_date(s).expect("date")
}

fn dt(s: &str) -> NaiveDateTime {
    tm_core::model::parse_datetime(s).expect("datetime")
}

fn statuses(v: &[Instance]) -> Vec<String> {
    v.iter()
        .map(|i| format!("{} {:?}", i.key, i.status))
        .collect()
}

/// The dates an item recurs on, over a range.
fn dates(item: &Item, from: &str, to: &str, today: &str, replay: &Replay) -> Vec<NaiveDate> {
    recur::instances(item, (date(from), date(to)), date(today), replay, &cfg())
        .into_iter()
        .filter_map(|i| match i.key {
            InstanceKey::Date(d) => Some(d),
            InstanceKey::Nth(_) => None,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// `every:Nd` phase anchor (§5.1 Calendar)
// ---------------------------------------------------------------------------

#[test]
fn every_nd_without_a_completion_does_not_depend_on_the_query_range() {
    // With no logged completion the phase used to fall back to the range
    // start, so `today_instances` (which asks about `today − 60`) made an
    // `every:3d` item due every single day and an `every:7d` item due never.
    let empty = replay_of("");
    for (line, n) in [
        ("- water win:08:00-20:00 dur:10m every:3d", 3),
        ("- filters win:08:00-20:00 dur:10m every:7d", 7),
    ] {
        let item = routine(line);
        let mut hits = 0;
        // 21 days is a whole number of periods either way, so the count is
        // exact whatever the phase.
        for day in 0..21 {
            let today = date("2026-09-07") + chrono::Duration::days(day);
            let now = today.and_hms_opt(10, 0, 0).expect("valid time");
            let planner = recur::today_instances([&item], today, now, &empty, &cfg());
            let alone = recur::instances(&item, (today, today), today, &empty, &cfg());
            assert_eq!(
                planner.len(),
                alone.len(),
                "{line}: today_instances and a one-day query disagree on {today}"
            );
            hits += planner.len();
        }
        assert_eq!(hits, 21 / n, "{line}: one occurrence every {n} days");
    }
}

#[test]
fn every_nd_agrees_between_the_day_planner_and_the_week_grid() {
    // Same item, same day, two entry points: the Today screen and the
    // Necessities grid must name the same dates.
    let item = routine("- flowers win:08:00-20:00 dur:10m every:3d");
    let empty = replay_of("");
    let week = IsoWeek::parse("2026-W37").expect("week");
    let today = date("2026-09-08");
    let now = dt("2026-09-08T10:00");
    let grid: Vec<String> = recur::week_instances([&item], week, today, now, &empty, &cfg())
        .iter()
        .map(|(i, _)| i.key.to_string())
        .collect();
    for day in week.dates() {
        let now = day.and_hms_opt(10, 0, 0).expect("valid time");
        let planned = !recur::today_instances([&item], day, now, &empty, &cfg()).is_empty();
        assert_eq!(
            planned,
            grid.contains(&day.to_string()),
            "{day}: Today and Necessities disagree"
        );
    }
    // …and the phase is the item's own: three days apart, whatever is asked.
    let from_far = dates(&item, "2026-08-01", "2026-09-30", "2026-09-08", &empty);
    let from_near = dates(&item, "2026-09-01", "2026-09-14", "2026-09-08", &empty);
    assert!(from_near.iter().all(|d| from_far.contains(d)));
    for pair in from_far.windows(2) {
        assert_eq!((pair[1] - pair[0]).num_days(), 3);
    }
}

#[test]
fn every_nd_is_still_anchored_at_the_first_logged_completion() {
    let item = routine("- water-plants win:08:00-20:00 dur:10m every:3d");
    let replay = replay_of(
        r#"{"t":"2026-08-26T09:55:00-05:00","ev":"routine","item":"water-plants","inst":"2026-08-26","status":"done","actual_min":8}"#,
    );
    assert_eq!(
        dates(&item, "2026-08-24", "2026-09-08", "2026-09-07", &replay)
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        vec![
            "2026-08-26",
            "2026-08-29",
            "2026-09-01",
            "2026-09-04",
            "2026-09-07"
        ]
    );
}

// ---------------------------------------------------------------------------
// `every:Nw` across a 53-week ISO year (§5.1 Calendar)
// ---------------------------------------------------------------------------

#[test]
fn every_2w_keeps_its_rhythm_across_a_53_week_year() {
    // 2026 is a 53-week ISO year: parity on the ISO week *number* used to put
    // 2027-01-03 (2026-W53) and 2027-01-10 (2027-W01) back to back.
    let empty = replay_of("");
    let sundays = routine("- deep-clean win:10:00-18:00 dur:2h every:2w:Sun");
    let v = dates(&sundays, "2026-11-01", "2027-03-01", "2026-11-01", &empty);
    assert!(v.contains(&date("2026-12-20")));
    assert!(!v.contains(&date("2027-01-10")), "{v:?}");
    for pair in v.windows(2) {
        assert_eq!((pair[1] - pair[0]).num_days(), 14, "{v:?}");
    }
    // `every:2w` (no weekday) spans whole weeks and must alternate too.
    let weeks = routine("- deep-clean-w win:10:00-18:00 dur:2h every:2w");
    let v = dates(&weeks, "2026-11-01", "2027-03-01", "2026-11-01", &empty);
    for pair in v.windows(2) {
        assert_eq!((pair[1] - pair[0]).num_days(), 14, "{v:?}");
    }
    // The 2026 phase is unchanged: the fixture's Sundays still hold.
    let v = dates(&sundays, "2026-08-01", "2026-10-31", "2026-09-07", &empty);
    assert_eq!(v[0], date("2026-08-02"));
    assert_eq!(v.last(), Some(&date("2026-10-25")));
}

// ---------------------------------------------------------------------------
// Ordinals (§5.1 "exactly one pending instance", §10.1)
// ---------------------------------------------------------------------------

#[test]
fn skipping_an_after_done_instance_moves_on_to_the_next_ordinal() {
    // The ordinal used to count completions only, so a skip left the pending
    // key pinned to an instance the log had already closed — and the routine
    // never came back.
    let shower = routine("- shower win:06:00-23:00 dur:20m after-done:2d~1d");
    let replay = replay_of(
        r##"{"t":"2026-09-05T08:00:00-05:00","ev":"routine","item":"shower","inst":"#1","status":"done","actual_min":18}
{"t":"2026-09-07T09:00:00-05:00","ev":"skip","item":"shower","inst":"#2"}"##,
    );
    let st = recur::after_done_state(&shower, &replay, date("2026-09-07"), &cfg()).expect("state");
    assert_eq!(st.count, 1, "one completion");
    assert_eq!(st.pending, 3, "#2 was skipped");
    for day in ["2026-09-07", "2026-09-08", "2026-09-15", "2026-10-15"] {
        let v = recur::instances(
            &shower,
            (date("2026-09-01"), date("2026-12-31")),
            date(day),
            &replay,
            &cfg(),
        );
        assert_eq!(
            statuses(&v),
            vec!["#1 Done", "#2 Skipped", "#3 Pending"],
            "on {day}"
        );
        let now = date(day).and_hms_opt(9, 30, 0).expect("valid time");
        assert!(
            !recur::today_instances([&shower], date(day), now, &replay, &cfg()).is_empty(),
            "the shower is still plannable on {day}"
        );
    }
}

#[test]
fn skipping_an_on_event_instance_moves_on_to_the_next_ordinal() {
    let item = backlog("- [ ] 2 15m Ping the landlord about the lease  on-event:lease ^a6");
    let replay = replay_of(r##"{"t":"2026-09-07T09:00:00-05:00","ev":"skip","item":"a6","inst":"#1"}"##);
    let v = recur::instances(
        &item,
        (date("2026-09-07"), date("2026-09-07")),
        date("2026-09-07"),
        &replay,
        &cfg(),
    );
    assert_eq!(statuses(&v), vec!["#1 Skipped", "#2 Pending"]);
}

#[test]
fn two_completions_on_one_day_get_their_own_ordinals() {
    // A sub-day `after-done:` item: the second dose used to collide with the
    // ordinal the log already had as done, leaving the rest of the day empty.
    let meds = routine("- meds win:06:00-23:00 dur:5m after-done:6h");
    let replay = replay_of(
        r##"{"t":"2026-09-07T08:00:00-05:00","ev":"routine","item":"meds","inst":"#1","status":"done","actual_min":5}
{"t":"2026-09-07T14:30:00-05:00","ev":"routine","item":"meds","inst":"#2","status":"done","actual_min":5}"##,
    );
    let st = recur::after_done_state(&meds, &replay, date("2026-09-07"), &cfg()).expect("state");
    assert_eq!(st.count, 2, "two doses, one day");
    assert_eq!(st.pending, 3);
    assert_eq!(st.due, date("2026-09-07"), "14:30 + 6h is still today");
    let v = recur::instances(
        &meds,
        (date("2026-09-07"), date("2026-09-07")),
        date("2026-09-07"),
        &replay,
        &cfg(),
    );
    assert_eq!(statuses(&v), vec!["#1 Done", "#2 Done", "#3 Pending"]);
    // …and the 20:30 dose is still plannable at 20:00.
    let planner: Vec<String> = recur::today_instances(
        [&meds],
        date("2026-09-07"),
        dt("2026-09-07T20:00"),
        &replay,
        &cfg(),
    )
    .iter()
    .map(|(i, _)| i.key.to_string())
    .collect();
    assert_eq!(planner, vec!["#3"]);
}

// ---------------------------------------------------------------------------
// §5.3 `on-miss:next` on an `after-done:` item
// ---------------------------------------------------------------------------

#[test]
fn a_missed_after_done_next_is_skipped_and_the_next_one_is_unchanged() {
    // `next` used to be lumped in with `expire`, which re-dues the occurrence
    // to today. §5.3: the instance is Skipped, the next occurrence unchanged.
    let shower = routine("- shower win:07:00-23:00 dur:20m after-done:2d~1d on-miss:next");
    let replay = replay_of(
        r##"{"t":"2026-09-01T08:00:00-05:00","ev":"routine","item":"shower","inst":"#1","status":"done","actual_min":18}"##,
    );
    let st = recur::after_done_state(&shower, &replay, date("2026-09-10"), &cfg()).expect("state");
    assert!(st.missed);
    assert_eq!(st.due, date("2026-09-03"), "09-01 + 2d, unchanged");
    assert_eq!(st.valid_until, Some(date("2026-09-04")));
    let v = recur::instances(
        &shower,
        (date("2026-09-01"), date("2026-09-10")),
        date("2026-09-10"),
        &replay,
        &cfg(),
    );
    assert_eq!(statuses(&v), vec!["#1 Done", "#2 Skipped", "#3 Pending"]);
    assert_eq!(v[2].due, Some(dt("2026-09-03T23:00")));

    // `expire` (the default) does re-due it to today, with no skip in between.
    let expire = routine("- shower win:07:00-23:00 dur:20m after-done:2d~1d");
    let st = recur::after_done_state(&expire, &replay, date("2026-09-10"), &cfg()).expect("state");
    assert_eq!(st.due, date("2026-09-10"));
    let v = recur::instances(
        &expire,
        (date("2026-09-01"), date("2026-09-10")),
        date("2026-09-10"),
        &replay,
        &cfg(),
    );
    assert_eq!(statuses(&v), vec!["#1 Done", "#2 Pending"]);
}

// ---------------------------------------------------------------------------
// §5.2 badges
// ---------------------------------------------------------------------------

#[test]
fn a_window_that_has_already_closed_is_not_a_last_chance() {
    // `last_chance` ignored `now` while `mandatory` did not, so an instance
    // that could no longer be placed still got the "last chance today" badge.
    let breakfast = routine("- breakfast win:06:00-09:00 dur:30m every:day");
    let empty = replay_of("");
    let inst = recur::instances(
        &breakfast,
        (date("2026-09-07"), date("2026-09-07")),
        date("2026-09-07"),
        &empty,
        &cfg(),
    )
    .remove(0);
    let open = recur::instance_info(&breakfast, &inst, date("2026-09-07"), dt("2026-09-07T07:30"));
    assert!(open.mandatory && open.last_chance);
    let closed = recur::instance_info(&breakfast, &inst, date("2026-09-07"), dt("2026-09-07T10:42"));
    assert!(!closed.mandatory && !closed.last_chance);
    assert!(
        recur::today_instances(
            [&breakfast],
            date("2026-09-07"),
            dt("2026-09-07T10:42"),
            &empty,
            &cfg()
        )
        .is_empty(),
        "and the planner has already dropped it"
    );

    // An overnight window read at the morning it ends is over too.
    let sleep = routine("- sleep win:22:00-08:00 dur:8h30m every:day ci:0");
    let last_night = recur::instances(
        &sleep,
        (date("2026-09-06"), date("2026-09-06")),
        date("2026-09-07"),
        &empty,
        &cfg(),
    )
    .remove(0);
    let info = recur::instance_info(&sleep, &last_night, date("2026-09-07"), dt("2026-09-07T10:42"));
    assert_eq!(last_night.status, InstanceStatus::Pending);
    assert!(!info.last_chance && !info.mandatory);
    assert!(info.deferred_from_yesterday);
}

// ---------------------------------------------------------------------------
// §5.3: a persisted routine is one pending instance, not two
// ---------------------------------------------------------------------------

/// A weekly `on-miss:persist` routine that was missed keeps **one** pending
/// instance. §5.3 carries the missed one — it "stays Pending", mandatory and
/// overdue — and the occurrence that comes round while it is still open is the
/// same obligation, not a second load of laundry: `today_instances` used to
/// hand the planner both, which placed the routine twice in one day (§5.2
/// gives a window instance one position, §7.2 gives an item one `p`).
///
/// The one instance is keyed on the **newest** occurrence and carries the
/// miss's overdue and mandatory flags, and a completion settles every
/// occurrence behind it. Keying it on the oldest miss instead made the
/// obligation undischargeable: `tm routine done laundry` logged a
/// two-month-old key and the next command surfaced the next-oldest miss.
#[test]
fn a_missed_persist_routine_and_this_weeks_occurrence_are_one_instance() {
    let item = routine("- laundry win:09:00-21:00 dur:30m every:week on-miss:persist");
    let today = date("2026-09-07"); // the Monday of W37
    let now = dt("2026-09-07T10:42");
    let keys = |v: &[(Instance, recur::InstanceInfo)]| -> Vec<String> {
        v.iter().map(|(i, _)| i.key.to_string()).collect()
    };
    /// Every listed week's laundry, done on its Monday.
    fn washed(mondays: &[&str]) -> String {
        mondays
            .iter()
            .map(|d| {
                format!(
                    "{{\"t\":\"{d}T11:00:00-05:00\",\"ev\":\"routine\",\"item\":\"laundry\",\
                     \"inst\":\"{d}\",\"status\":\"done\",\"actual_min\":30}}"
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    // Every week washed but the last: 2026-08-31's window closed on Sunday
    // with nothing logged, so §5.3 carries it into today.
    const KEPT_UP: [&str; 8] = [
        "2026-07-06",
        "2026-07-13",
        "2026-07-20",
        "2026-07-27",
        "2026-08-03",
        "2026-08-10",
        "2026-08-17",
        "2026-08-24",
    ];
    let kept_up = replay_of(&washed(&KEPT_UP));

    // The history holds both live occurrences, each with its own status …
    let all = recur::instances(
        &item,
        (date("2026-08-24"), today),
        today,
        &kept_up,
        &cfg(),
    );
    assert_eq!(
        statuses(&all),
        vec![
            "2026-08-24 Done",
            "2026-08-31 Pending",
            "2026-09-07 Pending"
        ]
    );

    // … but the planner is handed one: this week's occurrence, wearing §5.3's
    // overdue and mandatory badge for the miss it stands in for.
    let live = recur::today_instances([&item], today, now, &kept_up, &cfg());
    assert_eq!(keys(&live), vec!["2026-09-07"]);
    assert!(live[0].1.mandatory && live[0].1.overdue);
    assert_eq!(live[0].1.carried_from, Some(date("2026-09-06")));

    // Wash it once and the carry is discharged with it: nothing is left to do
    // today, and the next command does not surface 2026-08-31 again.
    let washed_today = replay_of(&format!(
        "{}\n{}",
        washed(&KEPT_UP),
        washed(&["2026-09-07"])
    ));
    let after =
        recur::today_instances([&item], today, dt("2026-09-07T11:30"), &washed_today, &cfg());
    assert!(after.is_empty(), "{:?}", keys(&after));
}

/// The backwards half of the same collapse, on its own: a routine that has
/// never been logged has a whole `CARRY_LOOKBACK_DAYS` of missed occurrences
/// behind it, and doing it once has to settle all of them. It used to walk
/// backwards one occurrence per `tm routine done`, ten invocations before it
/// reached today and one stacked `✓ laundry` row per invocation.
#[test]
fn one_completion_discharges_the_whole_persist_backlog() {
    let item = routine("- laundry win:09:00-21:00 dur:30m every:week on-miss:persist");
    let today = date("2026-09-07");
    let now = dt("2026-09-07T07:00");
    let empty = replay_of("");

    let live = recur::today_instances([&item], today, now, &empty, &cfg());
    assert_eq!(
        live.iter().map(|(i, _)| i.key.to_string()).collect::<Vec<_>>(),
        vec!["2026-09-07"],
        "one obligation, and it is today's"
    );

    let done = replay_of(
        "{\"t\":\"2026-09-07T07:30:00-05:00\",\"ev\":\"routine\",\"item\":\"laundry\",         \"inst\":\"2026-09-07\",\"status\":\"done\",\"actual_min\":30}",
    );
    let after = recur::today_instances([&item], today, dt("2026-09-07T08:00"), &done, &cfg());
    assert!(
        after.is_empty(),
        "the two months of misses behind it went with it: {:?}",
        after.iter().map(|(i, _)| i.key.to_string()).collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// Moved verbatim from `src/recur.rs`'s unit tests at step R12, where they read
// an empty log parsed in place: every replay is now read through the
// test chokepoint, which `src/` cannot reach.
// ---------------------------------------------------------------------------

mod from_unit_tests {
    use chrono::{NaiveDate, NaiveDateTime};
    use tm_core::config::Config;
    use tm_core::grammar::{parse_line, ParseCtx};
    use tm_core::log::Replay;
    use tm_core::model::{InstanceKey, InstanceStatus, Item};
    use tm_core::recur::{instances, is_mandatory};

    fn cfg() -> Config {
        Config::default()
    }

    fn item(text: &str) -> Item {
        let ctx = ParseCtx::new("routines.md", cfg().block_min());
        parse_line(text, &ctx).expect("fixture line parses")
    }

    fn backlog_item(text: &str) -> Item {
        let ctx = ParseCtx::new("backlog.md", cfg().block_min());
        parse_line(text, &ctx).expect("fixture line parses")
    }

    fn replay_of(jsonl: &str) -> Replay {
        super::chokepoint::replay_of_text(jsonl, cfg().tz)
    }

    fn date(s: &str) -> NaiveDate {
        tm_core::model::parse_date(s).expect("date")
    }

    fn dt(s: &str) -> NaiveDateTime {
        tm_core::model::parse_datetime(s).expect("datetime")
    }

    #[test]
    fn daily_window_expands_over_the_range() {
        let it = item("- lunch win:11:30-13:30 dur:30m every:day");
        let r = replay_of("");
        let v = instances(
            &it,
            (date("2026-09-07"), date("2026-09-09")),
            date("2026-09-07"),
            &r,
            &cfg(),
        );
        assert_eq!(v.len(), 3);
        assert_eq!(v[0].key, InstanceKey::Date(date("2026-09-07")));
        assert_eq!(v[0].window, Some((dt("2026-09-07T11:30"), dt("2026-09-07T13:30"))));
        assert_eq!(v[0].due, Some(dt("2026-09-07T13:30")));
        assert!(v.iter().all(|i| i.status == InstanceStatus::Pending));
    }

    #[test]
    fn overnight_window_runs_into_the_next_morning() {
        let it = item("- sleep win:22:00-08:00 dur:8h30m every:day ci:0");
        let r = replay_of("");
        let v = instances(
            &it,
            (date("2026-09-07"), date("2026-09-07")),
            date("2026-09-07"),
            &r,
            &cfg(),
        );
        assert_eq!(
            v[0].window,
            Some((dt("2026-09-07T22:00"), dt("2026-09-08T08:00")))
        );
    }

    #[test]
    fn monthly_clamps_to_the_month_length() {
        let it = item("- bins win:07:00-09:00 dur:10m every:month:31");
        let r = replay_of("");
        let v = instances(
            &it,
            (date("2026-02-01"), date("2026-03-31")),
            date("2026-02-01"),
            &r,
            &cfg(),
        );
        let keys: Vec<InstanceKey> = v.iter().map(|i| i.key).collect();
        assert_eq!(
            keys,
            vec![
                InstanceKey::Date(date("2026-02-28")),
                InstanceKey::Date(date("2026-03-31")),
            ]
        );
    }

    #[test]
    fn a_recurring_item_without_a_window_is_due_at_the_end_of_its_day() {
        let it = backlog_item("- [ ] 2 30m Pay the water bill  every:month:1 ^w1");
        let r = replay_of("");
        let v = instances(
            &it,
            (date("2026-09-01"), date("2026-10-31")),
            date("2026-09-07"),
            &r,
            &cfg(),
        );
        assert_eq!(v.len(), 2);
        assert_eq!(v[0].due, Some(dt("2026-09-01T23:59")));
        assert_eq!(v[0].window, None);
        assert_eq!(v[0].status, InstanceStatus::Pending, "on-miss:persist");
        // No window, so it is never a "placed before any task" instance.
        assert!(!is_mandatory(
            &it,
            &v[0],
            date("2026-09-07"),
            dt("2026-09-07T10:42")
        ));
    }

    #[test]
    fn missing_expire_window_expires_and_persist_carries() {
        let expire = item("- lunch win:11:30-13:30 dur:30m every:day");
        let persist = item("- laundry win:09:00-21:00 dur:30m every:day on-miss:persist");
        let next = item("- stretch win:07:00-09:00 dur:15m every:day on-miss:next");
        let r = replay_of("");
        let range = (date("2026-09-05"), date("2026-09-05"));
        let today = date("2026-09-07");
        assert_eq!(
            instances(&expire, range, today, &r, &cfg())[0].status,
            InstanceStatus::Expired
        );
        assert_eq!(
            instances(&persist, range, today, &r, &cfg())[0].status,
            InstanceStatus::Pending
        );
        assert_eq!(
            instances(&next, range, today, &r, &cfg())[0].status,
            InstanceStatus::Skipped
        );
    }

    #[test]
    fn waiting_item_has_no_pending_instance_until_the_timeout() {
        let it = backlog_item("- [?] 2 15m Ask about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4");
        let r = replay_of("");
        let range = (date("2026-09-07"), date("2026-09-07"));
        assert!(instances(&it, range, date("2026-09-07"), &r, &cfg()).is_empty());
        let later = (date("2026-09-13"), date("2026-09-13"));
        assert_eq!(
            instances(&it, later, date("2026-09-13"), &r, &cfg()).len(),
            1
        );
    }

}
