//! **`tm energy N --at HH:MM` names today's clock unless that is MORE THAN
//! TWELVE HOURS after now, and then yesterday's** — the owner's D86 (README
//! gap 4135), stage 6 W-42 track H, parity **P82**.
//!
//! Fork 4748911 put every `--at` clock on TODAY's date, so a report typed
//! after midnight for the evening before — `tm energy 3 --at 23:40` at 00:40 —
//! was logged 23 hours AHEAD, tomorrow evening, and the §8.5 posterior and the
//! fit filed it under the wrong day. D79 gave `tm stop --at` and `tm done
//! --at` the latest such time at or before now; the owner did NOT give
//! `energy` that rule, because a report may name a time a little ahead on the
//! same day — `cli_day.rs`' fork-pinned `energy_logs_a_report_against_the_prediction`
//! and its `energy_json` snapshot (`--at 10:30` at 09:00 is today's 10:30),
//! which this file leaves untouched and which still passes. The rule has one
//! definition, `tm_core::capacity::report_at`; the clock has one parser for
//! every `--at` (`cli_conformance.rs`' `every_at_flag_is_read_by_the_one_parser`).
//!
//! "More than twelve hours" is ELAPSED time, so a DST change moves the edge by
//! its hour, and a report dated yesterday counts its hours since wake from
//! THAT day's wake (README gap 4260, the composition with P79): P79's reading
//! — the wake before NOW — counted `--at 22:00` typed at 09:00 the next morning
//! as `hsw: -9.0`.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

/// Every `energy` line of the log.
fn energy_lines(tm: &Tm) -> Vec<Value> {
    tm.log().into_iter().filter(|e| e["ev"] == "energy").collect()
}

/// `tm --json energy 3 --at <at>` at `now`: the verb's own answer and the line it logged.
fn report(tm: &Tm, now: &str, at: &str) -> (Value, Value) {
    let shown = tm.json_at(now, &["energy", "3", "--at", at]);
    let logged = energy_lines(tm).pop().expect("the report is logged");
    (shown, logged)
}

/// A tree woken at `clock` on `date` (`--now` the wake itself).
fn woken(date: &str, clock: &str, offset: &str) -> Tm {
    let tm = Tm::new();
    tm.ok_at(&format!("{date}T{clock}:00{offset}"), &["wake", clock]);
    tm
}

/// **The owner's example**: `--at 23:40` typed at 00:40 is LAST NIGHT — logged
/// at Monday 23:40, said dated, its hours since wake Monday's 16.67 — where
/// fork 4748911 logged Tuesday 23:40, 23 hours ahead, with `hsw: 40.67`.
#[test]
fn a_report_typed_after_midnight_for_the_evening_before_is_last_nights() {
    let tm = woken("2026-09-07", "07:00", "-05:00");
    let (shown, logged) = report(&tm, "2026-09-08T00:40:00-05:00", "23:40");
    assert_eq!(logged["t"], "2026-09-07T23:40:00-05:00", "{logged}");
    assert_eq!(logged["hsw"].as_f64(), Some(16.67), "{logged}");
    assert_eq!(shown["at"], "2026-09-07 23:40", "the answer says the date it names: {shown}");
    // And without `--at` the report is now's, as ever.
    let (shown, logged) = (tm.json_at("2026-09-08T00:45:00-05:00", &["energy", "3"]), energy_lines(&tm).pop());
    assert_eq!(logged.expect("logged")["t"], "2026-09-08T00:45:00-05:00");
    assert_eq!(shown["at"], "00:45");
}

/// **The edge is twelve hours of ELAPSED time.** At 09:00 `--at 21:00` (exactly
/// twelve hours ahead) is today's and `--at 21:01` yesterday's; on the night
/// DST ends, 00:40 CDT to 12:30 CST is 12 h 50 m — yesterday's, where the wall
/// clock says 11 h 50 m; on the night it starts, 00:30 CST to 13:00 CDT is
/// 11 h 30 m — today's, where the wall clock says 12 h 30 m.
#[test]
fn the_edge_is_twelve_hours_of_elapsed_time_across_both_dst_changes() {
    for (at, t) in [("21:00", "2026-09-07T21:00:00-05:00"), ("21:01", "2026-09-06T21:01:00-05:00")] {
        let tm = woken("2026-09-07", "07:00", "-05:00");
        let (_, logged) = report(&tm, "2026-09-07T09:00:00-05:00", at);
        assert_eq!(logged["t"], t, "--at {at} at 09:00: {logged}");
    }
    let tm = woken("2026-10-31", "07:00", "-05:00");
    let (shown, logged) = report(&tm, "2026-11-01T00:40:00-05:00", "12:30");
    assert_eq!(logged["t"], "2026-10-31T12:30:00-05:00", "DST ends: {logged}");
    assert_eq!((shown["at"].as_str(), logged["hsw"].as_f64()), (Some("2026-10-31 12:30"), Some(5.5)), "{shown}");
    let tm = woken("2026-03-07", "07:00", "-06:00");
    let (shown, logged) = report(&tm, "2026-03-08T00:30:00-06:00", "13:00");
    assert_eq!(logged["t"], "2026-03-08T13:00:00-05:00", "DST starts: {logged}");
    assert_eq!(shown["at"], "13:00");
}

/// **A report dated yesterday is read on yesterday** (README gap 4260): woken
/// Monday 06:05 and Tuesday 07:00, `--at 22:00` typed Tuesday 09:00 is Monday
/// 22:00, and its hours since wake are Monday's 15.92 — the log's own wake
/// instant (D75) — never P79's `-9.0` from Tuesday's wake, after the report.
/// Its prediction reads Monday's night (`Ctx::slept_on`): two trees that differ
/// only in TUESDAY's sleep predict Monday evening alike, and Tuesday morning
/// apart (the sleep-debt shift, `energy.sleep_debt`).
#[test]
fn a_report_for_last_night_is_read_on_that_day() {
    let night = |slept: &str| {
        let tm = woken("2026-09-07", "06:05", "-05:00");
        tm.ok_at("2026-09-08T07:00:00-05:00", &["wake", "07:00", "--slept", slept]);
        let (_, evening) = report(&tm, "2026-09-08T09:00:00-05:00", "22:00");
        let (_, morning) = report(&tm, "2026-09-08T09:00:00-05:00", "08:30");
        (evening, morning)
    };
    let (short_evening, short_morning) = night("5h");
    let (long_evening, long_morning) = night("9h");
    for evening in [&short_evening, &long_evening] {
        assert_eq!(evening["t"], "2026-09-07T22:00:00-05:00", "{evening}");
        assert_eq!(evening["hsw"].as_f64(), Some(15.92), "Monday's wake, never negative: {evening}");
    }
    assert_eq!(short_evening["pred"], long_evening["pred"], "Tuesday's night does not move Monday evening");
    // Today's report counts from today's wake (P79, unchanged) and reads today's night.
    assert_eq!(short_morning["t"], "2026-09-08T08:30:00-05:00");
    assert_eq!(short_morning["hsw"].as_f64(), Some(1.5), "{short_morning}");
    assert_ne!(short_morning["pred"], long_morning["pred"], "Tuesday's night moves Tuesday morning: {short_morning} {long_morning}");
}

/// **`tm stop --at` and `tm done --at` keep D79's rule** — the same flag, the
/// same clock, the same instant, two rules, each the owner's: at 09:00 with a
/// block running since 08:30, `tm energy 3 --at 10:30` is today's 10:30 (a
/// forward report), while `tm stop --at 10:30` names the latest 10:30 at or
/// before now — yesterday's, before the block began — and is refused by name,
/// nothing written.
#[test]
fn stop_and_done_keep_d79s_rule_beside_energys() {
    let tm = woken("2026-09-07", "07:00", "-05:00");
    tm.ok_at("2026-09-07T08:30:00-05:00", &["start", "^t4", "--energy", "4"]);
    let (_, logged) = report(&tm, "2026-09-07T09:00:00-05:00", "10:30");
    assert_eq!(logged["t"], "2026-09-07T10:30:00-05:00", "{logged}");
    for verb in ["stop", "done"] {
        let before = tm.read(".tm/log.jsonl");
        let out = tm.run_at("2026-09-07T09:00:00-05:00", &[verb, "--at", "10:30"]);
        assert_eq!(out.code, 1, "{verb}: {}{}", out.stdout, out.stderr);
        assert!(
            out.stderr.contains("names 2026-09-06 10:30, the latest 10:30 at or before now"),
            "{verb}: D79's reading, by name: {}",
            out.stderr
        );
        assert_eq!(tm.read(".tm/log.jsonl"), before, "{verb}: nothing written");
    }
}
