//! **A block worked across local midnight logs its real worked minutes** — the
//! owner's D75 (README gap 3715, with gap 3625), parity P65, stage 6 W-40
//! track T.
//!
//! `tm done`, `tm stop` and `tm done --partial` computed the running block's
//! worked minutes from `.tm/state.json`'s `active.started`, a bare `HH:MM`,
//! placed on TODAY's date — fork 4748911's `day::worked_min`. After local
//! midnight that start is tonight's, in the future, so a block begun at 23:00
//! and finished at 01:00 logged `actual_min: 0`, `tm stop` wrote the whole
//! estimate back as left, and `tm now` read `0m of 60m` while `tm plan`'s `▶`
//! row read the right minutes (gap 3625). The duration fit read a zero for
//! every block done across midnight. Now every one of those paths reads the
//! block's start INSTANT from the log's own `start` line (`Replay::
//! running_worked_min`, `day::worked_min`), and nets out the pauses of every
//! day since — the evening's pause is filed under the evening's seam, and,
//! before the next `wake`, so is the morning's.
//!
//! The world is the owner's: `start` 23:00, `pause` 23:30, `pause` 00:30 (the
//! toggle resumes), finished at 01:00 — sixty minutes worked.

mod cli_common;

use cli_common::Tm;

/// The owner's drive, up to 00:40 on the Wednesday: `^t4` started Tuesday
/// 23:00, paused 23:30–00:30 by two typed `tm pause`.
fn worked_across_midnight(wake: bool) -> Tm {
    let tm = Tm::new();
    if wake {
        tm.ok_at("2026-09-08T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    }
    tm.ok_at("2026-09-08T23:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-08T23:30:00-05:00", &["pause"]);
    tm.ok_at("2026-09-09T00:30:00-05:00", &["pause"]);
    tm
}

/// `tm done` at 01:00 logs the sixty minutes worked, with a `wake` logged the
/// morning before (every entry then filed under Tuesday's wake) and without
/// one (each filed under its own local date) — and `tm now` at 00:40 agrees
/// with `tm plan`'s `▶` row: forty worked, twenty left.
#[test]
fn tm_done_after_midnight_logs_the_minutes_worked() {
    for wake in [true, false] {
        let tm = worked_across_midnight(wake);
        let at = "2026-09-09T00:40:00-05:00";
        let json = tm.json_at(at, &["now"]);
        assert_eq!(json["active"]["started"], "23:00", "wake {wake}: {json}");
        assert_eq!(json["active"]["elapsed_min"], 40, "wake {wake}: 23:00–23:30 and 00:30–00:40: {json}");
        let head = tm.ok_at(at, &["now"]).stdout;
        assert!(
            head.lines().next().unwrap_or_default().ends_with("· 40m of 60m"),
            "wake {wake}: the header reads the log's start, not tonight's 23:00: {head}"
        );
        assert!(head.contains("running · 20m left"), "wake {wake}: the ▶ row agrees: {head}");

        let done = tm.json_at("2026-09-09T01:00:00-05:00", &["done"]);
        assert_eq!(done["actual_min"], 60, "wake {wake}: {done}");
        let logged = tm.last_ev("done");
        assert_eq!(logged["actual_min"], 60, "wake {wake}: the log reads the minutes worked: {logged}");
        assert_eq!(logged["est_min"], 60, "wake {wake}: {logged}");
    }
}

/// `tm stop` at 01:00 says sixty minutes worked and writes the floor back as
/// left (60 − 60, at least `MIN_REMAINING_MIN`), where the fork wrote the
/// whole estimate back; and `tm done --partial` writes the same remainder.
#[test]
fn tm_stop_and_a_partial_done_after_midnight_count_the_minutes_worked() {
    let tm = worked_across_midnight(true);
    let stop = tm.json_at("2026-09-09T01:00:00-05:00", &["stop"]);
    assert_eq!(stop["worked_min"], 60, "{stop}");
    assert_eq!(stop["remaining_min"], 5, "{stop}");
    assert_eq!(tm.last_ev("stop")["remaining_min"], 5, "{:?}", tm.last());
    assert!(tm.line("week/2026-W37.md", "t4").contains(" 5m "), "{}", tm.line("week/2026-W37.md", "t4"));

    let tm = worked_across_midnight(true);
    let partial = tm.json_at("2026-09-09T01:00:00-05:00", &["done", "--partial"]);
    assert_eq!(partial["actual_min"], 60, "{partial}");
    assert_eq!(partial["remaining_min"], 5, "{partial}");
    let logged = tm.last_ev("done");
    assert_eq!((logged["actual_min"].as_u64(), logged["partial"].as_bool()), (Some(60), Some(true)), "{logged}");
}

/// The start is the LOG's, and `.tm/state.json`'s clock is never read for it:
/// a cache whose `active.started` says 23:55 changes nothing about the minutes
/// logged, because the log's `start` line says 23:00 — and deleting the cache
/// changes nothing either (D42).
#[test]
fn the_minutes_count_from_the_logs_start_and_not_the_caches_clock() {
    let tm = worked_across_midnight(true);
    let state_path = tm.plan.join(".tm/state.json");
    let mut state = tm.state();
    assert_eq!(state["active"]["started"], "23:00", "{state}");
    state["active"]["started"] = serde_json::Value::String("23:55".to_string());
    std::fs::write(&state_path, serde_json::to_string_pretty(&state).expect("json")).expect("write");
    let edited = tm.json_at("2026-09-09T00:40:00-05:00", &["now"]);
    assert_eq!(edited["active"]["elapsed_min"], 40, "{edited}");
    assert_eq!(edited["active"]["started"], "23:00", "the header prints the log's start: {edited}");

    std::fs::remove_file(&state_path).expect("delete the cache");
    let rebuilt = tm.json_at("2026-09-09T00:40:00-05:00", &["now"]);
    assert_eq!(rebuilt["active"]["elapsed_min"], 40, "{rebuilt}");
    assert_eq!(tm.json_at("2026-09-09T01:00:00-05:00", &["done"])["actual_min"], 60);
}

/// **A pause longer than a day is netted out whole.** The idle minutes were
/// clamped to one day (`24 * 60`, the one-day reading's own bound); a block
/// read from the log's start can run past one. `^t4` started Monday 09:00,
/// paused 09:30, resumed Tuesday 10:00 — 24½ hours paused — and done at 10:30:
/// sixty minutes worked, where the clamp netted out 1,440 of the 1,470 and
/// logged ninety. No `wake` is logged, so each mark is filed under its own
/// local date and the two halves of the pause are two days' seams.
#[test]
fn a_pause_longer_than_a_day_is_netted_out_whole() {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T09:30:00-05:00", &["pause"]);
    tm.ok_at("2026-09-08T10:00:00-05:00", &["pause"]);
    let now = tm.json_at("2026-09-08T10:20:00-05:00", &["now"]);
    assert_eq!(now["active"]["elapsed_min"], 50, "{now}");
    let done = tm.json_at("2026-09-08T10:30:00-05:00", &["done"]);
    assert_eq!(done["actual_min"], 60, "{done}");
    assert_eq!(tm.last_ev("done")["actual_min"], 60, "{:?}", tm.last());
}

/// Inside one day nothing moves: the same pause on a block begun and finished
/// on Tuesday is netted out exactly as before (the rule reads Tuesday's marks,
/// as it always did).
#[test]
fn a_block_inside_its_day_is_counted_as_before() {
    let tm = Tm::new();
    tm.ok_at("2026-09-08T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-08T21:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-08T21:30:00-05:00", &["pause"]);
    tm.ok_at("2026-09-08T22:30:00-05:00", &["pause"]);
    assert_eq!(tm.json_at("2026-09-08T22:40:00-05:00", &["now"])["active"]["elapsed_min"], 40);
    assert_eq!(tm.json_at("2026-09-08T23:00:00-05:00", &["done"])["actual_min"], 60);
}

/// **`tm resume` after local midnight logs the minutes the interruption lost** —
/// the W-40 repair (README gaps 3821 and 3951), parity P69: D75's clock applied to
/// the interruption, whose own `interrupt` line holds its instant. `tm interrupt` at
/// Tuesday 23:40 and `tm resume` at 00:20 lost forty minutes; fork 4748911 put
/// `.tm/state.json`'s `23:40` on TODAY's date and logged `lost_min: 0`, and so did
/// this binary until the repair. Inside one day nothing moves (twenty minutes).
#[test]
fn tm_resume_after_midnight_logs_the_minutes_lost() {
    for (from, to, lost) in [
        ("2026-09-08T23:40:00-05:00", "2026-09-09T00:20:00-05:00", 40),
        ("2026-09-08T22:00:00-05:00", "2026-09-08T22:20:00-05:00", 20),
    ] {
        let tm = Tm::new();
        tm.ok_at("2026-09-08T21:30:00-05:00", &["start", "^t4", "--energy", "4"]);
        tm.ok_at(from, &["interrupt"]);
        tm.ok_at(to, &["resume"]);
        let logged = tm.last_ev("resume");
        assert_eq!(logged["lost_min"], lost, "{from} → {to}: the log reads the minutes lost: {logged}");
    }
}
