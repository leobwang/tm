//! **`tm resume` ends the interruption, not a pause the user took before it** — the W-44 repair
//! (README gap 4610, the campaign's call, parity P96).
//!
//! The kernel's replay has always read the log so (fork 4748911's own machine: `pause`/`unpause`
//! set and clear the block's pause, `interrupt`/`resume` the interruption, and a block resumed from
//! an interruption it was paused across stays paused), and the host read it otherwise: one open span
//! that an `unpause` OR a `resume` closed. DRIVEN by W-44's auditor on the shipped binary — `start`
//! 09:00, `pause` 09:10, `interrupt` 09:20, `resume` 09:30 — `tm now` at 09:45 drew the block running
//! (`25m of 360m`), `tm stop` at 10:00 said "after 40m", and `tm review day` credited 10 while `tm
//! plan` drew 09:30-10:00 as the pause: one log, two readings. The host follows the log's replay now
//! (D42, D69: the cache follows the log): the block stays paused, `tm resume` says so, and `tm pause`
//! resumes it.
//!
//! Each test reads what a user reads — the words, `tm --json now` with the cache and after deleting
//! it, `tm stop`'s minutes, `tm review day`'s credit and `tm plan`'s past rows — on the example tree.

mod cli_common;

use std::fs;

use cli_common::Tm;
use serde_json::Value;

fn at(hm: &str) -> String {
    format!("2026-09-07T{hm}:00-05:00")
}

/// The example tree, woken at 07:00, `^m1` started at 09:00.
fn started() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    tm
}

/// `tm stop`'s "after Nm".
fn stopped_after(tm: &Tm, hm: &str) -> u64 {
    let out = tm.ok_at(&at(hm), &["stop"]);
    let after = out.stdout.split("after ").nth(1).expect("after").split('m').next().expect("minutes");
    after.parse().unwrap_or_else(|_| panic!("{}", out.stdout))
}

fn review_min(tm: &Tm, hm: &str) -> u64 {
    tm.json_at(&at(hm), &["review", "day"])["review"]["block_min"].as_u64().expect("block_min")
}

/// The plan's rows of `^m1`'s morning before `hm`: (start, end, kind).
fn rows(tm: &Tm, hm: &str) -> Vec<(String, String, String)> {
    let plan = tm.json_at(&at(hm), &["plan"]);
    plan["segments"]
        .as_array()
        .expect("segments")
        .iter()
        .filter(|g| ["block", "pause", "lost", "break"].contains(&g["kind"].as_str().unwrap_or_default()))
        .filter(|g| g["start"].as_str().unwrap_or_default() < hm)
        .map(|g| {
            let s = |k: &str| g[k].as_str().unwrap_or_default().to_string();
            (s("start"), s("end"), s("kind"))
        })
        .collect()
}

fn active(v: &Value) -> (bool, u64) {
    (v["active"]["paused"].as_bool().expect("paused"), v["active"]["elapsed_min"].as_u64().expect("elapsed"))
}

#[test]
fn a_block_paused_before_an_interruption_stays_paused_after_the_resume() {
    let tm = started();
    tm.ok_at(&at("09:10"), &["pause"]);
    tm.ok_at(&at("09:20"), &["interrupt"]);
    let out = tm.ok_at(&at("09:30"), &["resume"]);
    assert!(out.stdout.contains("resumed · lost 10m · ^m1 still paused"), "{}", out.stdout);
    let json = tm.json_at(&at("09:31"), &["now"]);
    assert_eq!(active(&json), (true, 10), "{json}");
    // The cache follows the log (D42): deleting it rebuilds the same reading.
    fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    assert_eq!(active(&tm.json_at(&at("09:45"), &["now"])), (true, 10));
    assert_eq!(stopped_after(&tm, "10:00"), 10, "the minutes after the resume were not worked");
    assert_eq!(review_min(&tm, "10:01"), 10, "one reading: the kernel's credit");
    let r = rows(&tm, "10:01");
    assert!(r.contains(&("09:30".into(), "10:00".into(), "pause".into())), "{r:?}");
    assert!(!r.iter().any(|(s, _, k)| k == "block" && s.as_str() >= "09:30"), "{r:?}");
}

#[test]
fn the_resume_reports_the_held_block_in_json() {
    let tm = started();
    tm.ok_at(&at("09:10"), &["pause"]);
    tm.ok_at(&at("09:20"), &["interrupt"]);
    let v = tm.json_at(&at("09:30"), &["resume"]);
    assert_eq!(v["still_paused"], "m1", "{v}");
    assert_eq!(v["lost_min"], 10, "{v}");
}

/// `tm pause` resumes the held block, and the minutes after it are worked — one number on every reader.
#[test]
fn tm_pause_resumes_the_held_block() {
    let tm = started();
    tm.ok_at(&at("09:10"), &["pause"]);
    tm.ok_at(&at("09:20"), &["interrupt"]);
    tm.ok_at(&at("09:30"), &["resume"]);
    let out = tm.ok_at(&at("09:50"), &["pause"]);
    assert!(out.stdout.contains("resumed ^m1"), "{}", out.stdout);
    assert_eq!(active(&tm.json_at(&at("09:55"), &["now"])), (false, 15));
    assert_eq!(stopped_after(&tm, "10:00"), 20);
    assert_eq!(review_min(&tm, "10:01"), 20);
}

/// The control: a pause the user lifted before the interruption — the resume runs the block, as it did.
#[test]
fn a_block_running_at_the_interruption_runs_after_the_resume() {
    let tm = started();
    tm.ok_at(&at("09:10"), &["pause"]);
    tm.ok_at(&at("09:15"), &["pause"]);
    tm.ok_at(&at("09:20"), &["interrupt"]);
    let out = tm.ok_at(&at("09:30"), &["resume"]);
    assert!(!out.stdout.contains("still paused"), "{}", out.stdout);
    assert_eq!(active(&tm.json_at(&at("09:45"), &["now"])), (false, 30));
    assert_eq!(stopped_after(&tm, "10:00"), 45);
    assert_eq!(review_min(&tm, "10:01"), 45);
}
