//! **`tm resume` plans before it appends its own line, and what that leaves out** — stage 6 W-45, track Q (README
//! gap 4046, measured here; gap 4661 opened for the owner).
//!
//! `tm resume` clears `.tm/state.json`'s interruption, plans, and only then appends its `resume` line, because the
//! line records `dropped` — the items the replan no longer holds — and so needs the plan first (`day.rs`' `resume`;
//! fork 4748911's `resume` did the same).  The replan's request therefore carries a `log` section that still holds
//! the interruption OPEN beside a `planner` section that says nothing is interrupted (README gap 4046).  What that
//! draws was NOT MEASURED until this step.  Measured, on every interrupted day the planner generator draws
//! (`support/plangen.rs`; `scratchpad/w45-q/probe4046.log`, 189 days, the fork planner asked in-process in a
//! scratch test that is not committed because it names the fork outside a region):
//!
//! * **the kernel draws the resumed interruption exactly as fork 4748911 does, before the append and after it** —
//!   189 of 189 days, every row over the interruption's span equal — so R3's swap of this replan moves nothing;
//! * **the replan's future half is the day every later replan draws** — 189 of 189 equal before and after the
//!   append, in the kernel and in the fork;
//! * **its past half is not**: on every day whose interruption began before `now` (137 of 137) the replan `tm resume`
//!   writes has NO row over the interruption, and every later replan draws one more row, `lost` from the
//!   interruption's start to `now` with the note `interruption` — the `interrupt` segment the `resume` line closes.
//!
//! So the plan `tm resume` writes — the day file's `tm:plan` block, `.tm/last_plan.json` and the `plan` event's
//! hash — holds a hole where the interruption was until the next planning verb rewrites it, as the fork's did.
//! Planning after the append would close it, and would move `tm resume`'s written bytes away from fork 4748911's,
//! a divergence no standing decision covers: README gap 4661, the owner's.  This file is the instrument the switch's
//! `tm resume` must keep green (the owner's D21): [`the_plan_tm_resume_writes_leaves_the_interruption_it_resumes_undrawn`]
//! on the binary, and [`the_append_adds_exactly_the_interruptions_lost_row_to_the_past_half`] over the generator's
//! class, kernel only.

mod cli_common;

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[path = "support/planreq.rs"]
#[allow(dead_code)]
mod planreq;

#[path = "support/plangen.rs"]
#[allow(dead_code)]
mod plangen;

use std::sync::Mutex;

use chrono::DateTime;
use chrono_tz::Tz;
use cli_common::Tm;
use proptest::prelude::*;
use serde_json::Value;
use tm_core::dayplan::{DayPlan, SegKind};
use tm_core::priority;

fn at(hm: &str) -> String {
    format!("2026-09-07T{hm}:00-05:00")
}

/// The stored plan's rows as `(start, end, kind, item)`.
fn stored(tm: &Tm) -> Vec<(String, String, String, String)> {
    let v: Value = serde_json::from_str(&std::fs::read_to_string(tm.plan.join(".tm/last_plan.json")).expect("the stored plan"))
        .expect("json");
    v["segments"]
        .as_array()
        .expect("segments")
        .iter()
        .map(|s| {
            let f = |k: &str| s[k].as_str().unwrap_or_default().to_string();
            (f("start"), f("end"), f("kind"), f("item"))
        })
        .collect()
}

/// **The binary's own `tm resume`** (README gap 4046): the example tree, `^m1` started at 09:00, `tm interrupt` at
/// 09:20, `tm resume` at 09:50.  The plan the resume writes draws nothing over 09:20-09:50; `tm plan` at the same
/// instant draws one more row there — `lost`, the interruption — and the same future.
#[test]
fn the_plan_tm_resume_writes_leaves_the_interruption_it_resumes_undrawn() {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    tm.ok_at(&at("09:20"), &["interrupt"]);
    let out = tm.ok_at(&at("09:50"), &["resume"]);
    assert!(out.stdout.contains("resumed · lost 30m"), "{}", out.stdout);
    let written = stored(&tm);
    let over = |rows: &[(String, String, String, String)]| -> Vec<(String, String, String, String)> {
        rows.iter().filter(|r| r.0.as_str() < "09:50" && "09:20" < r.1.as_str()).cloned().collect()
    };
    assert_eq!(over(&written), vec![], "the plan `tm resume` writes draws nothing over the interruption: {written:?}");
    // The next replan at the same instant — `tm plan`'s — reads the `resume` line the verb appended.
    let plan = tm.json_at(&at("09:50"), &["plan"]);
    assert!(plan["segments"].is_array(), "{plan}");
    let next = stored(&tm);
    assert_eq!(
        over(&next),
        vec![("09:20".to_string(), "09:50".to_string(), "lost".to_string(), "m1".to_string())],
        "the next replan draws the interruption lost: {next:?}"
    );
    let future = |rows: &[(String, String, String, String)]| -> Vec<(String, String, String, String)> {
        rows.iter().filter(|r| r.0.as_str() >= "09:50").cloned().collect()
    };
    assert!(!future(&written).is_empty(), "the day has a future half to compare: {written:?}");
    assert_eq!(future(&written), future(&next), "the replan's future half is the day the next replan draws");
    let past = |rows: &[(String, String, String, String)]| -> Vec<(String, String, String, String)> {
        rows.iter().filter(|r| r.0.as_str() < "09:50").cloned().collect()
    };
    let mut with_row = past(&written);
    with_row.push(("09:20".to_string(), "09:50".to_string(), "lost".to_string(), "m1".to_string()));
    with_row.sort();
    let mut next_past = past(&next);
    next_past.sort();
    assert_eq!(with_row, next_past, "the past halves differ by that row and nothing else");
}

fn rows(d: &DayPlan, keep: impl Fn(&tm_core::dayplan::Segment) -> bool) -> Vec<String> {
    d.segments
        .iter()
        .filter(|s| keep(s))
        .map(|s| format!("{} {} {:?} {:?} {:?}", s.start.to_rfc3339(), s.end.to_rfc3339(), s.kind, s.item, s.flags.note))
        .collect()
}

/// `[interrupted days, days whose interruption began before now, days with a row before now beside the lost one]`.
static CENSUS: Mutex<[u64; 3]> = Mutex::new([0; 3]);

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(128),
        max_shrink_iters: 1_000,
        ..ProptestConfig::default()
    })]

    /// **Over the generator's class** (README gap 4046): on every interrupted day `support/plangen.rs` draws, the
    /// kernel's day from `tm resume`'s request — `.tm/state.json` with the interruption cleared and the block's own
    /// pause kept (P96), the log WITHOUT the `resume` line — and from the same request after the append are equal in
    /// their future halves, and the past half after the append is the one before it plus exactly the interruption's
    /// `lost` row, `[start, now)`, noted `interruption` and carrying what it interrupted.
    #[test]
    fn the_append_adds_exactly_the_interruptions_lost_row_to_the_past_half(case in plangen::case_strategy()) {
        let case = plangen::Case { interrupt: case.interrupt.or(Some(20)), ..case };
        let w = plangen::build(&case);
        let tz = w.cfg.tz;
        let intr = plangen::interruption(&case, tz).expect("an interruption is drawn");
        let lost = (w.now - intr.at).num_minutes().max(0);
        let resume = format!("{{\"t\":\"{}\",\"ev\":\"resume\",\"lost_min\":{lost},\"dropped\":[]}}", w.now.fixed_offset().to_rfc3339());
        let post_log = format!("{}{resume}\n", w.log);
        let post_replay = chokepoint::replay_of_text(&post_log, tz);
        // `tm resume`'s state: the interruption cleared, the block's own pause kept (P96: the replay's reading).
        let mut st = w.state.clone();
        st.interrupt = None;
        let held = post_replay.open_block.as_ref().map(|b| b.paused);
        if let Some(a) = st.active.as_mut() {
            a.paused = held.unwrap_or(false);
        }
        let day = |log: &str, replay: &tm_core::log::Replay| -> (DayPlan, DateTime<Tz>) {
            let cands = priority::collect_candidates(&w.tree, replay, &w.cfg, &w.model, plangen::date(), w.now);
            let world = planreq::World { docs: &w.docs, log, tree: &w.tree, cfg: &w.cfg, state: &st, now: w.now, cands: &cands, replay };
            let (k, _) = planreq::kernel_day(&world, None).unwrap_or_else(|e| panic!("the kernel plans the resumed day: {e}"));
            (k.day, w.now)
        };
        let (before, now) = day(&w.log, &w.replay);
        let (after, _) = day(&post_log, &post_replay);
        prop_assert_eq!(rows(&before, |s| s.start >= now), rows(&after, |s| s.start >= now), "the future halves");
        let mut expected = rows(&before, |s| s.end <= now);
        let began = intr.at < now;
        if began {
            let start = intr.at;
            let lost_row = after
                .segments
                .iter()
                .find(|s| s.kind == SegKind::Lost && s.start == start && s.end == now)
                .unwrap_or_else(|| panic!("the append draws the interruption lost from {start}: {:?}", rows(&after, |s| s.end <= now)));
            prop_assert_eq!(lost_row.flags.note.as_deref(), Some("interruption"));
            prop_assert_eq!(lost_row.item.as_ref().map(|i| i.as_str().to_string()), intr.id.clone());
            expected.extend(rows(&after, |s| std::ptr::eq(s, lost_row)));
            expected.sort();
        }
        let mut got = rows(&after, |s| s.end <= now);
        got.sort();
        prop_assert_eq!(expected, got, "the past half after the append");
        let r = {
            let mut r = CENSUS.lock().unwrap_or_else(|p| p.into_inner());
            r[0] += 1;
            r[1] += u64::from(began);
            r[2] += u64::from(began && !rows(&before, |s| s.end <= now).is_empty());
            *r
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(128);
        if r[0] == generated {
            eprintln!(
                "cli_resume_replan census (gap 4046): {} interrupted days, {} whose interruption began before now ({} with \
                 other rows in the past half beside it)",
                r[0], r[1], r[2]
            );
            prop_assert!(r[1] * 2 > r[0], "fewer than half the days had an interruption that began before now: {r:?}");
            prop_assert!(r[2] > 0, "no day held a past half beside the interruption: {r:?}");
        }
    }
}
