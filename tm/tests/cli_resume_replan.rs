//! **`tm resume` plans AFTER its own line** — the owner's D106 (README gap 4661; stage 6 W-46 track H, parity
//! **P101**), and what the order it replaced left out — stage 6 W-45, track Q (README gap 4046, measured here).
//!
//! `tm resume` clears `.tm/state.json`'s interruption, plans, and appends its `resume` line, which records
//! `dropped` — the items the replan no longer holds — and so needs the plan first (`day.rs`' `resume`).  Fork
//! 4748911 planned BEFORE it appended the line, and so did this binary until W-46: the replan's request carried a
//! `log` section that still held the interruption OPEN beside a `planner` section that said nothing is interrupted
//! (README gap 4046).  What that drew was measured at W-45 track Q, on every interrupted day the planner generator
//! draws (`support/plangen.rs`; 189 days, the fork planner asked in-process in a scratch test):
//!
//! * **the kernel draws the resumed interruption exactly as fork 4748911 does, before the append and after it** —
//!   189 of 189 days, every row over the interruption's span equal — so R3's swap of this replan moves nothing;
//! * **the replan's future half is the day every later replan draws** — 189 of 189 equal before and after the
//!   append, in the kernel and in the fork;
//! * **its past half was not**: on every day whose interruption began before `now` (137 of 137) the replan `tm resume`
//!   wrote had NO row over the interruption, and every later replan drew one more row, `lost` from the interruption's
//!   start to `now` with the note `interruption` — the `interrupt` segment the `resume` line closes.
//!
//! So the plan `tm resume` wrote — the day file's `tm:plan` block, `.tm/last_plan.json` and the `plan` event's hash —
//! held a hole where the interruption was until the next planning verb rewrote it and moved the hash with no time
//! passing: two readings of one span (AGENTS §5.3).  **D106: the line is HELD in memory while the day is planned** —
//! by the one hold every in-memory housekeeping write goes through (the owner's D96: `Ctx::hold_begin`, the line
//! appended into the hold, `Ctx::reload` reading the context as the hold leaves it, `Ctx::release`) — and written
//! after, with `dropped` read off the plan it is written beside.  The held line says `dropped: []`, and the replay
//! keeps `dropped` as a record of the line: no fact the planner reads is one of it
//! ([`a_resume_lines_dropped_moves_no_row_of_the_day`]), so the day planned beside the held line is the day planned
//! beside the written one.  The instruments: [`the_plan_tm_resume_writes_draws_the_interruption_it_resumes`] on the
//! binary (the pin this file held until W-46 read the other way, as
//! the_plan_tm_resume_writes_leaves_the_interruption_it_resumes_undrawn: nothing over the interruption, and the next
//! `tm plan` adding the row and a `plan` event), and [`the_append_adds_exactly_the_interruptions_lost_row_to_the_past_half`]
//! over the generator's class, kernel only — the row D106 brings into the written plan.

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

/// The day file's text and the log's `plan` events, as a planning verb leaves them.
fn written_day(tm: &Tm) -> (String, String, Vec<String>) {
    let plans = tm.log().into_iter().filter(|e| e["ev"] == "plan").map(|e| e.to_string()).collect();
    (tm.read("day/2026-09-07.md"), tm.read(".tm/last_plan.json"), plans)
}

/// **The binary's own `tm resume`, under the owner's D106** (README gaps 4046 and 4661; parity P101): the example
/// tree, `^m1` started at 09:00, `tm interrupt` at 09:20, `tm resume` at 09:50.  The plan the resume writes draws the
/// interruption `lost` over 09:20-09:50, carrying `^m1` — the row every later replan draws — and the next planning
/// verb at the same instant, `tm plan`'s, finds nothing to move: `.tm/last_plan.json` and the day file byte for byte,
/// and no `plan` event (§10.1 logs one only when the day moved).  Until W-46 the written plan drew nothing over the
/// interruption (fork 4748911's order) and the next `tm plan` added the row and logged a `plan` event with a changed
/// hash — this test then pinned that, under another name.
#[test]
fn the_plan_tm_resume_writes_draws_the_interruption_it_resumes() {
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
    assert_eq!(
        over(&written),
        vec![("09:20".to_string(), "09:50".to_string(), "lost".to_string(), "m1".to_string())],
        "the plan `tm resume` writes draws the interruption lost (D106): {written:?}"
    );
    let resumes: Vec<Value> = tm.log().into_iter().filter(|e| e["ev"] == "resume").collect();
    assert_eq!(resumes.len(), 1, "one `resume` line is written, and the held one never: {resumes:?}");
    assert_eq!(resumes[0]["lost_min"], 30);
    let before = written_day(&tm);
    assert_eq!(before.2.len(), 1, "the resume logged its plan: {:?}", before.2);
    // The next replan at the same instant — `tm plan`'s — reads the `resume` line the verb appended.
    let plan = tm.json_at(&at("09:50"), &["plan"]);
    assert!(plan["segments"].is_array(), "{plan}");
    let after = written_day(&tm);
    assert_eq!(after.1, before.1, "the next replan stores the plan `tm resume` wrote, hash and all");
    assert_eq!(after.0, before.0, "the next replan writes the day file `tm resume` wrote");
    assert_eq!(after.2, before.2, "the next replan logs no `plan` event: the day did not move with no time passing");
}

/// **A `resume` line's `dropped` moves nothing `tm plan` answers** — the fact D106's hold stands on (README gap
/// 4661): `tm resume` plans beside its line held with `dropped: []` and writes it with `dropped` read off that plan,
/// so the day planned beside the held line must be the day planned beside the written one.  The binary's world
/// above, `tm plan --json` on two copies of the tree whose `resume` line differs only in `dropped`, each replaying
/// its log from nothing: the same answer, byte for byte — fork 4748911's planner's day before R3 and the kernel's
/// after it (the switch's clone runs this file too), the kernel's ranking in both.
#[test]
fn a_resume_lines_dropped_moves_no_row_of_the_day() {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    tm.ok_at(&at("09:20"), &["interrupt"]);
    tm.ok_at(&at("09:50"), &["resume"]);
    let log = tm.read(".tm/log.jsonl");
    let held = "\"ev\":\"resume\",\"lost_min\":30,\"dropped\":[]";
    assert_eq!(log.matches(held).count(), 1, "the written line drops nothing on this tree: {log}");
    let named = log.replace(held, "\"ev\":\"resume\",\"lost_min\":30,\"dropped\":[\"m1\",\"t3\"]");
    let day = |text: &str| -> Value {
        let copy = Tm::empty();
        copy_tree(&tm.plan, &copy.plan);
        std::fs::remove_dir_all(copy.plan.join(".tm/cache")).ok();
        std::fs::write(copy.plan.join(".tm/log.jsonl"), text).expect("the log");
        copy.json_at(&at("09:50"), &["plan"])
    };
    assert_eq!(day(&named), day(&log), "a `resume` line's `dropped` moved the day");
}

fn copy_tree(from: &std::path::Path, to: &std::path::Path) {
    std::fs::create_dir_all(to).expect("create dir");
    for entry in std::fs::read_dir(from).expect("read dir") {
        let entry = entry.expect("dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file type").is_dir() {
            copy_tree(&entry.path(), &target);
        } else {
            std::fs::copy(entry.path(), &target).expect("copy file");
        }
    }
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
