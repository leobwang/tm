//! **Every break on a block's ledger days is netted once, by the host and the replay alike** — the owner's
//! **D94** (README gaps 4361, 4506 and 4363; parity P92), held as a CLASS of generated logs rather than a list of
//! worlds (the campaign's lesson 2).
//!
//! The host's reading of a running block's minutes is `Replay::running_worked_min` — elapsed less the UNION of the
//! idle spans of the block's ledger days (pauses, interruptions, every `break`) — the number `tm stop` prints and
//! `tm done` logs.  The replay's is what its machine credits when the block is cut (`tm review`'s minutes, the heat
//! grid's, an item's done minutes) and the open block it reads at the end of the log (`OpenBlock::worked_min_at`, the
//! planner's open row).  Until D94 the replay netted only a break stepped while the clock ran (D87, P81) and the LAST
//! break stepped where a clock starts (D92, P85); a clock behind the log — a `--now` moved backwards, two machines
//! syncing one plan directory — writes every other shape: a break logged ahead of a `start` but begun after it, a
//! start inside an earlier break with a later one stepped between, overlapping breaks, a break filed on the ledger day
//! before the block's.  This file draws them all, with a pause or an interruption on top, and holds the two readings
//! to one number on every day it draws.
//!
//! **What it leaves out, by a stated rule** ([`retroactive`]): a break logged after a clock-stopping mark of the same
//! open block whose instant is after the break began — it can overlap a stretch the replay already closed and drew
//! (README gap 4520, the residual D94's build did not take), and the host's union would net it at the next reading.
//! It is counted, never silently dropped.

#[allow(dead_code)]
#[path = "support/replay.rs"]
mod replay;

use std::sync::Mutex;

use chrono::{DateTime, Duration, FixedOffset, NaiveDate, TimeZone};
use proptest::prelude::*;

/// 2026-09-07T09:00-05:00, the hour the drawn days are measured from.
fn nine() -> DateTime<FixedOffset> {
    FixedOffset::west_opt(5 * 3600).expect("offset").with_ymd_and_hms(2026, 9, 7, 9, 0, 0).single().expect("instant")
}

fn at(min: i64) -> DateTime<FixedOffset> {
    nine() + Duration::minutes(min)
}

fn stamp(t: DateTime<FixedOffset>) -> String {
    t.to_rfc3339()
}

/// When a drawn break's line is logged: before the block's `start` (a clock behind the log), or after it, at a
/// position among the block's own marks.
#[derive(Clone, Copy, Debug)]
enum When {
    Ahead,
    InBlock(u8),
}

/// One drawn break: its start in minutes from 09:00, its length, and when its line is logged.
#[derive(Clone, Copy, Debug)]
struct Brk {
    from: i64,
    len: i64,
    when: When,
}

/// A clock-stopping mark pair on the block: a `pause`/`unpause` or an `interrupt`/`resume`, its two instants, and
/// where among the in-block lines each is logged.
#[derive(Clone, Copy, Debug)]
struct Marks {
    interrupt: bool,
    on: i64,
    off: i64,
}

#[derive(Clone, Debug)]
struct Day {
    /// The block's `start`, in minutes from 09:00, and its `stop`.
    start: i64,
    stop: i64,
    breaks: Vec<Brk>,
    marks: Option<Marks>,
    /// A wake on the 6th and a break at 06:30-07:20 on the 7th, filed on the 6th (before the 7th's 07:00 wake): a
    /// break of the ledger day BEFORE the block's, logged ahead of the block or inside it (gap 4363).  The whole
    /// block is then drawn from 07:05 rather than 09:00, so it can start inside that break.
    day_before: Option<bool>,
}

impl Day {
    /// Minutes from 09:00 the block's own offsets are drawn from: 07:05 on a day with a break of the day before.
    fn base(&self) -> i64 {
        if self.day_before.is_some() { -115 } else { 0 }
    }

    /// The instant `min` minutes into the block's own frame.
    fn t(&self, min: i64) -> DateTime<FixedOffset> {
        at(self.base() + min)
    }
}

fn day_strategy() -> impl Strategy<Value = Day> {
    (0i64..=60, 30i64..=150).prop_flat_map(|(start, span)| {
        let stop = start + span;
        let brk = (start - 40..stop - 5, 1i64..=40, prop_oneof![3 => Just(None), 2 => (0u8..4).prop_map(Some)])
            .prop_map(|(from, len, when)| Brk { from, len, when: when.map_or(When::Ahead, When::InBlock) });
        let marks = prop::option::weighted(0.5, (any::<bool>(), 1i64..=span - 2, 1i64..=30)).prop_map(move |m| {
            m.map(|(interrupt, on, len)| Marks { interrupt, on: start + on, off: (start + on + len).min(stop - 1) })
        });
        (Just(start), Just(stop), prop::collection::vec(brk, 1..=3), marks, prop::option::weighted(0.25, any::<bool>()))
            .prop_map(|(start, stop, breaks, marks, day_before)| Day { start, stop, breaks, marks, day_before })
    })
}

fn line(t: DateTime<FixedOffset>, body: &str) -> String {
    format!("{{\"t\":\"{}\",{body}}}", stamp(t))
}

fn break_line(t: DateTime<FixedOffset>, len: i64) -> String {
    spelled_break_line(t, len, Spell::Both)
}

/// **How a drawn break's line spells its span** — the W-44 land's composition of D94 with the owner's **D95** (P93,
/// README gap 4360): a `break` line's span is `[t, t + actual_min)`, else `[t, t + planned_min)` for a line logged
/// without `actual_min`, to the host (`BreakRecord::span`) and the replay (`Replay.brkEnd`) alike.  Every spelling
/// below spans `len` minutes to both readers; the binary's own writers log only [`Spell::Both`]'s shape when the
/// break ran as planned, and a hand-edited log holds the other two.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Spell {
    /// `planned_min` and `actual_min` both `len` (the arm's draw since track K).
    Both,
    /// `planned_min` `len` and no `actual_min` — D95's shape: until the land merged track H's reading, the host read
    /// it as no span while the replay netted its planned minutes.
    PlannedOnly,
    /// `planned_min` fifteen more than `actual_min` `len` — a break ended early: the span is the actual one.
    EndedEarly,
}

fn spelled_break_line(t: DateTime<FixedOffset>, len: i64, spell: Spell) -> String {
    match spell {
        Spell::Both => line(t, &format!("\"ev\":\"break\",\"planned_min\":{len},\"actual_min\":{len}")),
        Spell::PlannedOnly => line(t, &format!("\"ev\":\"break\",\"planned_min\":{len}")),
        Spell::EndedEarly => {
            line(t, &format!("\"ev\":\"break\",\"planned_min\":{},\"actual_min\":{len}", len + 15))
        }
    }
}

/// The drawn day's log lines, in file order, WITHOUT the `stop` (the host reads the block running at the `stop`'s
/// instant), and the `stop` line.
fn lines(d: &Day) -> (Vec<String>, String) {
    lines_spelled(d, &[])
}

/// [`lines`] with the `k`-th drawn break spelled `spells[k]` ([`Spell::Both`] past the slice's end).
fn lines_spelled(d: &Day, spells: &[Spell]) -> (Vec<String>, String) {
    let spell = |k: usize| spells.get(k).copied().unwrap_or(Spell::Both);
    let mut out = Vec::new();
    if d.day_before.is_some() {
        out.push(line(at(-26 * 60), "\"ev\":\"wake\",\"slept_min\":420"));
    }
    if d.day_before == Some(true) {
        out.push(break_line(at(-150), 50));
    }
    out.push(line(at(-120), "\"ev\":\"wake\",\"slept_min\":420"));
    for (k, b) in d.breaks.iter().enumerate() {
        if matches!(b.when, When::Ahead) {
            out.push(spelled_break_line(d.t(b.from), b.len, spell(k)));
        }
    }
    out.push(line(
        d.t(d.start),
        "\"ev\":\"start\",\"id\":\"a\",\"pred\":4,\"rep\":3,\"hsw\":2.0,\"slept_min\":420,\"loc\":\"home\",\"blocks_done\":0,\"since_break_min\":0",
    ));
    // The in-block lines: the marks at slots 1 and 3, each break at its own slot (0-3, before or between them).
    let mut slots: Vec<(u8, u8, String)> = Vec::new();
    if let Some(m) = d.marks {
        let (on, off) = if m.interrupt {
            ("\"ev\":\"interrupt\",\"id\":\"a\"".to_string(), format!("\"ev\":\"resume\",\"lost_min\":{},\"dropped\":[]", m.off - m.on))
        } else {
            ("\"ev\":\"pause\",\"id\":\"a\"".to_string(), "\"ev\":\"unpause\",\"id\":\"a\"".to_string())
        };
        slots.push((1, 0, line(d.t(m.on), &on)));
        slots.push((3, 0, line(d.t(m.off), &off)));
    }
    for (k, b) in d.breaks.iter().enumerate() {
        if let When::InBlock(s) = b.when {
            slots.push((s, 1 + k as u8, spelled_break_line(d.t(b.from), b.len, spell(k))));
        }
    }
    if d.day_before == Some(false) {
        slots.push((0, 9, break_line(at(-150), 50)));
    }
    slots.sort_by_key(|(s, k, _)| (*s, *k));
    out.extend(slots.into_iter().map(|(_, _, l)| l));
    (out, line(d.t(d.stop), "\"ev\":\"stop\",\"id\":\"a\",\"remaining_min\":0"))
}

/// **The residual this file leaves out** (README gap 4520): a day whose lines logged inside the block are not in the
/// order of their stamps — a break, a `pause` or an `interrupt` logged after the replay may already have closed a
/// stretch it lies across (the replay closes the running stretch at every clock-stopping mark and, D87's `brkFx`, at
/// every break it steps while the clock runs), which the host's union nets at its next reading and the replay credited
/// and drew at the close.  Over-approximated: such a day may still read one way, and is left out all the same.  The
/// breaks logged AHEAD of the `start`, in any order — gaps 4361 and 4506, the class D94 nets — are not touched by it,
/// nor the break of the day before, which no reading counts.
fn retroactive(d: &Day) -> bool {
    // (log position, stamp in the block's frame) of every line logged between the `start` and the `stop`.
    let mut in_block: Vec<((u8, usize), i64)> = d
        .breaks
        .iter()
        .enumerate()
        .filter_map(|(k, b)| match b.when {
            When::InBlock(s) => Some(((s, 1 + k), b.from)),
            When::Ahead => None,
        })
        .collect();
    if let Some(m) = d.marks {
        in_block.push(((1, 0), m.on));
        in_block.push(((3, 0), m.off));
    }
    in_block.iter().any(|(pi, ti)| in_block.iter().any(|(pj, tj)| pi < pj && tj < ti))
}

/// The day the host's runtime reads — the block's own date.
fn today() -> NaiveDate {
    NaiveDate::from_ymd_opt(2026, 9, 7).expect("date")
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(256),
        max_shrink_iters: 2_000,
        ..ProptestConfig::default()
    })]

    /// **The host and the replay read a block one way, whatever breaks the log holds on its ledger days and in
    /// whatever order** — the owner's D94.  The `stop`'s credit (the replay's, `items.a.minutes`) is the host's
    /// `running_worked_min` at the `stop`'s instant over the log before it; and the open block the replay reads at
    /// the end of that log (`OpenBlock::worked_min_at`, `Replay.openOf`) is the host's number too wherever every break
    /// it holds ended by then.
    #[test]
    fn the_host_and_the_replay_net_every_break_on_a_blocks_ledger_days_once(d in day_strategy()) {
        /// `[cases, compared, left out (gap 4520), gap 4361 (a break the clock met after it started, logged ahead),
        /// gap 4506 (a start inside a break that is not the last one stepped), gap 4363 (a break of the day before,
        /// overlapping the block), open readings compared, open readings over a break held ahead of the clock]`.
        static CENSUS: Mutex<[u64; 8]> = Mutex::new([0; 8]);
        let tz = chrono_tz::America::Chicago;
        let (prefix, stop) = lines(&d);
        let held = !retroactive(&d);
        let ahead: Vec<&Brk> = d.breaks.iter().filter(|b| matches!(b.when, When::Ahead)).collect();
        let meets_after_start = ahead.iter().any(|b| b.from > d.start && b.from < d.stop);
        let covering: Vec<&&Brk> = ahead.iter().filter(|b| b.from <= d.start && d.start < b.from + b.len).collect();
        let not_last = covering.iter().any(|b| !std::ptr::eq(**b, *ahead.last().expect("covering is ahead")));
        let day_before = d.day_before.is_some() && d.base() + d.start < -100;
        let all_end_by_stop = d.breaks.iter().all(|b| b.from + b.len <= d.stop);
        let mut open_ahead = false;
        if held {
            let text = prefix.join("\n") + "\n";
            let running = replay::replay_of_text(&text, tz);
            let host = running.running_worked_min("a", today(), d.t(d.stop), None);
            let whole = replay::replay_of_text(&(text.clone() + &stop + "\n"), tz);
            let credit = whole.items.get("a").map(|i| i.minutes);
            prop_assert!(host.is_some(), "the host reads no running block before the stop:\n{text}");
            prop_assert_eq!(host, credit, "D94: the stop's credit is not the host's union (P92); the log:\n{}{}", text, stop);
            if all_end_by_stop {
                let open = running.open_block.as_ref().filter(|b| b.id == "a").map(|b| b.worked_min_at(d.t(d.stop)));
                prop_assert_eq!(host, open, "D94: the open block read at the end of the log is not the host's union (P92); the log:\n{}", text);
                open_ahead = meets_after_start;
            }
        }
        let r = {
            let mut r = CENSUS.lock().expect("census");
            r[0] += 1;
            r[1] += u64::from(held);
            r[2] += u64::from(!held);
            r[3] += u64::from(held && meets_after_start);
            r[4] += u64::from(held && not_last);
            r[5] += u64::from(held && day_before);
            r[6] += u64::from(held && all_end_by_stop);
            r[7] += u64::from(open_ahead);
            *r
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(256);
        if r[0] >= generated {
            // **Floors** (AGENTS §9.2): a class compared on no day compares nothing.  Red is a finding about the draw,
            // re-run and reported (D46), never reverted.
            prop_assert!(r[1] * 2 > r[0], "fewer than half the days drawn were compared: {r:?}");
            prop_assert!(r[3] > 0, "no compared day held a break logged ahead of the start that the clock met after it started (gap 4361): {r:?}");
            prop_assert!(r[4] > 0, "no compared day started inside a break that was not the last one stepped (gap 4506): {r:?}");
            prop_assert!(r[5] > 0, "no compared day held a break of the ledger day before overlapping the block (gap 4363): {r:?}");
            prop_assert!(r[7] > 0, "no open reading held a break ahead of the clock (gap 4361, the block running): {r:?}");
        }
        eprintln!(
            "kernel_break_union census (D94): {} cases, {} compared, {} left out (gap 4520), {} with a break met after the start \
             (gap 4361), {} starting inside a break not the last stepped (gap 4506), {} with a break of the day before (gap 4363), \
             {} open readings compared ({} over a break ahead of the clock)",
            r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7]
        );
    }
}

/// **The draw is not vacuous on its own terms**: S1's day from the drive (`scratchpad/w44-k/drive`, README §1) — a
/// thirty-minute break at 09:00, a five-minute one at 09:40, the `start` at 09:10, `stop` at 10:00 — is in the class,
/// is compared, and reads 25 both ways (D92's replay read 50).
#[test]
fn the_drawn_class_holds_the_driven_gap_4506_day() {
    let d = Day {
        start: 10,
        stop: 60,
        breaks: vec![Brk { from: 0, len: 30, when: When::Ahead }, Brk { from: 40, len: 5, when: When::Ahead }],
        marks: None,
        day_before: None,
    };
    assert!(!retroactive(&d));
    let tz = chrono_tz::America::Chicago;
    let (prefix, stop) = lines(&d);
    let text = prefix.join("\n") + "\n";
    let host = replay::replay_of_text(&text, tz).running_worked_min("a", today(), d.t(d.stop), None);
    let whole = replay::replay_of_text(&(text + &stop + "\n"), tz);
    assert_eq!(host, Some(25));
    assert_eq!(whole.items.get("a").map(|i| i.minutes), Some(25));
}

/// The host's reading at the `stop`'s instant and the replay's credit for `d`, read as the arm reads them.
fn the_two_readings(d: &Day) -> (Option<u32>, Option<u32>) {
    let tz = chrono_tz::America::Chicago;
    let (prefix, stop) = lines(d);
    let text = prefix.join("\n") + "\n";
    let host = replay::replay_of_text(&text, tz).running_worked_min("a", today(), d.t(d.stop), None);
    let whole = replay::replay_of_text(&(text + &stop + "\n"), tz);
    (host, whole.items.get("a").map(|i| i.minutes))
}

/// **The residual the arm leaves out is real, and these are its witnesses** (README gap 4520) — the two shapes the
/// arm's draw found before its rule named them (the first is the seed in `kernel_break_union.proptest-regressions`).
/// Each is a line logged inside the block after the replay closed a stretch it lies across: two breaks logged out of
/// order while the block runs (the replay closed `[09:00, 09:01]` at the 09:01 break, then stepped the 09:00 one —
/// 29 credited, the host's union 28), and a `pause` stamped 09:01 logged after a break at 09:17 (the replay had
/// banked `[09:00, 09:17]` at the break and banks `[09:02, 09:17]` again after the `unpause` — 44 credited, the host's
/// 28; it credited 45 at `ed72e36`, so this is the machine's order and not D94's).  Both are left out by
/// [`retroactive`]; when gap 4520 closes these readings meet, this test fails, and the rule can go.
#[test]
fn the_residual_the_arm_leaves_out_reads_two_ways_by_its_witnesses() {
    let breaks_out_of_order = Day {
        start: 0,
        stop: 30,
        breaks: vec![Brk { from: 1, len: 1, when: When::InBlock(0) }, Brk { from: 0, len: 1, when: When::InBlock(0) }],
        marks: None,
        day_before: None,
    };
    let pause_behind_a_break = Day {
        start: 0,
        stop: 30,
        breaks: vec![Brk { from: 17, len: 1, when: When::InBlock(0) }],
        marks: Some(Marks { interrupt: false, on: 1, off: 2 }),
        day_before: None,
    };
    for (d, want) in [(&breaks_out_of_order, (Some(28), Some(29))), (&pause_behind_a_break, (Some(28), Some(44)))] {
        assert!(retroactive(d), "the arm's rule no longer leaves out {d:?}");
        assert_eq!(the_two_readings(d), want, "gap 4520's witness moved: {d:?}");
    }
}

fn spell_strategy() -> impl Strategy<Value = Spell> {
    prop_oneof![1 => Just(Spell::Both), 2 => Just(Spell::PlannedOnly), 2 => Just(Spell::EndedEarly)]
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(256),
        max_shrink_iters: 2_000,
        ..ProptestConfig::default()
    })]

    /// **Every break a clock meets is netted ONCE, however its line spells its span** — the W-44 land's composition
    /// of track K's D94 (the replay nets every break on a block's ledger days, P92) with track H's D95 (the host reads
    /// a break's span as the replay does, P93).  The day is the arm above's, every drawn break spelled at random —
    /// with `actual_min`, without it (D95's shape), or ended before its plan — and the two readings are held to one
    /// number exactly as the arm holds them: the `stop`'s credit and, where every break ended by then, the open block.
    /// Either track alone leaves it two numbers: without D94 a planned-only break logged ahead of the clock is netted
    /// by the host and credited by the replay; without D95 a planned-only break is netted by the replay alone.
    #[test]
    fn the_host_and_the_replay_net_every_spelling_of_a_break_once(
        d in day_strategy(),
        spells in prop::collection::vec(spell_strategy(), 3),
    ) {
        /// `[cases, compared, compared holding a planned-only break the block's span overlaps, compared holding an
        /// early-ended one it overlaps, of the first: logged ahead of the start]`.
        static CENSUS: Mutex<[u64; 5]> = Mutex::new([0; 5]);
        let tz = chrono_tz::America::Chicago;
        let (prefix, stop) = lines_spelled(&d, &spells);
        let held = !retroactive(&d);
        let overlaps = |b: &Brk| b.from < d.stop && d.start < b.from + b.len;
        let spelled = |s: Spell| d.breaks.iter().zip(&spells).any(|(b, &x)| x == s && overlaps(b));
        let planned_ahead = d.breaks.iter().zip(&spells).any(|(b, &x)| x == Spell::PlannedOnly && overlaps(b) && matches!(b.when, When::Ahead));
        if held {
            let text = prefix.join("\n") + "\n";
            let running = replay::replay_of_text(&text, tz);
            let host = running.running_worked_min("a", today(), d.t(d.stop), None);
            let whole = replay::replay_of_text(&(text.clone() + &stop + "\n"), tz);
            let credit = whole.items.get("a").map(|i| i.minutes);
            prop_assert!(host.is_some(), "the host reads no running block before the stop:\n{text}");
            prop_assert_eq!(host, credit, "D94 + D95: the stop's credit is not the host's union (P92, P93); the log:\n{}{}", text, stop);
            if d.breaks.iter().all(|b| b.from + b.len <= d.stop) {
                let open = running.open_block.as_ref().filter(|b| b.id == "a").map(|b| b.worked_min_at(d.t(d.stop)));
                prop_assert_eq!(host, open, "D94 + D95: the open block is not the host's union (P92, P93); the log:\n{}", text);
            }
        }
        let r = {
            let mut r = CENSUS.lock().expect("census");
            r[0] += 1;
            r[1] += u64::from(held);
            r[2] += u64::from(held && spelled(Spell::PlannedOnly));
            r[3] += u64::from(held && spelled(Spell::EndedEarly));
            r[4] += u64::from(held && planned_ahead);
            *r
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(256);
        if r[0] >= generated {
            // Floors (AGENTS §9.2): a spelling compared on no day compares nothing.
            prop_assert!(r[1] * 2 > r[0], "fewer than half the days drawn were compared: {r:?}");
            prop_assert!(r[2] > 0, "no compared day held a planned-only break the block overlaps (D95): {r:?}");
            prop_assert!(r[3] > 0, "no compared day held an early-ended break the block overlaps: {r:?}");
            prop_assert!(r[4] > 0, "no compared day held a planned-only break logged ahead of the start (D94 with D95): {r:?}");
        }
        eprintln!(
            "kernel_break_union spellings census (W-44 land, D94 + D95): {} cases, {} compared, {} with a planned-only \
             break the block overlaps ({} logged ahead of the start), {} with an early-ended one",
            r[0], r[1], r[2], r[4], r[3]
        );
    }
}

/// **The composition is not vacuous on its own terms**: S1's day (two breaks logged ahead of a `start` at 09:10 that
/// starts inside the first) with BOTH breaks logged without `actual_min` reads 25 both ways — the replay nets the
/// planned spans (D94, `Replay.brkEnd`) and so does the host (D95, `BreakRecord::span`).
#[test]
fn the_driven_gap_4506_day_spelled_planned_only_reads_one_way() {
    let d = Day {
        start: 10,
        stop: 60,
        breaks: vec![Brk { from: 0, len: 30, when: When::Ahead }, Brk { from: 40, len: 5, when: When::Ahead }],
        marks: None,
        day_before: None,
    };
    let tz = chrono_tz::America::Chicago;
    let (prefix, stop) = lines_spelled(&d, &[Spell::PlannedOnly, Spell::PlannedOnly]);
    assert!(prefix.iter().all(|l| !l.contains("actual_min")), "{prefix:?}");
    let text = prefix.join("\n") + "\n";
    let host = replay::replay_of_text(&text, tz).running_worked_min("a", today(), d.t(d.stop), None);
    let whole = replay::replay_of_text(&(text + &stop + "\n"), tz);
    assert_eq!(host, Some(25));
    assert_eq!(whole.items.get("a").map(|i| i.minutes), Some(25));
}
