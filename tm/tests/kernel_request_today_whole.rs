//! **The request R3's switch sends holds today's record WHOLE, whatever tail the scope chooses** — stage 6 W-45,
//! track Q (README gap 3583, closed here; gap 4660 opened and closed here).
//!
//! # What the planner reads from the log, and where it lives in the request
//!
//! The planner request R3 sends from `tm plan`, `tm now` and every TUI replan is
//! `kernel_capacity::planner_request`: the ranked capacity request with a `planner` section, whose `log` section is
//! `kernel_log::capacity_log_section` — **the process checkpoint and the tail since its cut**, or genesis in one call.
//! The kernel reads the log ONLY through that section's run (D24's seam), and on the planner's path it reads exactly
//! two things off it:
//!
//! * **today's day record** — `Planner.PlanReq.todayRecord` (the logged arrival, `PlanReq.loggedArrival`; the
//!   replayed past half, `pastRows` over its segments; `PlanReq.blocksDone`; the starts and breaks
//!   `PlanReq.sinceBreak` and `dayRestDebtMin` read), and day 0's capacity through `Boundary.dayRecordOn` (the wake
//!   `WakeSrc.resolve` reads, the night's minutes and the energy reports `todayFromLog` reads);
//! * **the open block** — `Seal.Answer.openBlock` (`PlanReq.activeWorked`, `openBlockRows`).
//!
//! `Seal.Answer.openInterrupt` is read by no planner definition (the running interruption is `.tm/state.json`'s,
//! `interruptRows`); it is compared here all the same, because a tail that cut it would cut the block it holds.
//!
//! README gap 3583 asked that a tail starting after today's first `arrive` not plan from `now`.  Its class is wider
//! than the arrival: a tail can cut whatever today's record reads from lines before the cut — the wake, the day's
//! breaks and starts, a block begun before the tail, an interruption left open across it, and today's own lines a
//! clock ahead of the log wrote early in the file.  **None is a special case**: the section either reaches back to
//! line 1, or resumes a checkpoint whose ledger day is at or below today (`resume_section_from`'s
//! `now_day >= ledger_day`, and the kernel's own G4, `nowBelowLedger`), and a checkpoint keeps every day at or above
//! its ledger day as an OPEN day and its machine whole (`Seal.Ckpt.openDays`, `Seal.Ckpt.machine`), so a resumed
//! answer reads today as the whole log's replay does — `Seal.resume_is_replay` (law 2 through the disk),
//! `Seal.an_accepted_resume_covers_now` (`L ≤ T`), `Seal.the_answer_reads_the_replay` and
//! `Seal.the_answer_reads_the_replays_scalar_facts` (law 1).
//!
//! # And the one way it did not: a tail the kernel REFUSED (README gap 4660)
//!
//! Those laws read an ACCEPTED resume.  The first run of this arm drew a section the kernel refused —
//! `sealedDay` (G3) — on the TUI's shape: the checkpoint an earlier load left in the process, and a log that grew
//! after it by a line closing the stretch of a block begun on a day that checkpoint had sealed (a `^b` started on
//! the 2nd and never ended, a load on the 5th, then `tm interrupt`).  The verb's own replay rebuilds on that refusal
//! (`ReplayCache::replay_once`); the request's section had no such path, so the whole capacity request was refused.
//! Since this step a tail the process has not seen the kernel resume is asked once and, refused, rebuilt IN MEMORY
//! (`resume_section_from`); [`a_tail_that_names_a_day_the_process_checkpoint_sealed_is_rebuilt_not_refused`] is the
//! witness, and the arm's census counts how many drawn sections the old rule would have sent refused.
//!
//! # What this file measures
//!
//! The laws are the kernel's; this is the HOST's half, through the FFI, on the binary's own code: a log drawn over
//! several days, a history of loads that reseal the cache as verbs on those days would (`kernel_log::replay_scoped`,
//! at each load's own date, in a scope a verb asks for), then the section the binary's request carries at today
//! (`kernel_log::capacity_log_section`) asked of the kernel beside the whole log from line 1 — and today's record,
//! the open block and the open interruption compared by VALUE.  Floors make it non-vacuous: a census of the tails it
//! drew must reach each class above.

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

#[allow(dead_code)]
#[path = "../src/cli/kernel_log.rs"]
mod kernel_log;

use std::path::Path;
use std::sync::Mutex;

use chrono::{DateTime, Datelike, Duration, FixedOffset, NaiveDate, TimeZone};
use proptest::prelude::*;
use serde_json::Value;

const TZ: chrono_tz::Tz = chrono_tz::America::Chicago;

/// The first drawn day, a Tuesday.
fn base() -> NaiveDate {
    NaiveDate::from_ymd_opt(2026, 9, 1).expect("date")
}

/// `min` minutes into day `d`, at the offset the zone holds in September.
fn at(d: u8, min: u32) -> DateTime<FixedOffset> {
    let date = base() + Duration::days(i64::from(d));
    FixedOffset::west_opt(5 * 3600)
        .expect("offset")
        .with_ymd_and_hms(date.year(), date.month(), date.day(), min / 60, min % 60, 0)
        .single()
        .expect("instant")
}

fn line(t: DateTime<FixedOffset>, body: &str) -> String {
    format!("{{\"t\":\"{}\",{body}}}", t.to_rfc3339())
}

const ARRIVE: &str = "\"ev\":\"arrive\",\"loc\":\"home\",\"window\":[\"08:00\",\"17:00\"],\"budget\":6";
const ENERGY: &str = "\"ev\":\"energy\",\"pred\":3,\"rep\":4,\"hsw\":1.5,\"loc\":\"home\"";

/// One drawn world: the days, what each day logs, and the loads that resealed the cache.
#[derive(Clone, Debug)]
struct World {
    /// Days drawn; today is the last.
    days: u8,
    /// Per day: no session at all.
    skip: Vec<bool>,
    /// Per day: the wake's minutes after 07:00, or none.
    wake: Vec<Option<u32>>,
    /// Per day: 0, 1 or 2 arrivals.
    arrive: Vec<u8>,
    /// Per day: blocks begun.
    blocks: Vec<u8>,
    /// Per day: bit 0 a pause in the first block and in the block left open, bit 1 a break in the first block (or,
    /// with a block left open or an interruption running, on its own), bit 2 that break logged without `actual_min`,
    /// bit 3 an energy report, bit 4 a `plan`.
    marks: Vec<u8>,
    /// The day whose last block is never ended by its own day (no later block begins).
    open_block: Option<u8>,
    /// What today does to a block still open, at 14:00: 1 pauses it and unpauses it ten minutes on, 2 stops it.
    late_mark: u8,
    /// An interruption begun at 15:00 on the first day, resumed on the second (08:45, or 15:40 the same day), or never.
    open_int: Option<(u8, Option<u8>)>,
    /// Today's wake, first arrival and energy report logged early, after day `k`'s session: a clock ahead of the log.
    /// The three days before today are then quiet (no session), so no wake stands within G2's fence of them.
    ahead: Option<u8>,
    /// Per day: bit 0 a verb loaded after the wake, bit 1 after the session.
    loads: Vec<u8>,
    /// The planning verb's own load at today (else the TUI's: the checkpoint an earlier load left in the process).
    final_load: bool,
    /// The scope each load asks for: 0 hot, 1 the week's dates, 2 all.
    scope: u8,
}

impl World {
    fn today(&self) -> u8 {
        self.days - 1
    }
}

fn world_strategy() -> impl Strategy<Value = World> {
    (3u8..=11).prop_flat_map(|days| {
        let n = days as usize;
        (
            (
                Just(days),
                prop::collection::vec(prop::bool::weighted(0.15), n),
                prop::collection::vec(prop::option::weighted(0.85, 0u32..=60), n),
                prop::collection::vec(prop_oneof![1 => Just(0u8), 6 => Just(1u8), 2 => Just(2u8)], n),
                prop::collection::vec(0u8..=3, n),
                prop::collection::vec(0u8..32, n),
            ),
            (
                prop::option::weighted(0.6, 0..days),
                0u8..3,
                prop::option::weighted(0.45, (0..days, prop::option::weighted(0.6, 0..days))),
                prop::option::weighted(0.35, 0u8..=3),
                prop::collection::vec(0u8..4, n),
                prop::bool::weighted(0.6),
                0u8..3,
                prop::bool::weighted(0.7),
                prop::option::weighted(0.25, 0u8..=2),
                prop::option::weighted(0.2, 0u8..=2),
            ),
        )
            .prop_map(
                |((days, skip, wake, arrive, blocks, marks), (open_block, late_mark, open_int, ahead, loads, final_load, scope, alone, stall, marked))| {
                    let today = days - 1;
                    let mut skip = skip;
                    skip[today as usize] = false;
                    // **A stall a TUI holds across** (README gap 4660's shape, drawn on purpose a quarter of the time):
                    // a block left open three or more days back, the TUI's read this morning, and a mark today that
                    // closes the block's stretch after it.
                    // **A wall mark the checkpoint carries** (drawn on purpose a fifth of the time otherwise): a
                    // block left open three or more days back, paused and unpaused on its own day — the shape a D61
                    // wall mark leaves — still open at the end.
                    let (open_block, late_mark, open_int, final_load, alone) = match stall.and_then(|x| today.checked_sub(3 + x)) {
                        Some(b) => (Some(b), 1 + (b % 2), None, false, true),
                        None => match marked.and_then(|x| today.checked_sub(3 + x)) {
                            Some(b) => (Some(b), b % 2, None, final_load, false),
                            None => (open_block, late_mark, open_int, final_load, alone),
                        },
                    };
                    // The block left open is, most often, its day's only block and unpaused that day: a cut on its
                    // day (a block ended before it, a pause) holds the ledger day there (`Seal.machineDays`' last
                    // cut), so only an open block with no cut since holds nothing back — the shape of README gap 4660.
                    let (mut blocks, mut marks, mut loads) = (blocks, marks, loads);
                    if let (Some(b), true) = (open_block, alone) {
                        blocks[b as usize] = 1;
                        marks[b as usize] &= !1;
                        skip[b as usize] = false;
                    }
                    // A TUI read the log this morning, after the wake, and holds that checkpoint while the day runs.
                    if !final_load && alone {
                        loads[today as usize] |= 1;
                    }
                    // An interruption resumed before it began is no interruption: order the pair.
                    let open_int = open_int.map(|(a, b)| (a, b.filter(|b| *b >= a)));
                    // A clock ahead of the log by at least seven days, so a load in between can fold today's lines
                    // as FUTURE lines (`Seal.isFuture`: three UTC days past the reseal day) once the lines before
                    // them are below its floor, with the three days before today quiet.
                    // Today's wake is then written early too, with the arrival and the report: a wake of today's
                    // session within G2's fence of a folded future line would refuse the resume (`wakeBehindCut`),
                    // and the rebuild that follows folds nothing of today's.
                    let ahead = ahead.and_then(|x| today.checked_sub(7 + x));
                    if ahead.is_some() {
                        for d in today - 3..today {
                            skip[d as usize] = true;
                        }
                    }
                    // The block left open and not alone on its day is paused and unpaused there (a D61 wall mark's
                    // shape): its last cut holds the ledger day, and the checkpoint carries the block's pause history.
                    if let (Some(b), false) = (open_block, alone) {
                        marks[b as usize] |= 1;
                        blocks[b as usize] = blocks[b as usize].max(1);
                        skip[b as usize] = false;
                    }
                    World { days, skip, wake, arrive, blocks, marks, open_block, late_mark, open_int, ahead, loads, final_load, scope }
                },
            )
    })
}

/// A line of the drawn log, and what the census needs to know about it.
#[derive(Clone, Debug)]
struct Drawn {
    text: String,
    /// Dated today.
    today: bool,
    /// The open block's `start`.
    opens_block: bool,
    /// The interruption that is still open at the end of the log.
    opens_int: bool,
}

/// The drawn log in file order, and the positions (line counts) after which each load ran, with its day.
fn draw(w: &World) -> (Vec<Drawn>, Vec<(usize, u8)>) {
    let today = w.today();
    let mut out: Vec<Drawn> = Vec::new();
    let mut loads: Vec<(usize, u8)> = Vec::new();
    let mut open_block: Option<String> = None;
    let int_open_at_end = w.open_int.is_some_and(|(_, b)| b.is_none());
    let mut interrupted = false;
    for d in 0..w.days {
        let i = d as usize;
        let is_today = d == today;
        let push = |out: &mut Vec<Drawn>, t: DateTime<FixedOffset>, body: &str, opens_block: bool, opens_int: bool| {
            out.push(Drawn { text: line(t, body), today: is_today, opens_block, opens_int });
        };
        if w.skip[i] {
            continue;
        }
        let ahead_today = is_today && w.ahead.is_some();
        if let (Some(m), false) = (w.wake[i], ahead_today) {
            push(&mut out, at(d, 7 * 60 + m), "\"ev\":\"wake\",\"slept_min\":420", false, false);
        }
        if w.loads[i] & 1 != 0 {
            loads.push((out.len(), d));
        }
        let marks = w.marks[i];
        if marks & 16 != 0 {
            push(&mut out, at(d, 7 * 60 + 30), "\"ev\":\"plan\",\"hash\":\"00ab\",\"replans_today\":0,\"drift_min\":0", false, false);
        }
        if w.arrive[i] >= 1 && !ahead_today {
            push(&mut out, at(d, 8 * 60), ARRIVE, false, false);
        }
        if marks & 8 != 0 && !ahead_today {
            push(&mut out, at(d, 8 * 60 + 30), ENERGY, false, false);
        }
        // A resume on this day, before its blocks.
        if let Some((a, Some(b))) = w.open_int {
            if b == d && b > a && interrupted {
                push(&mut out, at(d, 8 * 60 + 45), "\"ev\":\"resume\",\"lost_min\":30,\"dropped\":[]", false, false);
                interrupted = false;
            }
        }
        let break_body = if marks & 4 != 0 {
            "\"ev\":\"break\",\"planned_min\":10"
        } else {
            "\"ev\":\"break\",\"planned_min\":10,\"actual_min\":10"
        };
        // Blocks: none while a block is open or an interruption runs.
        if open_block.is_none() && !interrupted {
            let nb = w.blocks[i];
            for j in 0..nb {
                let s = 9 * 60 + 100 * u32::from(j);
                let id = format!("b{d}x{j}");
                let leave_open = w.open_block == Some(d) && j + 1 == nb;
                push(
                    &mut out,
                    at(d, s),
                    &format!(
                        "\"ev\":\"start\",\"id\":\"{id}\",\"pred\":3,\"hsw\":2.0,\"slept_min\":420,\"loc\":\"home\",\"blocks_done\":{j},\"since_break_min\":0"
                    ),
                    leave_open,
                    false,
                );
                if (j == 0 || leave_open) && marks & 1 != 0 {
                    push(&mut out, at(d, s + 15), &format!("\"ev\":\"pause\",\"id\":\"{id}\""), false, false);
                    push(&mut out, at(d, s + 25), &format!("\"ev\":\"unpause\",\"id\":\"{id}\""), false, false);
                }
                if j == 0 && marks & 2 != 0 {
                    push(&mut out, at(d, s + 35), break_body, false, false);
                }
                if leave_open {
                    open_block = Some(id);
                } else if j % 2 == 0 {
                    push(
                        &mut out,
                        at(d, s + 60),
                        &format!("\"ev\":\"done\",\"id\":\"{id}\",\"est_min\":60,\"actual_min\":50,\"ci\":3"),
                        false,
                        false,
                    );
                } else {
                    push(&mut out, at(d, s + 60), &format!("\"ev\":\"stop\",\"id\":\"{id}\",\"remaining_min\":30"), false, false);
                }
            }
        } else if marks & 2 != 0 {
            // A break on a later day of a block left open, or inside an interruption.
            push(&mut out, at(d, 10 * 60), break_body, false, false);
        }
        if w.arrive[i] >= 2 {
            push(&mut out, at(d, 13 * 60 + 30), "\"ev\":\"arrive\",\"loc\":\"lounge\",\"window\":[\"13:30\",\"18:00\"],\"budget\":4", false, false);
        }
        // Today's mark on a block still open: after every load the day's session ran before it.
        if is_today && !interrupted {
            if let Some(id) = open_block.clone() {
                match w.late_mark {
                    1 => {
                        push(&mut out, at(d, 14 * 60), &format!("\"ev\":\"pause\",\"id\":\"{id}\""), false, false);
                        push(&mut out, at(d, 14 * 60 + 10), &format!("\"ev\":\"unpause\",\"id\":\"{id}\""), false, false);
                    }
                    2 => {
                        push(&mut out, at(d, 14 * 60), &format!("\"ev\":\"stop\",\"id\":\"{id}\",\"remaining_min\":30"), false, false);
                        open_block = None;
                    }
                    _ => {}
                }
            }
        }
        if let Some((a, b)) = w.open_int {
            if a == d && !interrupted {
                let body = match &open_block {
                    Some(id) => format!("\"ev\":\"interrupt\",\"id\":\"{id}\""),
                    None => "\"ev\":\"interrupt\"".to_string(),
                };
                push(&mut out, at(d, 15 * 60), &body, false, int_open_at_end);
                interrupted = true;
                if b == Some(a) {
                    push(&mut out, at(d, 15 * 60 + 40), "\"ev\":\"resume\",\"lost_min\":40,\"dropped\":[]", false, false);
                    interrupted = false;
                }
            }
        }
        if w.ahead == Some(d) {
            // A clock ahead of the log writes today's wake, arrival and energy report here, in this session.
            if let Some(m) = w.wake[today as usize] {
                out.push(Drawn {
                    text: line(at(today, 7 * 60 + m), "\"ev\":\"wake\",\"slept_min\":420"),
                    today: true,
                    opens_block: false,
                    opens_int: false,
                });
            }
            out.push(Drawn { text: line(at(today, 8 * 60), ARRIVE), today: true, opens_block: false, opens_int: false });
            out.push(Drawn { text: line(at(today, 8 * 60 + 30), ENERGY), today: true, opens_block: false, opens_int: false });
        }
        if w.loads[i] & 2 != 0 && !is_today {
            loads.push((out.len(), d));
        }
    }
    (out, loads)
}

fn text_of(lines: &[Drawn], n: usize) -> String {
    lines[..n].iter().map(|l| l.text.as_str()).collect::<Vec<_>>().join("\n") + if n == 0 { "" } else { "\n" }
}

/// The zone table, cached under the plan root as the binary caches it (D13).
fn wire(root: &Path) -> Value {
    tz_table::wire_for(Some(&root.join(kernel_log::CACHE_DIR)), TZ)
}

/// The kernel's `log` answer to `section`, asked at `today` with the zone table — the request the planner's `log`
/// section is answered in, with no documents and no capacity section around it.  `Err` names a refusal.
fn facts_of(section: &str, today: NaiveDate, tz: &Value) -> Result<Value, String> {
    let req = format!("{{\"docs\":[],\"now\":{},\"tz\":{},\"log\":{section}}}", Value::String(today.to_string()), tz);
    match kernel_log::log_call(&req).expect("the kernel answers") {
        Ok(a) => Ok(a.facts.expect("a section that asks for facts is answered with them")),
        Err(r) => Err(format!("{r:?}")),
    }
}

/// Today's 9-tuple in an answer's `facts.days`, by value.
fn day_entry(facts: &Value, day: u64) -> Option<Value> {
    facts["days"].as_array().expect("facts.days").iter().find(|d| d[0].as_u64() == Some(day)).cloned()
}

/// The scope a load asks for.
fn scope_of(w: &World, date: NaiveDate) -> kernel_log::Scope {
    match w.scope {
        0 => kernel_log::Scope::Hot,
        1 => kernel_log::Scope::Dates {
            from: date - Duration::days(i64::from(date.weekday().num_days_from_monday())),
            to: date,
        },
        _ => kernel_log::Scope::All,
    }
}

/// The facts the facts section asks for.
fn want() -> kernel_log::Want {
    kernel_log::Want { facts: true, headers_from: None, render: vec![] }
}

/// **The section the request carried before README gap 4660**: the stored checkpoint and the tail since its cut,
/// under exactly the conditions `resume_section_from` checks, never asked of the kernel first — `None` where it sent
/// genesis instead.  What the census measures the fix against; never the code under test.
fn unasked_section(root: &Path, bytes: &[u8], now_day: u64) -> Option<String> {
    let text = std::fs::read_to_string(root.join(kernel_log::CACHE_DIR).join(kernel_log::CKPT_FILE)).ok()?;
    let sn = kernel_log::Snapshot::from_text(&text).ok()?;
    let s = kernel_log::split(bytes);
    let cut = sn.meta.cut as usize;
    let ok = !sn.ckpt.is_empty()
        && sn.valid_for(bytes, &sn.tz_key).is_ok()
        && now_day >= sn.meta.ledger_day
        && cut <= s.lines.len()
        && s.lines.len() - cut <= kernel_log::RESEND_LINES
        && s.bytes_between(cut, s.lines.len()) <= kernel_log::RESEND_BYTES;
    ok.then(|| kernel_log::log_section(Some(&sn.ckpt), cut as u64 + 1, &s.lines[cut..], s.terminated, None, &want(), None))
}

/// One drawn world through the loads and the request: `(section, the whole log's facts, the section's facts, what
/// the census reads)`.  Panics, by name, where the binary's own code would fail.
struct Asked {
    section: Value,
    whole: Value,
    got: Value,
    /// The section the old rule would have sent was refused by the kernel.
    unasked_refused: bool,
}

fn ask(w: &World, lines: &[Drawn], loads: &[(usize, u8)]) -> Asked {
    let today = base() + Duration::days(i64::from(w.today()));
    let today_day = kernel_log::day_of(today);
    let dir = tempfile::tempdir().expect("a temp dir");
    let root = dir.path();
    std::fs::create_dir_all(root.join(".tm")).expect("mkdir .tm");
    let log = root.join(".tm/log.jsonl");
    let tz = wire(root);
    // The verbs' loads, each over the log as it stood then, at its own day.
    for (n, d) in loads {
        std::fs::write(&log, text_of(lines, *n)).expect("write the log");
        let bytes = std::fs::read(&log).expect("read the log");
        let date = base() + Duration::days(i64::from(*d));
        kernel_log::replay_scoped(root, &bytes, TZ, &tz, date, scope_of(w, date), None)
            .unwrap_or_else(|e| panic!("a load at {date} answers: {e:?}"));
    }
    std::fs::write(&log, text_of(lines, lines.len())).expect("write the log");
    let bytes = std::fs::read(&log).expect("read the log");
    if w.final_load {
        kernel_log::replay_scoped(root, &bytes, TZ, &tz, today, scope_of(w, today), None)
            .unwrap_or_else(|e| panic!("today's load answers: {e:?}"));
    }
    let unasked_refused = !w.final_load
        && unasked_section(root, &bytes, today_day).is_some_and(|sec| facts_of(&sec, today, &tz).is_err());
    // The section the binary's planner request carries, and the whole log's.
    let section = kernel_log::capacity_log_section(root, &bytes, &tz, today_day)
        .unwrap_or_else(|e| panic!("the request's section is built: {e:?}"));
    let s = kernel_log::split(&bytes);
    let whole_section = kernel_log::log_section(None, 1, &s.lines, s.terminated, None, &want(), None);
    let whole = facts_of(&whole_section, today, &tz).expect("the whole log from line 1 is answered");
    let got = facts_of(&section, today, &tz).unwrap_or_else(|why| {
        panic!("the request's section is REFUSED: {why}\nlog:\n{}", text_of(lines, lines.len()))
    });
    Asked { section: serde_json::from_str(&section).expect("the section is JSON"), whole, got, unasked_refused }
}

/// `[cases, resumed, today has a record, today's record has an arrival, an open block begun before the cut, an
/// interruption open across the cut, today's own lines folded into the checkpoint, today's record has a break,
/// today's record has segments, resumed from an earlier load's checkpoint (the TUI's), a section the old rule would
/// have sent refused (gap 4660), today's record has a wake, a pause or unpause of the open block before the cut (a
/// D61 wall mark's shape), today's wake folded into the checkpoint]`.
static CENSUS: Mutex<[u64; 14]> = Mutex::new([0; 14]);

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(256),
        max_shrink_iters: 1_000,
        ..ProptestConfig::default()
    })]

    /// **For every tail the scope can choose, the request's day record is the whole log's** (README gap 3583): the
    /// section `kernel_log::capacity_log_section` builds at today, after the loads `w` draws resealed the cache, is
    /// ANSWERED (never refused, README gap 4660), with today's record, the open block and the open interruption
    /// EQUAL, by value, to the answer to the whole log from line 1; and a resumed section's checkpoint never has a
    /// ledger day after today.
    #[test]
    fn the_planners_log_section_holds_today_whole_for_every_tail(w in world_strategy()) {
        let today_day = kernel_log::day_of(base() + Duration::days(i64::from(w.today())));
        let (lines, loads) = draw(&w);
        let a = ask(&w, &lines, &loads);
        let from = a.section["from"].as_u64().expect("from") as usize;
        let resumed = !a.section["ckpt"].is_null();
        let ledger = a.section["ckpt"]["ledgerDay"].as_u64();
        if resumed {
            prop_assert!(ledger.is_some_and(|l| l <= today_day),
                "a resumed section's ledger day {:?} is after today {}", ledger, today_day);
        } else {
            prop_assert_eq!(from, 1, "a section with no checkpoint reaches back to line 1");
        }
        let mine = day_entry(&a.got, today_day);
        let theirs = day_entry(&a.whole, today_day);
        prop_assert_eq!(&mine, &theirs, "today's record: the request's section is not the whole log's\nlog:\n{}", text_of(&lines, lines.len()));
        prop_assert_eq!(&a.got["open"]["block"], &a.whole["open"]["block"], "the open block: the request's section is not the whole log's");
        prop_assert_eq!(&a.got["open"]["interrupt"], &a.whole["open"]["interrupt"], "the open interruption: the request's section is not the whole log's");

        // The census: what the tail cut, by line number (`from` is the first line the tail sends).
        let before_cut = |p: &dyn Fn(&Drawn) -> bool| resumed && lines.iter().enumerate().any(|(i, l)| p(l) && i + 1 < from);
        let rec = theirs.as_ref().map(|d| d[1].clone()).unwrap_or(Value::Null);
        let open_id = a.whole["open"]["block"][0].as_str().map(str::to_string);
        let marks_open = |l: &Drawn| {
            open_id.as_ref().is_some_and(|id| {
                (l.text.contains("\"ev\":\"pause\"") || l.text.contains("\"ev\":\"unpause\""))
                    && l.text.contains(&format!("\"id\":\"{id}\""))
            })
        };
        let r = {
            let mut r = CENSUS.lock().unwrap_or_else(|p| p.into_inner());
            r[0] += 1;
            r[1] += u64::from(resumed);
            r[2] += u64::from(!rec.is_null());
            r[3] += u64::from(!rec.is_null() && !rec[14].is_null());
            r[4] += u64::from(before_cut(&|l: &Drawn| l.opens_block) && !a.whole["open"]["block"].is_null());
            r[5] += u64::from(before_cut(&|l: &Drawn| l.opens_int) && !a.whole["open"]["interrupt"].is_null());
            r[6] += u64::from(before_cut(&|l: &Drawn| l.today));
            r[7] += u64::from(!rec.is_null() && rec[22].as_array().is_some_and(|b| !b.is_empty()));
            r[8] += u64::from(!rec.is_null() && rec[10].as_array().is_some_and(|b| !b.is_empty()));
            r[9] += u64::from(resumed && !w.final_load);
            r[10] += u64::from(a.unasked_refused);
            r[11] += u64::from(!rec.is_null() && !rec[11].is_null());
            r[12] += u64::from(before_cut(&marks_open));
            r[13] += u64::from(before_cut(&|l: &Drawn| l.today && l.text.contains("\"ev\":\"wake\"")));
            *r
        };
        let generated: u64 = std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(256);
        if r[0] == generated {
            eprintln!(
                "kernel_request_today_whole census (gaps 3583, 4660): {} cases, {} resumed ({} from an earlier load's \
                 checkpoint), today with a record {} (an arrival {}, a break {}, segments {}), an open block begun \
                 before the cut {}, an interruption open across the cut {}, today's own lines folded into the \
                 checkpoint {} (its wake {}), a section the old rule would have sent REFUSED {}, today with a wake {}, a \
                 mark of the open block before the cut {}",
                r[0], r[1], r[9], r[2], r[3], r[7], r[8], r[4], r[5], r[6], r[13], r[10], r[11], r[12]
            );
            // **Floors** (AGENTS §9.2): a class compared on no case compares nothing.  Red is a finding about the
            // draw, re-run and reported (D46), never reverted.
            prop_assert!(r[1] * 2 > r[0], "fewer than half the sections resumed a checkpoint: {r:?}");
            prop_assert!(r[3] * 2 > r[0], "fewer than half the days compared held an arrival: {r:?}");
            prop_assert!(r[4] > 0, "no section cut an open block begun before its tail: {r:?}");
            prop_assert!(r[5] > 0, "no section cut an interruption open across its tail: {r:?}");
            prop_assert!(r[6] > 0, "no section held today's own lines in its checkpoint: {r:?}");
            prop_assert!(r[9] > 0, "no section resumed an earlier load's checkpoint (the TUI's): {r:?}");
            prop_assert!(r[10] > 0, "no drawn section was one the old rule sent refused (gap 4660): {r:?}");
            prop_assert!(r[12] > 0, "no section held a mark of the open block in its checkpoint: {r:?}");
            prop_assert!(r[13] > 0, "no section held today's wake in its checkpoint: {r:?}");
        }
    }
}

/// **README gap 4660's witness** — the arm's first failure, shrunk: `^b1x0` started on the 2nd with no energy
/// report and never ended, energy reports on the 3rd and 4th, a load on the 5th after the wake (genesis at the 5th
/// seals the 2nd: the ledger day is the 3rd), then `tm interrupt` at 15:00 — whose line closes the stretch begun on
/// the sealed 2nd.  The checkpoint the load left, resumed over the grown tail, is REFUSED (`sealedDay`, line 5, the
/// 2nd); the request's section is answered, and today's record and the open block are the whole log's.
#[test]
fn a_tail_that_names_a_day_the_process_checkpoint_sealed_is_rebuilt_not_refused() {
    let w = World {
        days: 5,
        skip: vec![false; 5],
        wake: vec![None, None, None, None, Some(0)],
        arrive: vec![0; 5],
        blocks: vec![0, 1, 0, 0, 0],
        marks: vec![0, 0, 8, 8, 0],
        open_block: Some(1),
        late_mark: 0,
        open_int: Some((4, None)),
        ahead: None,
        loads: vec![0, 0, 0, 0, 1],
        final_load: false,
        scope: 0,
    };
    let (lines, loads) = draw(&w);
    assert_eq!(lines.len(), 5, "{lines:?}");
    assert!(lines[4].text.contains("\"ev\":\"interrupt\""), "{lines:?}");
    assert_eq!(loads, vec![(4, 4)], "one load, after the 5th's wake");
    let a = ask(&w, &lines, &loads);
    assert!(a.unasked_refused, "the old rule's section must be the refused one, else this witness proves nothing");
    let today_day = kernel_log::day_of(base() + Duration::days(4));
    assert_eq!(day_entry(&a.got, today_day), day_entry(&a.whole, today_day));
    assert!(!a.whole["open"]["block"].is_null(), "the block is open in the whole log's answer");
    assert_eq!(a.got["open"]["block"], a.whole["open"]["block"]);
    assert_eq!(a.got["open"]["interrupt"], a.whole["open"]["interrupt"]);
}
